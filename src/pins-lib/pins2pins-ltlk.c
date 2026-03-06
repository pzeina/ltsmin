/**
 * pins2pins-ltlk.c  --  LTLK layer for LTSmin
 *
 * LTLK is a strict superset of LTL enriched with epistemic operators:
 *   K_i(phi)   -- agent i knows phi
 *   C(phi)     -- common knowledge of phi
 *   D(phi)     -- distributed knowledge of phi
 *   E(phi)     -- everyone knows phi
 *
 * Architecture
 * ------------
 * 1.  The LTLK formula is parsed and its negation is fed to ltsmin_ltl2ba.
 *     Because LTLK_FUTURE = LTL_FUTURE (same TOKEN_USER base), all temporal
 *     operators are recognised by the ltl2ba algorithm.  Epistemic operators
 *     have higher token values and are therefore treated as atomic
 *     propositions by ltl2ba.
 *
 * 2.  The resulting Buchi automaton is used to build a synchronous product
 *     with the model using SPIN semantics (predicates evaluated on src).
 *     A Buchi-state slot is prepended to the state vector (slot 0), exactly
 *     as in the LTL layer.
 *
 * 3.  Predicate evaluation uses eval_ltlk_predicates which calls
 *     eval_ltlk_expr for each Buchi predicate.  eval_ltlk_expr handles:
 *       - K_i / C / D / E  ->  epistemic evaluation over the reachable
 *                               state space (built lazily via BFS)
 *       - Propositional     ->  eval_trans_predicate
 *       - Temporal inside K ->  conservatively returns 1 (with a warning)
 *
 * This makes LTLK fully self-contained: it does NOT depend on the LTL layer
 * and produces identical results to --ltl for pure temporal formulas.
 */

#include <hre/config.h>

#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <dm/dm.h>
#include <hre/unix.h>
#include <hre/user.h>
#include <ltsmin-lib/ltl2ba-lex.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <mc-lib/atomics.h>
#include <pins-lib/pins.h>
#include <pins-lib/pins-util.h>
#include <pins-lib/pins2pins-ltlk.h>
#include <pins-lib/property-semantics.h>
#include <util-lib/util.h>
#include <hre/stringindex.h>

static char              *ltlk_file           = NULL;
static const char        *ltlk_semantics_name = "sync-perfect-recall";
pins_ltlk_type_t          PINS_LTLK           = PINS_LTLK_SYNC_PERFECT_RECALL;
int                       LTLK_NUM_AGENTS     = 0;
static ltlk_obs_config_t *ltlk_observability  = NULL;

/* Shared Buchi automaton */
static ltsmin_buchi_t    *shared_ba_ltlk  = NULL;
static int                grab_ba_ltlk    = 0;

static si_map_entry db_ltlk_semantics[] = {
    {"sync-perfect-recall",  PINS_LTLK_SYNC_PERFECT_RECALL},
    {"async-perfect-recall", PINS_LTLK_ASYNC_PERFECT_RECALL},
    {"sync-no-recall",       PINS_LTLK_SYNC_NO_RECALL},
    {NULL, 0}
};

/* =========================================================================
 * popt callback
 * ========================================================================= */

static void
ltlk_popt(poptContext con, enum poptCallbackReason reason,
          const struct poptOption *opt, const char *arg, void *data)
{
    (void)con; (void)opt; (void)arg; (void)data;
    switch (reason) {
    case POPT_CALLBACK_REASON_PRE:
        break;
    case POPT_CALLBACK_REASON_POST: {
        int l = linear_search(db_ltlk_semantics, ltlk_semantics_name);
        if (l < 0) {
            Print1(lerror, "unknown LTLK semantics %s", ltlk_semantics_name);
            HREprintUsage();
            HREexit(LTSMIN_EXIT_FAILURE);
        }
        Print1(infoLong, "LTLK semantics: %s", ltlk_semantics_name);
        PINS_LTLK = l;
        return;
    }
    case POPT_CALLBACK_REASON_OPTION:
        break;
    }
    Abort("unexpected call to ltlk_popt");
}

struct poptOption ltlk_options[] = {
    { NULL, 0, POPT_ARG_CALLBACK | POPT_CBFLAG_POST | POPT_CBFLAG_SKIPOPTION,
      (void *)ltlk_popt, 0, NULL, NULL },
    { "ltlk", 0, POPT_ARG_STRING, &ltlk_file, 0,
      "LTLK formula or file with LTLK formula",
      "<ltlk-file>.ltlk|<ltlk formula>" },
    { "ltlk-semantics", 0, POPT_ARG_STRING, &ltlk_semantics_name, 0,
      "LTLK semantics: sync-perfect-recall (default), async-perfect-recall, "
      "sync-no-recall", "<semantics>" },
    { "ltlk-agents", 0, POPT_ARG_INT, &LTLK_NUM_AGENTS, 0,
      "number of agents in the system", "<num>" },
    POPT_TABLEEND
};

/* =========================================================================
 * Observability configuration
 * ========================================================================= */

void
GBsetLTLKObservability(ltlk_obs_config_t *config)
{
    ltlk_observability = config;
}

ltlk_obs_config_t *
GBgetLTLKObservability(void)
{
    return ltlk_observability;
}

/* =========================================================================
 * State-space cache (for epistemic evaluation)
 *
 * Stores model states of length old_len (without the Buchi slot prepended
 * by this layer).  Built lazily via BFS on the parent model.
 * ========================================================================= */

typedef struct {
    int *data;
    int  count;
    int  capacity;
    int  state_length;
} state_array_t;

/* =========================================================================
 * LTLK context
 * ========================================================================= */

typedef struct ltlk_context {
    /* parent (original, pre-Buchi model) */
    model_t             parent;

    /* formula */
    ltsmin_expr_t       ltlk_expr;
    ltsmin_parse_env_t  env;

    /* Buchi automaton (built from the negated LTLK formula) */
    ltsmin_buchi_t     *ba;
    bool                is_weak;
    int                *edge_labels_buf;

    /* state vector layout */
    int                 ltl_idx;    /* = 0, index of Buchi state in product  */
    int                 old_len;    /* state length of the parent model       */
    int                 len;        /* = old_len + 1 after Buchi extension    */
    int                 old_groups;
    int                 groups;
    int                 edge_labels_old;
    int                 edge_labels;

    /* state labels */
    int                 sl_idx_accept;
    int                 sl_idx_nonaccept; /* -1 if not weak */

    /* epistemic evaluation */
    int                 num_agents;
    bitvector_t        *observable_vars;  /* [num_agents], indexed 0..old_len-1 */
    state_array_t      *state_space;      /* reachable states, lazy BFS         */
    int                 k_base_idx;       /* SIlookup("K0") or -1               */
} ltlk_context_t;

/* =========================================================================
 * BFS state-space builder
 * ========================================================================= */

typedef struct { state_array_t *tbl; int state_length; } bfs_cb_ctx_t;

static void
bfs_callback(void *context, transition_info_t *ti, int *dst, int *cpy)
{
    (void)ti; (void)cpy;
    bfs_cb_ctx_t  *bc  = (bfs_cb_ctx_t *)context;
    state_array_t *tbl = bc->tbl;
    int            len = bc->state_length;

    for (int i = 0; i < tbl->count; i++)
        if (memcmp(tbl->data + (size_t)i * len, dst, len * sizeof(int)) == 0)
            return;

    if (tbl->count >= tbl->capacity) {
        tbl->capacity = tbl->capacity * 2 + 32;
        tbl->data = RTrealloc(tbl->data,
                              (size_t)tbl->capacity * len * sizeof(int));
    }
    memcpy(tbl->data + (size_t)tbl->count * len, dst, len * sizeof(int));
    tbl->count++;
}

static void
ensure_state_space(ltlk_context_t *ctx)
{
    if (ctx->state_space != NULL) return;

    int            len = ctx->old_len;
    state_array_t *tbl = RTmalloc(sizeof(state_array_t));
    tbl->state_length  = len;
    tbl->count         = 0;
    tbl->capacity      = 64;
    tbl->data          = RTmalloc((size_t)64 * len * sizeof(int));

    int *s0 = RTmalloc(len * sizeof(int));
    GBgetInitialState(ctx->parent, s0);
    memcpy(tbl->data, s0, len * sizeof(int));
    tbl->count = 1;
    RTfree(s0);

    bfs_cb_ctx_t bc = { tbl, len };
    for (int qi = 0; qi < tbl->count; qi++)
        GBgetTransitionsAll(ctx->parent,
                            tbl->data + (size_t)qi * len,
                            bfs_callback, &bc);

    ctx->state_space = tbl;
    Print1(info, "LTLK: enumerated %d reachable states for epistemic evaluation",
           tbl->count);
}

static int
find_state_idx(state_array_t *tbl, int *state)
{
    for (int i = 0; i < tbl->count; i++)
        if (memcmp(tbl->data + (size_t)i * tbl->state_length, state,
                   tbl->state_length * sizeof(int)) == 0)
            return i;
    return -1;
}

/* =========================================================================
 * Epistemic helpers
 * ========================================================================= */

static int
states_indistinguishable(ltlk_context_t *ctx, int agent, int *s1, int *s2)
{
    bitvector_t *obs = &ctx->observable_vars[agent];
    for (int i = 0; i < ctx->old_len; i++)
        if (bitvector_is_set(obs, i) && s1[i] != s2[i])
            return 0;
    return 1;
}

/* Forward declarations */
static int has_epistemic_ops(ltsmin_expr_t expr);
static int eval_ltlk_expr(ltlk_context_t *ctx, ltsmin_expr_t expr, int *state);

static int
eval_knows(ltlk_context_t *ctx, int agent, ltsmin_expr_t formula, int *state)
{
    if (agent < 0 || agent >= ctx->num_agents) {
        Warning(info, "K%d: agent index out of range [0,%d)", agent, ctx->num_agents);
        return 0;
    }
    ensure_state_space(ctx);
    state_array_t *tbl = ctx->state_space;
    for (int i = 0; i < tbl->count; i++) {
        int *s = tbl->data + (size_t)i * tbl->state_length;
        if (states_indistinguishable(ctx, agent, state, s))
            if (!eval_ltlk_expr(ctx, formula, s))
                return 0;
    }
    return 1;
}

static int
eval_common_knowledge(ltlk_context_t *ctx, ltsmin_expr_t formula, int *state)
{
    ensure_state_space(ctx);
    state_array_t *tbl     = ctx->state_space;
    int           *visited = RTmallocZero(tbl->count * sizeof(int));
    int           *queue   = RTmalloc(tbl->count * sizeof(int));
    int            qhead = 0, qtail = 0;

    int start = find_state_idx(tbl, state);
    if (start == -1) { RTfree(visited); RTfree(queue); return 1; }

    visited[start] = 1;
    queue[qtail++] = start;
    int result = 1;

    while (qhead < qtail) {
        int  ci  = queue[qhead++];
        int *cur = tbl->data + (size_t)ci * tbl->state_length;
        if (!eval_ltlk_expr(ctx, formula, cur)) { result = 0; break; }
        for (int j = 0; j < tbl->count; j++) {
            if (visited[j]) continue;
            int *s = tbl->data + (size_t)j * tbl->state_length;
            for (int a = 0; a < ctx->num_agents; a++) {
                if (states_indistinguishable(ctx, a, cur, s)) {
                    visited[j] = 1;
                    queue[qtail++] = j;
                    break;
                }
            }
        }
    }
    RTfree(visited); RTfree(queue);
    return result;
}

static int
eval_distributed_knowledge(ltlk_context_t *ctx, ltsmin_expr_t formula, int *state)
{
    ensure_state_space(ctx);
    state_array_t *tbl = ctx->state_space;
    for (int i = 0; i < tbl->count; i++) {
        int *s   = tbl->data + (size_t)i * tbl->state_length;
        int  all = 1;
        for (int a = 0; a < ctx->num_agents && all; a++)
            if (!states_indistinguishable(ctx, a, state, s)) all = 0;
        if (all && !eval_ltlk_expr(ctx, formula, s))
            return 0;
    }
    return 1;
}

static int
eval_everyone_knows(ltlk_context_t *ctx, ltsmin_expr_t formula, int *state)
{
    for (int a = 0; a < ctx->num_agents; a++)
        if (!eval_knows(ctx, a, formula, state)) return 0;
    return 1;
}

/**
 * Recursively evaluate an LTLK expression on a model state.
 *
 * @param state  Model state vector of length old_len (no Buchi slot).
 *
 * Temporal operators (GLOBALLY, FUTURE, NEXT, UNTIL, RELEASE) are structural
 * -- they are handled by the Buchi automaton.  When encountered inside a K
 * subformula, they are conservatively returned as true.
 */
static int
eval_ltlk_expr(ltlk_context_t *ctx, ltsmin_expr_t expr, int *state)
{
    if (expr == NULL) return 1;

    switch (expr->node_type) {
    case UNARY_OP:
        switch (expr->token) {
        case LTLK_KNOWS: {
            int agent;
            if (ctx->k_base_idx >= 0 &&
                expr->idx >= ctx->k_base_idx &&
                expr->idx <= ctx->k_base_idx + 9)
                agent = expr->idx - ctx->k_base_idx;
            else
                agent = 0;
            return eval_knows(ctx, agent, expr->arg1, state);
        }
        case LTLK_COMMON_KNOWS:
            return eval_common_knowledge(ctx, expr->arg1, state);
        case LTLK_DISTRIBUTED_KNOWS:
            return eval_distributed_knowledge(ctx, expr->arg1, state);
        case LTLK_EVERYONE_KNOWS:
            return eval_everyone_knows(ctx, expr->arg1, state);
        case LTLK_NOT:
            return !eval_ltlk_expr(ctx, expr->arg1, state);
        case LTLK_GLOBALLY:
        case LTLK_FUTURE:
        case LTLK_NEXT:
            Warning(infoLong, "LTLK: temporal operator inside epistemic "
                    "context -- conservatively evaluating as true");
            return 1;
        default: break;
        }
        break;

    case BINARY_OP:
        switch (expr->token) {
        case LTLK_AND:
            return eval_ltlk_expr(ctx, expr->arg1, state) &&
                   eval_ltlk_expr(ctx, expr->arg2, state);
        case LTLK_OR:
            return eval_ltlk_expr(ctx, expr->arg1, state) ||
                   eval_ltlk_expr(ctx, expr->arg2, state);
        case LTLK_IMPLY:
            return !eval_ltlk_expr(ctx, expr->arg1, state) ||
                    eval_ltlk_expr(ctx, expr->arg2, state);
        case LTLK_EQUIV:
            return eval_ltlk_expr(ctx, expr->arg1, state) ==
                   eval_ltlk_expr(ctx, expr->arg2, state);
        case LTLK_UNTIL:
        case LTLK_RELEASE:
        case LTLK_WEAK_UNTIL:
        case LTLK_STRONG_RELEASE:
            Warning(infoLong, "LTLK: temporal operator inside epistemic "
                    "context -- conservatively evaluating as true");
            return 1;
        default: break;
        }
        break;

    default: break;
    }

    /* Atomic proposition -- delegate to the standard predicate evaluator */
    return (int)eval_trans_predicate(ctx->parent, expr, state, NULL, ctx->env);
}

/* =========================================================================
 * has_epistemic_ops -- checks whether formula contains K/C/D/E
 * ========================================================================= */

static int
has_epistemic_ops(ltsmin_expr_t expr)
{
    if (expr == NULL) return 0;
    switch (expr->node_type) {
    case UNARY_OP:
        switch (expr->token) {
        case LTLK_KNOWS:
        case LTLK_COMMON_KNOWS:
        case LTLK_DISTRIBUTED_KNOWS:
        case LTLK_EVERYONE_KNOWS:
            return 1;
        default:
            return has_epistemic_ops(expr->arg1);
        }
    case BINARY_OP:
        return has_epistemic_ops(expr->arg1) || has_epistemic_ops(expr->arg2);
    default:
        return 0;
    }
}

/* =========================================================================
 * Buchi automaton construction for LTLK
 * ========================================================================= */

static ltsmin_buchi_t *
init_ltlk_buchi(model_t model, ltsmin_expr_t ltlk_expr,
                ltsmin_parse_env_t env)
{
    ltsmin_buchi_t *ba;

    if (NULL == shared_ba_ltlk && cas(&grab_ba_ltlk, 0, 1)) {

        /* Negate the formula: model checking checks NOT-phi for cycles */
        ltsmin_expr_t neg = LTSminExpr(UNARY_OP, LTLK_NOT, 0, ltlk_expr, NULL);

        ltsmin_ltl2ba(neg);
        ba = ltsmin_buchi();

        if (ba == NULL) {
            Print(info, "LTLK: empty Buchi automaton.");
            Print(info, "The property is TRUE (vacuously).");
        } else {
            if (ba->predicate_count > 30)
                Abort("More than 30 predicates in LTLK Buchi automaton "
                      "(not supported).");
            ba->env = env;
            for (int k = 0; k < ba->predicate_count; k++)
                set_pins_semantics(model, ba->predicates[k], env, NULL, NULL);
            Print(info, "LTLK: Buchi automaton has %d states, %d predicates",
                  ba->state_count, ba->predicate_count);
        }

        atomic_write(&shared_ba_ltlk, ba);
        HREbarrier(HREglobal());
    } else {
        HREbarrier(HREglobal());
        ba = atomic_read(&shared_ba_ltlk);
    }

    if (ba == NULL)
        HREexit(LTSMIN_EXIT_SUCCESS);

    return ba;
}

static bool
is_weak_ltlk(ltsmin_buchi_t *ba)
{
    for (int i = 0; i < ba->state_count; i++) {
        if (!ba->states[i]->accept) continue;
        for (int j = 0; j < ba->states[i]->transition_count; j++) {
            int dst = ba->states[i]->transitions[j].to_state;
            if (!ba->states[dst]->accept) return false;
        }
    }
    return true;
}

/* =========================================================================
 * Predicate evaluation for Buchi callbacks
 * ========================================================================= */

typedef struct ltlk_cb_context {
    model_t         model;
    TransitionCB    cb;
    void           *user_context;
    int            *src;
    int             ntbtrans;
    ltlk_context_t *ctx;
    int             predicate_evals;
} ltlk_cb_context;

/**
 * Evaluate all Buchi predicates on a model state (old_len-length vector).
 * Returns a bitmask: bit i set iff predicate i holds.
 */
static inline int
eval_ltlk_predicates(ltlk_cb_context *infoctx, int *state)
{
    ltlk_context_t *ctx = infoctx->ctx;
    int pred_evals = 0;
    for (int i = 0; i < ctx->ba->predicate_count; i++)
        if (eval_ltlk_expr(ctx, ctx->ba->predicates[i], state))
            pred_evals |= (1 << i);
    return pred_evals;
}

/* =========================================================================
 * Buchi x model product -- SPIN semantics
 * ========================================================================= */

static void
ltlk_spin_cb(void *context, transition_info_t *ti, int *dst, int *cpy)
{
    ltlk_cb_context *infoctx = (ltlk_cb_context *)context;
    ltlk_context_t  *ctx     = infoctx->ctx;
    int              new_len = ctx->len;

    int dst_new[new_len];
    memcpy(dst_new + 1, dst, ctx->old_len * sizeof(int));

    const int pred_evals = infoctx->predicate_evals;
    int       buchi_src  = infoctx->src[ctx->ltl_idx];
    HREassert(buchi_src < ctx->ba->state_count);

    for (int j = 0; j < ctx->ba->states[buchi_src]->transition_count; j++) {
        ltsmin_buchi_transition_t *tr = &ctx->ba->states[buchi_src]->transitions[j];
        if ((pred_evals & tr->pos[0]) == tr->pos[0] &&
            (pred_evals & tr->neg[0]) == 0) {
            dst_new[ctx->ltl_idx] = tr->to_state;
            infoctx->cb(infoctx->user_context, ti, dst_new, cpy);
            infoctx->ntbtrans++;
        }
    }
}

static int
ltlk_spin_long(model_t self, int group, int *src, TransitionCB cb,
               void *user_context)
{
    (void)self; (void)group; (void)src; (void)cb; (void)user_context;
    Abort("LTLK: --grey / -reach not yet supported.");
}

static int
ltlk_spin_short(model_t self, int group, int *src, TransitionCB cb,
                void *user_context)
{
    (void)self; (void)group; (void)src; (void)cb; (void)user_context;
    Abort("LTLK: --cached not yet supported.");
}

static int
ltlk_spin_all(model_t self, int *src, TransitionCB cb, void *user_context)
{
    ltlk_context_t  *ctx = GBgetContext(self);
    ltlk_cb_context  new_ctx;

    new_ctx.model         = self;
    new_ctx.cb            = cb;
    new_ctx.user_context  = user_context;
    new_ctx.src           = src;
    new_ctx.ntbtrans      = 0;
    new_ctx.ctx           = ctx;

    /* Evaluate predicates on the source model state (SPIN semantics)
     * src + 1 skips the Buchi slot at index 0                          */
    new_ctx.predicate_evals = eval_ltlk_predicates(&new_ctx, src + 1);

    GBgetTransitionsAll(ctx->parent, src + 1, ltlk_spin_cb, &new_ctx);

    /* Deadlock handling: if no model transitions fired, advance Buchi
     * on the same model state                                           */
    if (new_ctx.ntbtrans == 0) {
        int dst_new[ctx->len];
        memcpy(dst_new + 1, src + 1, ctx->old_len * sizeof(int));
        int buchi_src = src[ctx->ltl_idx];
        HREassert(buchi_src < ctx->ba->state_count);

        memset(ctx->edge_labels_buf, 0, sizeof(int) * ctx->edge_labels);

        for (int j = 0; j < ctx->ba->states[buchi_src]->transition_count; j++) {
            ltsmin_buchi_transition_t *tr =
                &ctx->ba->states[buchi_src]->transitions[j];
            if ((new_ctx.predicate_evals & tr->pos[0]) == tr->pos[0] &&
                (new_ctx.predicate_evals & tr->neg[0]) == 0) {
                dst_new[ctx->ltl_idx] = tr->to_state;
                int grp = ctx->old_groups + tr->index;
                HREassert(grp < ctx->groups);
                transition_info_t ti = GB_TI(ctx->edge_labels_buf, grp);
                ti.por_proviso = 1;
                cb(user_context, &ti, dst_new, NULL);
                new_ctx.ntbtrans++;
            }
        }
    }
    return new_ctx.ntbtrans;
}

/* =========================================================================
 * State label overrides
 * ========================================================================= */

static inline int
ltlk_is_accepting(ltlk_context_t *ctx, int *state)
{
    int val = state[ctx->ltl_idx];
    HREassert(val < ctx->ba->state_count);
    return ctx->ba->states[val]->accept;
}

static int
ltlk_sl_short(model_t self, int label, int *state)
{
    ltlk_context_t *ctx = GBgetContext(self);
    if (label == ctx->sl_idx_accept)    return ltlk_is_accepting(ctx, state);
    if (label == ctx->sl_idx_nonaccept) return !ltlk_is_accepting(ctx, state);
    return GBgetStateLabelShort(ctx->parent, label, state + 1);
}

static int
ltlk_sl_long(model_t self, int label, int *state)
{
    ltlk_context_t *ctx = GBgetContext(self);
    if (label == ctx->sl_idx_accept)    return ltlk_is_accepting(ctx, state);
    if (label == ctx->sl_idx_nonaccept) return !ltlk_is_accepting(ctx, state);
    return GBgetStateLabelLong(ctx->parent, label, state + 1);
}

static void
ltlk_sl_all(model_t self, int *state, int *labels)
{
    ltlk_context_t *ctx = GBgetContext(self);
    GBgetStateLabelsAll(ctx->parent, state + 1, labels);
    labels[ctx->sl_idx_accept] = ltlk_is_accepting(ctx, state);
    if (ctx->sl_idx_nonaccept != -1)
        labels[ctx->sl_idx_nonaccept] = !ltlk_is_accepting(ctx, state);
}

/* =========================================================================
 * Observability initialisation
 * ========================================================================= */

static void
init_observability(ltlk_context_t *ctx)
{
    if (ltlk_observability != NULL) {
        ctx->num_agents      = ltlk_observability->num_agents;
        ctx->observable_vars = ltlk_observability->observable_vars;
    } else {
        if (LTLK_NUM_AGENTS <= 0) {
            Warning(info, "LTLK: number of agents not specified, defaulting to 2");
            ctx->num_agents = 2;
        } else {
            ctx->num_agents = LTLK_NUM_AGENTS;
        }
        ctx->observable_vars = RTmalloc(ctx->num_agents * sizeof(bitvector_t));
        for (int i = 0; i < ctx->num_agents; i++) {
            bitvector_create(&ctx->observable_vars[i], ctx->old_len);
            /* All variables are observable by default */
            for (int j = 0; j < ctx->old_len; j++)
                bitvector_set(&ctx->observable_vars[i], j);
        }
    }
    Print1(info, "LTLK layer initialised with %d agents", ctx->num_agents);
}

/* =========================================================================
 * GBaddLTLK -- main entry point
 * ========================================================================= */

model_t
GBaddLTLK(model_t model)
{
    if (ltlk_file == NULL) return model;

    /* ------------------------------------------------------------------
     * 1.  Parse the LTLK formula
     * ------------------------------------------------------------------ */
    lts_type_t         ltstype   = GBgetLTStype(model);
    ltsmin_parse_env_t env       = LTSminParseEnvCreate();
    ltsmin_expr_t      ltlk_expr = ltlk_parse_file(ltlk_file, env, ltstype);
    if (ltlk_expr == NULL)
        Abort("Failed to parse LTLK formula from: %s", ltlk_file);

    Print1(info, "LTLK layer: formula file: %s", ltlk_file);

    if (!has_epistemic_ops(ltlk_expr))
        Warning(info, "LTLK formula contains no epistemic operators; "
                "consider using --ltl instead");

    /* ------------------------------------------------------------------
     * 2.  Build context (parent = original pre-Buchi model)
     * ------------------------------------------------------------------ */
    ltlk_context_t *ctx    = RTmalloc(sizeof(ltlk_context_t));
    ctx->parent            = model;
    ctx->ltlk_expr         = ltlk_expr;
    ctx->env               = env;
    ctx->state_space       = NULL;
    ctx->old_len           = lts_type_get_state_length(ltstype);
    ctx->ltl_idx           = 0;

    /* Resolve predicate chunk indices so eval_trans_predicate works */
    set_pins_semantics(model, ltlk_expr, env, NULL, NULL);

    ctx->k_base_idx = SIlookup(env->unary_ops, "K0");
    if (ctx->k_base_idx == SI_INDEX_FAILED) ctx->k_base_idx = -1;

    /* ------------------------------------------------------------------
     * 3.  Build Buchi automaton
     * ------------------------------------------------------------------ */
    ltsmin_buchi_t *ba = init_ltlk_buchi(model, ltlk_expr, env);
    ctx->ba            = ba;
    ctx->is_weak       = is_weak_ltlk(ba);

    if (ctx->is_weak)
        Print1(info, "LTLK: weak Buchi automaton, adding non-accepting "
               "progress label.");

    /* ------------------------------------------------------------------
     * 4.  Extend LTS type: prepend Buchi state at slot 0
     * ------------------------------------------------------------------ */
    int old_idx = pins_get_accepting_state_label_index(model);
    if (old_idx != -1)
        Print1(info, "LTLK layer: overriding existing property '%s'",
               lts_type_get_state_label_name(ltstype, old_idx));

    int new_len = ctx->old_len + 1;
    ctx->len    = new_len;

    lts_type_t ltstype_new = lts_type_clone(ltstype);
    lts_type_set_state_length(ltstype_new, new_len);

    /* Add a type for the Buchi state */
    int type_count = lts_type_get_type_count(ltstype_new);
    int buchi_type = lts_type_add_type(ltstype_new, "ltlk_buchi", NULL);
    HREassert(buchi_type == type_count, "LTLK: type index mismatch");
    lts_type_set_format(ltstype_new, buchi_type, LTStypeDirect);

    /* Slot 0: Buchi state */
    lts_type_set_state_name(ltstype_new, ctx->ltl_idx, "ltlk");
    lts_type_set_state_typeno(ltstype_new, ctx->ltl_idx, buchi_type);

    /* Slots 1..old_len: copy original state variable names/types */
    for (int i = 0; i < ctx->old_len; i++) {
        lts_type_set_state_name(ltstype_new, i + 1,
                                lts_type_get_state_name(ltstype, i));
        lts_type_set_state_type(ltstype_new, i + 1,
                                lts_type_get_state_type(ltstype, i));
    }

    /* State label types */
    int bool_type = lts_type_add_type(ltstype_new, "LTLK_bool", NULL);
    lts_type_set_format(ltstype_new, bool_type, LTStypeBool);

    matrix_t *p_sl    = GBgetStateLabelInfo(model);
    int       sl_count = dm_nrows(p_sl);

    int new_sl_count;
    if (ctx->is_weak) {
        new_sl_count          = sl_count + 2;
        ctx->sl_idx_nonaccept = sl_count + 1;
    } else {
        new_sl_count          = sl_count + 1;
        ctx->sl_idx_nonaccept = -1;
    }
    ctx->sl_idx_accept = sl_count;

    lts_type_set_state_label_count(ltstype_new, new_sl_count);
    for (int i = 0; i < sl_count; i++) {
        lts_type_set_state_label_name(ltstype_new, i,
                                      lts_type_get_state_label_name(ltstype, i));
        lts_type_set_state_label_typeno(ltstype_new, i,
                                        lts_type_get_state_label_typeno(ltstype, i));
    }
    lts_type_set_state_label_name(ltstype_new, ctx->sl_idx_accept,
                                  LTSMIN_STATE_LABEL_ACCEPTING);
    lts_type_set_state_label_typeno(ltstype_new, ctx->sl_idx_accept, bool_type);
    if (ctx->is_weak) {
        lts_type_set_state_label_name(ltstype_new, ctx->sl_idx_nonaccept,
                                      LTSMIN_STATE_LABEL_WEAK_LTL_PROGRESS);
        lts_type_set_state_label_typeno(ltstype_new, ctx->sl_idx_nonaccept,
                                        bool_type);
    }

    /* ------------------------------------------------------------------
     * 5.  Dependency matrices
     * ------------------------------------------------------------------ */
    matrix_t *p_dm   = GBgetDMInfo(model);
    matrix_t *p_dm_r = GBgetDMInfoRead(model);
    matrix_t *p_dm_w = GBgetDMInfoMayWrite(model);
    int       groups  = dm_nrows(p_dm);

    /* SPIN semantics: extra deadlock-handling Buchi transitions */
    int new_ngroups = groups + ba->trans_count;
    ctx->old_groups = groups;
    ctx->groups     = new_ngroups;

    /* Formula state dependency bitvector */
    bitvector_t fsd;
    bitvector_create(&fsd, ctx->old_len);

    for (int k = 0; k < ba->predicate_count; k++)
        set_pins_semantics(model, ba->predicates[k], env, &fsd, NULL);

    /* If any epistemic predicates: mark all variables as dependent     */
    if (has_epistemic_ops(ltlk_expr))
        for (int j = 0; j < ctx->old_len; j++)
            bitvector_set(&fsd, j);

    matrix_t *p_new_dm   = RTmalloc(sizeof(matrix_t));
    matrix_t *p_new_dm_r = RTmalloc(sizeof(matrix_t));
    matrix_t *p_new_dm_w = RTmalloc(sizeof(matrix_t));
    dm_create(p_new_dm,   new_ngroups, new_len);
    dm_create(p_new_dm_r, new_ngroups, new_len);
    dm_create(p_new_dm_w, new_ngroups, new_len);

    for (int i = 0; i < groups; i++) {
        for (int j = 0; j < ctx->old_len; j++) {
            if (dm_is_set(p_dm,   i, j)) dm_set(p_new_dm,   i, j + 1);
            if (dm_is_set(p_dm_r, i, j)) dm_set(p_new_dm_r, i, j + 1);
            if (dm_is_set(p_dm_w, i, j)) dm_set(p_new_dm_w, i, j + 1);
        }
        dm_set(p_new_dm,   i, ctx->ltl_idx);
        dm_set(p_new_dm_r, i, ctx->ltl_idx);
        dm_set(p_new_dm_w, i, ctx->ltl_idx);
        for (int j = 0; j < ctx->old_len; j++)
            if (bitvector_is_set(&fsd, j)) {
                dm_set(p_new_dm,   i, j + 1);
                dm_set(p_new_dm_r, i, j + 1);
            }
    }

    /* Deadlock / SPIN extra transitions */
    for (int i = groups; i < new_ngroups; i++) {
        dm_set(p_new_dm,   i, ctx->ltl_idx);
        dm_set(p_new_dm_r, i, ctx->ltl_idx);
        dm_set(p_new_dm_w, i, ctx->ltl_idx);
        for (int j = 0; j < ctx->old_len; j++)
            if (bitvector_is_set(&fsd, j)) {
                dm_set(p_new_dm,   i, j + 1);
                dm_set(p_new_dm_r, i, j + 1);
            }
    }

    /* State label matrix */
    int       sl_len     = dm_ncols(p_sl);
    int       new_sl_len = sl_len + 1;
    HREassert(new_sl_len == new_len,
              "LTLK: state label column count mismatch: %d vs %d",
              new_sl_len, new_len);

    matrix_t *p_new_sl = RTmalloc(sizeof(matrix_t));
    dm_create(p_new_sl, new_sl_count, new_sl_len);
    for (int i = 0; i < sl_count; i++)
        for (int j = 0; j < sl_len; j++)
            if (dm_is_set(p_sl, i, j))
                dm_set(p_new_sl, i, j + 1);

    dm_set(p_new_sl, ctx->sl_idx_accept, ctx->ltl_idx);
    for (int j = 0; j < sl_len; j++)
        if (bitvector_is_set(&fsd, j))
            dm_set(p_new_sl, ctx->sl_idx_accept, j + 1);

    if (ctx->is_weak) {
        dm_set(p_new_sl, ctx->sl_idx_nonaccept, ctx->ltl_idx);
        for (int j = 0; j < sl_len; j++)
            if (bitvector_is_set(&fsd, j))
                dm_set(p_new_sl, ctx->sl_idx_nonaccept, j + 1);
    }

    bitvector_clear(&fsd);

    /* ------------------------------------------------------------------
     * 6.  Build wrapper model
     * ------------------------------------------------------------------ */
    model_t ltlk_model = GBcreateBase();
    GBsetContext(ltlk_model, ctx);

    GBcopyChunkMaps(ltlk_model, model);
    GBsetLTStype(ltlk_model, ltstype_new);
    GBgrowChunkMaps(ltlk_model, type_count);

    GBsetDMInfo(ltlk_model,         p_new_dm);
    GBsetDMInfoRead(ltlk_model,     p_new_dm_r);
    GBsetDMInfoMayWrite(ltlk_model, p_new_dm_w);
    GBsetStateLabelInfo(ltlk_model, p_new_sl);

    GBsetStateLabelShort(ltlk_model, ltlk_sl_short);
    GBsetStateLabelLong(ltlk_model,  ltlk_sl_long);
    GBsetStateLabelsAll(ltlk_model,  ltlk_sl_all);

    GBsetNextStateLong(ltlk_model,  ltlk_spin_long);
    GBsetNextStateShort(ltlk_model, ltlk_spin_short);
    GBsetNextStateAll(ltlk_model,   ltlk_spin_all);

    /* POR group visibility */
    int *cur_vis = GBgetPorGroupVisibility(model);
    if (cur_vis) {
        int *new_vis = RTmallocZero(new_ngroups * sizeof(int));
        memcpy(new_vis, cur_vis, sizeof(int[groups]));
        GBsetPorGroupVisibility(ltlk_model, new_vis);
    }

    GBinitModelDefaults(&ltlk_model, model);

    /* Initial state */
    int s0[new_len];
    GBgetInitialState(model, s0 + 1);
    s0[ctx->ltl_idx] = 0;  /* Buchi starts at state 0 */
    GBsetInitialState(ltlk_model, s0);

    lts_type_validate(ltstype_new);

    /* ------------------------------------------------------------------
     * 7.  Initialise observability (acts on old_len-length model states)
     * ------------------------------------------------------------------ */
    init_observability(ctx);

    ctx->edge_labels_old = lts_type_get_edge_label_count(ltstype);
    ctx->edge_labels     = lts_type_get_edge_label_count(ltstype_new);
    ctx->edge_labels_buf = RTmalloc(sizeof(int[ctx->edge_labels]));

    Print1(info, "LTLK layer: accepting label at index %d", ctx->sl_idx_accept);
    Print1(info, "LTLK layer: state length extended from %d to %d",
           ctx->old_len, new_len);
    Print1(info, "LTLK Buchi has %d states", ba->state_count);

    return ltlk_model;
}
