#include <hre/config.h>

#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <dm/dm.h>
#include <hre/stringindex.h>
#include <hre/unix.h>
#include <hre/user.h>
#include <ltsmin-lib/ltl2ba-lex.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <ltsmin-lib/ltsmin-buchi.h>
#include <ltsmin-lib/ltsmin-syntax.h>
#include <mc-lib/atomics.h>
#include <pins-lib/knowledge.h>
#include <pins-lib/pins-util.h>
#include <pins-lib/pins2pins-ltlk.h>
#include <pins-lib/property-semantics.h>
#include <util-lib/util.h>

static char              *ltlk_file       = NULL;
static const char        *ltlk_semantics  = "sync-perfect-recall";
pins_ltlk_type_t          PINS_LTLK       = PINS_LTLK_SYNC_PERFECT_RECALL;
int                       LTLK_NUM_AGENTS = 0;
static ltlk_obs_config_t *ltlk_obs        = NULL;

static ltsmin_buchi_t    *shared_ba_ltlk = NULL;
static int                grab_ba_ltlk   = 0;

static si_map_entry db_ltlk_semantics[] = {
    {"sync-perfect-recall", PINS_LTLK_SYNC_PERFECT_RECALL},
    {NULL, 0}
};

typedef struct ltlk_context {
    model_t             parent;
    ltsmin_expr_t       ltlk_expr;
    ltsmin_parse_env_t  env;

    ltsmin_buchi_t     *ba;
    bool                is_weak;

    int                 ltl_idx;
    int                 old_len;
    int                 len;
    int                 old_groups;
    int                 groups;

    int                 old_edge_labels;
    int                 edge_labels;
    int                *edge_labels_buf;

    int                 sl_idx_accept;
    int                 sl_idx_nonaccept;

    int                 num_agents;
    bitvector_t        *observable_vars;
    int                 know_idx;
    int                 k_base_idx;

    knowledge_mgr_t    *knowledge;

     /* companion Büchi automata – one entry per outer BA predicate         */
     /* (NULL.ba means the predicate is plain propositional, not a K-atom) */
     k_atom_companion_t *k_atoms;
     int                 k_atoms_count; /* = ba->predicate_count            */
} ltlk_context_t;

typedef struct ltlk_cb_context {
    model_t         model;
    TransitionCB    cb;
    void           *user_context;
    int            *src;
    int             ntbtrans;
    ltlk_context_t *ctx;
    int             predicate_evals;
} ltlk_cb_context_t;

static void
ltlk_popt(poptContext con, enum poptCallbackReason reason,
          const struct poptOption *opt, const char *arg, void *data)
{
    (void)con; (void)opt; (void)arg; (void)data;
    switch (reason) {
    case POPT_CALLBACK_REASON_PRE:
        break;
    case POPT_CALLBACK_REASON_POST: {
        int l = linear_search(db_ltlk_semantics, ltlk_semantics);
        if (l < 0) {
            Print1(lerror, "unknown LTLK semantics %s", ltlk_semantics);
            HREprintUsage();
            HREexit(LTSMIN_EXIT_FAILURE);
        }
        PINS_LTLK = l;
        break;
    }
    case POPT_CALLBACK_REASON_OPTION:
        break;
    }
}

struct poptOption ltlk_options[] = {
    { NULL, 0, POPT_ARG_CALLBACK | POPT_CBFLAG_POST | POPT_CBFLAG_SKIPOPTION,
      (void *)ltlk_popt, 0, NULL, NULL },
    { "ltlk", 0, POPT_ARG_STRING, &ltlk_file, 0,
      "LTLK formula or file with LTLK formula",
      "<ltlk-file>.ltlk|<ltlk formula>" },
    { "ltlk-semantics", 0, POPT_ARG_STRING, &ltlk_semantics, 0,
      "LTLK semantics (currently only sync-perfect-recall)",
      "<sync-perfect-recall>" },
    { "ltlk-agents", 0, POPT_ARG_INT, &LTLK_NUM_AGENTS, 0,
      "number of agents", "<num>" },
    POPT_TABLEEND
};

void
GBsetLTLKObservability(ltlk_obs_config_t *config)
{
    ltlk_obs = config;
}

ltlk_obs_config_t *
GBgetLTLKObservability(void)
{
    return ltlk_obs;
}

static int
is_accepting(ltlk_context_t *ctx, int *state)
{
    int b = state[ctx->ltl_idx];
    HREassert(b < ctx->ba->state_count);
    return ctx->ba->states[b]->accept;
}

static int
ltlk_sl_short(model_t self, int label, int *state)
{
    ltlk_context_t *ctx = GBgetContext(self);
    if (label == ctx->sl_idx_accept) {
        return is_accepting(ctx, state);
    } else if (label == ctx->sl_idx_nonaccept) {
        return !is_accepting(ctx, state);
    }
    return GBgetStateLabelShort(ctx->parent, label, state + 1);
}

static int
ltlk_sl_long(model_t self, int label, int *state)
{
    ltlk_context_t *ctx = GBgetContext(self);
    if (label == ctx->sl_idx_accept) {
        return is_accepting(ctx, state);
    } else if (label == ctx->sl_idx_nonaccept) {
        return !is_accepting(ctx, state);
    }
    return GBgetStateLabelLong(ctx->parent, label, state + 1);
}

static void
ltlk_sl_all(model_t self, int *state, int *labels)
{
    ltlk_context_t *ctx = GBgetContext(self);
    GBgetStateLabelsAll(ctx->parent, state + 1, labels);
    labels[ctx->sl_idx_accept] = is_accepting(ctx, state);
    if (ctx->sl_idx_nonaccept != -1)
        labels[ctx->sl_idx_nonaccept] = !is_accepting(ctx, state);
}

static bool
has_epistemic(ltsmin_expr_t e)
{
    if (e == NULL) return false;
    switch (e->node_type) {
    case UNARY_OP:
        if (e->token >= LTLK_KNOWS)
            return true;
        return has_epistemic(e->arg1);
    case BINARY_OP:
        return has_epistemic(e->arg1) || has_epistemic(e->arg2);
    default:
        return false;
    }
}

static bool
has_unsupported_epistemic(ltsmin_expr_t e)
{
    if (e == NULL) return false;
    switch (e->node_type) {
    case UNARY_OP:
        if (e->token >= LTLK_KNOWS && e->token != LTLK_KNOWS)
            return true;
        return has_unsupported_epistemic(e->arg1);
    case BINARY_OP:
        return has_unsupported_epistemic(e->arg1) || has_unsupported_epistemic(e->arg2);
    default:
        return false;
    }
}

static bool
has_temporal_operator(ltsmin_expr_t e)
{
    if (e == NULL) return false;
    switch (e->node_type) {
    case UNARY_OP:
        if (e->token == LTLK_GLOBALLY ||
            e->token == LTLK_FUTURE   ||
            e->token == LTLK_NEXT)
            return true;
        return has_temporal_operator(e->arg1);
    case BINARY_OP:
        if (e->token == LTLK_UNTIL ||
            e->token == LTLK_RELEASE ||
            e->token == LTLK_WEAK_UNTIL ||
            e->token == LTLK_STRONG_RELEASE)
            return true;
        return has_temporal_operator(e->arg1) || has_temporal_operator(e->arg2);
    default:
        return false;
    }
}

/* Forward declaration: real implementation after companion helpers. */
static ltsmin_buchi_t *init_ltlk_buchi_real(model_t, ltsmin_expr_t, ltsmin_parse_env_t);

/* Thin wrapper so callers use the familiar init_ltlk_buchi name.       */
static ltsmin_buchi_t *
init_ltlk_buchi(model_t model, ltsmin_expr_t ltlk_expr, ltsmin_parse_env_t env)
{
    return init_ltlk_buchi_real(model, ltlk_expr, env);
}

/* Build companion BA: call ltl2ba directly on phi_j (NOT negated). */
static ltsmin_buchi_t *
init_companion_ba(ltsmin_expr_t phi)
{
    ltsmin_ltl2ba(phi);
    return ltsmin_buchi();
}

/* -----------------------------------------------------------------------
 * build_k_atom_companions: for every K_i(phi_j) atomic predicate in the
 * outer Büchi automaton, build a companion BA for phi_j.
 *
 * Returns a freshly RTmalloc'd array of k_atom_companion_t of length
 * ba->predicate_count.  Entries with ba==NULL are plain propositional.
 *
 * IMPORTANT: this must be called BEFORE init_ltlk_buchi so that the
 * final ltl2ba_init() inside init_ltlk_buchi resets cleanly after the
 * companion builds.
 * ----------------------------------------------------------------------- */
static k_atom_companion_t *
build_k_atom_companions(model_t model, ltsmin_buchi_t *outer_ba,
                        ltsmin_parse_env_t env)
{
    int n = outer_ba->predicate_count;
    k_atom_companion_t *companions = RTmallocZero(sizeof(k_atom_companion_t) * n);

    for (int i = 0; i < n; i++) {
        ltsmin_expr_t pred = outer_ba->predicates[i];

        if (pred->token != LTLK_KNOWS) {
            companions[i].ba  = NULL;
            companions[i].env = NULL;
            continue;
        }

        /* pred = K_i(phi_j); we want to build a companion BA for phi_j.   */
        ltsmin_expr_t phi = pred->arg1;

        /* Build the companion by calling ltl2ba directly on phi_j.        */
        /* ltl2ba_init() (called inside ltsmin_ltl2ba()) fully resets the  */
        /* global state after the ltl2ba_reset_mem/_lex fixes, so repeated */
        /* calls are now safe.                                              */
        ltsmin_buchi_t *comp = init_companion_ba(phi);

        if (comp == NULL) {
            /* ltl2ba produced no automaton. For propositional phi this will
             * be handled by the classic evaluation fallback. For temporal phi,
             * eval_ltlk_expr treats this as unsatisfiable (always false).     */
            companions[i].ba  = NULL;
            companions[i].env = NULL;
            Print1(info, "LTLK: K-atom %d companion BA is empty", i);
        } else {
            comp->env = env;
            /* Register predicate semantics so eval_state_predicate works. */
            for (int p = 0; p < comp->predicate_count; p++)
                set_pins_semantics(model, comp->predicates[p], env, NULL, NULL);
            companions[i].ba  = comp;
            companions[i].env = env;
            Print1(info, "LTLK: built companion BA for K-atom %d (%d states, %d preds)",
                   i, comp->state_count, comp->predicate_count);
        }
    }

    return companions;
}

/* Find the outer BA predicate index that matches a given LTLK_KNOWS expr. */
static int
find_k_atom_pred_idx(const ltsmin_buchi_t *ba, ltsmin_expr_t k_expr)
{
    for (int i = 0; i < ba->predicate_count; i++) {
        ltsmin_expr_t pred = ba->predicates[i];
        if (pred->token == LTLK_KNOWS && LTSminExprEq(pred, k_expr))
            return i;
    }
    return -1;
}

static ltsmin_buchi_t *
init_ltlk_buchi_real(model_t model, ltsmin_expr_t ltlk_expr, ltsmin_parse_env_t env)
{
    ltsmin_buchi_t *ba;

    if (NULL == shared_ba_ltlk && cas(&grab_ba_ltlk, 0, 1)) {
        ltsmin_expr_t neg = LTSminExpr(UNARY_OP, LTLK_NOT, 0, ltlk_expr, NULL);
        ltsmin_ltl2ba(neg);
        ba = ltsmin_buchi();

        if (ba == NULL) {
            Print(info, "LTLK: empty Buchi automaton.");
            HREexit(LTSMIN_EXIT_SUCCESS);
        }

        if (ba->predicate_count > 30)
            Abort("More than 30 predicates in LTLK Buchi automaton (unsupported)");

        ba->env = env;
        for (int i = 0; i < ba->predicate_count; i++)
            set_pins_semantics(model, ba->predicates[i], env, NULL, NULL);

        atomic_write(&shared_ba_ltlk, ba);
        HREbarrier(HREglobal());
    } else {
        HREbarrier(HREglobal());
        ba = atomic_read(&shared_ba_ltlk);
    }

    return ba;
}

static bool
is_weak_buchi(ltsmin_buchi_t *ba)
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

static int
resolve_agent(ltlk_context_t *ctx, ltsmin_expr_t expr)
{
    if (expr->token != LTLK_KNOWS)
        Abort("resolve_agent called with non-K operator");

    if (ctx->k_base_idx != SI_INDEX_FAILED && expr->idx >= ctx->k_base_idx) {
        int aid = expr->idx - ctx->k_base_idx;
        if (aid >= 0 && aid < ctx->num_agents)
            return aid;
    }

    if (expr->idx >= 0) {
        const char *op = SIget(ctx->env->unary_ops, expr->idx);
        if (op != NULL && op[0] == 'K') {
            if (op[1] == '\0') return 0;
            char *end = NULL;
            long val = strtol(op + 1, &end, 10);
            if (end != NULL && *end == '\0' && val >= 0 && val < ctx->num_agents)
                return (int)val;
        }
    }

    return 0;
}

static int eval_ltlk_expr(ltlk_context_t *ctx, ltsmin_expr_t expr,
                          const int *model_state, const int *knowledge_ids);

typedef struct k_eval_ctx {
    ltlk_context_t *ctx;
    ltsmin_expr_t   phi;
    const int      *knowledge_ids;
} k_eval_ctx_t;

static int
k_eval_cb(void *arg, const int *candidate_state)
{
    k_eval_ctx_t *ec = (k_eval_ctx_t *)arg;
    return eval_ltlk_expr(ec->ctx, ec->phi, candidate_state, ec->knowledge_ids);
}

static int
eval_ltlk_expr(ltlk_context_t *ctx, ltsmin_expr_t expr,
               const int *model_state, const int *knowledge_ids)
{
    if (expr == NULL) return 1;

    switch (expr->node_type) {
    case UNARY_OP:
        switch (expr->token) {
        case LTLK_KNOWS: {
            int aid = resolve_agent(ctx, expr);
            int bid = knowledge_ids[aid];
            /* If a companion BA was built for this K-atom, use it directly –
             * it correctly handles temporal sub-formulas (G, F, U, X, ...)
             * inside the knowledge operator.                                */
            if (ctx->k_atoms != NULL) {
                int pred_idx = find_k_atom_pred_idx(ctx->ba, expr);
                if (pred_idx >= 0) {
                    if (ctx->k_atoms[pred_idx].ba != NULL)
                        return knowledge_k_atom_holds(ctx->knowledge, bid, pred_idx);
                    if (has_temporal_operator(expr->arg1))
                        return 0;
                }
            }
            /* Fallback: plain propositional phi – use classic forall check. */
            k_eval_ctx_t ec = { ctx, expr->arg1, knowledge_ids };
            return knowledge_forall(ctx->knowledge, bid, k_eval_cb, &ec);
        }
        case LTLK_NOT:
            return !eval_ltlk_expr(ctx, expr->arg1, model_state, knowledge_ids);
        case LTLK_GLOBALLY:
        case LTLK_FUTURE:
        case LTLK_NEXT:
            return 1;
        default:
            break;
        }
        break;
    case BINARY_OP:
        switch (expr->token) {
        case LTLK_AND:
            return eval_ltlk_expr(ctx, expr->arg1, model_state, knowledge_ids) &&
                   eval_ltlk_expr(ctx, expr->arg2, model_state, knowledge_ids);
        case LTLK_OR:
            return eval_ltlk_expr(ctx, expr->arg1, model_state, knowledge_ids) ||
                   eval_ltlk_expr(ctx, expr->arg2, model_state, knowledge_ids);
        case LTLK_IMPLY:
            return !eval_ltlk_expr(ctx, expr->arg1, model_state, knowledge_ids) ||
                    eval_ltlk_expr(ctx, expr->arg2, model_state, knowledge_ids);
        case LTLK_EQUIV:
            return eval_ltlk_expr(ctx, expr->arg1, model_state, knowledge_ids) ==
                   eval_ltlk_expr(ctx, expr->arg2, model_state, knowledge_ids);
        case LTLK_UNTIL:
        case LTLK_RELEASE:
        case LTLK_WEAK_UNTIL:
        case LTLK_STRONG_RELEASE:
            return 1;
        default:
            break;
        }
        break;
    default:
        break;
    }

    return (int)eval_trans_predicate(ctx->parent, expr, (int *)model_state, NULL, ctx->env);
}

static inline int
eval_predicates(ltlk_cb_context_t *infoctx)
{
    ltlk_context_t *ctx = infoctx->ctx;
    const int *model_state = infoctx->src + 1;
    const int *knowledge_ids = infoctx->src + ctx->know_idx;
    int pred_evals = 0;

    for (int i = 0; i < ctx->ba->predicate_count; i++) {
        if (eval_ltlk_expr(ctx, ctx->ba->predicates[i], model_state, knowledge_ids))
            pred_evals |= (1 << i);
    }

    return pred_evals;
}

static void
ltlk_spin_cb(void *context, transition_info_t *ti, int *dst, int *cpy)
{
    ltlk_cb_context_t *infoctx = (ltlk_cb_context_t *)context;
    ltlk_context_t    *ctx = infoctx->ctx;

    int dst_new[ctx->len];
    memcpy(dst_new + 1, dst, sizeof(int) * ctx->old_len);

    const int *src_knowledge = infoctx->src + ctx->know_idx;
    int *dst_knowledge = dst_new + ctx->know_idx;
    for (int a = 0; a < ctx->num_agents; a++) {
        dst_knowledge[a] = knowledge_update_belief(ctx->knowledge, a,
                                                   src_knowledge[a], dst);
    }

    int pred_evals = infoctx->predicate_evals;
    int buchi_src = infoctx->src[ctx->ltl_idx];
    HREassert(buchi_src < ctx->ba->state_count);

    for (int j = 0; j < ctx->ba->states[buchi_src]->transition_count; j++) {
        ltsmin_buchi_transition_t *tr = &ctx->ba->states[buchi_src]->transitions[j];
        if ((pred_evals & tr->pos[0]) == tr->pos[0] && (pred_evals & tr->neg[0]) == 0) {
            dst_new[ctx->ltl_idx] = tr->to_state;
            infoctx->cb(infoctx->user_context, ti, dst_new, cpy);
            infoctx->ntbtrans++;
        }
    }
}

static int
ltlk_spin_long(model_t self, int group, int *src, TransitionCB cb, void *user_context)
{
    (void)self; (void)group; (void)src; (void)cb; (void)user_context;
    Abort("LTLK: --grey / -reach not supported by this layer");
}

static int
ltlk_spin_short(model_t self, int group, int *src, TransitionCB cb, void *user_context)
{
    (void)self; (void)group; (void)src; (void)cb; (void)user_context;
    Abort("LTLK: --cached not supported by this layer");
}

static int
ltlk_spin_all(model_t self, int *src, TransitionCB cb, void *user_context)
{
    ltlk_context_t *ctx = GBgetContext(self);
    ltlk_cb_context_t new_ctx;

    new_ctx.model = self;
    new_ctx.cb = cb;
    new_ctx.user_context = user_context;
    new_ctx.src = src;
    new_ctx.ntbtrans = 0;
    new_ctx.ctx = ctx;
    new_ctx.predicate_evals = eval_predicates(&new_ctx);

    GBgetTransitionsAll(ctx->parent, src + 1, ltlk_spin_cb, &new_ctx);

    if (new_ctx.ntbtrans == 0) {
        int dst_new[ctx->len];
        memcpy(dst_new, src, sizeof(int) * ctx->len);

        int buchi_src = src[ctx->ltl_idx];
        HREassert(buchi_src < ctx->ba->state_count);

        memset(ctx->edge_labels_buf, 0, sizeof(int) * ctx->edge_labels);

        for (int j = 0; j < ctx->ba->states[buchi_src]->transition_count; j++) {
            ltsmin_buchi_transition_t *tr = &ctx->ba->states[buchi_src]->transitions[j];
            if ((new_ctx.predicate_evals & tr->pos[0]) == tr->pos[0] &&
                (new_ctx.predicate_evals & tr->neg[0]) == 0) {
                dst_new[ctx->ltl_idx] = tr->to_state;
                int grp = ctx->old_groups + tr->index;
                transition_info_t ti = GB_TI(ctx->edge_labels_buf, grp);
                ti.por_proviso = 1;
                cb(user_context, &ti, dst_new, NULL);
                new_ctx.ntbtrans++;
            }
        }
    }

    return new_ctx.ntbtrans;
}

static void
init_observability(ltlk_context_t *ctx)
{
    if (ltlk_obs != NULL) {
        ctx->num_agents = ltlk_obs->num_agents;
        ctx->observable_vars = ltlk_obs->observable_vars;
        return;
    }

    ctx->num_agents = LTLK_NUM_AGENTS > 0 ? LTLK_NUM_AGENTS : 2;
    ctx->observable_vars = RTmalloc(sizeof(bitvector_t) * ctx->num_agents);

    for (int a = 0; a < ctx->num_agents; a++) {
        bitvector_create(&ctx->observable_vars[a], ctx->old_len);
        for (int i = 0; i < ctx->old_len; i++)
            bitvector_set(&ctx->observable_vars[a], i);
    }
}

model_t
GBaddLTLK(model_t model)
{
    if (ltlk_file == NULL) return model;
    if (PINS_LTLK != PINS_LTLK_SYNC_PERFECT_RECALL)
        Abort("Only sync-perfect-recall LTLK semantics is supported");

    lts_type_t ltstype = GBgetLTStype(model);
    ltsmin_parse_env_t env = LTSminParseEnvCreate();
    ltsmin_expr_t ltlk_expr = ltlk_parse_file(ltlk_file, env, ltstype);
    if (ltlk_expr == NULL)
        Abort("Failed to parse LTLK formula: %s", ltlk_file);

    if (has_unsupported_epistemic(ltlk_expr))
        Abort("This LTLK layer currently supports only K_i(phi)");

    ltlk_context_t *ctx = RTmallocZero(sizeof(*ctx));
    ctx->parent = model;
    ctx->ltlk_expr = ltlk_expr;
    ctx->env = env;
    ctx->old_len = lts_type_get_state_length(ltstype);
    ctx->ltl_idx = 0;

    set_pins_semantics(model, ltlk_expr, env, NULL, NULL);
    ctx->k_base_idx = SIlookup(env->unary_ops, "K0");

    init_observability(ctx);

    ctx->ba = init_ltlk_buchi(model, ltlk_expr, env);

    /* Build companion automata for every K_i(phi_j) predicate in the outer
     * Büchi automaton.  This MUST happen after init_ltlk_buchi() so that
     * ba->predicates[] is populated.  Each subsequent ltl2ba call inside
     * build_k_atom_companions() is safe because ltl2ba_init() now fully
     * resets the global memory and lex symbol table between invocations.  */
    ctx->k_atoms       = build_k_atom_companions(model, ctx->ba, env);
    ctx->k_atoms_count = ctx->ba->predicate_count;

    ctx->is_weak = is_weak_buchi(ctx->ba);

    int new_len = 1 + ctx->old_len + ctx->num_agents;
    ctx->len = new_len;
    ctx->know_idx = 1 + ctx->old_len;

    int old_accept = pins_get_accepting_state_label_index(model);
    if (old_accept != -1) {
        Print1(info, "LTLK: overriding existing property '%s'",
               lts_type_get_state_label_name(ltstype, old_accept));
    }

    lts_type_t ltstype_new = lts_type_clone(ltstype);
    lts_type_set_state_length(ltstype_new, new_len);

    int type_count = lts_type_get_type_count(ltstype_new);
    int buchi_type = lts_type_add_type(ltstype_new, "ltlk_buchi", NULL);
    lts_type_set_format(ltstype_new, buchi_type, LTStypeDirect);

    int belief_type = lts_type_add_type(ltstype_new, "ltlk_belief", NULL);
    lts_type_set_format(ltstype_new, belief_type, LTStypeDirect);

    lts_type_set_state_name(ltstype_new, ctx->ltl_idx, "ltlk");
    lts_type_set_state_typeno(ltstype_new, ctx->ltl_idx, buchi_type);

    for (int i = 0; i < ctx->old_len; i++) {
        lts_type_set_state_name(ltstype_new, i + 1,
                                lts_type_get_state_name(ltstype, i));
        lts_type_set_state_type(ltstype_new, i + 1,
                                lts_type_get_state_type(ltstype, i));
    }

    for (int a = 0; a < ctx->num_agents; a++) {
        char name[32];
        snprintf(name, sizeof(name), "K%d", a);
        lts_type_set_state_name(ltstype_new, ctx->know_idx + a, name);
        lts_type_set_state_typeno(ltstype_new, ctx->know_idx + a, belief_type);
    }

    int bool_type = lts_type_add_type(ltstype_new, "LTLK_bool", NULL);
    lts_type_set_format(ltstype_new, bool_type, LTStypeBool);

    matrix_t *p_sl = GBgetStateLabelInfo(model);
    int sl_count = dm_nrows(p_sl);

    int new_sl_count = sl_count + (ctx->is_weak ? 2 : 1);
    ctx->sl_idx_accept = sl_count;
    ctx->sl_idx_nonaccept = ctx->is_weak ? sl_count + 1 : -1;

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
        lts_type_set_state_label_typeno(ltstype_new, ctx->sl_idx_nonaccept, bool_type);
    }

    matrix_t *p_dm = GBgetDMInfo(model);
    matrix_t *p_dm_r = GBgetDMInfoRead(model);
    matrix_t *p_dm_w = GBgetDMInfoMayWrite(model);
    int groups = dm_nrows(p_dm);
    int new_groups = groups + ctx->ba->trans_count;

    ctx->old_groups = groups;
    ctx->groups = new_groups;

    bitvector_t fsd;
    bitvector_create(&fsd, ctx->old_len);
    for (int i = 0; i < ctx->ba->predicate_count; i++)
        set_pins_semantics(model, ctx->ba->predicates[i], env, &fsd, NULL);

    if (has_epistemic(ltlk_expr)) {
        for (int i = 0; i < ctx->old_len; i++)
            bitvector_set(&fsd, i);
    }

    matrix_t *new_dm = RTmalloc(sizeof(matrix_t));
    matrix_t *new_dm_r = RTmalloc(sizeof(matrix_t));
    matrix_t *new_dm_w = RTmalloc(sizeof(matrix_t));
    dm_create(new_dm, new_groups, new_len);
    dm_create(new_dm_r, new_groups, new_len);
    dm_create(new_dm_w, new_groups, new_len);

    for (int g = 0; g < groups; g++) {
        for (int i = 0; i < ctx->old_len; i++) {
            if (dm_is_set(p_dm, g, i)) dm_set(new_dm, g, i + 1);
            if (dm_is_set(p_dm_r, g, i)) dm_set(new_dm_r, g, i + 1);
            if (dm_is_set(p_dm_w, g, i)) dm_set(new_dm_w, g, i + 1);
        }

        dm_set(new_dm, g, ctx->ltl_idx);
        dm_set(new_dm_r, g, ctx->ltl_idx);
        dm_set(new_dm_w, g, ctx->ltl_idx);

        for (int a = 0; a < ctx->num_agents; a++) {
            dm_set(new_dm, g, ctx->know_idx + a);
            dm_set(new_dm_r, g, ctx->know_idx + a);
            dm_set(new_dm_w, g, ctx->know_idx + a);
        }

        for (int i = 0; i < ctx->old_len; i++) {
            if (bitvector_is_set(&fsd, i)) {
                dm_set(new_dm, g, i + 1);
                dm_set(new_dm_r, g, i + 1);
            }
        }
    }

    for (int g = groups; g < new_groups; g++) {
        dm_set(new_dm, g, ctx->ltl_idx);
        dm_set(new_dm_r, g, ctx->ltl_idx);
        dm_set(new_dm_w, g, ctx->ltl_idx);

        for (int a = 0; a < ctx->num_agents; a++) {
            dm_set(new_dm, g, ctx->know_idx + a);
            dm_set(new_dm_r, g, ctx->know_idx + a);
        }

        for (int i = 0; i < ctx->old_len; i++) {
            if (bitvector_is_set(&fsd, i)) {
                dm_set(new_dm, g, i + 1);
                dm_set(new_dm_r, g, i + 1);
            }
        }
    }

    int sl_len = dm_ncols(p_sl);
    matrix_t *new_sl = RTmalloc(sizeof(matrix_t));
    dm_create(new_sl, new_sl_count, new_len);
    for (int i = 0; i < sl_count; i++) {
        for (int j = 0; j < sl_len; j++) {
            if (dm_is_set(p_sl, i, j)) dm_set(new_sl, i, j + 1);
        }
    }

    dm_set(new_sl, ctx->sl_idx_accept, ctx->ltl_idx);
    for (int a = 0; a < ctx->num_agents; a++)
        dm_set(new_sl, ctx->sl_idx_accept, ctx->know_idx + a);

    for (int i = 0; i < ctx->old_len; i++)
        if (bitvector_is_set(&fsd, i))
            dm_set(new_sl, ctx->sl_idx_accept, i + 1);

    if (ctx->is_weak) {
        dm_set(new_sl, ctx->sl_idx_nonaccept, ctx->ltl_idx);
        for (int a = 0; a < ctx->num_agents; a++)
            dm_set(new_sl, ctx->sl_idx_nonaccept, ctx->know_idx + a);

        for (int i = 0; i < ctx->old_len; i++)
            if (bitvector_is_set(&fsd, i))
                dm_set(new_sl, ctx->sl_idx_nonaccept, i + 1);
    }

    bitvector_clear(&fsd);

    model_t out = GBcreateBase();
    GBsetContext(out, ctx);
    GBcopyChunkMaps(out, model);
    GBsetLTStype(out, ltstype_new);
    GBgrowChunkMaps(out, type_count);

    GBsetDMInfo(out, new_dm);
    GBsetDMInfoRead(out, new_dm_r);
    GBsetDMInfoMayWrite(out, new_dm_w);
    GBsetStateLabelInfo(out, new_sl);

    GBsetStateLabelShort(out, ltlk_sl_short);
    GBsetStateLabelLong(out, ltlk_sl_long);
    GBsetStateLabelsAll(out, ltlk_sl_all);

    GBsetNextStateLong(out, ltlk_spin_long);
    GBsetNextStateShort(out, ltlk_spin_short);
    GBsetNextStateAll(out, ltlk_spin_all);

    int *cur_vis = GBgetPorGroupVisibility(model);
    if (cur_vis) {
        int *new_vis = RTmallocZero(sizeof(int) * new_groups);
        memcpy(new_vis, cur_vis, sizeof(int) * groups);
        GBsetPorGroupVisibility(out, new_vis);
    }

    GBinitModelDefaults(&out, model);

    ctx->old_edge_labels = lts_type_get_edge_label_count(ltstype);
    ctx->edge_labels = lts_type_get_edge_label_count(ltstype_new);
    ctx->edge_labels_buf = RTmalloc(sizeof(int) * ctx->edge_labels);

    ctx->knowledge = knowledge_create(model, ctx->old_len, ctx->num_agents,
                                      ctx->observable_vars,
                                      ctx->k_atoms_count, ctx->k_atoms);

    int init[new_len];
    GBgetInitialState(model, init + 1);
    init[ctx->ltl_idx] = 0;

    int init_sid = knowledge_register_initial_state(ctx->knowledge, init + 1);
    for (int a = 0; a < ctx->num_agents; a++)
        init[ctx->know_idx + a] = knowledge_make_singleton(ctx->knowledge, init_sid);

    GBsetInitialState(out, init);

    lts_type_validate(ltstype_new);

    Print1(info, "LTLK: loaded formula %s", ltlk_file);
    Print1(info, "LTLK: product state length %d (model=%d, buchi=1, knowledge=%d)",
           new_len, ctx->old_len, ctx->num_agents);

    return out;
}
