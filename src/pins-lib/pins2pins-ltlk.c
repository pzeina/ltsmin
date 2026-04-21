#include <hre/config.h>

#include <ctype.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <dm/dm.h>
#include <hre/stringindex.h>
#include <hre/unix.h>
#include <hre/user.h>
#include <ltsmin-lib/ltl2ba-lex.h>
#ifdef HAVE_SPOT
#include <ltsmin-lib/ltl2spot.h>
#endif
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
    bitvector_t        *observable_labels;
    int                 know_idx;
    int                 past_idx;
    int                 model_ext_len;
    int                 k_base_idx;

    knowledge_mgr_t    *knowledge;

     /* companion Büchi automata – one entry per outer BA predicate         */
     /* (NULL.ba means the predicate is plain propositional, not a K-atom) */
     k_atom_companion_t *k_atoms;
     int                 k_atoms_count; /* = ba->predicate_count            */

    ltsmin_expr_t       original_expr;
    struct past_slot_s *past_slots;
    int                 past_count;
} ltlk_context_t;

typedef struct past_slot_s {
    ltsmin_expr_t orig;          /* original past subformula */
    int           token;         /* LTLK_PREVIOUS/LTLK_ONCE/LTLK_HISTORICALLY/LTLK_SINCE */
    int           state_idx;     /* index in extended model state (without BA slot) */
    ltsmin_expr_t arg1_rewritten;/* arg with past recursively replaced by history vars */
    ltsmin_expr_t arg2_rewritten;/* idem for binary since */
} past_slot_t;

typedef struct ltlk_cb_context {
    model_t         model;
    TransitionCB    cb;
    void           *user_context;
    int            *src;
    int             ntbtrans;
    ltlk_context_t *ctx;
    int             predicate_evals;
    int             group_filter;
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

static char *
trim_ws(char *s)
{
    while (*s != '\0' && isspace((unsigned char)*s)) s++;
    if (*s == '\0') return s;
    char *end = s + strlen(s) - 1;
    while (end >= s && isspace((unsigned char)*end)) {
        *end = '\0';
        end--;
    }
    return s;
}

static bool
starts_with_word(const char *s, const char *word)
{
    size_t n = strlen(word);
    if (strncmp(s, word, n) != 0) return false;
    char c = s[n];
    return c == '\0' || isspace((unsigned char)c) || c == ':' || c == '=';
}

static int
find_state_var_index(lts_type_t ltstype, const char *name)
{
    int n = lts_type_get_state_length(ltstype);
    for (int i = 0; i < n; i++) {
        const char *cur = lts_type_get_state_name(ltstype, i);
        if (cur != NULL && strcmp(cur, name) == 0) return i;
    }
    return -1;
}

static int
find_edge_label_index(lts_type_t ltstype, const char *name)
{
    int n = lts_type_get_edge_label_count(ltstype);
    for (int i = 0; i < n; i++) {
        const char *cur = lts_type_get_edge_label_name(ltstype, i);
        if (cur != NULL && strcmp(cur, name) == 0) return i;
    }
    return -1;
}

static void
set_all_observable(ltlk_obs_config_t *cfg, int state_len, int edge_labels)
{
    for (int a = 0; a < cfg->num_agents; a++) {
        bitvector_create(&cfg->observable_vars[a], state_len);
        bitvector_create(&cfg->observable_labels[a], edge_labels);
        for (int i = 0; i < state_len; i++) bitvector_set(&cfg->observable_vars[a], i);
        for (int i = 0; i < edge_labels; i++) bitvector_set(&cfg->observable_labels[a], i);
    }
}

static void
clear_agent_observable(ltlk_obs_config_t *cfg, int agent)
{
    bitvector_clear(&cfg->observable_vars[agent]);
    bitvector_clear(&cfg->observable_labels[agent]);
}

static void
parse_name_list_into_bits(char *list, lts_type_t ltstype, bitvector_t *dst,
                          bool vars, int lineno)
{
    char *save = NULL;
    for (char *tok = strtok_r(list, ",", &save); tok != NULL; tok = strtok_r(NULL, ",", &save)) {
        char *name = trim_ws(tok);
        if (*name == '\0') continue;
        if (vars) {
            int idx = find_state_var_index(ltstype, name);
            if (idx < 0)
                Abort("LTLK obs parse error (line %d): unknown state variable '%s'", lineno, name);
            bitvector_set(dst, idx);
        } else {
            int idx = find_edge_label_index(ltstype, name);
            if (idx < 0)
                Abort("LTLK obs parse error (line %d): unknown edge label '%s'", lineno, name);
            bitvector_set(dst, idx);
        }
    }
}

static void
parse_obs_clauses(char *clauses, lts_type_t ltstype, ltlk_obs_config_t *cfg,
                  int agent, int lineno)
{
    bool saw_any = false;
    bool touched = false;
    char *p = clauses;

    while (*p != '\0') {
        while (*p != '\0' && (isspace((unsigned char)*p) || *p == ',')) p++;
        if (*p == '\0') break;

        if (strncmp(p, "vars", 4) == 0 && strchr(" (", p[4]) != NULL) {
            p += 4;
            while (*p != '\0' && isspace((unsigned char)*p)) p++;
            if (*p != '(')
                Abort("LTLK obs parse error (line %d): expected '(' after vars", lineno);
            p++;
            char *start = p;
            char *end = strchr(start, ')');
            if (end == NULL)
                Abort("LTLK obs parse error (line %d): missing ')' in vars(...)", lineno);
            *end = '\0';
            if (!touched) {
                clear_agent_observable(cfg, agent);
                touched = true;
            }
            parse_name_list_into_bits(start, ltstype, &cfg->observable_vars[agent], true, lineno);
            saw_any = true;
            p = end + 1;
            continue;
        }

        if (strncmp(p, "labels", 6) == 0 && strchr(" (", p[6]) != NULL) {
            p += 6;
            while (*p != '\0' && isspace((unsigned char)*p)) p++;
            if (*p != '(')
                Abort("LTLK obs parse error (line %d): expected '(' after labels", lineno);
            p++;
            char *start = p;
            char *end = strchr(start, ')');
            if (end == NULL)
                Abort("LTLK obs parse error (line %d): missing ')' in labels(...)", lineno);
            *end = '\0';
            if (!touched) {
                clear_agent_observable(cfg, agent);
                touched = true;
            }
            parse_name_list_into_bits(start, ltstype, &cfg->observable_labels[agent], false, lineno);
            saw_any = true;
            p = end + 1;
            continue;
        }

        Abort("LTLK obs parse error (line %d): expected vars(...) or labels(...) clause", lineno);
    }

    if (!saw_any)
        Abort("LTLK obs parse error (line %d): obs declaration needs vars(...) and/or labels(...)", lineno);
}

static void
append_text(char **out, size_t *len, size_t *cap, const char *s)
{
    size_t n = strlen(s);
    if (*len + n + 1 > *cap) {
        size_t new_cap = *cap == 0 ? 256 : *cap;
        while (*len + n + 1 > new_cap) new_cap *= 2;
        *out = RTrealloc(*out, new_cap);
        *cap = new_cap;
    }
    memcpy(*out + *len, s, n);
    *len += n;
    (*out)[*len] = '\0';
}

static bool
try_parse_ltlk_file_with_obs(const char *path, lts_type_t ltstype, char **formula_out)
{
    FILE *f = fopen(path, "r");
    if (f == NULL) return false;

    int state_len = lts_type_get_state_length(ltstype);
    int edge_labels = lts_type_get_edge_label_count(ltstype);

    int declared_agents = -1;
    int max_agent_in_obs = -1;
    bool saw_obs_decl = false;
    bool header = true;

    char line[4096];
    char *formula = NULL;
    size_t formula_len = 0, formula_cap = 0;

    typedef struct {
        int agent;
        char *clauses;
        int lineno;
    } obs_decl_t;
    obs_decl_t *decls = NULL;
    size_t decl_count = 0, decl_cap = 0;

    int lineno = 0;
    while (fgets(line, sizeof(line), f) != NULL) {
        lineno++;
        char *raw = line;
        char *trim = trim_ws(raw);

        if (header && (*trim == '\0' || *trim == '#'))
            continue;
        if (header && trim[0] == '/' && trim[1] == '/')
            continue;

        if (header && starts_with_word(trim, "agents")) {
            char *eq = strchr(trim, '=');
            char *num = (eq != NULL) ? eq + 1 : trim + 6;
            num = trim_ws(num);
            char *end = num;
            long val = strtol(num, &end, 10);
            while (*end != '\0' && isspace((unsigned char)*end)) end++;
            if (*end == ';') end++;
            while (*end != '\0' && isspace((unsigned char)*end)) end++;
            if (*num == '\0' || *end != '\0' || val <= 0)
                Abort("LTLK obs parse error (line %d): expected 'agents = <positive-int>;'", lineno);
            declared_agents = (int)val;
            continue;
        }

        if (header && starts_with_word(trim, "obs")) {
            saw_obs_decl = true;
            char *rest = trim + 3;
            rest = trim_ws(rest);
            char *colon = strchr(rest, ':');
            if (colon == NULL)
                Abort("LTLK obs parse error (line %d): expected ':' in obs declaration", lineno);
            *colon = '\0';
            char *aid_end = NULL;
            long aid = strtol(rest, &aid_end, 10);
            while (aid_end != NULL && *aid_end != '\0' && isspace((unsigned char)*aid_end)) aid_end++;
            if (aid < 0)
                Abort("LTLK obs parse error (line %d): invalid agent id", lineno);
            if (aid_end == NULL || *aid_end != '\0')
                Abort("LTLK obs parse error (line %d): expected numeric agent id", lineno);
            if ((int)aid > max_agent_in_obs) max_agent_in_obs = (int)aid;

            char *clauses = trim_ws(colon + 1);
            size_t clen = strlen(clauses);
            if (clen == 0 || clauses[clen - 1] != ';')
                Abort("LTLK obs parse error (line %d): obs declaration must end with ';'", lineno);
            clauses[clen - 1] = '\0';

            if (decl_count == decl_cap) {
                size_t new_cap = decl_cap == 0 ? 4 : decl_cap * 2;
                decls = RTrealloc(decls, sizeof(obs_decl_t) * new_cap);
                decl_cap = new_cap;
            }
            decls[decl_count].agent = (int)aid;
            decls[decl_count].clauses = HREstrdup(trim_ws(clauses));
            decls[decl_count].lineno = lineno;
            decl_count++;
            continue;
        }

        header = false;
        append_text(&formula, &formula_len, &formula_cap, raw);
    }
    fclose(f);

    if (formula == NULL || trim_ws(formula)[0] == '\0')
        Abort("LTLK parse error: file '%s' does not contain a formula", path);

    if (declared_agents > 0 && !saw_obs_decl) {
        LTLK_NUM_AGENTS = declared_agents;
    }

    if (saw_obs_decl) {
        int num_agents = declared_agents;
        if (num_agents <= 0)
            num_agents = (LTLK_NUM_AGENTS > 0) ? LTLK_NUM_AGENTS : (max_agent_in_obs + 1);
        if (num_agents <= 0)
            Abort("LTLK obs parse error: cannot infer number of agents");
        if (max_agent_in_obs >= num_agents)
            Abort("LTLK obs parse error: agent id %d out of range for agents=%d",
                  max_agent_in_obs, num_agents);

        ltlk_obs_config_t *cfg = RTmallocZero(sizeof(*cfg));
        cfg->num_agents = num_agents;
        cfg->observable_vars = RTmalloc(sizeof(bitvector_t) * num_agents);
        cfg->observable_labels = RTmalloc(sizeof(bitvector_t) * num_agents);
        set_all_observable(cfg, state_len, edge_labels);

        for (size_t i = 0; i < decl_count; i++) {
            parse_obs_clauses(decls[i].clauses, ltstype, cfg, decls[i].agent, decls[i].lineno);
        }

        LTLK_NUM_AGENTS = num_agents;
        GBsetLTLKObservability(cfg);
    }

    for (size_t i = 0; i < decl_count; i++)
        RTfree(decls[i].clauses);
    RTfree(decls);

    *formula_out = formula;
    return true;
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
            e->token == LTLK_NEXT     ||
            e->token == LTLK_PREVIOUS ||
            e->token == LTLK_ONCE     ||
            e->token == LTLK_HISTORICALLY)
            return true;
        return has_temporal_operator(e->arg1);
    case BINARY_OP:
        if (e->token == LTLK_UNTIL ||
            e->token == LTLK_RELEASE ||
            e->token == LTLK_WEAK_UNTIL ||
            e->token == LTLK_STRONG_RELEASE ||
            e->token == LTLK_SINCE)
            return true;
        return has_temporal_operator(e->arg1) || has_temporal_operator(e->arg2);
    default:
        return false;
    }
}

static bool
has_past_operator(ltsmin_expr_t e)
{
    if (e == NULL) return false;
    switch (e->node_type) {
    case UNARY_OP:
        if (e->token == LTLK_PREVIOUS ||
            e->token == LTLK_ONCE ||
            e->token == LTLK_HISTORICALLY)
            return true;
        return has_past_operator(e->arg1);
    case BINARY_OP:
        if (e->token == LTLK_SINCE)
            return true;
        return has_past_operator(e->arg1) || has_past_operator(e->arg2);
    default:
        return false;
    }
}

static bool
has_state_ref_ge(ltsmin_expr_t e, int threshold)
{
    if (e == NULL) return false;
    if (e->node_type == SVAR && e->idx >= threshold)
        return true;
    return has_state_ref_ge(e->arg1, threshold) || has_state_ref_ge(e->arg2, threshold);
}

static bool
is_past_token(int token)
{
    return token == LTLK_PREVIOUS ||
           token == LTLK_ONCE ||
           token == LTLK_HISTORICALLY ||
           token == LTLK_SINCE;
}

static int
find_past_slot(const ltlk_context_t *ctx, ltsmin_expr_t e)
{
    for (int i = 0; i < ctx->past_count; i++) {
        if (LTSminExprEq(ctx->past_slots[i].orig, e))
            return i;
    }
    return -1;
}

static int
collect_past_slots_rec(ltlk_context_t *ctx, ltsmin_expr_t e, int old_len)
{
    (void)old_len;
    if (e == NULL) return 0;

    if (e->arg1 != NULL) collect_past_slots_rec(ctx, e->arg1, old_len);
    if (e->arg2 != NULL) collect_past_slots_rec(ctx, e->arg2, old_len);

    if (e->node_type != UNARY_OP && e->node_type != BINARY_OP)
        return 0;
    if (!is_past_token(e->token))
        return 0;

    if (find_past_slot(ctx, e) != -1)
        return 0;

    ctx->past_slots = RTrealloc(ctx->past_slots, sizeof(past_slot_t) * (ctx->past_count + 1));
    past_slot_t *slot = &ctx->past_slots[ctx->past_count];
    memset(slot, 0, sizeof(*slot));
    slot->orig = e;
    slot->token = e->token;
    slot->state_idx = -1;
    ctx->past_count++;
    return 0;
}

static ltsmin_expr_t
make_hist_var_expr(int idx)
{
    return LTSminExpr(SVAR, SVAR, idx, NULL, NULL);
}

static ltsmin_expr_t
rewrite_past_to_history_vars(ltlk_context_t *ctx, ltsmin_expr_t e)
{
    if (e == NULL) return NULL;

    if ((e->node_type == UNARY_OP || e->node_type == BINARY_OP) && is_past_token(e->token)) {
        int slot = find_past_slot(ctx, e);
        HREassert(slot >= 0, "Missing past-slot mapping during rewrite");
        return make_hist_var_expr(ctx->past_slots[slot].state_idx);
    }

    ltsmin_expr_t out = LTSminExpr(e->node_type, e->token, e->idx, NULL, NULL);
    if (e->arg1) {
        out->arg1 = rewrite_past_to_history_vars(ctx, e->arg1);
        out->arg1->parent = out;
    }
    if (e->arg2) {
        out->arg2 = rewrite_past_to_history_vars(ctx, e->arg2);
        out->arg2->parent = out;
    }
    LTSminExprRehash(out);
    return out;
}

static void
prepare_past_elimination(ltlk_context_t *ctx, ltsmin_parse_env_t env, int old_len)
{
    if (!has_past_operator(ctx->ltlk_expr))
        return;

    collect_past_slots_rec(ctx, ctx->ltlk_expr, old_len);
    int max_idx = old_len - 1;

    for (int i = 0; i < ctx->past_count; i++) {
        char name[32];
        snprintf(name, sizeof(name), "__past_%d", i);
        int idx = LTSminStateVarIndex(env, name);
        ctx->past_slots[i].state_idx = idx;
        if (idx > max_idx) max_idx = idx;
    }
    ctx->model_ext_len = max_idx + 1;

    for (int i = 0; i < ctx->past_count; i++) {
        past_slot_t *slot = &ctx->past_slots[i];
        if (slot->orig->arg1 != NULL) {
            slot->arg1_rewritten = rewrite_past_to_history_vars(ctx, slot->orig->arg1);
        }
        if (slot->orig->arg2 != NULL) {
            slot->arg2_rewritten = rewrite_past_to_history_vars(ctx, slot->orig->arg2);
        }
    }

    ctx->ltlk_expr = rewrite_past_to_history_vars(ctx, ctx->ltlk_expr);
}

static ltsmin_buchi_t *
ltlk_expr_to_buchi(ltsmin_expr_t expr, ltsmin_parse_env_t env)
{
    (void)env;
    ltsmin_ltl2ba(expr);
    return ltsmin_buchi();
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
init_companion_ba(ltsmin_expr_t phi, ltsmin_parse_env_t env)
{
    return ltlk_expr_to_buchi(phi, env);
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

        /* Companion BA predicates are evaluated with eval_state_predicate,
         * which does not understand epistemic operators. For epistemic
         * inners, keep companion NULL and use recursive knowledge_forall.
         */
        if (has_epistemic(phi)) {
            companions[i].ba  = NULL;
            companions[i].env = NULL;
            Print1(info, "LTLK: K-atom %d uses epistemic inner formula; using recursive evaluator", i);
            continue;
        }

        /* Build the companion by calling ltl2ba directly on phi_j.        */
        /* ltl2ba_init() (called inside ltsmin_ltl2ba()) fully resets the  */
        /* global state after the ltl2ba_reset_mem/_lex fixes, so repeated */
        /* calls are now safe.                                              */
        ltsmin_buchi_t *comp = init_companion_ba(phi, env);

        if (comp == NULL) {
            /* ltl2ba produced no automaton. For propositional phi this will
             * be handled by the classic evaluation fallback. For temporal phi,
             * eval_ltlk_expr treats this as unsatisfiable (always false).     */
            companions[i].ba  = NULL;
            companions[i].env = NULL;
            Print1(info, "LTLK: K-atom %d companion BA is empty", i);
        } else {
            comp->env = env;
            bool uses_internal_history = false;
            for (int p = 0; p < comp->predicate_count; p++) {
                if (has_state_ref_ge(comp->predicates[p], lts_type_get_state_length(GBgetLTStype(model)))) {
                    uses_internal_history = true;
                    break;
                }
            }
            if (uses_internal_history) {
                companions[i].ba  = NULL;
                companions[i].env = NULL;
                Print1(info, "LTLK: K-atom %d companion uses internal history vars; using recursive evaluator", i);
                continue;
            }
            /* Register predicate semantics so eval_state_predicate works. */
            for (int p = 0; p < comp->predicate_count; p++) {
                if (!has_state_ref_ge(comp->predicates[p], lts_type_get_state_length(GBgetLTStype(model))))
                    set_pins_semantics(model, comp->predicates[p], env, NULL, NULL);
            }
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
        ba = ltlk_expr_to_buchi(neg, env);

        if (ba == NULL) {
            Print(info, "LTLK: empty Buchi automaton.");
            HREexit(LTSMIN_EXIT_SUCCESS);
        }

        if (ba->predicate_count > 30)
            Abort("More than 30 predicates in LTLK Buchi automaton (unsupported)");

        ba->env = env;
        int base_len = lts_type_get_state_length(GBgetLTStype(model));
        for (int i = 0; i < ba->predicate_count; i++) {
            if (!has_state_ref_ge(ba->predicates[i], base_len))
                set_pins_semantics(model, ba->predicates[i], env, NULL, NULL);
        }

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

static int eval_local_expr(ltlk_context_t *ctx, ltsmin_expr_t expr,
                           const int *model_state, const int *knowledge_ids, int *ok);

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
    case SVAR:
        if (expr->idx >= ctx->old_len)
            return model_state[expr->idx] != 0;
        break;
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
        case LTLK_PREVIOUS:
        case LTLK_ONCE:
        case LTLK_HISTORICALLY:
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
        case LTLK_SINCE:
            return 1;
        default:
            break;
        }
        break;
    default:
        break;
    }

    if (has_state_ref_ge(expr, ctx->old_len)) {
        int ok = 1;
        int v = eval_local_expr(ctx, expr, model_state, knowledge_ids, &ok);
        if (ok) return v;
    }

    return (int)eval_trans_predicate(ctx->parent, expr, (int *)model_state, NULL, ctx->env);
}

static int
eval_local_expr(ltlk_context_t *ctx, ltsmin_expr_t expr,
                const int *model_state, const int *knowledge_ids, int *ok)
{
    (void)knowledge_ids;
    if (expr == NULL) {
        *ok = 0;
        return 0;
    }

    switch (expr->node_type) {
    case SVAR:
        if (expr->idx < ctx->old_len) return model_state[expr->idx];
        if (expr->idx < ctx->model_ext_len) return model_state[expr->idx];
        *ok = 0;
        return 0;
    case CHUNK:
    case INT:
        return expr->idx;
    case CONSTANT:
        if (expr->token == LTLK_TRUE || expr->token == PRED_TRUE) return 1;
        if (expr->token == LTLK_FALSE || expr->token == PRED_FALSE) return 0;
        *ok = 0;
        return 0;
    case UNARY_OP: {
        if (expr->token == LTLK_NOT || expr->token == PRED_NOT) {
            int a = eval_local_expr(ctx, expr->arg1, model_state, knowledge_ids, ok);
            return !a;
        }
        *ok = 0;
        return 0;
    }
    case BINARY_OP: {
        int a = eval_local_expr(ctx, expr->arg1, model_state, knowledge_ids, ok);
        if (!*ok) return 0;
        int b = eval_local_expr(ctx, expr->arg2, model_state, knowledge_ids, ok);
        if (!*ok) return 0;
        switch (expr->token) {
        case LTLK_AND:   return a && b;
        case LTLK_OR:    return a || b;
        case LTLK_IMPLY: return (!a) || b;
        case LTLK_EQUIV: return a == b;
        case LTLK_EQ:    return a == b;
        case LTLK_NEQ:   return a != b;
        case LTLK_LT:    return a < b;
        case LTLK_LEQ:   return a <= b;
        case LTLK_GT:    return a > b;
        case LTLK_GEQ:   return a >= b;
        case LTLK_ADD:   return a + b;
        case LTLK_SUB:   return a - b;
        case LTLK_MULT:  return a * b;
        case LTLK_DIV:   return b == 0 ? 0 : (a / b);
        case LTLK_REM:   return b == 0 ? 0 : (a % b);
        default:
            *ok = 0;
            return 0;
        }
    }
    default:
        *ok = 0;
        return 0;
    }
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

static int
eval_rewritten_now(ltlk_context_t *ctx, ltsmin_expr_t expr,
                   const int *model_ext_state, const int *knowledge_ids)
{
    int ok = 1;
    int v = eval_local_expr(ctx, expr, model_ext_state, knowledge_ids, &ok);
    if (ok) return v;
    return eval_ltlk_expr(ctx, expr, model_ext_state, knowledge_ids);
}

static void
initialize_past_slots(ltlk_context_t *ctx, int *init_model_ext, const int *knowledge_ids)
{
    for (int i = 0; i < ctx->past_count; i++) {
        past_slot_t *slot = &ctx->past_slots[i];
        int v = 0;
        switch (slot->token) {
        case LTLK_PREVIOUS:
            v = 0;
            break;
        case LTLK_ONCE:
            v = eval_rewritten_now(ctx, slot->arg1_rewritten, init_model_ext, knowledge_ids);
            break;
        case LTLK_HISTORICALLY:
            v = eval_rewritten_now(ctx, slot->arg1_rewritten, init_model_ext, knowledge_ids);
            break;
        case LTLK_SINCE:
            v = eval_rewritten_now(ctx, slot->arg2_rewritten, init_model_ext, knowledge_ids);
            break;
        default:
            Abort("Unsupported past token in initialization: %d", slot->token);
        }
        init_model_ext[slot->state_idx] = v ? 1 : 0;
    }
}

static void
update_past_slots(ltlk_context_t *ctx,
                  const int *src_model_ext,
                  const int *dst_model_only,
                  int *dst_model_ext,
                  const int *src_knowledge_ids,
                  const int *dst_knowledge_ids)
{
    for (int i = 0; i < ctx->past_count; i++) {
        past_slot_t *slot = &ctx->past_slots[i];
        int prev_self = src_model_ext[slot->state_idx] ? 1 : 0;
        int v = 0;

        switch (slot->token) {
        case LTLK_PREVIOUS: {
            v = eval_rewritten_now(ctx, slot->arg1_rewritten, src_model_ext, src_knowledge_ids);
            break;
        }
        case LTLK_ONCE: {
            int now = eval_rewritten_now(ctx, slot->arg1_rewritten, dst_model_ext, dst_knowledge_ids);
            v = now || prev_self;
            break;
        }
        case LTLK_HISTORICALLY: {
            int now = eval_rewritten_now(ctx, slot->arg1_rewritten, dst_model_ext, dst_knowledge_ids);
            v = now && prev_self;
            break;
        }
        case LTLK_SINCE: {
            int left_now  = eval_rewritten_now(ctx, slot->arg1_rewritten, dst_model_ext, dst_knowledge_ids);
            int right_now = eval_rewritten_now(ctx, slot->arg2_rewritten, dst_model_ext, dst_knowledge_ids);
            v = right_now || (left_now && prev_self);
            break;
        }
        default:
            Abort("Unsupported past token in transition update: %d", slot->token);
        }

        dst_model_ext[slot->state_idx] = v ? 1 : 0;
    }

    (void)dst_model_only;
}

static void
ltlk_spin_cb(void *context, transition_info_t *ti, int *dst, int *cpy)
{
    ltlk_cb_context_t *infoctx = (ltlk_cb_context_t *)context;
    ltlk_context_t    *ctx = infoctx->ctx;

    if (infoctx->group_filter >= 0 && ti != NULL && ti->group != infoctx->group_filter)
        return;

    int dst_new[ctx->len];
    memcpy(dst_new + 1, dst, sizeof(int) * ctx->old_len);
    if (ctx->model_ext_len > ctx->old_len) {
        memset(dst_new + 1 + ctx->old_len, 0,
               sizeof(int) * (ctx->model_ext_len - ctx->old_len));
    }

    const int *src_knowledge = infoctx->src + ctx->know_idx;
    int *dst_knowledge = dst_new + ctx->know_idx;
    const int *src_model_ext = infoctx->src + 1;
    int *dst_model_ext = dst_new + 1;

    update_past_slots(ctx, src_model_ext, dst, dst_model_ext, src_knowledge, dst_knowledge);

    const int *obs_labels = (ti != NULL) ? ti->labels : NULL;
    for (int a = 0; a < ctx->num_agents; a++) {
        dst_knowledge[a] = knowledge_update_belief(ctx->knowledge, a,
                                                   src_knowledge[a], dst_model_ext,
                                                   obs_labels);
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

static void
ltlk_count_successors_cb(void *context, transition_info_t *ti, int *dst, int *cpy)
{
    int *count = (int *)context;
    (void)ti;
    (void)dst;
    (void)cpy;
    (*count)++;
}

static int
ltlk_parent_has_successors(ltlk_context_t *ctx, const int *src)
{
    int count = 0;
    GBgetTransitionsAll(ctx->parent, (int *)src + 1, ltlk_count_successors_cb, &count);
    return count > 0;
}

static int
ltlk_emit_buchi_group(ltlk_context_t *ctx, ltlk_cb_context_t *new_ctx, int group, int *src, TransitionCB cb, void *user_context)
{
    int ba_index = group - ctx->old_groups;
    int buchi_src = src[ctx->ltl_idx];
    HREassert(buchi_src < ctx->ba->state_count);

    if (ltlk_parent_has_successors(ctx, src))
        return 0;

    memset(ctx->edge_labels_buf, 0, sizeof(int) * ctx->edge_labels);

    int emitted = 0;
    for (int j = 0; j < ctx->ba->states[buchi_src]->transition_count; j++) {
        ltsmin_buchi_transition_t *tr = &ctx->ba->states[buchi_src]->transitions[j];
        if (tr->index != ba_index)
            continue;
        if ((new_ctx->predicate_evals & tr->pos[0]) != tr->pos[0] ||
            (new_ctx->predicate_evals & tr->neg[0]) != 0)
            continue;

        int dst_new[ctx->len];
        memcpy(dst_new, src, sizeof(int) * ctx->len);
        dst_new[ctx->ltl_idx] = tr->to_state;

        transition_info_t ti = GB_TI(ctx->edge_labels_buf, group);
        ti.por_proviso = 1;
        cb(user_context, &ti, dst_new, NULL);
        emitted++;
    }

    return emitted;
}

static int
ltlk_spin_long(model_t self, int group, int *src, TransitionCB cb, void *user_context)
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
    new_ctx.group_filter = group;

    GBgetTransitionsAll(ctx->parent, src + 1, ltlk_spin_cb, &new_ctx);

    if (group >= ctx->old_groups && new_ctx.ntbtrans == 0)
        return ltlk_emit_buchi_group(ctx, &new_ctx, group, src, cb, user_context);

    return new_ctx.ntbtrans;
}

static int
ltlk_spin_short(model_t self, int group, int *src, TransitionCB cb, void *user_context)
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
    new_ctx.group_filter = group;

    GBgetTransitionsAll(ctx->parent, src + 1, ltlk_spin_cb, &new_ctx);

    if (group >= ctx->old_groups && new_ctx.ntbtrans == 0)
        return ltlk_emit_buchi_group(ctx, &new_ctx, group, src, cb, user_context);

    return new_ctx.ntbtrans;
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
    new_ctx.group_filter = -1;

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
    int ext_len = ctx->model_ext_len > 0 ? ctx->model_ext_len : ctx->old_len;

    if (ltlk_obs != NULL) {
        ctx->num_agents = ltlk_obs->num_agents;
        ctx->observable_vars = RTmalloc(sizeof(bitvector_t) * ctx->num_agents);
        for (int a = 0; a < ctx->num_agents; a++) {
            bitvector_create(&ctx->observable_vars[a], ext_len);
            for (int i = 0; i < ctx->old_len; i++) {
                if (bitvector_is_set(&ltlk_obs->observable_vars[a], i))
                    bitvector_set(&ctx->observable_vars[a], i);
            }
        }
        if (ltlk_obs->observable_labels != NULL) {
            ctx->observable_labels = ltlk_obs->observable_labels;
        } else {
            ctx->observable_labels = RTmalloc(sizeof(bitvector_t) * ctx->num_agents);
            for (int a = 0; a < ctx->num_agents; a++) {
                bitvector_create(&ctx->observable_labels[a], ctx->old_edge_labels);
                for (int i = 0; i < ctx->old_edge_labels; i++)
                    bitvector_set(&ctx->observable_labels[a], i);
            }
        }
        return;
    }

    ctx->num_agents = LTLK_NUM_AGENTS > 0 ? LTLK_NUM_AGENTS : 2;
    ctx->observable_vars = RTmalloc(sizeof(bitvector_t) * ctx->num_agents);
    ctx->observable_labels = RTmalloc(sizeof(bitvector_t) * ctx->num_agents);

    for (int a = 0; a < ctx->num_agents; a++) {
        bitvector_create(&ctx->observable_vars[a], ext_len);
        bitvector_create(&ctx->observable_labels[a], ctx->old_edge_labels);
        for (int i = 0; i < ctx->old_len; i++)
            bitvector_set(&ctx->observable_vars[a], i);
        for (int i = 0; i < ctx->old_edge_labels; i++)
            bitvector_set(&ctx->observable_labels[a], i);
    }
}

model_t
GBaddLTLK(model_t model)
{
    if (ltlk_file == NULL) return model;
    if (PINS_LTLK != PINS_LTLK_SYNC_PERFECT_RECALL)
        Abort("Only sync-perfect-recall LTLK semantics is supported");

    lts_type_t ltstype = GBgetLTStype(model);
    char *parsed_formula = NULL;
    bool parsed_ltlk_file = try_parse_ltlk_file_with_obs(ltlk_file, ltstype, &parsed_formula);
    ltsmin_parse_env_t env = LTSminParseEnvCreate();
    ltsmin_expr_t ltlk_expr = ltlk_parse_file(parsed_ltlk_file ? parsed_formula : ltlk_file,
                                              env, ltstype);
    if (parsed_ltlk_file) RTfree(parsed_formula);
    if (ltlk_expr == NULL)
        Abort("Failed to parse LTLK formula: %s", ltlk_file);

    if (has_unsupported_epistemic(ltlk_expr))
        Abort("This LTLK layer currently supports only K_i(phi)");

    ltlk_context_t *ctx = RTmallocZero(sizeof(*ctx));
    ctx->parent = model;
    ctx->original_expr = ltlk_expr;
    ctx->ltlk_expr = ltlk_expr;
    ctx->env = env;
    ctx->old_len = lts_type_get_state_length(ltstype);
    ctx->model_ext_len = ctx->old_len;
    ctx->old_edge_labels = lts_type_get_edge_label_count(ltstype);
    ctx->ltl_idx = 0;

    prepare_past_elimination(ctx, env, ctx->old_len);

    set_pins_semantics(model, ctx->original_expr, env, NULL, NULL);
    ctx->k_base_idx = SIlookup(env->unary_ops, "K0");

    init_observability(ctx);

    ctx->ba = init_ltlk_buchi(model, ctx->ltlk_expr, env);

    /* Build companion automata for every K_i(phi_j) predicate in the outer
     * Büchi automaton.  This MUST happen after init_ltlk_buchi() so that
     * ba->predicates[] is populated.  Each subsequent ltl2ba call inside
     * build_k_atom_companions() is safe because ltl2ba_init() now fully
     * resets the global memory and lex symbol table between invocations.  */
    ctx->k_atoms       = build_k_atom_companions(model, ctx->ba, env);
    ctx->k_atoms_count = ctx->ba->predicate_count;

    ctx->is_weak = is_weak_buchi(ctx->ba);

    int new_len = 1 + ctx->model_ext_len + ctx->num_agents;
    ctx->len = new_len;
    ctx->past_idx = 1 + ctx->old_len;
    ctx->know_idx = 1 + ctx->model_ext_len;

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

    int past_type = lts_type_add_type(ltstype_new, "ltlk_past", NULL);
    lts_type_set_format(ltstype_new, past_type, LTStypeBool);

    lts_type_set_state_name(ltstype_new, ctx->ltl_idx, "ltlk");
    lts_type_set_state_typeno(ltstype_new, ctx->ltl_idx, buchi_type);

    for (int i = 0; i < ctx->old_len; i++) {
        lts_type_set_state_name(ltstype_new, i + 1,
                                lts_type_get_state_name(ltstype, i));
        lts_type_set_state_type(ltstype_new, i + 1,
                                lts_type_get_state_type(ltstype, i));
    }

    for (int i = ctx->old_len; i < ctx->model_ext_len; i++) {
        char name[32];
        snprintf(name, sizeof(name), "__aux_%d", i - ctx->old_len);
        lts_type_set_state_name(ltstype_new, 1 + i, name);
        lts_type_set_state_typeno(ltstype_new, 1 + i, past_type);
    }

    for (int i = 0; i < ctx->past_count; i++) {
        char name[32];
        snprintf(name, sizeof(name), "__past_%d", i);
        lts_type_set_state_name(ltstype_new, 1 + ctx->past_slots[i].state_idx, name);
        lts_type_set_state_typeno(ltstype_new, 1 + ctx->past_slots[i].state_idx, past_type);
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
    for (int j = 0; j < ctx->old_len; j++)
        bitvector_set(&fsd, j);

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
        for (int i = ctx->old_len; i < ctx->model_ext_len; i++) {
            dm_set(new_dm, g, i + 1);
            dm_set(new_dm_r, g, i + 1);
            dm_set(new_dm_w, g, i + 1);
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
        for (int i = ctx->old_len; i < ctx->model_ext_len; i++) {
            dm_set(new_dm, g, i + 1);
            dm_set(new_dm_r, g, i + 1);
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
    for (int i = ctx->old_len; i < ctx->model_ext_len; i++)
        dm_set(new_sl, ctx->sl_idx_accept, i + 1);

    if (ctx->is_weak) {
        dm_set(new_sl, ctx->sl_idx_nonaccept, ctx->ltl_idx);
        for (int a = 0; a < ctx->num_agents; a++)
            dm_set(new_sl, ctx->sl_idx_nonaccept, ctx->know_idx + a);

        for (int i = 0; i < ctx->old_len; i++)
            if (bitvector_is_set(&fsd, i))
                dm_set(new_sl, ctx->sl_idx_nonaccept, i + 1);
        for (int i = ctx->old_len; i < ctx->model_ext_len; i++)
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


    ctx->edge_labels = lts_type_get_edge_label_count(ltstype_new);
    ctx->edge_labels_buf = RTmalloc(sizeof(int) * ctx->edge_labels);

    ctx->knowledge = knowledge_create(model, ctx->model_ext_len, ctx->old_edge_labels,
                                      ctx->num_agents,
                                      ctx->observable_vars,
                                      ctx->observable_labels,
                                      ctx->k_atoms_count, ctx->k_atoms);


    int init[new_len];
    GBgetInitialState(model, init + 1);
    if (ctx->model_ext_len > ctx->old_len) {
        memset(init + 1 + ctx->old_len, 0,
               sizeof(int) * (ctx->model_ext_len - ctx->old_len));
    }
    init[ctx->ltl_idx] = 0;

    int init_bid = knowledge_make_initial_belief(ctx->knowledge, init + 1);
    for (int a = 0; a < ctx->num_agents; a++)
        init[ctx->know_idx + a] = init_bid;

    initialize_past_slots(ctx, init + 1, init + ctx->know_idx);

    GBsetInitialState(out, init);

    lts_type_validate(ltstype_new);

    Print1(info, "LTLK: loaded formula %s", ltlk_file);
    Print1(info, "LTLK: product state length %d (model=%d, buchi=1, knowledge=%d)",
           new_len, ctx->old_len, ctx->num_agents);

    return out;
}
