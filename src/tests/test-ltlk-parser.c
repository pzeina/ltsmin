#include <hre/config.h>

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#undef Debug
#include <hre/user.h>
#include <ltsmin-lib/ltl2ba-lex.h>
#ifdef HAVE_SPOT
#include <ltsmin-lib/ltl2spot.h>
#endif
#include <ltsmin-lib/lts-type.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <ltsmin-lib/ltsmin-buchi.h>
#include <ltsmin-lib/ltsmin-syntax.h>
#include <ltsmin-lib/ltsmin-tl.h>
#include <pins-lib/pins.h>

static lts_type_t
make_test_type(void)
{
    lts_type_t ltstype = lts_type_create();
    lts_type_set_state_length(ltstype, 1);
    lts_type_set_state_name(ltstype, 0, "x");
    lts_type_set_state_type(ltstype, 0, "state");
    lts_type_set_state_label_count(ltstype, 1);
    lts_type_set_state_label_name(ltstype, 0, "p");
    lts_type_set_state_label_type(ltstype, 0, "boolean");
    lts_type_set_edge_label_count(ltstype, 1);
    lts_type_set_edge_label_name(ltstype, 0, LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    lts_type_set_edge_label_type(ltstype, 0, LTSMIN_EDGE_TYPE_ACTION_PREFIX);
    return ltstype;
}

static int
count_predicates_with_token(ltsmin_buchi_t *ba, int token)
{
    int count = 0;
    for (int i = 0; i < ba->predicate_count; i++) {
        if (ba->predicates[i]->token == token)
            count++;
    }
    return count;
}

static int
has_past_operator(const ltsmin_expr_t e)
{
    if (e == NULL) return 0;
    switch (e->node_type) {
    case UNARY_OP:
        if (e->token == LTLK_PREVIOUS || e->token == LTLK_ONCE || e->token == LTLK_HISTORICALLY)
            return 1;
        return has_past_operator(e->arg1);
    case BINARY_OP:
        if (e->token == LTLK_SINCE)
            return 1;
        return has_past_operator(e->arg1) || has_past_operator(e->arg2);
    default:
        return 0;
    }
}

static ltsmin_buchi_t *
build_buchi_from_neg(ltsmin_expr_t neg, ltsmin_parse_env_t env)
{
    if (has_past_operator(neg)) {
#ifdef HAVE_SPOT
        ltsmin_ltl2spot(neg, 0, env);
        return ltsmin_hoa_buchi(env);
#else
        return NULL;
#endif
    }

    ltsmin_ltl2ba(neg);
    return ltsmin_buchi();
}

static void
check_formula_once(const char *formula, int expected_k_preds)
{
    lts_type_t ltstype = make_test_type();
    ltsmin_parse_env_t env = LTSminParseEnvCreate();
    ltsmin_expr_t expr = ltlk_parse_file(formula, env, ltstype);
    assert(expr != NULL);

    ltsmin_expr_t neg = LTSminExpr(UNARY_OP, LTLK_NOT, 0, expr, NULL);
    ltsmin_buchi_t *ba = build_buchi_from_neg(neg, env);
#ifndef HAVE_SPOT
    if (ba == NULL) {
        /* Past operators require Spot; parser/type-check coverage is still valid. */
        LTSminParseEnvDestroy(env);
        return;
    }
#endif
    assert(ba != NULL);
    assert(count_predicates_with_token(ba, LTLK_KNOWS) == expected_k_preds);

    LTSminParseEnvDestroy(env);
}

static void
check_formula(const char *formula, int expected_k_preds)
{
    pid_t pid = fork();
    assert(pid >= 0);

    if (pid == 0) {
        check_formula_once(formula, expected_k_preds);
        _exit(EXIT_SUCCESS);
    }

    int status = 0;
    pid_t waited = waitpid(pid, &status, 0);
    assert(waited == pid);
    assert(WIFEXITED(status));
    assert(WEXITSTATUS(status) == EXIT_SUCCESS);
}

static void
check_reproducibility(void)
{
    for (int i = 0; i < 100; i++) {
        check_formula("<> (K0(true) && K1(true))", 2);
    }
}

static void
check_scalability(void)
{
    check_formula("<> (K0(true) && K1(true) && K2(true) && K3(true) && K4(true) && K5(true) && K6(true) && K7(true))", 8);
}

int
main(int argc, char *argv[])
{
    HREinitBegin(argv[0]);
    HREinitStart(&argc, &argv, 0, 0, NULL, "");

    check_formula("K0(true)", 1);
    check_formula("<> K0(true)", 1);
    check_formula("K0(<> true)", 1);
    check_formula("K0([] true)", 1);
    check_formula("K0(true U true)", 1);
    check_formula("<> K0([] true)", 1);
    check_formula("<> (K0(true) && K1(true))", 2);
#ifdef HAVE_SPOT
    check_formula("K0(O true)", 1);
    check_formula("K0(H true)", 1);
    check_formula("K0(Y true)", 1);
    check_formula("K0(true S true)", 1);
#endif
    check_reproducibility();
    check_scalability();

    return 0;
}
