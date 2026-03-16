#include <hre/config.h>

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#undef Debug
#include <hre/user.h>
#include <ltsmin-lib/ltl2ba-lex.h>
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

static void
check_formula_once(const char *formula, int expected_k_preds)
{
    lts_type_t ltstype = make_test_type();
    ltsmin_parse_env_t env = LTSminParseEnvCreate();
    ltsmin_expr_t expr = ltlk_parse_file(formula, env, ltstype);
    assert(expr != NULL);

    ltsmin_expr_t neg = LTSminExpr(UNARY_OP, LTLK_NOT, 0, expr, NULL);
    ltsmin_ltl2ba(neg);
    ltsmin_buchi_t *ba = ltsmin_buchi();
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
    check_reproducibility();
    check_scalability();

    return 0;
}
