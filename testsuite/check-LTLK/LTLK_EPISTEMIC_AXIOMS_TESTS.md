# LTLK Epistemic Axioms Regression Tests

This document describes the epistemic-axiom test block in
`testsuite/check-LTLK/cases.txt`.

All tests in this block are expected to be true under synchronous perfect recall.
In this harness, that means:

- exit code: `0`
- output contains: `Empty product with LTL!`

## Axiom Schemas Covered

The suite targets four axioms:

1. Veridicality: `K_a phi => phi`
2. Positive introspection: `K_a phi => K_a K_a phi`
3. Negative introspection: `!K_a phi => K_a !K_a phi`
4. Non-forgetting: direct and persistence forms are both supported

## Coverage Goals and Dimensions

Coverage is intentionally widened across three dimensions:

1. Agents: both `a=0` and `a=1` are tested.
2. Observability definitions: formulas include explicit `agents` and `obs` declarations.
3. Systems/models: tests are distributed over multiple DVE systems.

Models covered:

- `examples/simple_ltlk.dve`
- `examples/anderson.1.prop4.dve`
- `testsuite/check-LTLK/models/custom_obs_demo.dve`

## Test Matrix

### Baseline Axiom Instances

These are the original four anchor tests:

- `ax_veridicality`
- `ax_positive_introspection`
- `ax_negative_introspection`
- `ax_non_forgetting`

### Expanded Coverage Instances

The following files provide cross-agent and cross-system expansion:

#### Veridicality

- `testsuite/check-LTLK/formulas/ax_v_simple_a0_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_v_anderson_a1_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_v_custom_a0_obs.ltlk`

#### Positive introspection

- `testsuite/check-LTLK/formulas/ax_pi_simple_a1_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_pi_anderson_a0_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_pi_custom_a0_obs.ltlk`

#### Negative introspection

- `testsuite/check-LTLK/formulas/ax_ni_simple_a0_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_ni_anderson_a1_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_ni_custom_a1_obs.ltlk`

#### Non-forgetting

- `testsuite/check-LTLK/formulas/ax_nf_simple_a1_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_nf_anderson_a1_obs.ltlk`
- `testsuite/check-LTLK/formulas/ax_nf_custom_a0_obs.ltlk`

Total axiom tests:

- 4 baseline + 12 expanded = 16 axiom tests

## Notes on Non-forgetting Formula Shape

The direct shape

- `K_a(phi) -> [] K_a(O phi)`

now runs successfully in the current backend. The suite keeps the persistence equivalent as the canonical regression case:

- `K_a(O phi) -> [] K_a(O phi)`

This still tests the key property that known past facts remain known, while the direct form is validated separately as a non-crashing supported shape.

## How to Run

Run the full LTLK regression suite:

```bash
cd ~/Documents/ltsmin/ltsmin
./testsuite/check-LTLK/run-ltlk-regression.sh
```

Current expected summary after expansion:

```text
Summary: 50/50 passed, 0 failed
```

## Integration Point

All axiom tests are registered in:

- `testsuite/check-LTLK/cases.txt`
