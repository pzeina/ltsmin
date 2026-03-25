#ifndef PINS_KNOWLEDGE_H
#define PINS_KNOWLEDGE_H

#include <stddef.h>
#include <stdint.h>

#include <dm/bitvector.h>
#include <pins-lib/pins.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct knowledge_mgr knowledge_mgr_t;

typedef struct knowledge_state {
    const size_t *possible_states;
    size_t        word_count;
} knowledge_state_t;

typedef int (*knowledge_eval_cb)(void *ctx, const int *model_state);

/*
    * Companion Büchi automaton specification for a K_i(phi_j) knowledge atom.
    *
    * For each K_i(phi_j) predicate in the outer Büchi automaton:
    *   - ba:  the Büchi automaton for phi_j  (NOT negated; built by
    *          ltsmin_ltl2ba(phi_j) then ltsmin_buchi()).
    *          NULL  ⟺  phi_j is a pure propositional formula – in that case
    *          the traditional knowledge_forall path is used.
    *   - env: the parse environment used to evaluate ba's predicates at model
    *          states that are stored inside the belief set.
    *
    * The BA state is carried as an extra integer appended to every state stored
    * in the belief set:
    *
    *   enriched_state = [ model_state[0 .. model_len-1]
    *                    | ba_q[0 .. num_k_atoms-1] ]
    *
    * Belief updates advance both the model-state part (standard observation
    * filter) and the BA parts (one step of each companion automaton).
    *
    * K_i(phi_j) is TRUE at step t iff every enriched belief state in B_i(t)
    * has the k_j component in a BA state that can still reach an accepting
    * SCC of ba_j (i.e., the companion automaton still has an accepting
    * continuation from that state).
    */

/* Forward declarations – avoid pulling full headers into knowledge.h */
struct ltsmin_buchi;
struct ltsmin_parse_env_s;

typedef struct k_atom_companion {
        struct ltsmin_buchi      *ba;   /**< companion BA for phi_j; NULL => propositional */
        struct ltsmin_parse_env_s *env;  /**< environment for evaluating ba predicates       */
} k_atom_companion_t;

/*
    * On-the-fly belief update under synchronous perfect recall:
 *
 *  input: belief B, observed concrete successor s', agent i
 *  output: B' = { t' | exists t in B . (t -> t') and obs_i(t') = obs_i(s') }
 *
 *  pseudocode:
 *
 *    B' := empty
 *    for each t in B:
 *        for each successor t' of t:
 *            if same_observation(i, t', s'):
 *                add t' to B'
 *    return intern(B')   // canonical hash-consing
    *
    * With companion automata the same loop additionally advances each
    * companion BA state based on the predicates evaluated at t'.
 */
/**
 * Create a knowledge manager.
 *
 * @param parent_model    base PINS model (for GBgetTransitionsAll)
 * @param model_len       state-vector length of parent_model
 * @param edge_label_count number of edge labels in parent_model
 * @param num_agents      number of agents
 * @param observable_vars per-agent observable-variable bitvectors
 *                        (length = num_agents, indexed over model state vars)
 * @param observable_labels per-agent observable-edge-label bitvectors
 *                        (length = num_agents, indexed over edge labels)
 * @param num_k_atoms     number of K_i(phi_j) atoms in the formula
 *                        (= outer Büchi predicate count; use 0 for the old
 *                         behaviour where all predicates are propositional)
 * @param k_atoms         array of length num_k_atoms with one entry per
 *                        outer BA predicate; entries with ba==NULL are
 *                        treated as plain propositional predicates.
 *                        May be NULL when num_k_atoms == 0.
 */
knowledge_mgr_t *knowledge_create(model_t parent_model, int model_len,
                                  int edge_label_count,
                                  int num_agents,
                                  const bitvector_t *observable_vars,
                                  const bitvector_t *observable_labels,
                                  int num_k_atoms,
                                  const k_atom_companion_t *k_atoms);

void knowledge_destroy(knowledge_mgr_t *km);

int knowledge_num_agents(const knowledge_mgr_t *km);

/**
 * Legacy helper: register the INITIAL model state as
 * [model_state | 0 | 0 | ...] (companion BA states initialised to 0).
 *
 * This does NOT advance companion BAs on the initial valuation.
 * LTLK product initialization should use knowledge_make_initial_belief().
 */
int knowledge_register_initial_state(knowledge_mgr_t *km,
                                                                         const int *model_state);

int knowledge_make_initial_belief(knowledge_mgr_t *km,
                                  const int *model_state);

int knowledge_register_state(knowledge_mgr_t *km, const int *state);

const int *knowledge_get_state(const knowledge_mgr_t *km, int state_id);

int knowledge_make_singleton(knowledge_mgr_t *km, int state_id);

int knowledge_update_belief(knowledge_mgr_t *km, int agent, int belief_id,
                            const int *observed_successor_state,
                            const int *observed_edge_labels);

knowledge_state_t knowledge_get_belief(const knowledge_mgr_t *km, int belief_id);

int knowledge_forall(const knowledge_mgr_t *km, int belief_id,
                     knowledge_eval_cb cb, void *cb_ctx);

/**
 * Evaluate K_i(phi_j) using the companion automaton for k_atom_idx.
 *
 * Returns 1  if every enriched belief state has ba_j in a state that can
 *            still reach an accepting SCC.
 * Returns 0  if at least one enriched belief state is already in a BA state
 *            with no accepting continuation, or
 *            if ba_j == NULL (caller should fall back to knowledge_forall).
 * Returns -1 if k_atom_idx is out of range or has no companion BA (ba==NULL).
 */
int knowledge_k_atom_holds(const knowledge_mgr_t *km, int belief_id,
                                                     int k_atom_idx);

#ifdef __cplusplus
}
#endif

#endif
