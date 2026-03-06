#ifndef PINS2PINS_LTLK
#define PINS2PINS_LTLK

#include <pins-lib/pins.h>
#include <ltsmin-lib/ltsmin-tl.h>

/**
\brief The behaviour of the LTLK (epistemic LTL) product

LTLK extends LTL with epistemic operators for multi-agent systems.
The semantics are based on synchronous perfect recall with 
observational equivalence.
*/
typedef enum {
    PINS_LTLK_SYNC_PERFECT_RECALL,  // Synchronous with perfect recall
    PINS_LTLK_ASYNC_PERFECT_RECALL, // Asynchronous with perfect recall
    PINS_LTLK_SYNC_NO_RECALL,       // Synchronous without memory
} pins_ltlk_type_t;

/**
 * \brief boolean indicating whether PINS uses LTLK
 */
extern pins_ltlk_type_t PINS_LTLK;

/**
 * \brief number of agents in the system
 */
extern int LTLK_NUM_AGENTS;

/**
 * \brief observability configuration for agents
 * Array where each element i contains a bitvector indicating
 * which state variables agent i can observe
 */
typedef struct {
    int num_agents;
    bitvector_t *observable_vars;  // Per-agent observable state variables
} ltlk_obs_config_t;

/**
\brief Add LTLK layer on top of all other pins layers

This layer creates a product of the model with the knowledge automaton
derived from the LTLK formula, using observational equivalence for
epistemic operators.
*/
extern model_t GBaddLTLK(model_t model);

/**
\brief Set the observability configuration for agents

This must be called before GBaddLTLK if you want to specify
which state variables each agent can observe. If not called,
all agents can observe all state variables by default.

\param config Observability configuration structure
*/
extern void GBsetLTLKObservability(ltlk_obs_config_t *config);

/**
\brief Get the current observability configuration
*/
extern ltlk_obs_config_t* GBgetLTLKObservability();

extern struct poptOption ltlk_options[];

#endif // PINS2PINS_LTLK
