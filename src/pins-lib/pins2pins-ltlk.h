#ifndef PINS2PINS_LTLK
#define PINS2PINS_LTLK

#include <pins-lib/pins.h>
#include <ltsmin-lib/ltsmin-tl.h>

/**
\brief LTLK (LTL with knowledge) product layer.

This layer builds an on-the-fly product of:
 - model state,
 - Buchi state,
 - per-agent knowledge monitor state (belief set id).

Semantics implemented here: synchronous perfect recall.
Knowledge operator supported in formulas: K_i phi.
*/
typedef enum {
    PINS_LTLK_SYNC_PERFECT_RECALL,
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
 * \brief observability configuration for agents.
 *
 * Each bitvector marks which model variables are observable by the agent.
 */
typedef struct {
    int num_agents;
    bitvector_t *observable_vars;
} ltlk_obs_config_t;

/**
\brief Add LTLK layer on top of all other pins layers

The resulting product can be explored with the standard on-the-fly
Buchi cycle detection algorithms.
*/
extern model_t GBaddLTLK(model_t model);

/**
\brief Set the observability configuration for agents

This must be called before GBaddLTLK if you want to specify
which state variables each agent can observe. If not called, all
agents observe all model variables by default.

\param config Observability configuration structure
*/
extern void GBsetLTLKObservability(ltlk_obs_config_t *config);

/**
\brief Get the current observability configuration
*/
extern ltlk_obs_config_t* GBgetLTLKObservability();

extern struct poptOption ltlk_options[];

#endif // PINS2PINS_LTLK
