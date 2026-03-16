#include <hre/config.h>

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include <hre/user.h>
#include <pins-lib/knowledge.h>
#include <ltsmin-lib/ltsmin-buchi.h>
#include <pins-lib/property-semantics.h>

typedef struct knowledge_belief {
    size_t   *words;
    size_t    word_count;
    uint64_t  hash;
} knowledge_belief_t;

typedef struct knowledge_state_tbl {
    int      *flat;
    int       count;
    int       capacity;
    int      *hash_slots;
    int       hash_cap;
} knowledge_state_tbl_t;

typedef struct knowledge_belief_tbl {
    knowledge_belief_t *items;
    int                 count;
    int                 capacity;
    int                *hash_slots;
    int                 hash_cap;
} knowledge_belief_tbl_t;

struct knowledge_mgr {
    model_t                 parent;
     int                     model_len;     /* original model state length          */
     int                     state_length;  /* enriched = model_len + num_k_atoms   */
    int                     num_agents;
    const bitvector_t      *observable_vars;
    knowledge_state_tbl_t   states;
    knowledge_belief_tbl_t  beliefs;
     /* companion Büchi automata for K_i(phi_j) predicates ------------------- */
     int                       num_k_atoms; /* 0 => propositional-only (legacy) */
     const k_atom_companion_t *k_atoms;     /* array[num_k_atoms]; may be NULL  */
};

#define EMPTY_SLOT (-1)

static inline uint64_t
mix_u64(uint64_t h, uint64_t x)
{
    h ^= x + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
    return h;
}

static uint64_t
hash_int_state(const int *state, int len)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (int i = 0; i < len; i++) {
        h ^= (uint32_t)state[i];
        h *= 0x100000001b3ULL;
    }
    return h;
}

static uint64_t
hash_belief_words(const size_t *words, size_t count)
{
    uint64_t h = 0x9e3779b97f4a7c15ULL;
    h = mix_u64(h, count);
    for (size_t i = 0; i < count; i++) {
        h = mix_u64(h, (uint64_t)words[i]);
    }
    return h;
}

static void
state_hash_init(knowledge_state_tbl_t *tbl)
{
    tbl->hash_cap = 1024;
    tbl->hash_slots = RTmalloc(sizeof(int) * tbl->hash_cap);
    for (int i = 0; i < tbl->hash_cap; i++) tbl->hash_slots[i] = EMPTY_SLOT;
}

static void
belief_hash_init(knowledge_belief_tbl_t *tbl)
{
    tbl->hash_cap = 1024;
    tbl->hash_slots = RTmalloc(sizeof(int) * tbl->hash_cap);
    for (int i = 0; i < tbl->hash_cap; i++) tbl->hash_slots[i] = EMPTY_SLOT;
}

static void
state_hash_rebuild(knowledge_mgr_t *km)
{
    knowledge_state_tbl_t *tbl = &km->states;
    int *old = tbl->hash_slots;
    int old_cap = tbl->hash_cap;

    tbl->hash_cap *= 2;
    tbl->hash_slots = RTmalloc(sizeof(int) * tbl->hash_cap);
    for (int i = 0; i < tbl->hash_cap; i++) tbl->hash_slots[i] = EMPTY_SLOT;

    for (int i = 0; i < tbl->count; i++) {
        const int *state = tbl->flat + (size_t)i * km->state_length;
        uint64_t hash = hash_int_state(state, km->state_length);
        int pos = (int)(hash & (uint64_t)(tbl->hash_cap - 1));
        while (tbl->hash_slots[pos] != EMPTY_SLOT)
            pos = (pos + 1) & (tbl->hash_cap - 1);
        tbl->hash_slots[pos] = i;
    }

    RTfree(old);
    (void)old_cap;
}

static void
belief_hash_rebuild(knowledge_mgr_t *km)
{
    knowledge_belief_tbl_t *tbl = &km->beliefs;
    int *old = tbl->hash_slots;

    tbl->hash_cap *= 2;
    tbl->hash_slots = RTmalloc(sizeof(int) * tbl->hash_cap);
    for (int i = 0; i < tbl->hash_cap; i++) tbl->hash_slots[i] = EMPTY_SLOT;

    for (int i = 0; i < tbl->count; i++) {
        uint64_t hash = tbl->items[i].hash;
        int pos = (int)(hash & (uint64_t)(tbl->hash_cap - 1));
        while (tbl->hash_slots[pos] != EMPTY_SLOT)
            pos = (pos + 1) & (tbl->hash_cap - 1);
        tbl->hash_slots[pos] = i;
    }

    RTfree(old);
}

static bool
same_observation(const knowledge_mgr_t *km, int agent,
                 const int *lhs, const int *rhs)
{
    const bitvector_t *obs = &km->observable_vars[agent];
     /* Only compare the MODEL portion; BA-state slots are never observable. */
     for (int i = 0; i < km->model_len; i++) {
        if (bitvector_is_set(obs, i) && lhs[i] != rhs[i]) return false;
    }
    return true;
}

static int
state_lookup(const knowledge_mgr_t *km, const int *state)
{
    const knowledge_state_tbl_t *tbl = &km->states;
    uint64_t hash = hash_int_state(state, km->state_length);
    int pos = (int)(hash & (uint64_t)(tbl->hash_cap - 1));

    while (tbl->hash_slots[pos] != EMPTY_SLOT) {
        int id = tbl->hash_slots[pos];
        const int *cur = tbl->flat + (size_t)id * km->state_length;
        if (memcmp(cur, state, sizeof(int) * km->state_length) == 0)
            return id;
        pos = (pos + 1) & (tbl->hash_cap - 1);
    }
    return -1;
}

int
knowledge_register_state(knowledge_mgr_t *km, const int *state)
{
    int id = state_lookup(km, state);
    if (id >= 0) return id;

    knowledge_state_tbl_t *tbl = &km->states;
    if (tbl->count >= (tbl->hash_cap * 7) / 10)
        state_hash_rebuild(km);

    if (tbl->count == tbl->capacity) {
        int new_cap = tbl->capacity * 2;
        tbl->flat = RTrealloc(tbl->flat, sizeof(int) * (size_t)new_cap * km->state_length);
        tbl->capacity = new_cap;
    }

    id = tbl->count++;
    int *dst = tbl->flat + (size_t)id * km->state_length;
    memcpy(dst, state, sizeof(int) * km->state_length);

    uint64_t hash = hash_int_state(state, km->state_length);
    int pos = (int)(hash & (uint64_t)(tbl->hash_cap - 1));
    while (tbl->hash_slots[pos] != EMPTY_SLOT)
        pos = (pos + 1) & (tbl->hash_cap - 1);
    tbl->hash_slots[pos] = id;

    return id;
}

static inline void
belief_bit_set(size_t *words, int id)
{
    size_t word = (size_t)id / (8 * sizeof(size_t));
    size_t bit = (size_t)id % (8 * sizeof(size_t));
    words[word] |= ((size_t)1 << bit);
}

static int
belief_lookup(const knowledge_mgr_t *km, const size_t *words, size_t word_count, uint64_t hash)
{
    const knowledge_belief_tbl_t *tbl = &km->beliefs;
    int pos = (int)(hash & (uint64_t)(tbl->hash_cap - 1));

    while (tbl->hash_slots[pos] != EMPTY_SLOT) {
        int id = tbl->hash_slots[pos];
        const knowledge_belief_t *b = &tbl->items[id];
        if (b->word_count == word_count &&
            (word_count == 0 || memcmp(b->words, words, sizeof(size_t) * word_count) == 0))
            return id;
        pos = (pos + 1) & (tbl->hash_cap - 1);
    }
    return -1;
}

static int
intern_belief(knowledge_mgr_t *km, const size_t *words, size_t word_count)
{
    while (word_count > 0 && words[word_count - 1] == 0) word_count--;

    uint64_t hash = hash_belief_words(words, word_count);
    int id = belief_lookup(km, words, word_count, hash);
    if (id >= 0) return id;

    knowledge_belief_tbl_t *tbl = &km->beliefs;
    if (tbl->count >= (tbl->hash_cap * 7) / 10)
        belief_hash_rebuild(km);

    if (tbl->count == tbl->capacity) {
        int new_cap = tbl->capacity * 2;
        tbl->items = RTrealloc(tbl->items, sizeof(knowledge_belief_t) * new_cap);
        tbl->capacity = new_cap;
    }

    id = tbl->count++;
    knowledge_belief_t *slot = &tbl->items[id];
    slot->word_count = word_count;
    slot->hash = hash;
    if (word_count == 0) {
        slot->words = NULL;
    } else {
        slot->words = RTmalloc(sizeof(size_t) * word_count);
        memcpy(slot->words, words, sizeof(size_t) * word_count);
    }

    int pos = (int)(hash & (uint64_t)(tbl->hash_cap - 1));
    while (tbl->hash_slots[pos] != EMPTY_SLOT)
        pos = (pos + 1) & (tbl->hash_cap - 1);
    tbl->hash_slots[pos] = id;

    return id;
}

knowledge_mgr_t *
 knowledge_create(model_t parent_model, int model_len, int num_agents,
                  const bitvector_t *observable_vars,
                  int num_k_atoms, const k_atom_companion_t *k_atoms)
{
    knowledge_mgr_t *km = RTmallocZero(sizeof(*km));
    km->parent = parent_model;
     km->model_len    = model_len;
     km->num_k_atoms  = num_k_atoms;
     km->k_atoms      = k_atoms;
     /* Enriched state length = model part + one int per K-atom for BA state */
     km->state_length = model_len + num_k_atoms;
    km->num_agents = num_agents;
    km->observable_vars = observable_vars;

    km->states.capacity = 1024;
     km->states.flat = RTmalloc(sizeof(int) * (size_t)km->states.capacity * km->state_length);
    km->states.count = 0;
    state_hash_init(&km->states);

    km->beliefs.capacity = 1024;
    km->beliefs.items = RTmallocZero(sizeof(knowledge_belief_t) * km->beliefs.capacity);
    km->beliefs.count = 0;
    belief_hash_init(&km->beliefs);

    (void)intern_belief(km, NULL, 0);

    return km;
}

void
knowledge_destroy(knowledge_mgr_t *km)
{
    if (km == NULL) return;

    for (int i = 0; i < km->beliefs.count; i++)
        RTfree(km->beliefs.items[i].words);

    RTfree(km->beliefs.items);
    RTfree(km->beliefs.hash_slots);
    RTfree(km->states.flat);
    RTfree(km->states.hash_slots);
    RTfree(km);
}

int
knowledge_num_agents(const knowledge_mgr_t *km)
{
    return km->num_agents;
}

const int *
knowledge_get_state(const knowledge_mgr_t *km, int state_id)
{
    if (state_id < 0 || state_id >= km->states.count)
        Abort("knowledge_get_state: invalid state id %d", state_id);
    return km->states.flat + (size_t)state_id * km->state_length;
}

int
knowledge_make_singleton(knowledge_mgr_t *km, int state_id)
{
    size_t word_count = (size_t)state_id / (8 * sizeof(size_t)) + 1;
    size_t *words = RTmallocZero(sizeof(size_t) * word_count);
    belief_bit_set(words, state_id);
    int id = intern_belief(km, words, word_count);
    RTfree(words);
    return id;
}

 int
 knowledge_register_initial_state(knowledge_mgr_t *km, const int *model_state)
 {
     if (km->num_k_atoms == 0) {
         /* No companion BAs: register the bare model state directly. */
         return knowledge_register_state(km, model_state);
     }
     /* Build enriched state: [model_state | 0 … 0] for all companion BAs. */
     int enriched[km->state_length];
     memcpy(enriched, model_state, sizeof(int) * km->model_len);
     for (int k = 0; k < km->num_k_atoms; k++)
         enriched[km->model_len + k] = 0; /* initial BA state = 0 */
     return knowledge_register_state(km, enriched);
 }

 typedef struct update_cb_ctx {
    knowledge_mgr_t *km;
    int              agent;
    const int       *observed;
     const int       *src_enriched;  /* full enriched source state (model+BA) */
    size_t          *tmp_words;
    size_t           tmp_count;
} update_cb_ctx_t;

 /* --------------------------------------------------------------------- */
 /* Helper: add an enriched state to the new belief word array.            */
 /* --------------------------------------------------------------------- */
 static void
 belief_add_enriched(update_cb_ctx_t *ctx, const int *enriched)
 {
     int sid = knowledge_register_state(ctx->km, enriched);
     size_t word = (size_t)sid / (8 * sizeof(size_t));
     if (word >= ctx->tmp_count) {
         size_t old = ctx->tmp_count;
         size_t new_count = ctx->tmp_count;
         while (word >= new_count) new_count = new_count * 2 + 1;
         ctx->tmp_words = RTrealloc(ctx->tmp_words, sizeof(size_t) * new_count);
         memset(ctx->tmp_words + old, 0, sizeof(size_t) * (new_count - old));
         ctx->tmp_count = new_count;
     }
     belief_bit_set(ctx->tmp_words, sid);
 }

 /* --------------------------------------------------------------------- */
 /* Recursive expansion of non-deterministic companion BA transitions.     */
 /* `enriched' holds the model part (already filled); we fill BA slots     */
 /* starting at k_idx and then add to the new belief set.                  */
 /* --------------------------------------------------------------------- */
 static void
 expand_ba_states(update_cb_ctx_t *ctx, int *enriched, int k_idx)
 {
     knowledge_mgr_t *km = ctx->km;

     if (k_idx >= km->num_k_atoms) {
         belief_add_enriched(ctx, enriched);
         return;
     }

     const k_atom_companion_t *atom = &km->k_atoms[k_idx];

     if (atom->ba == NULL) {
         /* Propositional K-atom: no companion BA – carry a 0 placeholder. */
         enriched[km->model_len + k_idx] = 0;
         expand_ba_states(ctx, enriched, k_idx + 1);
         return;
     }

     int old_q = ctx->src_enriched[km->model_len + k_idx];

     /* If this belief state already carries the "dead / rejected" sentinel
      * (= ba->state_count, one beyond the valid range) it was rejected by
      * the companion automaton at some earlier step.  Keep it permanently
      * with the sentinel so knowledge_k_atom_holds() always returns FALSE.  */
     if (old_q == atom->ba->state_count) {
         enriched[km->model_len + k_idx] = atom->ba->state_count;
         expand_ba_states(ctx, enriched, k_idx + 1);
         enriched[km->model_len + k_idx] = 0;
         return;
     }

     /* Unrecognised out-of-range state: treat as dead. */
     if (old_q < 0 || old_q >= atom->ba->state_count) {
         enriched[km->model_len + k_idx] = atom->ba->state_count;
         expand_ba_states(ctx, enriched, k_idx + 1);
         enriched[km->model_len + k_idx] = 0;
         return;
     }

     /* Evaluate the companion BA's predicates at the MODEL dest state. */
     int pred_bits = 0;
     for (int p = 0; p < atom->ba->predicate_count; p++) {
         if (eval_state_predicate(km->parent, atom->ba->predicates[p],
                                  enriched /*model part*/, atom->env))
             pred_bits |= (1 << p);
     }

     /* Find all matching transitions from old_q. */
     ltsmin_buchi_state_t *bs = atom->ba->states[old_q];
     bool any = false;
     for (int t = 0; t < bs->transition_count; t++) {
         ltsmin_buchi_transition_t *tr = &bs->transitions[t];
         if ((pred_bits & tr->pos[0]) != tr->pos[0]) continue;
         if ((pred_bits & tr->neg[0]) != 0)           continue;
         any = true;
         /* Copy for each branch (harmless on the common single-succ path). */
         int saved_q = enriched[km->model_len + k_idx];
         enriched[km->model_len + k_idx] = tr->to_state;
         if (bs->transition_count == 1) {
             /* Common case: deterministic – no copy needed. */
             expand_ba_states(ctx, enriched, k_idx + 1);
         } else {
             /* Non-deterministic: deep-copy so sibling branches are clean. */
             int copy[km->state_length];
             memcpy(copy, enriched, sizeof(int) * km->state_length);
             expand_ba_states(ctx, copy, k_idx + 1);
         }
         enriched[km->model_len + k_idx] = saved_q;
     }

     if (!any) {
         /* No valid BA transition (the companion automaton has rejected this
          * trajectory for this belief state).  We still keep the belief state
          * in the set, but mark it with a "dead/non-accepting" sentinel index
          * (= ba->state_count, which is one beyond the valid range) so that
          * knowledge_k_atom_holds() correctly returns FALSE.               */
         enriched[km->model_len + k_idx] = atom->ba->state_count;
         expand_ba_states(ctx, enriched, k_idx + 1);
         /* Restore so the outer loop can continue cleanly. */
         enriched[km->model_len + k_idx] = 0;
     }
 }

static void
knowledge_update_cb(void *context, transition_info_t *ti, int *dst, int *cpy)
{
    (void)ti; (void)cpy;
    update_cb_ctx_t *ctx = (update_cb_ctx_t *)context;

    if (!same_observation(ctx->km, ctx->agent, dst, ctx->observed))
        return;

     if (ctx->km->num_k_atoms == 0) {
         /* Simple (legacy) path: no companion BAs. */
         belief_add_enriched(ctx, dst);
     } else {
         /* Enriched path: combine model dst with advanced companion BA states. */
         int enriched[ctx->km->state_length];
         memcpy(enriched, dst, sizeof(int) * ctx->km->model_len);
         /* BA states will be filled by expand_ba_states; zero first. */
         memset(enriched + ctx->km->model_len, 0,
                sizeof(int) * ctx->km->num_k_atoms);
         expand_ba_states(ctx, enriched, 0);
     }
}

int
knowledge_update_belief(knowledge_mgr_t *km, int agent, int belief_id,
                        const int *observed_successor_state)
{
    if (agent < 0 || agent >= km->num_agents)
        Abort("knowledge_update_belief: invalid agent %d", agent);
    if (belief_id < 0 || belief_id >= km->beliefs.count)
        Abort("knowledge_update_belief: invalid belief %d", belief_id);

    const knowledge_belief_t *belief = &km->beliefs.items[belief_id];
    size_t tmp_count = belief->word_count == 0 ? 1 : belief->word_count;
    size_t *tmp_words = RTmallocZero(sizeof(size_t) * tmp_count);

    for (size_t word = 0; word < belief->word_count; word++) {
        size_t bits = belief->words[word];
        while (bits != 0) {
            size_t lsb = bits & (~bits + 1);
            int bit = __builtin_ctzl(bits);
            int sid = (int)(word * (8 * sizeof(size_t)) + (size_t)bit);
            bits ^= lsb;

            const int *src = knowledge_get_state(km, sid);
            update_cb_ctx_t cb_ctx = {
                .km = km,
                .agent = agent,
                .observed = observed_successor_state,
                 .src_enriched = src,
                .tmp_words = tmp_words,
                .tmp_count = tmp_count,
            };
            GBgetTransitionsAll(km->parent, (int *)src, knowledge_update_cb, &cb_ctx);
            tmp_words = cb_ctx.tmp_words;
            tmp_count = cb_ctx.tmp_count;
        }
    }

    int next = intern_belief(km, tmp_words, tmp_count);
    RTfree(tmp_words);
    return next;
}

knowledge_state_t
knowledge_get_belief(const knowledge_mgr_t *km, int belief_id)
{
    if (belief_id < 0 || belief_id >= km->beliefs.count)
        Abort("knowledge_get_belief: invalid belief id %d", belief_id);

    knowledge_state_t out;
    out.possible_states = km->beliefs.items[belief_id].words;
    out.word_count = km->beliefs.items[belief_id].word_count;
    return out;
}

int
knowledge_forall(const knowledge_mgr_t *km, int belief_id,
                 knowledge_eval_cb cb, void *cb_ctx)
{
    if (belief_id < 0 || belief_id >= km->beliefs.count)
        Abort("knowledge_forall: invalid belief id %d", belief_id);

    const knowledge_belief_t *belief = &km->beliefs.items[belief_id];
    for (size_t word = 0; word < belief->word_count; word++) {
        size_t bits = belief->words[word];
        while (bits != 0) {
            int bit = __builtin_ctzl(bits);
            int sid = (int)(word * (8 * sizeof(size_t)) + (size_t)bit);
            bits &= bits - 1;

            const int *state = knowledge_get_state(km, sid);
             /* Pass only the model portion so callbacks see a plain model state. */
             if (!cb(cb_ctx, state)) return 0;   /* state[0..model_len-1] are model vars */
        }
    }
    return 1;
}

 int
 knowledge_k_atom_holds(const knowledge_mgr_t *km, int belief_id, int k_atom_idx)
 {
     if (k_atom_idx < 0 || k_atom_idx >= km->num_k_atoms) return -1;

     const k_atom_companion_t *atom = &km->k_atoms[k_atom_idx];
     if (atom->ba == NULL) return -1;   /* propositional: caller uses knowledge_forall */

     if (belief_id < 0 || belief_id >= km->beliefs.count)
         Abort("knowledge_k_atom_holds: invalid belief id %d", belief_id);

     const knowledge_belief_t *belief = &km->beliefs.items[belief_id];

     /* Empty belief set: vacuously true. */
     if (belief->word_count == 0) return 1;

     for (size_t word = 0; word < belief->word_count; word++) {
         size_t bits = belief->words[word];
         while (bits != 0) {
             int bit = __builtin_ctzl(bits);
             int sid = (int)(word * (8 * sizeof(size_t)) + (size_t)bit);
             bits &= bits - 1;

             const int *enriched = knowledge_get_state(km, sid);
             int q = enriched[km->model_len + k_atom_idx];

             /* Dead sentinel (= ba->state_count) or any out-of-range value:
              * the companion automaton rejected this trajectory.          */
             if (q < 0 || q >= atom->ba->state_count) return 0;

             /* K_i(phi_j) is true only if ALL belief-state companion BA states
              * are currently ACCEPTING.  For safety formulas (G p) the BA has
              * one accepting sink; for liveness (F p) the accepting state is
              * reached once p has been witnessed.                            */
             if (!atom->ba->states[q]->accept) return 0;
         }
     }
     return 1;
 }
