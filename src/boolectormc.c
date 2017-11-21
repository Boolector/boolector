/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolectormc.h"

#include "boolector.h"
#include "btorabort.h"
#include "btorcore.h"
#include "btormsg.h"
#include "btornode.h"
#include "btoropt.h"
#include "dumper/btordumpbtor.h"
#include "utils/boolectornodemap.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

#include <stdarg.h>

/*------------------------------------------------------------------------*/

#define BTOR_MC_ABORT_IF_STATE(MC)               \
  do                                             \
  {                                              \
    BTOR_ABORT ((MC)->state != BTOR_NO_MC_STATE, \
                "model checker was run before"); \
  } while (0)

// TODO
#define BTOR_MC_CHECK_OWNS_NODE_ARG(NODE)                             \
  do                                                                  \
  {                                                                   \
    BTOR_ABORT_ARG_NULL (NODE);                                       \
    BTOR_ABORT (BTOR_REAL_ADDR_NODE (NODE)->btor != mc->btor,         \
                "node '" #NODE                                        \
                "' does not belong to 'Btor' of this model checker"); \
  } while (0)

/*------------------------------------------------------------------------*/

BtorMsg *boolector_get_btor_msg (Btor *btor);

/*------------------------------------------------------------------------*/

typedef struct BtorMCOpt BtorMCOpt;

/*------------------------------------------------------------------------*/

struct BtorMCInput
{
  int32_t id;
  BoolectorNode *node;
};
typedef struct BtorMCInput BtorMCInput;

struct BtorMCstate
{
  int32_t id;
  BoolectorNode *node, *next, *init;
};
typedef struct BtorMCstate BtorMCstate;

enum BtorMCState
{
  BTOR_NO_MC_STATE    = 0,
  BTOR_SAT_MC_STATE   = 10,
  BTOR_UNSAT_MC_STATE = 20,
};
typedef enum BtorMCState BtorMCState;

struct BtorMCFrame
{
  int32_t time;
  BoolectorNodeMap *model2const;
  BoolectorNodePtrStack inputs, init, states, next, bad;
};
typedef struct BtorMCFrame BtorMCFrame;

BTOR_DECLARE_STACK (BtorMCFrame, BtorMCFrame);

/*------------------------------------------------------------------------*/

struct BtorMC
{
  BtorMemMgr *mm;
  BtorMCOpt *options;
  BtorMCState state;
  int32_t initialized, nextstates;
  Btor *btor, *forward;
  BtorMCFrameStack frames;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *states;
  BoolectorNodePtrStack bad;
  BoolectorNodePtrStack constraints;
  BoolectorNodeMap *forward2const;
  BtorIntStack reached;
  int32_t num_reached;
  struct
  {
    struct
    {
      void *state;
      BtorMCReachedAtBound fun;
    } reached_at_bound;
    struct
    {
      void *state;
      BtorMCStartingBound fun;
    } starting_bound;
  } call_backs;
};

/*------------------------------------------------------------------------*/

struct BtorMCOpt
{
  bool isflag;      /* flag? */
  const char *shrt; /* short option identifier (may be 0) */
  const char *lng;  /* long option identifier */
  const char *desc; /* description */
  uint32_t val;     /* value */
  uint32_t dflt;    /* default value */
  uint32_t min;     /* min value */
  uint32_t max;     /* max value */
};

static void
init_opt (BtorMC *btormc,
          BtorMCOption opt,
          bool isflag,
          char *lng,
          char *shrt,
          uint32_t val,
          uint32_t min,
          uint32_t max,
          char *desc)
{
  assert (btormc);
  assert (opt >= 0 && opt < BTOR_MC_OPT_NUM_OPTS);
  assert (lng);
  assert (max <= UINT32_MAX);
  assert (min <= val);
  assert (val <= max);

  uint32_t v;
  char *valstr;

  btormc->options[opt].isflag = isflag;
  btormc->options[opt].lng    = lng;
  btormc->options[opt].shrt   = shrt;
  btormc->options[opt].val    = val;
  btormc->options[opt].dflt   = val;
  btormc->options[opt].min    = min;
  btormc->options[opt].max    = max;
  btormc->options[opt].desc   = desc;

  if ((valstr = btor_util_getenv_value (lng)))
  {
    v = atoi (valstr);
    if (v < min)
      v = min;
    else if (v > max)
      v = max;
    if (v == val) return;
    btormc->options[opt].val = val;
  }
}

static void
init_options (BtorMC *btormc)
{
  assert (btormc);
  BTOR_CNEWN (btormc->mm, btormc->options, BTOR_MC_OPT_NUM_OPTS);
  init_opt (btormc,
            BTOR_MC_OPT_VERBOSITY,
            false,
            "verbosity",
            "v",
            0,
            0,
            UINT32_MAX,
            "set verbosity");
  init_opt (btormc,
            BTOR_MC_OPT_STOP_FIRST,
            true,
            "stop-first",
            0,
            1,
            0,
            1,
            "stop at first reached property");
  init_opt (btormc,
            BTOR_MC_OPT_TRACE_GEN,
            true,
            "trace-gen",
            0,
            0,
            0,
            1,
            "enable/disable trace generation");
}

void
boolector_mc_set_opt (BtorMC *btormc, BtorMCOption opt, uint32_t val)
{
  BTOR_ABORT_ARG_NULL (btormc);
  BTOR_ABORT (!boolector_mc_is_valid_opt (btormc, opt), "invalid option");
  BTOR_ABORT (val < boolector_mc_get_opt_min (btormc, opt)
                  || val > boolector_mc_get_opt_max (btormc, opt),
              "invalid option value '%u' for option '%s'",
              val,
              boolector_mc_get_opt_lng (btormc, opt));
  if (val && opt == BTOR_MC_OPT_TRACE_GEN)
  {
    BTOR_MC_ABORT_IF_STATE (btormc);
    assert (!BTOR_COUNT_STACK (btormc->frames));
  }

  BtorMCOpt *o = &btormc->options[opt];
  o->val       = val;

  if (opt == BTOR_MC_OPT_VERBOSITY)
    boolector_set_opt (btormc->btor, BTOR_OPT_VERBOSITY, val);
}

uint32_t
boolector_mc_get_opt (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].val;
}

uint32_t
boolector_mc_get_opt_min (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].min;
}

uint32_t
boolector_mc_get_opt_max (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].max;
}

uint32_t
boolector_mc_get_opt_dflt (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].dflt;
}

const char *
boolector_mc_get_opt_lng (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].lng;
}

const char *
boolector_mc_get_opt_shrt (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].shrt;
}

const char *
boolector_mc_get_opt_desc (BtorMC *btormc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return btormc->options[opt].desc;
}

bool
boolector_mc_is_valid_opt (BtorMC *btormc, const BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (btormc);
  return opt < BTOR_MC_OPT_NUM_OPTS;
}

/*------------------------------------------------------------------------*/

BtorMC *
boolector_mc_new (void)
{
  BtorMemMgr *mm;
  BtorMC *res;
  Btor *btor;

  btor = boolector_new ();
  mm   = btor_mem_mgr_new ();
  BTOR_CNEW (mm, res);
  res->mm     = mm;
  res->btor   = btor;
  res->inputs = btor_hashptr_table_new (mm,
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);
  res->states = btor_hashptr_table_new (mm,
                                        (BtorHashPtr) btor_node_hash_by_id,
                                        (BtorCmpPtr) btor_node_compare_by_id);
  assert (res->state == BTOR_NO_MC_STATE);
  assert (!res->forward2const);
  BTOR_INIT_STACK (mm, res->frames);
  BTOR_INIT_STACK (mm, res->bad);
  BTOR_INIT_STACK (mm, res->constraints);
  BTOR_INIT_STACK (mm, res->reached);
  init_options (res);
  return res;
}

void
boolector_mc_set_reached_at_bound_call_back (BtorMC *mc,
                                             void *state,
                                             BtorMCReachedAtBound fun)
{
  mc->call_backs.reached_at_bound.state = state;
  mc->call_backs.reached_at_bound.fun   = fun;
}

void
boolector_mc_set_starting_bound_call_back (BtorMC *mc,
                                           void *state,
                                           BtorMCStartingBound fun)
{
  mc->call_backs.starting_bound.state = state;
  mc->call_backs.starting_bound.fun   = fun;
}

Btor *
boolector_mc_get_btor (BtorMC *mc)
{
  BTOR_ABORT_ARG_NULL (mc);
  return mc->btor;
}

static void
delete_mc_input (BtorMC *mc, BtorMCInput *input)
{
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  boolector_release (btor, input->node);
  BTOR_DELETE (mc->mm, input);
}

static void
delete_mc_state (BtorMC *mc, BtorMCstate *state)
{
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  boolector_release (btor, state->node);
  if (state->init) boolector_release (btor, state->init);
  if (state->next) boolector_release (btor, state->next);
  BTOR_DELETE (mc->mm, state);
}

static void
release_mc_frame_stack (BtorMC *mc, BoolectorNodePtrStack *stack)
{
  BoolectorNode *node;

  while (!BTOR_EMPTY_STACK (*stack))
  {
    node = BTOR_POP_STACK (*stack);
    if (node) boolector_release (mc->forward, node);
  }

  BTOR_RELEASE_STACK (*stack);
}

static void
release_mc_frame (BtorMC *mc, BtorMCFrame *frame)
{
  release_mc_frame_stack (mc, &frame->inputs);
  release_mc_frame_stack (mc, &frame->init);
  release_mc_frame_stack (mc, &frame->states);
  release_mc_frame_stack (mc, &frame->next);
  release_mc_frame_stack (mc, &frame->bad);
}

static void
mc_release_assignment (BtorMC *mc)
{
  BtorMCFrame *f;
  if (mc->forward2const)
  {
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              1,
              "releasing forward to constant mapping of size %d",
              boolector_nodemap_count (mc->forward2const));
    boolector_nodemap_delete (mc->forward2const);
    mc->forward2const = 0;
  }

  for (f = mc->frames.start; f < mc->frames.top; f++)
    if (f->model2const)
    {
      BTOR_MSG (boolector_get_btor_msg (mc->btor),
                1,
                "releasing model to constant mapping of size %d at time %d",
                boolector_nodemap_count (f->model2const),
                (int32_t) (f - mc->frames.start));
      boolector_nodemap_delete (f->model2const);
      f->model2const = 0;
    }
}

void
boolector_mc_delete (BtorMC *mc)
{
  BTOR_ABORT_ARG_NULL (mc);

  BtorPtrHashTableIterator it;
  BtorMCFrame *f;
  Btor *btor;
  BtorMemMgr *mm;

  btor = mc->btor;
  mm   = mc->mm;

  mc_release_assignment (mc);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor),
      1,
      "deleting model checker: %u inputs, %u states, %u bad, %u constraints",
      mc->inputs->count,
      mc->states->count,
      BTOR_COUNT_STACK (mc->bad),
      BTOR_COUNT_STACK (mc->constraints));
  for (f = mc->frames.start; f < mc->frames.top; f++) release_mc_frame (mc, f);
  BTOR_RELEASE_STACK (mc->frames);
  btor_iter_hashptr_init (&it, mc->inputs);
  while (btor_iter_hashptr_has_next (&it))
    delete_mc_input (mc, btor_iter_hashptr_next_data (&it)->as_ptr);
  btor_hashptr_table_delete (mc->inputs);
  btor_iter_hashptr_init (&it, mc->states);
  while (btor_iter_hashptr_has_next (&it))
    delete_mc_state (mc, btor_iter_hashptr_next_data (&it)->as_ptr);
  btor_hashptr_table_delete (mc->states);
  while (!BTOR_EMPTY_STACK (mc->bad))
    boolector_release (btor, BTOR_POP_STACK (mc->bad));
  BTOR_RELEASE_STACK (mc->bad);
  while (!BTOR_EMPTY_STACK (mc->constraints))
    boolector_release (btor, BTOR_POP_STACK (mc->constraints));
  BTOR_RELEASE_STACK (mc->constraints);
  BTOR_RELEASE_STACK (mc->reached);
  if (mc->forward) boolector_delete (mc->forward);
  BTOR_DELETEN (mm, mc->options, BTOR_MC_OPT_NUM_OPTS);
  BTOR_DELETE (mm, mc);
  btor_mem_mgr_delete (mm);
  btor_delete (btor);
}

BoolectorNode *
boolector_mc_input (BtorMC *mc, uint32_t width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMCInput *input;
  BoolectorNode *res;
  BoolectorSort s;
  Btor *btor;
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (mc->state != BTOR_NO_MC_STATE,
              "can only be called before checking");
  BTOR_ABORT (1 > width, "given width < 1");
  btor = mc->btor;
  s    = boolector_bitvec_sort (btor, width);
  res  = boolector_var (btor, s, name);
  boolector_release_sort (btor, s);
  BTOR_NEW (mc->mm, input);
  assert (input);
  input->id   = (int32_t) mc->inputs->count;
  input->node = res;
  bucket      = btor_hashptr_table_add (mc->inputs, res);
  assert (bucket);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = input;
  if (name)
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              2,
              "declared input %d '%s' of width %d",
              input->id,
              name,
              width);
  else
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              2,
              "declared input %d of width %d",
              input->id,
              width);
  return res;
}

BoolectorNode *
boolector_mc_state (BtorMC *mc, uint32_t width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMCstate *state;
  BoolectorNode *res;
  BoolectorSort s;
  Btor *btor;
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (mc->state != BTOR_NO_MC_STATE,
              "can only be callsed before checking");
  assert (1 <= width);
  btor = mc->btor;
  s    = boolector_bitvec_sort (btor, width);
  res  = boolector_var (btor, s, name);
  boolector_release_sort (btor, s);
  BTOR_NEW (mc->mm, state);
  assert (state);
  state->id   = (int32_t) mc->states->count;
  state->node = res;
  state->init = state->next = 0;
  bucket                    = btor_hashptr_table_add (mc->states, res);
  assert (bucket);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = state;
  if (name)
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              2,
              "declared state %d '%s' of width %d",
              state->id,
              name,
              width);
  else
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              2,
              "declared state %d of width %d",
              state->id,
              width);
  return res;
}

static BtorMCstate *
find_mc_state (BtorMC *mc, BoolectorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorMCstate *res;
  assert (mc);
  assert (node);
  bucket = btor_hashptr_table_get (mc->states, node);
  if (!bucket) return 0;
  res = bucket->data.as_ptr;
  assert (res->node == bucket->key);
  return res;
}

void
boolector_mc_next (BtorMC *mc, BoolectorNode *node, BoolectorNode *next)
{
  BtorMCstate *state;
  Btor *btor;
  (void) btor;
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (node);
  BTOR_MC_CHECK_OWNS_NODE_ARG (next);
  btor = mc->btor;
  assert (!boolector_is_array (btor, node));
  assert (!boolector_is_array (btor, next));
  assert (boolector_get_width (btor, node) == boolector_get_width (btor, next));
  state = find_mc_state (mc, node);
  assert (state);
  assert (state->node == node);
  assert (!state->next);
  state->next = boolector_copy (mc->btor, next);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor), 2, "adding NEXT state %d", state->id);
  mc->nextstates++;
}

void
boolector_mc_init (BtorMC *mc, BoolectorNode *node, BoolectorNode *init)
{
  BtorMCstate *state;
  Btor *btor;
  (void) btor;
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (node);
  BTOR_MC_CHECK_OWNS_NODE_ARG (init);
  assert (boolector_is_const (mc->btor, init));
  btor = mc->btor;
  assert (boolector_get_width (btor, node) == boolector_get_width (btor, init));
  state = find_mc_state (mc, node);
  assert (state);
  assert (state->node == node);
  assert (!state->init);
  state->init = boolector_copy (mc->btor, init);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor), 2, "adding INIT state %d", state->id);
  mc->initialized++;
}

int32_t
boolector_mc_bad (BtorMC *mc, BoolectorNode *bad)
{
  int32_t res;
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (bad);
  assert (boolector_get_width (mc->btor, bad) == 1);
  assert (!boolector_is_array (mc->btor, bad));
  res = BTOR_COUNT_STACK (mc->bad);
  (void) boolector_copy (mc->btor, bad);
  BTOR_PUSH_STACK (mc->bad, bad);
  assert (res == BTOR_COUNT_STACK (mc->reached));
  BTOR_PUSH_STACK (mc->reached, -1);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor), 2, "adding BAD property %d", res);
  return res;
}

int32_t
boolector_mc_constraint (BtorMC *mc, BoolectorNode *constraint)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (constraint);
  assert (!boolector_is_array (mc->btor, constraint));
  assert (boolector_get_width (mc->btor, constraint) == 1);

  int32_t res = BTOR_COUNT_STACK (mc->constraints);
  (void) boolector_copy (mc->btor, constraint);
  BTOR_PUSH_STACK (mc->constraints, constraint);
  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "adding environment CONSTRAINT %d",
            res);
  return res;
}

static char *
timed_symbol (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  assert (mc);
  assert (node);
  assert (BTOR_IS_REGULAR_NODE (node));
  assert (time >= 0);

  char *res, suffix[20];
  const char *symbol;
  uint32_t symlen, reslen;

  symbol = boolector_get_symbol (mc->btor, node);
  if (!symbol) return 0;
  sprintf (suffix, "@%d", time);
  symlen = strlen (symbol);
  reslen = symlen + strlen (suffix) + 1;
  res    = btor_mem_malloc (mc->mm, reslen);
  (void) strcpy (res, symbol);
  strcpy (res + symlen, suffix);
  return res;
}

static void
initialize_inputs_of_frame (BtorMC *mc, BtorMCFrame *f)
{
  BoolectorNode *src, *dst;
  BoolectorSort s;
  BtorPtrHashTableIterator it;
  char *sym;
  uint32_t w;

#ifndef NDEBUG
  int32_t i = 0;
  BtorMCInput *input;
#endif

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %u inputs of frame %d",
            mc->inputs->count,
            f->time);

  BTOR_INIT_STACK (mc->mm, f->inputs);

  btor_iter_hashptr_init (&it, mc->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
#ifndef NDEBUG
    input = it.bucket->data.as_ptr;
    assert (input);
#endif
    src = (BoolectorNode *) btor_iter_hashptr_next (&it);
    assert (src);
    assert (BTOR_IS_REGULAR_NODE (src));
#ifndef NDEBUG
    assert (input->node == src);
    assert (input->id == i);
#endif
    sym = timed_symbol (mc, src, f->time);
    w   = boolector_get_width (mc->btor, src);
    s   = boolector_bitvec_sort (mc->forward, w);
    dst = boolector_var (mc->forward, s, sym);
    boolector_release_sort (mc->forward, s);
    btor_mem_freestr (mc->mm, sym);
    assert (BTOR_COUNT_STACK (f->inputs) == i++);
    BTOR_PUSH_STACK (f->inputs, dst);
  }
}

static void
initialize_states_of_frame (BtorMC *mc, BtorMCFrame *f)
{
  BoolectorNode *src, *dst;
  BoolectorSort s;
  BtorPtrHashTableIterator it;
  BtorMCstate *state;
  const char *bits;
  BtorMCFrame *p;
  char *sym;
  int32_t i;
  uint32_t w;

  assert (mc);
  assert (f);
  assert (f->time >= 0);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %u states in frame %d",
            mc->states->count,
            f->time);

  BTOR_INIT_STACK (mc->mm, f->states);

  i = 0;
  btor_iter_hashptr_init (&it, mc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    state = it.bucket->data.as_ptr;
    assert (state);
    assert (state->id == i);
    src = (BoolectorNode *) btor_iter_hashptr_next (&it);
    assert (src);
    assert (BTOR_IS_REGULAR_NODE (src));
    assert (state->node == src);

    if (!f->time && state->init)
    {
      bits = boolector_get_bits (mc->btor, state->init);
      dst  = boolector_const (mc->forward, bits);
      boolector_free_bits (mc->btor, bits);
    }
    else if (f->time > 0 && state->next)
    {
      p   = f - 1;
      dst = BTOR_PEEK_STACK (p->next, i);
      dst = boolector_copy (mc->forward, dst);
    }
    else
    {
      sym = timed_symbol (mc, src, f->time);
      w   = boolector_get_width (mc->btor, src);
      s   = boolector_bitvec_sort (mc->forward, w);
      dst = boolector_var (mc->forward, s, sym);
      boolector_release_sort (mc->forward, s);
      btor_mem_freestr (mc->mm, sym);
    }
    assert (BTOR_COUNT_STACK (f->states) == i);
    BTOR_PUSH_STACK (f->states, dst);
    i += 1;
  }
}

static void
initialize_next_state_functions_of_frame (BtorMC *mc,
                                          BoolectorNodeMap *map,
                                          BtorMCFrame *f)
{
  BoolectorNode *src, *dst, *node;
  BtorMCstate *state;
  BtorPtrHashTableIterator it;
  int32_t nextstates, i;
  (void) node;

  assert (mc);
  assert (map);
  assert (f);
  assert (f->time >= 0);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %d next state functions of frame %d",
            mc->nextstates,
            f->time);

  BTOR_INIT_STACK (mc->mm, f->next);

  i          = 0;
  nextstates = 0;
  btor_iter_hashptr_init (&it, mc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    state = it.bucket->data.as_ptr;
    assert (state);
    node = (BoolectorNode *) btor_iter_hashptr_next (&it);
    assert (state->node == node);
    assert (BTOR_COUNT_STACK (f->next) == i);
    src = state->next;
    if (src)
    {
      dst = boolector_nodemap_non_recursive_substitute_node (
          mc->forward, map, src);
      dst = boolector_copy (mc->forward, dst);
      BTOR_PUSH_STACK (f->next, dst);
      nextstates++;
    }
    else
      BTOR_PUSH_STACK (f->next, 0);
    i += 1;
  }
  assert (nextstates == mc->nextstates);
  assert (BTOR_COUNT_STACK (f->next) == mc->states->count);
}

static void
initialize_constraints_of_frame (BtorMC *mc,
                                 BoolectorNodeMap *map,
                                 BtorMCFrame *f)
{
  BoolectorNode *src, *dst, *constraint;
  uint32_t i;

  assert (mc);
  assert (map);
  assert (f);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %u environment constraints of frame %d",
            BTOR_COUNT_STACK (mc->constraints),
            f->time);

  constraint = 0;

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    src = BTOR_PEEK_STACK (mc->constraints, i);
    assert (src);
    dst =
        boolector_nodemap_non_recursive_substitute_node (mc->forward, map, src);
    if (constraint)
    {
      BoolectorNode *tmp = boolector_and (mc->forward, constraint, dst);
      boolector_release (mc->forward, constraint);
      constraint = tmp;
    }
    else
      constraint = boolector_copy (mc->forward, dst);
  }

  if (constraint)
  {
    boolector_assert (mc->forward, constraint);
    boolector_release (mc->forward, constraint);
  }
}

static void
initialize_bad_state_properties_of_frame (BtorMC *mc,
                                          BoolectorNodeMap *map,
                                          BtorMCFrame *f)
{
  BoolectorNode *src, *dst;
  uint32_t i;

  assert (mc);
  assert (map);
  assert (f);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %u bad state properties of frame %d",
            BTOR_COUNT_STACK (mc->bad),
            f->time);

  BTOR_INIT_STACK (mc->mm, f->bad);

  for (i = 0; i < BTOR_COUNT_STACK (mc->bad); i++)
  {
    if (BTOR_PEEK_STACK (mc->reached, i) < 0)
    {
      src = BTOR_PEEK_STACK (mc->bad, i);
      assert (src);
      dst = boolector_nodemap_non_recursive_substitute_node (
          mc->forward, map, src);
      dst = boolector_copy (mc->forward, dst);
    }
    else
      dst = 0;

    BTOR_PUSH_STACK (f->bad, dst);
  }
}

static BoolectorNodeMap *
map_inputs_and_states_of_frame (BtorMC *mc, BtorMCFrame *f)
{
  BoolectorNode *src, *dst;
  BoolectorNodeMap *res;
  BtorPtrHashTableIterator it;
  uint32_t i;

  assert (mc);
  assert (f);
  assert (BTOR_COUNT_STACK (f->inputs) == mc->inputs->count);
  assert (BTOR_COUNT_STACK (f->states) == mc->states->count);

  res = boolector_nodemap_new (mc->forward);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "mapping inputs and states of frame %d",
            f->time);

  i = 0;
  btor_iter_hashptr_init (&it, mc->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    src = (BoolectorNode *) btor_iter_hashptr_next (&it);
    dst = BTOR_PEEK_STACK (f->inputs, i);
    boolector_nodemap_map (res, src, dst);
    i += 1;
  }

  i = 0;
  btor_iter_hashptr_init (&it, mc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    src = (BoolectorNode *) btor_iter_hashptr_next (&it);
    dst = BTOR_PEEK_STACK (f->states, i);
    boolector_nodemap_map (res, src, dst);
    i += 1;
  }

  assert ((uint32_t) boolector_nodemap_count (res)
          == mc->inputs->count + mc->states->count);

  return res;
}

static void
initialize_new_forward_frame (BtorMC *mc)
{
  BtorMCFrame frame, *f;
  BoolectorNodeMap *map;
  int32_t time;
#ifndef NDEBUG
  uint32_t old_mc_btor_num_nodes;
#endif

  assert (mc);
#ifndef NDEBUG
  old_mc_btor_num_nodes = mc->btor->nodes_unique_table.num_elements;
#endif

  time = BTOR_COUNT_STACK (mc->frames);
  BTOR_CLR (&frame);
  BTOR_PUSH_STACK (mc->frames, frame);
  f       = mc->frames.start + time;
  f->time = time;

  if (!mc->forward)
  {
    uint32_t v;
    BTOR_MSG (boolector_get_btor_msg (mc->btor), 1, "new forward manager");
    mc->forward = btor_new ();
    boolector_set_opt (mc->forward, BTOR_OPT_INCREMENTAL, 1);
    if (boolector_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN))
      boolector_set_opt (mc->forward, BTOR_OPT_MODEL_GEN, 1);
    if ((v = boolector_mc_get_opt (mc, BTOR_MC_OPT_VERBOSITY)))
      boolector_set_opt (mc->forward, BTOR_OPT_VERBOSITY, v);
  }

  BTOR_INIT_STACK (mc->mm, f->init);

  initialize_inputs_of_frame (mc, f);
  initialize_states_of_frame (mc, f);

  map = map_inputs_and_states_of_frame (mc, f);

  initialize_next_state_functions_of_frame (mc, map, f);
  initialize_constraints_of_frame (mc, map, f);
  initialize_bad_state_properties_of_frame (mc, map, f);

  boolector_nodemap_delete (map);

  assert (old_mc_btor_num_nodes == mc->btor->nodes_unique_table.num_elements);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            1,
            "initialized forward frame at bound k = %d",
            time);
}

#if 0

static void
print_trace (BtorMC * mc, int32_t p, int32_t k)
{
  const char * symbol;
  BoolectorNode * node;
  BtorMCFrame * f;
  char buffer[30];
  char * a;
  int32_t i, j;

  printf ("bad state property %d at bound k = %d satisfiable:\n", p, k);

  for (i = 0; i <= k; i++)
    {
      printf ("\n");
      printf ("[ state %d ]\n", i);
      printf ("\n");

      f = mc->frames.start + i;
      for (j = 0; j < BTOR_COUNT_STACK (f->inputs); j++)
        {
          node = BTOR_PEEK_STACK (f->inputs, j);
          a = btor_bv_assignment_str (f->btor, node);
          if (node->symbol)
            symbol = node->symbol;
          else
            {
              sprintf (buffer, "input%d@%d", j, i);
              symbol = buffer;
            }
          printf ("%s = %s\n", symbol, a);
          btor_mem_freestr (f->mm, a);
        }
    }
  fflush (stdout);
}

#endif

static int32_t
check_last_forward_frame (BtorMC *mc)
{
  int32_t k, i, res, satisfied;
  BtorMCFrame *f;
  BoolectorNode *bad;

  k = BTOR_COUNT_STACK (mc->frames) - 1;
  assert (k >= 0);
  f = mc->frames.top - 1;
  assert (f->time == k);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            1,
            "checking forward frame at bound k = %d",
            k);
  satisfied = 0;

  for (i = 0; i < BTOR_COUNT_STACK (f->bad); i++)
  {
    bad = BTOR_PEEK_STACK (f->bad, i);
    if (!bad)
    {
      int32_t reached;
      reached = BTOR_PEEK_STACK (mc->reached, i);
      assert (reached >= 0);
      BTOR_MSG (boolector_get_btor_msg (mc->btor),
                1,
                "skipping checking bad state property %d at bound %d reached "
                "before at %d",
                i,
                k,
                reached);
      continue;
    }
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              1,
              "checking forward frame bad state property %d at bound k = %d",
              i,
              k);
    boolector_assume (mc->forward, bad);
    res = boolector_sat (mc->forward);
    if (res == BOOLECTOR_SAT)
    {
      mc->state = BTOR_SAT_MC_STATE;
      BTOR_MSG (boolector_get_btor_msg (mc->btor),
                1,
                "bad state property %d at bound k = %d SATISFIABLE",
                i,
                k);
      satisfied++;
      if (BTOR_PEEK_STACK (mc->reached, i) < 0)
      {
        mc->num_reached++;
        assert (mc->num_reached <= BTOR_COUNT_STACK (mc->bad));
        BTOR_POKE_STACK (mc->reached, i, k);
        if (mc->call_backs.reached_at_bound.fun)
        {
          mc->call_backs.reached_at_bound.fun (
              mc->call_backs.reached_at_bound.state, i, k);
        }
      }
    }
    else
    {
      assert (res == BOOLECTOR_UNSAT);
      mc->state = BTOR_UNSAT_MC_STATE;
      BTOR_MSG (boolector_get_btor_msg (mc->btor),
                1,
                "bad state property %d at bound k = %d UNSATISFIABLE",
                i,
                k);
    }
  }

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            1,
            "found %d satisfiable bad state properties at bound k = %d",
            satisfied,
            k);

  return satisfied;
}

int32_t
boolector_mc_bmc (BtorMC *mc, int32_t mink, int32_t maxk)
{
  int32_t k;

  BTOR_ABORT_ARG_NULL (mc);

  mc_release_assignment (mc);

  BTOR_MSG (
      boolector_get_btor_msg (mc->btor),
      1,
      "calling BMC on %u properties from bound %d up-to maximum bound k = %d",
      BTOR_COUNT_STACK (mc->bad),
      mink,
      maxk);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            1,
            "trace generation %s",
            boolector_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN) ? "enabled"
                                                             : "disabled");

  mc->state = BTOR_NO_MC_STATE;

  while ((k = BTOR_COUNT_STACK (mc->frames)) <= maxk)
  {
    if (mc->call_backs.starting_bound.fun)
      mc->call_backs.starting_bound.fun (mc->call_backs.starting_bound.state,
                                         k);

    initialize_new_forward_frame (mc);
    if (k < mink) continue;
    if (check_last_forward_frame (mc))
    {
      if (boolector_mc_get_opt (mc, BTOR_MC_OPT_STOP_FIRST)
          || mc->num_reached == BTOR_COUNT_STACK (mc->bad) || k == maxk)
      {
        BTOR_MSG (boolector_get_btor_msg (mc->btor),
                  2,
                  "entering SAT state at bound k=%d",
                  k);
        assert (k >= 0);
        return k;
      }
    }
  }

  BTOR_MSG (boolector_get_btor_msg (mc->btor), 2, "entering UNSAT state");
  mc->state = BTOR_UNSAT_MC_STATE;

  return -1;
}

static BoolectorNodeMap *
get_mc_forward2const (BtorMC *mc)
{
  if (!mc->forward2const) mc->forward2const = boolector_nodemap_new (mc->btor);
  return mc->forward2const;
}

static BoolectorNodeMap *
get_mc_model2const_map (BtorMC *mc, BtorMCFrame *frame)
{
  if (!frame->model2const)
    frame->model2const = boolector_nodemap_new (mc->btor);
  return frame->model2const;
}

static void
zero_normalize_assignment (char *assignment)
{
  char *p;
  for (p = assignment; *p; p++)
    if (*p == 'x') *p = '0';
}

static BoolectorNode *
mc_forward2const_mapper (Btor *btor, void *f2c_mc, BoolectorNode *node)
{
  const char *assignment;
  BtorMC *mc = f2c_mc;
  BoolectorNode *res;
  char *normalized;

  assert (!BTOR_IS_INVERTED_NODE (node));

  if (!boolector_is_var (mc->forward, node)) return 0;

  assert (mc);
  assert (mc->btor == btor);
  assert (mc->forward == boolector_get_btor (node));
  (void) btor;

  res = 0;

  assignment = boolector_bv_assignment (mc->forward, node);
  normalized = btor_mem_strdup (mc->mm, assignment);
  zero_normalize_assignment (normalized);
  res = boolector_const (mc->btor, normalized);
  btor_mem_freestr (mc->mm, normalized);
  boolector_free_bv_assignment (mc->forward, assignment);

  return res;
}

static BoolectorNode *
mc_forward2const (BtorMC *mc, BoolectorNode *node)
{
  BoolectorNodeMap *map;
  assert (BTOR_REAL_ADDR_NODE (node)->btor == mc->forward);
  map = get_mc_forward2const (mc);
  return boolector_nodemap_non_recursive_extended_substitute_node (
      mc->btor, map, mc, mc_forward2const_mapper, boolector_release, node);
}

typedef struct BtorMCModel2ConstMapper BtorMCModel2ConstMapper;

struct BtorMCModel2ConstMapper
{
  int32_t time;
  BtorMC *mc;
};

static BoolectorNode *
mc_model2const_mapper (Btor *btor, void *m2cmapper, BoolectorNode *node)
{
  assert (!BTOR_IS_INVERTED_NODE (node));

  BtorMCModel2ConstMapper *mapper;
  BoolectorNode *node_at_time, *res;
  const char *sym, *constbits;
  BtorPtrHashBucket *bucket;
  BtorMCFrame *frame;
  BtorMCInput *input;
  BtorMCstate *state;
  BtorMC *mc;
  char *bits;
  int32_t time;

  if (!boolector_is_var (btor, node)) return 0;

  mapper = m2cmapper;
  assert (mapper);
  mc = mapper->mc;
  assert (mc);
  assert (mc->btor == btor);
  assert (mc->btor == boolector_get_btor (node));
  (void) btor;
  time = mapper->time;

  assert (0 <= time && time < BTOR_COUNT_STACK (mc->frames));
  frame = mc->frames.start + time;

  bucket = btor_hashptr_table_get (mc->inputs, node);

  if (bucket)
  {
    input = bucket->data.as_ptr;
    assert (input);
    assert (input->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->inputs, input->id);
    assert (node_at_time);
    assert (BTOR_REAL_ADDR_NODE (node_at_time)->btor == mc->forward);
    constbits = boolector_bv_assignment (mc->forward, node_at_time);
    bits      = btor_mem_strdup (mc->mm, constbits);
    boolector_free_bv_assignment (mc->forward, constbits);
    zero_normalize_assignment (bits);
    res = boolector_const (mc->btor, bits);
    btor_mem_freestr (mc->mm, bits);
  }
  else
  {
    bucket = btor_hashptr_table_get (mc->states, node);
    if (!boolector_is_var (mc->btor, node))
      sym = 0;
    else
      sym = boolector_get_symbol (mc->btor, node);
    if (sym)
      BTOR_ABORT (!bucket, "variable '%s' not a state nor an input", sym);
    else
      BTOR_ABORT (!bucket, "variable without symbol not a state nor an input");
    state = bucket->data.as_ptr;
    assert (state);
    assert (state->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->states, state->id);
    assert (BTOR_REAL_ADDR_NODE (node_at_time)->btor == mc->forward);
    res = mc_forward2const (mc, node_at_time);
    res = boolector_copy (mc->btor, res);
  }

  // TODO wrap into Aina's BtorBVAss ....

  return res;
}

static BoolectorNode *
mc_model2const (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  BtorMCModel2ConstMapper mapper;
  BoolectorNodeMap *map;
  BtorMCFrame *f;
  assert (BTOR_REAL_ADDR_NODE (node)->btor == mc->btor);
  assert (0 <= time && time < BTOR_COUNT_STACK (mc->frames));
  mapper.mc   = mc;
  mapper.time = time;
  f           = mc->frames.start + time;
  map         = get_mc_model2const_map (mc, f);
  return boolector_nodemap_non_recursive_extended_substitute_node (
      mc->btor, map, &mapper, mc_model2const_mapper, boolector_release, node);
}

char *
boolector_mc_assignment (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  BoolectorNode *node_at_time, *const_node;
  const char *bits_owned_by_forward, *bits;
  BtorPtrHashBucket *bucket;
  BtorMCInput *input;
  BtorMCFrame *frame;
  char *res;

  BTOR_ABORT_ARG_NULL (mc);

  BTOR_ABORT (mc->state == BTOR_NO_MC_STATE,
              "model checker was not run before");

  BTOR_ABORT (mc->state == BTOR_UNSAT_MC_STATE,
              "model checking status is UNSAT");

  assert (mc->state == BTOR_SAT_MC_STATE);
  BTOR_ABORT (!boolector_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN),
              "'boolector_mc_enable_trace_gen' was not called before");

  assert (mc->state == BTOR_SAT_MC_STATE);
  BTOR_ABORT_ARG_NULL (node);
  BTOR_ABORT_REFS_NOT_POS (node);

  BTOR_MC_CHECK_OWNS_NODE_ARG (node);

  BTOR_ABORT (0 > time, "negative 'time' argument");
  BTOR_ABORT (time >= BTOR_COUNT_STACK (mc->frames),
              "'time' exceeds previously returned bound");

  bucket = btor_hashptr_table_get (mc->inputs, node);
  if (bucket)
  {
    input = bucket->data.as_ptr;
    assert (input);
    assert (input->node == node);
    frame        = mc->frames.start + time;
    node_at_time = BTOR_PEEK_STACK (frame->inputs, input->id);
    assert (node_at_time);
    bits_owned_by_forward = boolector_bv_assignment (mc->forward, node_at_time);
    res                   = btor_mem_strdup (mc->mm, bits_owned_by_forward);
    zero_normalize_assignment (res);
    boolector_free_bv_assignment (mc->forward, bits_owned_by_forward);
  }
  else
  {
    const_node = mc_model2const (mc, node, time);
    assert (const_node);
    assert (boolector_is_const (mc->btor, const_node));
    assert (boolector_get_btor (const_node) == mc->btor);
    bits = boolector_get_bits (mc->btor, const_node);
    res  = btor_mem_strdup (mc->mm, bits);
    boolector_free_bits (mc->btor, bits);
  }

  return res;
}

void
boolector_mc_free_assignment (BtorMC *mc, char *assignment)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (assignment);
  btor_mem_freestr (mc->mm, assignment);
}

void
boolector_mc_dump (BtorMC *mc, FILE *file)
{
  BtorPtrHashTableIterator it;
  BtorDumpContext *bdc;
  uint32_t i;

  (void) boolector_simplify (mc->btor);

  bdc = btor_dumpbtor_new_dump_context (mc->btor);

  btor_iter_hashptr_init (&it, mc->inputs);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorMCInput *input = btor_iter_hashptr_next_data (&it)->as_ptr;
    assert (input);
    assert (input->node);
    btor_dumpbtor_add_input_to_dump_context (
        bdc, BTOR_IMPORT_BOOLECTOR_NODE (input->node));
  }

  btor_iter_hashptr_init (&it, mc->states);
  while (btor_iter_hashptr_has_next (&it))
  {
    BtorMCstate *state = btor_iter_hashptr_next_data (&it)->as_ptr;
    assert (state);
    assert (state->node);
    assert (BTOR_IS_REGULAR_NODE (state->node));
    btor_dumpbtor_add_state_to_dump_context (
        bdc, BTOR_IMPORT_BOOLECTOR_NODE (state->node));
    if (state->init)
      btor_dumpbtor_add_init_to_dump_context (
          bdc,
          BTOR_IMPORT_BOOLECTOR_NODE (state->node),
          BTOR_IMPORT_BOOLECTOR_NODE (state->init));
    if (state->next)
      btor_dumpbtor_add_next_to_dump_context (
          bdc,
          BTOR_IMPORT_BOOLECTOR_NODE (state->node),
          BTOR_IMPORT_BOOLECTOR_NODE (state->next));
  }

  for (i = 0; i < BTOR_COUNT_STACK (mc->bad); i++)
  {
    BoolectorNode *bad = BTOR_PEEK_STACK (mc->bad, i);
    btor_dumpbtor_add_bad_to_dump_context (bdc,
                                           BTOR_IMPORT_BOOLECTOR_NODE (bad));
  }

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    BoolectorNode *constraint = BTOR_PEEK_STACK (mc->constraints, i);
    btor_dumpbtor_add_constraint_to_dump_context (
        bdc, BTOR_IMPORT_BOOLECTOR_NODE (constraint));
  }

  btor_dumpbtor_dump_bdc (bdc, file);
  btor_dumpbtor_delete_dump_context (bdc);
}

int32_t
boolector_mc_reached_bad_at_bound (BtorMC *mc, int32_t badidx)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (mc->state == BTOR_NO_MC_STATE,
              "model checker was not run before");
  BTOR_ABORT (boolector_mc_get_opt (mc, BTOR_MC_OPT_STOP_FIRST),
              "stopping at first reached property must be disabled");
  BTOR_ABORT (badidx < 0, "negative bad state property index");
  BTOR_ABORT (badidx >= BTOR_COUNT_STACK (mc->bad),
              "bad state property index too large");
  return BTOR_PEEK_STACK (mc->reached, badidx);
}
