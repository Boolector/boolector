/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormc.h"
#include "boolector.h"
#include "btorabort.h"
#include "btorconst.h"
#include "btorexp.h"
#include "btoriter.h"
#include "btormap.h"
#include "btormsg.h"
#include "dumper/btordumpbtor.h"

/*------------------------------------------------------------------------*/

#include <stdarg.h>

/*------------------------------------------------------------------------*/

#define BTOR_ABORT_IF_STATE(MC)                            \
  do                                                       \
  {                                                        \
    BTOR_ABORT_BOOLECTOR ((MC)->state != BTOR_NO_MC_STATE, \
                          "model checker was run before"); \
  } while (0)

#define BTOR_MC_CHECK_OWNS_NODE_ARG(NODE)                                    \
  do                                                                         \
  {                                                                          \
    BTOR_ABORT_ARG_NULL_BOOLECTOR (NODE);                                    \
    BTOR_ABORT_BOOLECTOR (                                                   \
        BTOR_REAL_ADDR_NODE (NODE)->btor != mc->btor,                        \
        "node '" #NODE "' does not belong to 'Btor' of this model checker"); \
  } while (0)

/*------------------------------------------------------------------------*/

BtorMsg *boolector_get_btor_msg (Btor *btor);

/*------------------------------------------------------------------------*/

typedef struct BtorMcInput
{
  int id;
  BoolectorNode *node;
} BtorMcInput;

typedef struct BtorMcLatch
{
  int id;
  BoolectorNode *node, *next, *init;
} BtorMcLatch;

typedef enum BtorMcState
{
  BTOR_NO_MC_STATE    = 0,
  BTOR_SAT_MC_STATE   = 10,
  BTOR_UNSAT_MC_STATE = 20,
} BtorMcState;

typedef struct BtorMcFrame
{
  int time;
  BoolectorNodeMap *model2const;
  BoolectorNodePtrStack inputs, init, latches, next, bad;
} BtorMcFrame;

BTOR_DECLARE_STACK (BtorMcFrame, BtorMcFrame);

struct BtorMC
{
  BtorMcState state;
  int verbosity, trace_enabled, stop, continue_checking_if_reached;
  int initialized, nextstates;
  Btor *btor, *forward;
  BtorMcFrameStack frames;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *latches;
  BoolectorNodePtrStack bad;
  BoolectorNodePtrStack constraints;
  BoolectorNodeMap *forward2const;
  BtorIntStack reached;
  int num_reached;
  struct
  {
    struct
    {
      void *state;
      BtorMCReachedAtBound fun;
    } reached_at_bound;
  } call_backs;
};

/*------------------------------------------------------------------------*/

BtorMC *
boolector_new_mc (void)
{
  BtorMemMgr *mm;
  BtorMC *res;
  Btor *btor;
  btor = boolector_new ();
  assert (btor);
  mm = btor->mm;
  BTOR_CNEW (mm, res);
  res->btor    = btor;
  res->inputs  = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_new_ptr_hash_table (mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  assert (res->state == BTOR_NO_MC_STATE);
  assert (!res->forward2const);
  res->continue_checking_if_reached = 0;
  res->stop                         = 1;
  return res;
}

void
boolector_set_verbosity_mc (BtorMC *mc, int verbosity)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  mc->verbosity = verbosity;
  boolector_set_opt (mc->btor, "verbosity", verbosity);
}

void
boolector_set_stop_at_first_reached_property_mc (BtorMC *mc, int stop)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  mc->stop = stop;
}

void
boolector_set_reached_at_bound_call_back_mc (BtorMC *mc,
                                             void *state,
                                             BtorMCReachedAtBound fun)
{
  mc->call_backs.reached_at_bound.state = state;
  mc->call_backs.reached_at_bound.fun   = fun;
}

void
boolector_enable_trace_gen (BtorMC *mc)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  assert (!BTOR_COUNT_STACK (mc->frames));
  mc->trace_enabled = 1;
}

Btor *
boolector_btor_mc (BtorMC *mc)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  return mc->btor;
}

static void
btor_delete_mc_input (BtorMC *mc, BtorMcInput *input)
{
  BtorMemMgr *mm;
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  boolector_release (btor, input->node);
  BTOR_DELETE (mm, input);
}

static void
btor_delete_mc_latch (BtorMC *mc, BtorMcLatch *latch)
{
  BtorMemMgr *mm;
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  boolector_release (btor, latch->node);
  if (latch->init) boolector_release (btor, latch->init);
  if (latch->next) boolector_release (btor, latch->next);
  BTOR_DELETE (mm, latch);
}

static void
btor_release_mc_frame_stack (BtorMC *mc, BoolectorNodePtrStack *stack)
{
  BoolectorNode *node;

  while (!BTOR_EMPTY_STACK (*stack))
  {
    node = BTOR_POP_STACK (*stack);
    if (node) boolector_release (mc->forward, node);
  }

  BTOR_RELEASE_STACK (mc->btor->mm, *stack);
}

static void
btor_release_mc_frame (BtorMC *mc, BtorMcFrame *frame)
{
  btor_release_mc_frame_stack (mc, &frame->inputs);
  btor_release_mc_frame_stack (mc, &frame->init);
  btor_release_mc_frame_stack (mc, &frame->latches);
  btor_release_mc_frame_stack (mc, &frame->next);
  btor_release_mc_frame_stack (mc, &frame->bad);
}

static void
btor_mc_release_assignment (BtorMC *mc)
{
  BtorMcFrame *f;
  if (mc->forward2const)
  {
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              1,
              "releasing forward to constant mapping of size %d",
              boolector_count_map (mc->forward2const));
    boolector_delete_node_map (mc->forward2const);
    mc->forward2const = 0;
  }

  for (f = mc->frames.start; f < mc->frames.top; f++)
    if (f->model2const)
    {
      BTOR_MSG (boolector_get_btor_msg (mc->btor),
                1,
                "releasing model to constant mapping of size %d at time %d",
                boolector_count_map (f->model2const),
                (int) (f - mc->frames.start));
      boolector_delete_node_map (f->model2const);
      f->model2const = 0;
    }
}

void
boolector_delete_mc (BtorMC *mc)
{
  BtorHashTableIterator it;
  BtorMemMgr *mm;
  BtorMcFrame *f;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  btor_mc_release_assignment (mc);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor),
      1,
      "deleting model checker: %u inputs, %u latches, %u bad, %u constraints",
      mc->inputs->count,
      mc->latches->count,
      BTOR_COUNT_STACK (mc->bad),
      BTOR_COUNT_STACK (mc->constraints));
  btor = mc->btor;
  mm   = btor->mm;
  for (f = mc->frames.start; f < mc->frames.top; f++)
    btor_release_mc_frame (mc, f);
  BTOR_RELEASE_STACK (mm, mc->frames);
  init_hash_table_iterator (&it, mc->inputs);
  while (has_next_hash_table_iterator (&it))
    btor_delete_mc_input (mc, next_data_hash_table_iterator (&it)->asPtr);
  btor_delete_ptr_hash_table (mc->inputs);
  init_hash_table_iterator (&it, mc->latches);
  while (has_next_hash_table_iterator (&it))
    btor_delete_mc_latch (mc, next_data_hash_table_iterator (&it)->asPtr);
  btor_delete_ptr_hash_table (mc->latches);
  while (!BTOR_EMPTY_STACK (mc->bad))
    boolector_release (btor, BTOR_POP_STACK (mc->bad));
  BTOR_RELEASE_STACK (mm, mc->bad);
  while (!BTOR_EMPTY_STACK (mc->constraints))
    boolector_release (btor, BTOR_POP_STACK (mc->constraints));
  BTOR_RELEASE_STACK (mm, mc->constraints);
  BTOR_RELEASE_STACK (mm, mc->reached);
  if (mc->forward) boolector_delete (mc->forward);
  BTOR_DELETE (mm, mc);
  btor_delete_btor (btor);
}

BoolectorNode *
boolector_input (BtorMC *mc, int width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMcInput *input;
  BtorMemMgr *mm;
  BoolectorNode *res;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_BOOLECTOR (mc->state != BTOR_NO_MC_STATE,
                        "can only be called before checking");
  BTOR_ABORT_BOOLECTOR (1 > width, "given width < 1");
  btor = mc->btor;
  mm   = btor->mm;
  res  = boolector_var (btor, width, name);
  BTOR_NEW (mm, input);
  assert (input);
  input->id   = (int) mc->inputs->count;
  input->node = res;
  bucket      = btor_insert_in_ptr_hash_table (mc->inputs, res);
  assert (bucket);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = input;
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
boolector_latch (BtorMC *mc, int width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMcLatch *latch;
  BtorMemMgr *mm;
  BoolectorNode *res;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_BOOLECTOR (mc->state != BTOR_NO_MC_STATE,
                        "can only be callsed before checking");
  assert (1 <= width);
  btor = mc->btor;
  mm   = btor->mm;
  res  = boolector_var (btor, width, name);
  BTOR_NEW (mm, latch);
  assert (latch);
  latch->id   = (int) mc->latches->count;
  latch->node = res;
  latch->init = latch->next = 0;
  bucket                    = btor_insert_in_ptr_hash_table (mc->latches, res);
  assert (bucket);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = latch;
  if (name)
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              2,
              "declared latch %d '%s' of width %d",
              latch->id,
              name,
              width);
  else
    BTOR_MSG (boolector_get_btor_msg (mc->btor),
              2,
              "declared latch %d of width %d",
              latch->id,
              width);
  return res;
}

static BtorMcLatch *
btor_find_mc_latch (BtorMC *mc, BoolectorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorMcLatch *res;
  assert (mc);
  assert (node);
  bucket = btor_find_in_ptr_hash_table (mc->latches, node);
  if (!bucket) return 0;
  res = bucket->data.asPtr;
  assert (res->node == bucket->key);
  return res;
}

void
boolector_next (BtorMC *mc, BoolectorNode *node, BoolectorNode *next)
{
  BtorMcLatch *latch;
  Btor *btor;
  (void) btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (node);
  BTOR_MC_CHECK_OWNS_NODE_ARG (next);
  btor = mc->btor;
  assert (!boolector_is_array (btor, node));
  assert (!boolector_is_array (btor, next));
  assert (boolector_get_width (btor, node) == boolector_get_width (btor, next));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->next);
  latch->next = boolector_copy (mc->btor, next);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor), 2, "adding NEXT latch %d", latch->id);
  mc->nextstates++;
}

void
boolector_init (BtorMC *mc, BoolectorNode *node, BoolectorNode *init)
{
  BtorMcLatch *latch;
  Btor *btor;
  (void) btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (node);
  BTOR_MC_CHECK_OWNS_NODE_ARG (init);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (init)));
  btor = mc->btor;
  assert (boolector_get_width (btor, node) == boolector_get_width (btor, init));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->init);
  latch->init = boolector_copy (mc->btor, init);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor), 2, "adding INIT latch %d", latch->id);
  mc->initialized++;
}

int
boolector_bad (BtorMC *mc, BoolectorNode *bad)
{
  int res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (bad);
  assert (boolector_get_width (mc->btor, bad) == 1);
  assert (!boolector_is_array (mc->btor, bad));
  res = BTOR_COUNT_STACK (mc->bad);
  (void) boolector_copy (mc->btor, bad);
  BTOR_PUSH_STACK (mc->btor->mm, mc->bad, bad);
  assert (res == BTOR_COUNT_STACK (mc->reached));
  BTOR_PUSH_STACK (mc->btor->mm, mc->reached, -1);
  BTOR_MSG (
      boolector_get_btor_msg (mc->btor), 2, "adding BAD property %d", res);
  return res;
}

int
boolector_constraint (BtorMC *mc, BoolectorNode *constraint)
{
  int res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (constraint);
  assert (!boolector_is_array (mc->btor, constraint));
  assert (boolector_get_width (mc->btor, constraint) == 1);
  res = BTOR_COUNT_STACK (mc->constraints);
  (void) boolector_copy (mc->btor, constraint);
  BTOR_PUSH_STACK (mc->btor->mm, mc->constraints, constraint);
  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "adding environment CONSTRAINT %d",
            res);
  return res;
}

static char *
timed_symbol (Btor *btor, BoolectorNode *node, int time)
{
  char *res, suffix[20];
  const char *symbol;
  int symlen, reslen;
  assert (btor);
  assert (node);
  assert (time >= 0);
  assert (BTOR_IS_REGULAR_NODE (node));
  symbol = boolector_get_symbol (btor, node);
  if (!symbol) return 0;
  sprintf (suffix, "@%d", time);
  symlen = strlen (symbol);
  reslen = symlen + strlen (suffix) + 1;
  res    = btor_malloc (btor->mm, reslen);
  (void) strcpy (res, symbol);
  strcpy (res + symlen, suffix);
  return res;
}

static void
initialize_inputs_of_frame (BtorMC *mc, BtorMcFrame *f)
{
  BoolectorNode *src, *dst;
  BtorHashTableIterator it;
  char *sym;
  int w;

#ifndef NDEBUG
  int i = 0;
  BtorMcInput *input;
#endif

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %d inputs of frame %d",
            (int) mc->inputs->count,
            f->time);

  init_hash_table_iterator (&it, mc->inputs);
  while (has_next_hash_table_iterator (&it))
  {
#ifndef NDEBUG
    input = it.bucket->data.asPtr;
    assert (input);
#endif
    src = (BoolectorNode *) next_hash_table_iterator (&it);
    assert (src);
    assert (BTOR_IS_REGULAR_NODE (src));
#ifndef NDEBUG
    assert (input->node == src);
    assert (input->id == i);
#endif
    sym = timed_symbol (mc->btor, src, f->time);
    w   = boolector_get_width (mc->btor, src);
    dst = boolector_var (mc->forward, w, sym);
    btor_freestr (mc->btor->mm, sym);
    assert (BTOR_COUNT_STACK (f->inputs) == i++);
    BTOR_PUSH_STACK (mc->btor->mm, f->inputs, dst);
  }
}

static void
initialize_latches_of_frame (BtorMC *mc, BtorMcFrame *f)
{
  BoolectorNode *src, *dst;
  BtorHashTableIterator it;
  BtorMcLatch *latch;
  const char *bits;
  BtorMcFrame *p;
  char *sym;
  int i, w;

  assert (mc);
  assert (f);
  assert (f->time >= 0);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %d latches in frame %d",
            (int) mc->latches->count,
            f->time);

  i = 0;
  init_hash_table_iterator (&it, mc->latches);
  while (has_next_hash_table_iterator (&it))
  {
    latch = it.bucket->data.asPtr;
    assert (latch);
    assert (latch->id == i);
    src = (BoolectorNode *) next_hash_table_iterator (&it);
    assert (src);
    assert (BTOR_IS_REGULAR_NODE (src));
    assert (latch->node == src);

    if (!f->time && latch->init)
    {
      bits = boolector_get_bits (mc->btor, latch->init);
      dst  = boolector_const (mc->forward, bits);
    }
    else if (f->time > 0 && latch->next)
    {
      p   = f - 1;
      dst = BTOR_PEEK_STACK (p->next, i);
      dst = boolector_copy (mc->forward, dst);
    }
    else
    {
      sym = timed_symbol (mc->btor, src, f->time);
      w   = boolector_get_width (mc->btor, src);
      dst = boolector_var (mc->forward, w, sym);
      btor_freestr (mc->btor->mm, sym);
    }
    assert (BTOR_COUNT_STACK (f->latches) == i);
    BTOR_PUSH_STACK (mc->btor->mm, f->latches, dst);
    i += 1;
  }
}

static void
initialize_next_state_functions_of_frame (BtorMC *mc,
                                          BoolectorNodeMap *map,
                                          BtorMcFrame *f)
{
  BoolectorNode *src, *dst, *node;
  BtorMcLatch *latch;
  BtorHashTableIterator it;
  int nextstates, i;
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

  i          = 0;
  nextstates = 0;
  init_hash_table_iterator (&it, mc->latches);
  while (has_next_hash_table_iterator (&it))
  {
    latch = it.bucket->data.asPtr;
    assert (latch);
    node = (BoolectorNode *) next_hash_table_iterator (&it);
    assert (latch->node == node);
    assert (BTOR_COUNT_STACK (f->next) == i);
    src = latch->next;
    if (src)
    {
      dst = boolector_non_recursive_substitute_node (mc->forward, map, src);
      dst = boolector_copy (mc->forward, dst);
      BTOR_PUSH_STACK (mc->btor->mm, f->next, dst);
      nextstates++;
    }
    else
      BTOR_PUSH_STACK (mc->btor->mm, f->next, 0);
    i += 1;
  }
  assert (nextstates == mc->nextstates);
  assert (BTOR_COUNT_STACK (f->next) == mc->latches->count);
}

static void
initialize_constraints_of_frame (BtorMC *mc,
                                 BoolectorNodeMap *map,
                                 BtorMcFrame *f)
{
  BoolectorNode *src, *dst, *constraint;
  int i;

  assert (mc);
  assert (map);
  assert (f);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %d environment constraints of frame %d",
            (int) BTOR_COUNT_STACK (mc->constraints),
            f->time);

  constraint = 0;

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    src = BTOR_PEEK_STACK (mc->constraints, i);
    assert (src);
    dst = boolector_non_recursive_substitute_node (mc->forward, map, src);
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
                                          BtorMcFrame *f)
{
  BoolectorNode *src, *dst;
  int i;

  assert (mc);
  assert (map);
  assert (f);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %d bad state propeties of frame %d",
            (int) BTOR_COUNT_STACK (mc->bad),
            f->time);

  for (i = 0; i < BTOR_COUNT_STACK (mc->bad); i++)
  {
    if (mc->continue_checking_if_reached
        || BTOR_PEEK_STACK (mc->reached, i) < 0)
    {
      src = BTOR_PEEK_STACK (mc->bad, i);
      assert (src);
      dst = boolector_non_recursive_substitute_node (mc->forward, map, src);
      dst = boolector_copy (mc->forward, dst);
    }
    else
      dst = 0;

    BTOR_PUSH_STACK (mc->btor->mm, f->bad, dst);
  }
}

static BoolectorNodeMap *
map_inputs_and_latches_of_frame (BtorMC *mc, BtorMcFrame *f)
{
  BoolectorNode *src, *dst;
  BoolectorNodeMap *res;
  BtorHashTableIterator it;
  int i;

  assert (mc);
  assert (f);
  assert (BTOR_COUNT_STACK (f->inputs) == mc->inputs->count);
  assert (BTOR_COUNT_STACK (f->latches) == mc->latches->count);

  res = boolector_new_node_map (mc->forward);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "mapping inputs and latchs of frame %d",
            f->time);

  i = 0;
  init_hash_table_iterator (&it, mc->inputs);
  while (has_next_hash_table_iterator (&it))
  {
    src = (BoolectorNode *) next_hash_table_iterator (&it);
    dst = BTOR_PEEK_STACK (f->inputs, i);
    boolector_map_node (res, src, dst);
    i += 1;
  }

  i = 0;
  init_hash_table_iterator (&it, mc->latches);
  while (has_next_hash_table_iterator (&it))
  {
    src = (BoolectorNode *) next_hash_table_iterator (&it);
    dst = BTOR_PEEK_STACK (f->latches, i);
    boolector_map_node (res, src, dst);
    i += 1;
  }

  assert ((unsigned) boolector_count_map (res)
          == mc->inputs->count + mc->latches->count);

  return res;
}

static void
initialize_new_forward_frame (BtorMC *mc)
{
  BtorMcFrame frame, *f;
  BoolectorNodeMap *map;
  int time;
#ifndef NDEBUG
  int old_mc_btor_num_nodes;
#endif

  assert (mc);
#ifndef NDEBUG
  old_mc_btor_num_nodes = mc->btor->nodes_unique_table.num_elements;
#endif

  time = BTOR_COUNT_STACK (mc->frames);
  BTOR_CLR (&frame);
  BTOR_PUSH_STACK (mc->btor->mm, mc->frames, frame);
  f       = mc->frames.start + time;
  f->time = time;

  if (!mc->forward)
  {
    BTOR_MSG (boolector_get_btor_msg (mc->btor), 1, "new forward manager");
    mc->forward = btor_new_btor ();
    boolector_set_opt (mc->forward, "incremental", 1);
    if (mc->trace_enabled) boolector_set_opt (mc->forward, "model_gen", 1);
    if (mc->verbosity)
      boolector_set_opt (mc->forward, "verbosity", mc->verbosity);
  }

  initialize_inputs_of_frame (mc, f);
  initialize_latches_of_frame (mc, f);

  map = map_inputs_and_latches_of_frame (mc, f);

  initialize_next_state_functions_of_frame (mc, map, f);
  initialize_constraints_of_frame (mc, map, f);
  initialize_bad_state_properties_of_frame (mc, map, f);

  boolector_delete_node_map (map);

  assert (old_mc_btor_num_nodes == mc->btor->nodes_unique_table.num_elements);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            1,
            "initialized forward frame at bound k = %d",
            time);
}

#if 0

static void
print_trace (BtorMC * mc, int p, int k)
{
  const char * symbol;
  BoolectorNode * node;
  BtorMcFrame * f;
  char buffer[30];
  char * a;
  int i, j;

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
	  btor_release_bv_assignment_str (f->btor, a);
	}
    }
  fflush (stdout);
}

#endif

static int
check_last_forward_frame (BtorMC *mc)
{
  int k, i, res, satisfied;
  BtorMcFrame *f;
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
      int reached;
      assert (!mc->continue_checking_if_reached);
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

int
boolector_bmc (BtorMC *mc, int mink, int maxk)
{
  int k;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);

  btor_mc_release_assignment (mc);

  BTOR_MSG (
      boolector_get_btor_msg (mc->btor),
      1,
      "calling BMC on %d properties from bound %d up-to maximum bound k = %d",
      (int) BTOR_COUNT_STACK (mc->bad),
      mink,
      maxk);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            1,
            "trace generation %s",
            mc->trace_enabled ? "enabled" : "disabled");

  mc->state = BTOR_NO_MC_STATE;

  while ((k = BTOR_COUNT_STACK (mc->frames)) <= maxk)
  {
    initialize_new_forward_frame (mc);
    if (k < mink) continue;
    if (check_last_forward_frame (mc))
    {
      if (mc->stop || mc->num_reached == BTOR_COUNT_STACK (mc->bad)
          || k == maxk)
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
btor_get_mc_forward2const (BtorMC *mc)
{
  if (!mc->forward2const) mc->forward2const = boolector_new_node_map (mc->btor);
  return mc->forward2const;
}

static BoolectorNodeMap *
btor_get_mc_model2const_map (BtorMC *mc, BtorMcFrame *frame)
{
  if (!frame->model2const)
    frame->model2const = boolector_new_node_map (mc->btor);
  return frame->model2const;
}

static void
btor_zero_normalize_assignment (char *assignment)
{
  char *p;
  for (p = assignment; *p; p++)
    if (*p == 'x') *p = '0';
}

static BoolectorNode *
btor_mc_forward2const_mapper (Btor *btor, void *state, BoolectorNode *node)
{
  const char *assignment;
  BtorMC *mc = state;
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
  normalized = btor_strdup (mc->btor->mm, assignment);
  btor_zero_normalize_assignment (normalized);
  res = boolector_const (mc->btor, normalized);
  btor_freestr (mc->btor->mm, normalized);
  boolector_free_bv_assignment (mc->forward, assignment);

  return res;
}

static BoolectorNode *
btor_mc_forward2const (BtorMC *mc, BoolectorNode *node)
{
  BoolectorNodeMap *map;
  assert (BTOR_REAL_ADDR_NODE (node)->btor == mc->forward);
  map = btor_get_mc_forward2const (mc);
  return boolector_non_recursive_extended_substitute_node (
      mc->btor, map, mc, btor_mc_forward2const_mapper, boolector_release, node);
}

typedef struct BtorMcModel2ConstMapper BtorMcModel2ConstMapper;

struct BtorMcModel2ConstMapper
{
  int time;
  BtorMC *mc;
};

static BoolectorNode *
btor_mc_model2const_mapper (Btor *btor, void *state, BoolectorNode *node)
{
  BtorMcModel2ConstMapper *mapper;
  BoolectorNode *node_at_time, *res;
  const char *sym, *constbits;
  BtorPtrHashBucket *bucket;
  BtorMcFrame *frame;
  BtorMcInput *input;
  BtorMcLatch *latch;
  BtorMC *mc;
  char *bits;
  int time;

  assert (!BTOR_IS_INVERTED_NODE (node));

  if (!boolector_is_var (btor, node)) return 0;

  mapper = state;
  assert (mapper);
  mc = mapper->mc;
  assert (mc);
  assert (mc->btor == btor);
  assert (mc->btor == boolector_get_btor (node));
  (void) btor;
  time = mapper->time;

  assert (0 <= time && time < BTOR_COUNT_STACK (mc->frames));
  frame = mc->frames.start + time;

  bucket = btor_find_in_ptr_hash_table (mc->inputs, node);

  if (bucket)
  {
    input = bucket->data.asPtr;
    assert (input);
    assert (input->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->inputs, input->id);
    assert (node_at_time);
    assert (BTOR_REAL_ADDR_NODE (node_at_time)->btor == mc->forward);
    constbits = boolector_bv_assignment (mc->forward, node_at_time);
    bits      = btor_strdup (mc->btor->mm, constbits);
    boolector_free_bv_assignment (mc->btor, constbits);
    btor_zero_normalize_assignment (bits);
    res = boolector_const (mc->btor, bits);
    btor_freestr (mc->btor->mm, bits);
  }
  else
  {
    bucket = btor_find_in_ptr_hash_table (mc->latches, node);
    if (!boolector_is_var (mc->btor, node))
      sym = 0;
    else
      sym = boolector_get_symbol (mc->btor, node);
    if (sym)
      BTOR_ABORT_BOOLECTOR (
          !bucket, "variable '%s' not a latch nor an input", sym);
    else
      BTOR_ABORT_BOOLECTOR (!bucket,
                            "variable without symbol not a latch nor an input");
    latch = bucket->data.asPtr;
    assert (latch);
    assert (latch->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->latches, latch->id);
    assert (BTOR_REAL_ADDR_NODE (node_at_time)->btor == mc->forward);
    res = btor_mc_forward2const (mc, node_at_time);
    res = boolector_copy (mc->btor, res);
  }

  // TODO wrap into Aina's BtorBVAssignment ....

  return res;
}

static BoolectorNode *
btor_mc_model2const (BtorMC *mc, BoolectorNode *node, int time)
{
  BtorMcModel2ConstMapper mapper;
  BoolectorNodeMap *map;
  BtorMcFrame *f;
  assert (BTOR_REAL_ADDR_NODE (node)->btor == mc->btor);
  assert (0 <= time && time < BTOR_COUNT_STACK (mc->frames));
  mapper.mc   = mc;
  mapper.time = time;
  f           = mc->frames.start + time;
  map         = btor_get_mc_model2const_map (mc, f);
  return boolector_non_recursive_extended_substitute_node (
      mc->btor,
      map,
      &mapper,
      btor_mc_model2const_mapper,
      boolector_release,
      node);
}

char *
boolector_mc_assignment (BtorMC *mc, BoolectorNode *node, int time)
{
  BoolectorNode *node_at_time, *const_node;
  const char *bits_owned_by_forward, *bits;
  BtorPtrHashBucket *bucket;
  BtorMcInput *input;
  BtorMcFrame *frame;
  char *res;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);

  BTOR_ABORT_BOOLECTOR (mc->state == BTOR_NO_MC_STATE,
                        "model checker was not run before");

  BTOR_ABORT_BOOLECTOR (mc->state == BTOR_UNSAT_MC_STATE,
                        "model checking status is UNSAT");

  assert (mc->state == BTOR_SAT_MC_STATE);
  BTOR_ABORT_BOOLECTOR (!mc->trace_enabled,
                        "'boolector_enable_trace_gen' was not called before");

  assert (mc->state == BTOR_SAT_MC_STATE);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (node);
  BTOR_ABORT_REFS_NOT_POS_BOOLECTOR (node);

  BTOR_MC_CHECK_OWNS_NODE_ARG (node);

  BTOR_ABORT_BOOLECTOR (0 > time, "negative 'time' argument");
  BTOR_ABORT_BOOLECTOR (time >= BTOR_COUNT_STACK (mc->frames),
                        "'time' exceeds previously returned bound");

  bucket = btor_find_in_ptr_hash_table (mc->inputs, node);
  if (bucket)
  {
    input = bucket->data.asPtr;
    assert (input);
    assert (input->node == node);
    frame        = mc->frames.start + time;
    node_at_time = BTOR_PEEK_STACK (frame->inputs, input->id);
    assert (node_at_time);
    bits_owned_by_forward = boolector_bv_assignment (mc->forward, node_at_time);
    res                   = btor_strdup (mc->btor->mm, bits_owned_by_forward);
    btor_zero_normalize_assignment (res);
    boolector_free_bv_assignment (mc->forward, bits_owned_by_forward);
  }
  else
  {
    const_node = btor_mc_model2const (mc, node, time);
    assert (const_node);
    assert (boolector_is_const (mc->btor, const_node));
    assert (boolector_get_btor (const_node) == mc->btor);
    bits = boolector_get_bits (mc->btor, const_node);
    res  = btor_strdup (mc->btor->mm, bits);
  }

  return res;
}

void
boolector_free_mc_assignment (BtorMC *mc, char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
  btor_freestr (mc->btor->mm, assignment);
}

void
boolector_dump_btormc (BtorMC *mc, FILE *file)
{
  BtorHashTableIterator it;
  BtorDumpContext *bdc;
  int i;

  bdc = btor_new_dump_context (mc->btor);

  init_hash_table_iterator (&it, mc->inputs);
  while (has_next_hash_table_iterator (&it))
  {
    BtorMcInput *input = next_data_hash_table_iterator (&it)->asPtr;
    assert (input);
    assert (input->node);
    btor_add_input_to_dump_context (bdc,
                                    BTOR_IMPORT_BOOLECTOR_NODE (input->node));
  }

  init_hash_table_iterator (&it, mc->latches);
  while (has_next_hash_table_iterator (&it))
  {
    BtorMcLatch *latch = next_data_hash_table_iterator (&it)->asPtr;
    assert (latch);
    assert (latch->node);
    assert (BTOR_IS_REGULAR_NODE (latch->node));
    btor_add_latch_to_dump_context (bdc,
                                    BTOR_IMPORT_BOOLECTOR_NODE (latch->node));
    if (latch->init)
      btor_add_init_to_dump_context (bdc,
                                     BTOR_IMPORT_BOOLECTOR_NODE (latch->node),
                                     BTOR_IMPORT_BOOLECTOR_NODE (latch->init));
    if (latch->next)
      btor_add_next_to_dump_context (bdc,
                                     BTOR_IMPORT_BOOLECTOR_NODE (latch->node),
                                     BTOR_IMPORT_BOOLECTOR_NODE (latch->next));
  }

  for (i = 0; i < BTOR_COUNT_STACK (mc->bad); i++)
  {
    BoolectorNode *bad = BTOR_PEEK_STACK (mc->bad, i);
    btor_add_bad_to_dump_context (bdc, BTOR_IMPORT_BOOLECTOR_NODE (bad));
  }

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    BoolectorNode *constraint = BTOR_PEEK_STACK (mc->constraints, i);
    btor_add_constraint_to_dump_context (
        bdc, BTOR_IMPORT_BOOLECTOR_NODE (constraint));
  }

  btor_dump_btor_bdc (bdc, file);
  btor_delete_dump_context (bdc);
}

int
boolector_reached_bad_at_bound_mc (BtorMC *mc, int badidx)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_BOOLECTOR (mc->state == BTOR_NO_MC_STATE,
                        "model checker was not run before");
  BTOR_ABORT_BOOLECTOR (
      mc->stop, "stopping at first reached property has to be disabled");
  BTOR_ABORT_BOOLECTOR (badidx < 0, "negative bad state property index");
  BTOR_ABORT_BOOLECTOR (badidx >= BTOR_COUNT_STACK (mc->bad),
                        "bad state property index too large");
  return BTOR_PEEK_STACK (mc->reached, badidx);
}
