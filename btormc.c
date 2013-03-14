/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormc.h"
#include "btorabort.h"
#include "btorexp.h"
#include "btormap.h"

/*------------------------------------------------------------------------*/

#include <stdarg.h>

/*------------------------------------------------------------------------*/

#define BTOR_ABORT_IF_STATE(MC)                            \
  do                                                       \
  {                                                        \
    BTOR_ABORT_BOOLECTOR ((MC)->state != BTOR_NO_MC_STATE, \
                          "model checker was run before"); \
  } while (0)

/*------------------------------------------------------------------------*/

typedef struct BtorMcInput
{
  int id;
  BtorNode *node;
} BtorMcInput;

typedef struct BtorMcLatch
{
  int id;
  BtorNode *node, *next, *init;
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
  Btor *btor;
  BtorNodePtrStack inputs, init, latches, next, bad;
} BtorMcFrame;

BTOR_DECLARE_STACK (McFrame, BtorMcFrame);

struct BtorMC
{
  BtorMcState state;
  int verbosity, trace_enabled, initialized, nextstates;
  Btor *btor, *forward;
  BtorMcFrameStack frames;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *latches;
  BtorNodePtrStack bad;
};

/*------------------------------------------------------------------------*/

BtorMC *
boolector_new_mc (void)
{
  BtorMemMgr *mm;
  BtorMC *res;
  Btor *btor = boolector_new ();
  mm         = btor->mm;
  BTOR_CNEW (mm, res);
  res->btor    = btor;
  res->inputs  = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_new_ptr_hash_table (mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  assert (res->state == BTOR_NO_MC_STATE);
  return res;
}

void
boolector_set_verbosity_mc (BtorMC *mc, int verbosity)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  mc->verbosity = verbosity;
  btor_set_verbosity_btor (mc->btor, verbosity);
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
  btor_release_exp (btor, input->node);
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
  btor_release_exp (btor, latch->node);
  if (latch->init) btor_release_exp (btor, latch->init);
  if (latch->next) btor_release_exp (btor, latch->next);
  BTOR_DELETE (mm, latch);
}

static void
btor_msg_mc (BtorMC *mc, int level, const char *fmt, ...)
{
  va_list ap;
  assert (mc);
  if (mc->verbosity < level) return;
  assert (fmt != NULL);
  fprintf (stdout, "[btormc] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  putc ('\n', stdout);
  fflush (stdout);
}

static void
release_frame_stack (BtorMcFrame *frame, BtorNodePtrStack *stack)
{
  BtorNode *node;

  while (!BTOR_EMPTY_STACK (*stack))
  {
    node = BTOR_POP_STACK (*stack);
    if (node) btor_release_exp (frame->btor, node);
  }

  BTOR_RELEASE_STACK (frame->btor->mm, *stack);
}

static void
btor_release_mc_frame (BtorMcFrame *frame)
{
  release_frame_stack (frame, &frame->inputs);
  release_frame_stack (frame, &frame->init);
  release_frame_stack (frame, &frame->latches);
  release_frame_stack (frame, &frame->next);
  release_frame_stack (frame, &frame->bad);
}

void
boolector_delete_mc (BtorMC *mc)
{
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  BtorMcFrame *f;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  btor_msg_mc (mc,
               1,
               "deleting model checker: %u inputs, %u latches, %u bad",
               mc->inputs->count,
               mc->latches->count,
               BTOR_COUNT_STACK (mc->bad));
  btor = mc->btor;
  mm   = btor->mm;
  for (f = mc->frames.start; f < mc->frames.top; f++) btor_release_mc_frame (f);
  BTOR_RELEASE_STACK (mm, mc->frames);
  for (bucket = mc->inputs->first; bucket; bucket = bucket->next)
    btor_delete_mc_input (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->inputs);
  for (bucket = mc->latches->first; bucket; bucket = bucket->next)
    btor_delete_mc_latch (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->latches);
  while (!BTOR_EMPTY_STACK (mc->bad))
    btor_release_exp (btor, BTOR_POP_STACK (mc->bad));
  BTOR_RELEASE_STACK (mm, mc->bad);
  if (mc->forward) boolector_delete (mc->forward);
  boolector_delete (btor);
  BTOR_DELETE (mm, mc);
}

BtorNode *
boolector_input (BtorMC *mc, int width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMcInput *input;
  BtorMemMgr *mm;
  BtorNode *res;
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
    btor_msg_mc (
        mc, 2, "declared input%d[%d] named \"%s\"", input->id, width, name);
  else
    btor_msg_mc (mc, 2, "declared input%d[%d]", input->id, width);
  return res;
}

BtorNode *
boolector_latch (BtorMC *mc, int width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMcLatch *latch;
  BtorMemMgr *mm;
  BtorNode *res;
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
    btor_msg_mc (
        mc, 2, "declared latch%d[%d] named \"%s\"", latch->id, width, name);
  else
    btor_msg_mc (mc, 2, "declared latch%d[%d]", latch->id, width);
  return res;
}

static BtorMcLatch *
btor_find_mc_latch (BtorMC *mc, BtorNode *node)
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
boolector_next (BtorMC *mc, BtorNode *node, BtorNode *next)
{
  BtorMcLatch *latch;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  assert (node);
  assert (next);
  btor = mc->btor;
  assert (!btor_is_array_exp (btor, node));
  assert (!btor_is_array_exp (btor, next));
  assert (btor_get_exp_len (btor, node) == btor_get_exp_len (btor, next));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->next);
  latch->next = btor_copy_exp (mc->btor, next);
  btor_msg_mc (mc, 2, "adding NEXT latch%d", latch->id);
  mc->nextstates++;
}

void
boolector_init (BtorMC *mc, BtorNode *node, BtorNode *init)
{
  BtorMcLatch *latch;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  assert (node);
  assert (init);
  assert (BTOR_IS_BV_CONST_NODE (init));
  btor = mc->btor;
  assert (btor_get_exp_len (btor, node) == btor_get_exp_len (btor, init));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->init);
  latch->init = btor_copy_exp (mc->btor, init);
  btor_msg_mc (mc, 2, "adding INIT latch%d", latch->id);
  mc->initialized++;
}

int
boolector_bad (BtorMC *mc, BtorNode *bad)
{
  int res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  assert (bad);
  assert (!btor_is_array_exp (mc->btor, bad));
  assert (btor_get_exp_len (mc->btor, bad) == 1);
  res = BTOR_COUNT_STACK (mc->bad);
  (void) btor_copy_exp (mc->btor, bad);
  BTOR_PUSH_STACK (mc->btor->mm, mc->bad, bad);
  btor_msg_mc (mc, 2, "adding BAD property%d", res);
  return res;
}

static char *
timed_symbol (Btor *btor, BtorNode *node, int time)
{
  char *res, suffix[20];
  int symlen, reslen;
  assert (btor);
  assert (node);
  assert (time >= 0);
  assert (BTOR_IS_REGULAR_NODE (node));
  if (!node->symbol) return 0;
  sprintf (suffix, "@%d", time);
  symlen = strlen (node->symbol);
  reslen = symlen + strlen (suffix) + 1;
  res    = btor_malloc (btor->mm, reslen);
  (void) strcpy (res, node->symbol);
  strcpy (res + symlen, suffix);
  return res;
}

static void
initialize_inputs_of_frame (BtorMC *mc, BtorMcFrame *f)
{
  BtorNode *src, *dst;
  BtorPtrHashBucket *b;
  char *sym;
  int i;

#ifndef NDEBUG
  BtorMcInput *input;
#endif

  btor_msg_mc (mc,
               2,
               "initializing %d inputs of frame %d",
               (int) mc->inputs->count,
               f->time);

  for (b = mc->inputs->first, i = 0; b; b = b->next, i++)
  {
    src = b->key;
    assert (src);
    assert (BTOR_IS_REGULAR_NODE (src));
#ifndef NDEBUG
    input = b->data.asPtr;
    assert (input);
    assert (input->node == src);
    assert (input->id == i);
#endif
    sym = timed_symbol (f->btor, src, f->time);
    dst = boolector_var (f->btor, src->len, sym);
    btor_freestr (f->btor->mm, sym);
    assert (BTOR_COUNT_STACK (f->inputs) == i);
    BTOR_PUSH_STACK (f->btor->mm, f->inputs, dst);
  }
}

static void
initialize_latches_of_frame (BtorMC *mc, BtorMcFrame *f)
{
  BtorNode *src, *tmp, *dst;
  BtorPtrHashBucket *b;
  BtorMcLatch *latch;
  BtorMcFrame *p;
  char *sym;
  int i;

  assert (mc);
  assert (f);
  assert (f->time >= 0);

  btor_msg_mc (mc,
               2,
               "initializing %d latches in frame %d",
               (int) mc->latches->count,
               f->time);

  for (b = mc->latches->first, i = 0; b; b = b->next, i++)
  {
    src = b->key;
    assert (src);
    assert (BTOR_IS_REGULAR_NODE (src));
    latch = b->data.asPtr;
    assert (latch);
    assert (latch->node == src);
    assert (latch->id == i);

    if (!f->time && latch->init)
    {
      tmp = BTOR_REAL_ADDR_NODE (latch->init);
      dst = btor_const_exp (f->btor, tmp->bits);
      if (BTOR_IS_INVERTED_NODE (latch->init)) dst = BTOR_INVERT_NODE (dst);
    }
    else if (f->time > 0 && latch->next)
    {
      p   = f - 1;
      dst = BTOR_PEEK_STACK (p->next, i);
      dst = btor_copy_exp (f->btor, dst);
    }
    else
    {
      sym = timed_symbol (f->btor, src, f->time);
      dst = boolector_var (f->btor, src->len, sym);
      btor_freestr (f->btor->mm, sym);
    }
    assert (BTOR_COUNT_STACK (f->latches) == i);
    BTOR_PUSH_STACK (f->btor->mm, f->latches, dst);
  }
}

static void
initialize_next_state_functions_of_frame (BtorMC *mc,
                                          BtorNodeMap *map,
                                          BtorMcFrame *f)
{
  BtorPtrHashBucket *b;
  BtorNode *src, *dst;
  BtorMcLatch *latch;
  int nextstates, i;

  assert (mc);
  assert (map);
  assert (f);
  assert (f->time >= 0);

  btor_msg_mc (mc,
               2,
               "initializing %d next state functions of frame %d",
               mc->nextstates,
               f->time);

  i = nextstates = 0;
  for (b = mc->latches->first, i = 0; b; b = b->next, i++)
  {
    latch = b->data.asPtr;
    assert (latch);
    assert (latch->node == b->key);
    assert (BTOR_COUNT_STACK (f->next) == i);
    src = latch->next;
    if (src)
    {
      dst = btor_non_recursive_substitute_node (f->btor, map, src);
      dst = btor_copy_exp (f->btor, dst);
      BTOR_PUSH_STACK (f->btor->mm, f->next, dst);
      nextstates++;
    }
    else
      BTOR_PUSH_STACK (f->btor->mm, f->next, 0);
  }
  assert (nextstates == mc->nextstates);
  assert (BTOR_COUNT_STACK (f->next) == mc->latches->count);
}

static void
initialize_bad_state_properties_of_frame (BtorMC *mc,
                                          BtorNodeMap *map,
                                          BtorMcFrame *f)
{
  BtorNode *src, *dst;
  int i;

  assert (mc);
  assert (map);
  assert (f);

  btor_msg_mc (mc,
               2,
               "initializing %d bad state propeties of frame %d",
               (int) BTOR_COUNT_STACK (mc->bad),
               f->time);

  for (i = 0; i < BTOR_COUNT_STACK (mc->bad); i++)
  {
    src = BTOR_PEEK_STACK (mc->bad, i);
    assert (src);
    dst = btor_non_recursive_substitute_node (f->btor, map, src);
    dst = btor_copy_exp (f->btor, dst);
    BTOR_PUSH_STACK (f->btor->mm, f->bad, dst);
  }
}

static BtorNodeMap *
map_inputs_and_latches_of_frame (BtorMC *mc, BtorMcFrame *f)
{
  BtorPtrHashBucket *b;
  BtorNode *src, *dst;
  BtorNodeMap *res;
  int i;

  assert (mc);
  assert (f);
  assert (BTOR_COUNT_STACK (f->inputs) == mc->inputs->count);
  assert (BTOR_COUNT_STACK (f->latches) == mc->latches->count);

  res = btor_new_node_map (f->btor);

  btor_msg_mc (mc, 2, "mapping inputs and latchs of frame %d", f->time);

  for (b = mc->inputs->first, i = 0; b; b = b->next, i++)
  {
    src = b->key;
    dst = BTOR_PEEK_STACK (f->inputs, i);
    btor_map_node (f->btor, res, src, dst);
  }

  for (b = mc->latches->first, i = 0; b; b = b->next, i++)
  {
    src = b->key;
    dst = BTOR_PEEK_STACK (f->latches, i);
    btor_map_node (f->btor, res, src, dst);
  }

  assert (res->count == mc->inputs->count + mc->latches->count);

  return res;
}

static void
initialize_new_forward_frame (BtorMC *mc)
{
  BtorMcFrame frame, *f;
  BtorNodeMap *map;
  int time, k;
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
    btor_msg_mc (mc, 1, "new forward manager");
    mc->forward = btor_new_btor ();
    btor_enable_inc_usage (mc->forward);
    if (mc->trace_enabled) btor_enable_model_gen (mc->forward);
    if (mc->verbosity) btor_set_verbosity_btor (mc->forward, mc->verbosity);
  }
  f->btor = mc->forward;

  initialize_inputs_of_frame (mc, f);
  initialize_latches_of_frame (mc, f);

  map = map_inputs_and_latches_of_frame (mc, f);

  initialize_next_state_functions_of_frame (mc, map, f);
  initialize_bad_state_properties_of_frame (mc, map, f);

  btor_delete_node_map (f->btor, map);

  assert (old_mc_btor_num_nodes == mc->btor->nodes_unique_table.num_elements);

  k = BTOR_COUNT_STACK (mc->frames);
  btor_msg_mc (mc, 1, "initialized forward frame at bound k = %d", k);
}

#if 0

static void
print_trace (BtorMC * mc, int p, int k)
{
  const char * symbol;
  BtorNode * node;
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
	  a = boolector_bv_assignment (f->btor, node);
	  if (node->symbol)
	    symbol = node->symbol;
	  else
	    {
	      sprintf (buffer, "input%d@%d", j, i);
	      symbol = buffer;
	    }
	  printf ("%s = %s\n", symbol, a);
	  boolector_free_bv_assignment (f->btor, a);
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
  BtorNode *bad;

  k = BTOR_COUNT_STACK (mc->frames) - 1;
  assert (k >= 0);
  f = mc->frames.top - 1;
  assert (f->time == k);

  btor_msg_mc (mc, 1, "checking forward frame at bound k = %d", k);
  satisfied = 0;

  for (i = 0; i < BTOR_COUNT_STACK (f->bad); i++)
  {
    btor_msg_mc (mc,
                 1,
                 "checking forward frame bad state property %d at bound k = %d",
                 i,
                 k);
    bad = BTOR_PEEK_STACK (f->bad, i);
    boolector_assume (f->btor, bad);
    res = boolector_sat (f->btor);
    if (res == BOOLECTOR_SAT)
    {
      btor_msg_mc (
          mc, 1, "bad state property %d at bound k = %d SATISFIABLE", i, k);
      satisfied++;
    }
    else
    {
      assert (res == BOOLECTOR_UNSAT);
      btor_msg_mc (
          mc, 1, "bad state property %d at bound k = %d UNSATISFIABLE", i, k);
    }
  }

  btor_msg_mc (mc,
               1,
               "found %d satisfiable bad state properties at bound k = %d",
               satisfied,
               k);

  return satisfied;
}

int
boolector_bmc (BtorMC *mc, int maxk)
{
  int k;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);

  btor_msg_mc (mc,
               1,
               "calling BMC on %d properties up-to maximum bound k = %d",
               (int) BTOR_COUNT_STACK (mc->bad),
               maxk);

  // For debugging purposes temporarily reset the state.
  //
  mc->state = BTOR_NO_MC_STATE;

  while ((k = BTOR_COUNT_STACK (mc->frames)) <= maxk)
  {
    initialize_new_forward_frame (mc);
    if (check_last_forward_frame (mc))
    {
      btor_msg_mc (mc, 2, "entering SAT state");
      mc->state = BTOR_SAT_MC_STATE;
      assert (k >= 0);
      return k;
    }
  }

  btor_msg_mc (mc, 2, "entering UNSAT state");
  mc->state = BTOR_UNSAT_MC_STATE;

  return -1;
}

char *
boolector_mc_assignment (BtorMC *mc, BtorNode *node, int time)
{
  BtorPtrHashBucket *bucket;
  BtorNode *node_at_time;
  BtorMcLatch *latch;
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
  BTOR_ABORT_BOOLECTOR (0 > time, "negative 'time' argument");
  BTOR_ABORT_BOOLECTOR (time > BTOR_COUNT_STACK (mc->frames),
                        "'time' exceeds previously returned bound");
  assert (!BTOR_EMPTY_STACK (mc->frames));
  frame  = mc->frames.start + time;
  bucket = btor_find_in_ptr_hash_table (mc->inputs, node);
  if (bucket)
  {
    input = bucket->data.asPtr;
    assert (input);
    assert (input->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->inputs, input->id);
    assert (node_at_time);
    res = boolector_bv_assignment (mc->forward, node_at_time);
  }
  else
  {
    bucket = btor_find_in_ptr_hash_table (mc->latches, node);

    if (bucket)
    {
      latch = bucket->data.asPtr;
      assert (latch);
      assert (latch->node == node);
      node_at_time = BTOR_PEEK_STACK (frame->latches, latch->id);
      assert (node_at_time);
      res = boolector_bv_assignment (mc->forward, node_at_time);
    }
    else
      res = 0;
  }

  BTOR_ABORT_BOOLECTOR (!bucket,
                        "'node' argument is neither an input nor a latch");

  return res;
  ;
}

void
boolector_free_mc_assignment (BtorMC *mc, char *assignment)
{
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_ARG_NULL_BOOLECTOR (assignment);
  btor_freestr (mc->btor->mm, assignment);
}
