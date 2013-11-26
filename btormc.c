/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormc.h"
#include "btorabort.h"
#include "btorconst.h"
#include "btorexp.h"
#include "btormap.h"
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
  BtorNodeMap *model2const;
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
  BtorNodePtrStack constraints;
  BtorNodeMap *forward2const;
};

/*------------------------------------------------------------------------*/

BtorMC *
boolector_new_mc (void)
{
  BtorMemMgr *mm;
  BtorMC *res;
  Btor *btor;
  btor = btor_new_btor ();
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
btor_release_mc_frame_stack (BtorMC *mc, BtorNodePtrStack *stack)
{
  BtorNode *node;

  while (!BTOR_EMPTY_STACK (*stack))
  {
    node = BTOR_POP_STACK (*stack);
    if (node) btor_release_exp (mc->forward, node);
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
    btor_msg_mc (mc,
                 1,
                 "releasing forward to constant mapping of size %d",
                 BTOR_COUNT_MAP (mc->forward2const));
    btor_delete_node_map (mc->forward2const);
    mc->forward2const = 0;
  }

  for (f = mc->frames.start; f < mc->frames.top; f++)
    if (f->model2const)
    {
      btor_msg_mc (mc,
                   1,
                   "releasing model to constant mapping of size %d at time %d",
                   BTOR_COUNT_MAP (f->model2const),
                   (int) (f - mc->frames.start));
      btor_delete_node_map (f->model2const);
      f->model2const = 0;
    }
}

void
boolector_delete_mc (BtorMC *mc)
{
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  BtorMcFrame *f;
  Btor *btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  btor_mc_release_assignment (mc);
  btor_msg_mc (
      mc,
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
  for (bucket = mc->inputs->first; bucket; bucket = bucket->next)
    btor_delete_mc_input (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->inputs);
  for (bucket = mc->latches->first; bucket; bucket = bucket->next)
    btor_delete_mc_latch (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->latches);
  while (!BTOR_EMPTY_STACK (mc->bad))
    btor_release_exp (btor, BTOR_POP_STACK (mc->bad));
  BTOR_RELEASE_STACK (mm, mc->bad);
  while (!BTOR_EMPTY_STACK (mc->constraints))
    btor_release_exp (btor, BTOR_POP_STACK (mc->constraints));
  BTOR_RELEASE_STACK (mm, mc->constraints);
  if (mc->forward) btor_delete_btor (mc->forward);
  BTOR_DELETE (mm, mc);
  btor_delete_btor (btor);
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
  res  = btor_var_exp (btor, width, name);
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
        mc, 2, "declared input %d '%s' of width %d", input->id, name, width);
  else
    btor_msg_mc (mc, 2, "declared input %d of width", input->id, width);
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
  res  = btor_var_exp (btor, width, name);
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
        mc, 2, "declared latch %d width %d named '%s'", latch->id, width, name);
  else
    btor_msg_mc (mc, 2, "declared latch %d of width %d", latch->id, width);
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
  (void) btor;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (node);
  BTOR_MC_CHECK_OWNS_NODE_ARG (next);
  btor = mc->btor;
  assert (!btor_is_array_exp (btor, node));
  assert (!btor_is_array_exp (btor, next));
  assert (btor_get_exp_len (btor, node) == btor_get_exp_len (btor, next));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->next);
  latch->next = btor_copy_exp (mc->btor, next);
  btor_msg_mc (mc, 2, "adding NEXT latch %d", latch->id);
  mc->nextstates++;
}

void
boolector_init (BtorMC *mc, BtorNode *node, BtorNode *init)
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
  assert (btor_get_exp_len (btor, node) == btor_get_exp_len (btor, init));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->init);
  latch->init = btor_copy_exp (mc->btor, init);
  btor_msg_mc (mc, 2, "adding INIT latch %d", latch->id);
  mc->initialized++;
}

int
boolector_bad (BtorMC *mc, BtorNode *bad)
{
  int res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (bad);
  assert (!btor_is_array_exp (mc->btor, bad));
  assert (btor_get_exp_len (mc->btor, bad) == 1);
  res = BTOR_COUNT_STACK (mc->bad);
  (void) btor_copy_exp (mc->btor, bad);
  BTOR_PUSH_STACK (mc->btor->mm, mc->bad, bad);
  btor_msg_mc (mc, 2, "adding BAD property %d", res);
  return res;
}

int
boolector_constraint (BtorMC *mc, BtorNode *constraint)
{
  int res;
  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);
  BTOR_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (constraint);
  assert (!btor_is_array_exp (mc->btor, constraint));
  assert (btor_get_exp_len (mc->btor, constraint) == 1);
  res = BTOR_COUNT_STACK (mc->constraints);
  (void) btor_copy_exp (mc->btor, constraint);
  BTOR_PUSH_STACK (mc->btor->mm, mc->constraints, constraint);
  btor_msg_mc (mc, 2, "adding environment CONSTRAINT %d", res);
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
    sym = timed_symbol (mc->btor, src, f->time);
    dst = btor_var_exp (mc->forward, src->len, sym);
    btor_freestr (mc->btor->mm, sym);
    assert (BTOR_COUNT_STACK (f->inputs) == i);
    BTOR_PUSH_STACK (mc->btor->mm, f->inputs, dst);
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
      dst = btor_const_exp (mc->forward, tmp->bits);
      if (BTOR_IS_INVERTED_NODE (latch->init)) dst = BTOR_INVERT_NODE (dst);
    }
    else if (f->time > 0 && latch->next)
    {
      p   = f - 1;
      dst = BTOR_PEEK_STACK (p->next, i);
      dst = btor_copy_exp (mc->forward, dst);
    }
    else
    {
      sym = timed_symbol (mc->btor, src, f->time);
      dst = btor_var_exp (mc->forward, src->len, sym);
      btor_freestr (mc->btor->mm, sym);
    }
    assert (BTOR_COUNT_STACK (f->latches) == i);
    BTOR_PUSH_STACK (mc->btor->mm, f->latches, dst);
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

  nextstates = 0;
  for (b = mc->latches->first, i = 0; b; b = b->next, i++)
  {
    latch = b->data.asPtr;
    assert (latch);
    assert (latch->node == b->key);
    assert (BTOR_COUNT_STACK (f->next) == i);
    src = latch->next;
    if (src)
    {
      dst = btor_non_recursive_substitute_node (mc->forward, map, src);
      dst = btor_copy_exp (mc->forward, dst);
      BTOR_PUSH_STACK (mc->btor->mm, f->next, dst);
      nextstates++;
    }
    else
      BTOR_PUSH_STACK (mc->btor->mm, f->next, 0);
  }
  assert (nextstates == mc->nextstates);
  assert (BTOR_COUNT_STACK (f->next) == mc->latches->count);
}

static void
initialize_constraints_of_frame (BtorMC *mc, BtorNodeMap *map, BtorMcFrame *f)
{
  BtorNode *src, *dst, *constraint;
  int i;

  assert (mc);
  assert (map);
  assert (f);

  btor_msg_mc (mc,
               2,
               "initializing %d environment constraints of frame %d",
               (int) BTOR_COUNT_STACK (mc->constraints),
               f->time);

  constraint = 0;

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    src = BTOR_PEEK_STACK (mc->constraints, i);
    assert (src);
    dst = btor_non_recursive_substitute_node (mc->forward, map, src);
    if (constraint)
    {
      BtorNode *tmp = btor_and_exp (mc->forward, constraint, dst);
      btor_release_exp (mc->forward, constraint);
      constraint = tmp;
    }
    else
      constraint = btor_copy_exp (mc->forward, dst);
  }

  if (constraint)
  {
    btor_assert_exp (mc->forward, constraint);
    btor_release_exp (mc->forward, constraint);
  }
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
    dst = btor_non_recursive_substitute_node (mc->forward, map, src);
    dst = btor_copy_exp (mc->forward, dst);
    BTOR_PUSH_STACK (mc->btor->mm, f->bad, dst);
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

  res = btor_new_node_map (mc->forward);

  btor_msg_mc (mc, 2, "mapping inputs and latchs of frame %d", f->time);

  for (b = mc->inputs->first, i = 0; b; b = b->next, i++)
  {
    src = b->key;
    dst = BTOR_PEEK_STACK (f->inputs, i);
    btor_map_node (res, src, dst);
  }

  for (b = mc->latches->first, i = 0; b; b = b->next, i++)
  {
    src = b->key;
    dst = BTOR_PEEK_STACK (f->latches, i);
    btor_map_node (res, src, dst);
  }

  assert (res->table->count == mc->inputs->count + mc->latches->count);

  return res;
}

static void
initialize_new_forward_frame (BtorMC *mc)
{
  BtorMcFrame frame, *f;
  BtorNodeMap *map;
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
    btor_msg_mc (mc, 1, "new forward manager");
    mc->forward = btor_new_btor ();
    btor_enable_inc_usage (mc->forward);
    if (mc->trace_enabled) btor_enable_model_gen (mc->forward);
    if (mc->verbosity) btor_set_verbosity_btor (mc->forward, mc->verbosity);
  }

  initialize_inputs_of_frame (mc, f);
  initialize_latches_of_frame (mc, f);

  map = map_inputs_and_latches_of_frame (mc, f);

  initialize_next_state_functions_of_frame (mc, map, f);
  initialize_constraints_of_frame (mc, map, f);
  initialize_bad_state_properties_of_frame (mc, map, f);

  btor_delete_node_map (map);

  assert (old_mc_btor_num_nodes == mc->btor->nodes_unique_table.num_elements);

  btor_msg_mc (mc, 1, "initialized forward frame at bound k = %d", time);
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
	  a = btor_bv_assignment_exp (f->btor, node);
	  if (node->symbol)
	    symbol = node->symbol;
	  else
	    {
	      sprintf (buffer, "input%d@%d", j, i);
	      symbol = buffer;
	    }
	  printf ("%s = %s\n", symbol, a);
	  btor_free_bv_assignment_exp (f->btor, a);
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
    btor_assume_exp (mc->forward, bad);
    res = btor_sat_btor (mc->forward);
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
boolector_bmc (BtorMC *mc, int mink, int maxk)
{
  int k;

  BTOR_ABORT_ARG_NULL_BOOLECTOR (mc);

  btor_mc_release_assignment (mc);

  btor_msg_mc (
      mc,
      1,
      "calling BMC on %d properties from bound %d up-to maximum bound k = %d",
      (int) BTOR_COUNT_STACK (mc->bad),
      mink,
      maxk);

  btor_msg_mc (
      mc, 1, "trace generation %s", mc->trace_enabled ? "enabled" : "disabled");

  mc->state = BTOR_NO_MC_STATE;

  while ((k = BTOR_COUNT_STACK (mc->frames)) <= maxk)
  {
    initialize_new_forward_frame (mc);
    if (k >= mink && check_last_forward_frame (mc))
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

static BtorNodeMap *
btor_get_mc_forward2const (BtorMC *mc)
{
  if (!mc->forward2const) mc->forward2const = btor_new_node_map (mc->btor);
  return mc->forward2const;
}

static BtorNodeMap *
btor_get_mc_model2const_map (BtorMC *mc, BtorMcFrame *frame)
{
  if (!frame->model2const) frame->model2const = btor_new_node_map (mc->btor);
  return frame->model2const;
}

static void
btor_zero_normalize_assignment (char *assignment)
{
  char *p;
  for (p = assignment; *p; p++)
    if (*p == 'x') *p = '0';
}

static BtorNode *
btor_mc_forward2const_mapper (Btor *btor, void *state, BtorNode *node)
{
  BtorMC *mc = state;
  char *assignment;
  BtorNode *res;

  assert (!BTOR_IS_INVERTED_NODE (node));

  if (!BTOR_IS_BV_VAR_NODE (node)) return 0;

  assert (mc);
  assert (mc->btor == btor);
  assert (mc->forward == node->btor);
  (void) btor;

  res = 0;

  assignment = btor_bv_assignment_exp (mc->forward, node);
  btor_zero_normalize_assignment (assignment);
  res = btor_const_exp (mc->btor, assignment);
  btor_free_bv_assignment_exp (mc->forward, assignment);

  return res;
}

static BtorNode *
btor_mc_forward2const (BtorMC *mc, BtorNode *node)
{
  BtorNodeMap *map;
  assert (BTOR_REAL_ADDR_NODE (node)->btor == mc->forward);
  map = btor_get_mc_forward2const (mc);
  return btor_non_recursive_extended_substitute_node (
      mc->btor, map, mc, btor_mc_forward2const_mapper, btor_release_exp, node);
}

typedef struct BtorMcModel2ConstMapper BtorMcModel2ConstMapper;

struct BtorMcModel2ConstMapper
{
  int time;
  BtorMC *mc;
};

static BtorNode *
btor_mc_model2const_mapper (Btor *btor, void *state, BtorNode *node)
{
  BtorMcModel2ConstMapper *mapper;
  BtorNode *node_at_time, *res;
  BtorPtrHashBucket *bucket;
  BtorMcFrame *frame;
  BtorMcInput *input;
  BtorMcLatch *latch;
  const char *sym;
  BtorMC *mc;
  char *bits;
  int time;

  assert (!BTOR_IS_INVERTED_NODE (node));

  if (!BTOR_IS_BV_VAR_NODE (node)) return 0;

  mapper = state;
  assert (mapper);
  mc = mapper->mc;
  assert (mc);
  assert (mc->btor == btor);
  assert (mc->btor == node->btor);
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
    bits = btor_bv_assignment_exp (mc->forward, node_at_time);
    btor_zero_normalize_assignment (bits);
    res = btor_const_exp (mc->btor, bits);
    btor_free_bv_assignment_exp (mc->btor, bits);
  }
  else
  {
    bucket = btor_find_in_ptr_hash_table (mc->latches, node);
    sym    = btor_get_symbol_exp (mc->btor, node);
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
    res = btor_copy_exp (mc->btor, res);
  }

  return res;
}

static BtorNode *
btor_mc_model2const (BtorMC *mc, BtorNode *node, int time)
{
  BtorMcModel2ConstMapper mapper;
  BtorNodeMap *map;
  BtorMcFrame *f;
  assert (BTOR_REAL_ADDR_NODE (node)->btor == mc->btor);
  assert (0 <= time && time < BTOR_COUNT_STACK (mc->frames));
  mapper.mc   = mc;
  mapper.time = time;
  f           = mc->frames.start + time;
  map         = btor_get_mc_model2const_map (mc, f);
  return btor_non_recursive_extended_substitute_node (
      mc->btor,
      map,
      &mapper,
      btor_mc_model2const_mapper,
      btor_release_exp,
      node);
}

char *
boolector_mc_assignment (BtorMC *mc, BtorNode *node, int time)
{
  BtorNode *node_at_time, *real_node, *const_node;
  char *bits_owned_by_forward, *res;
  BtorPtrHashBucket *bucket;
  BtorMcInput *input;
  BtorMcFrame *frame;

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
    bits_owned_by_forward = btor_bv_assignment_exp (mc->forward, node_at_time);
    res                   = btor_strdup (mc->btor->mm, bits_owned_by_forward);
    btor_zero_normalize_assignment (res);
    btor_free_bv_assignment_exp (mc->forward, bits_owned_by_forward);
  }
  else
  {
    const_node = btor_mc_model2const (mc, node, time);
    assert (const_node);
    real_node = BTOR_REAL_ADDR_NODE (const_node);
    assert (BTOR_IS_BV_CONST_NODE (real_node));
    assert (real_node->btor == mc->btor);
    res = btor_copy_const (mc->btor->mm, real_node->bits);
    if (BTOR_IS_INVERTED_NODE (const_node))
      btor_invert_const (mc->btor->mm, res);
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
  BtorPtrHashBucket *b;
  BtorDumpContext *bdc;
  int i;

  bdc = btor_new_dump_context (mc->btor);

  for (b = mc->inputs->first; b; b = b->next)
  {
    BtorMcInput *input = b->data.asPtr;
    assert (input);
    assert (input->node);
    btor_add_input_to_dump_context (bdc, input->node);
  }

  for (b = mc->latches->first; b; b = b->next)
  {
    BtorMcLatch *latch = b->data.asPtr;
    assert (latch);
    assert (latch->node);
    assert (BTOR_IS_REGULAR_NODE (latch->node));
    btor_add_latch_to_dump_context (bdc, latch->node);
    if (latch->init)
      btor_add_init_to_dump_context (bdc, latch->node, latch->init);
    if (latch->next)
      btor_add_next_to_dump_context (bdc, latch->node, latch->next);
  }

  for (i = 0; i < BTOR_COUNT_STACK (mc->bad); i++)
  {
    BtorNode *bad = BTOR_PEEK_STACK (mc->bad, i);
    btor_add_bad_to_dump_context (bdc, bad);
  }

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    BtorNode *constraint = BTOR_PEEK_STACK (mc->constraints, i);
    btor_add_constraint_to_dump_context (bdc, constraint);
  }

  btor_dump_btor (bdc, file);
  btor_delete_dump_context (bdc);
}
