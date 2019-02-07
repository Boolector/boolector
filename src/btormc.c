/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormc.h"

#include "boolector.h"
#include "boolectormc.h"
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

BtorMsg *boolector_get_btor_msg (Btor *btor);

/*------------------------------------------------------------------------*/

typedef struct BtorMCModel2ConstMapper BtorMCModel2ConstMapper;

struct BtorMCModel2ConstMapper
{
  int32_t time;
  BtorMC *mc;
};

/*------------------------------------------------------------------------*/

static void
init_opt (BtorMC *mc,
          BtorMCOption opt,
          bool isflag,
          char *lng,
          char *shrt,
          uint32_t val,
          uint32_t min,
          uint32_t max,
          char *desc)
{
  assert (mc);
  assert (opt >= 0 && opt < BTOR_MC_OPT_NUM_OPTS);
  assert (lng);
  assert (max <= UINT32_MAX);
  assert (min <= val);
  assert (val <= max);

  uint32_t v;
  char *valstr;

  mc->options[opt].isflag = isflag;
  mc->options[opt].lng    = lng;
  mc->options[opt].shrt   = shrt;
  mc->options[opt].val    = val;
  mc->options[opt].dflt   = val;
  mc->options[opt].min    = min;
  mc->options[opt].max    = max;
  mc->options[opt].desc   = desc;

  if ((valstr = btor_util_getenv_value (mc->mm, lng)))
  {
    v = atoi (valstr);
    if (v < min)
      v = min;
    else if (v > max)
      v = max;
    if (v == val) return;
    mc->options[opt].val = val;
  }
}

static void
init_options (BtorMC *mc)
{
  assert (mc);
  BTOR_CNEWN (mc->mm, mc->options, BTOR_MC_OPT_NUM_OPTS);
  init_opt (mc,
            BTOR_MC_OPT_BTOR_STATS,
            true,
            "btor-stats",
            0,
            0,
            0,
            1,
            "print boolector stats at each k");
  init_opt (mc,
            BTOR_MC_OPT_MIN_K,
            false,
            "bound-min",
            "kmin",
            0,
            0,
            UINT32_MAX,
            "min bound for bmc, "
            "set to > 0 to disable property checking in initial state");
  init_opt (mc,
            BTOR_MC_OPT_MAX_K,
            false,
            "bound-max",
            "kmax",
            20,
            0,
            UINT32_MAX,
            "max bound for bmc (inclusive)");
  init_opt (mc,
            BTOR_MC_OPT_VERBOSITY,
            true,
            "verbosity",
            "v",
            0,
            0,
            UINT32_MAX,
            "set verbosity");
  init_opt (mc,
            BTOR_MC_OPT_STOP_FIRST,
            true,
            "stop-first",
            0,
            1,
            0,
            1,
            "stop at first reached property");
  init_opt (mc,
            BTOR_MC_OPT_TRACE_GEN,
            true,
            "trace-gen",
            0,
            1,
            0,
            1,
            "enable/disable trace generation");
  init_opt (mc,
            BTOR_MC_OPT_TRACE_GEN_FULL,
            true,
            "trace-gen-full",
            0,
            0,
            0,
            1,
            "always print states in trace");
}

/*------------------------------------------------------------------------*/

static void
mc_release_assignments (BtorMC *mc)
{
  BtorMCFrame *f;
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

/*------------------------------------------------------------------------*/

BtorMC *
btor_mc_new (void)
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
  BTOR_INIT_STACK (mm, res->frames);
  BTOR_INIT_STACK (mm, res->bad);
  BTOR_INIT_STACK (mm, res->constraints);
  BTOR_INIT_STACK (mm, res->reached);
  init_options (res);
  return res;
}

/*------------------------------------------------------------------------*/

static void
delete_mc_input (BtorMC *mc, BtorMCInput *input)
{
  assert (mc);
  assert (input);
  boolector_release (mc->btor, input->node);
  BTOR_DELETE (mc->mm, input);
}

static void
delete_mc_state (BtorMC *mc, BtorMCstate *state)
{
  assert (mc);
  assert (state);

  Btor *btor;

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

void
btor_mc_delete (BtorMC *mc)
{
  assert (mc);

  BtorPtrHashTableIterator it;
  BtorMCFrame *f;
  Btor *btor;
  BtorMemMgr *mm;

  btor = mc->btor;
  mm   = mc->mm;

  mc_release_assignments (mc);
  BTOR_MSG (
      boolector_get_btor_msg (btor),
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
  boolector_delete (btor);
}

/*------------------------------------------------------------------------*/

void
btor_mc_set_opt (BtorMC *mc, BtorMCOption opt, uint32_t val)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  assert (val >= btor_mc_get_opt_min (mc, opt)
          && val <= btor_mc_get_opt_max (mc, opt));

  if (val && opt == BTOR_MC_OPT_TRACE_GEN)
  {
    assert (mc->state == BTOR_NO_MC_STATE);
    assert (!BTOR_COUNT_STACK (mc->frames));
  }

  mc->options[opt].val = val;

  if (opt == BTOR_MC_OPT_VERBOSITY)
    boolector_set_opt (mc->btor, BTOR_OPT_VERBOSITY, val);
}

uint32_t
btor_mc_get_opt (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].val;
}

uint32_t
btor_mc_get_opt_min (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].min;
}

uint32_t
btor_mc_get_opt_max (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].max;
}

uint32_t
btor_mc_get_opt_dflt (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].dflt;
}

const char *
btor_mc_get_opt_lng (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].lng;
}

const char *
btor_mc_get_opt_shrt (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].shrt;
}

const char *
btor_mc_get_opt_desc (BtorMC *mc, BtorMCOption opt)
{
  assert (mc);
  assert (btor_mc_is_valid_opt (mc, opt));
  return mc->options[opt].desc;
}

bool
btor_mc_is_valid_opt (BtorMC *mc, const BtorMCOption opt)
{
  assert (mc);
  (void) mc;
  return opt < BTOR_MC_OPT_NUM_OPTS;
}

/*------------------------------------------------------------------------*/

Btor *
btor_mc_get_btor (BtorMC *mc)
{
  assert (mc);
  return mc->btor;
}

/*------------------------------------------------------------------------*/

BoolectorNode *
btor_mc_input (BtorMC *mc, BoolectorSort sort, const char *symbol)
{
  assert (mc);
  assert (mc->state == BTOR_NO_MC_STATE);
  assert (sort);
  assert (boolector_is_bitvec_sort (mc->btor, sort)
          || boolector_is_array_sort (mc->btor, sort));

  BtorPtrHashBucket *bucket;
  BtorMCInput *input;
  BoolectorNode *res;
  Btor *btor;

  btor = mc->btor;
  if (boolector_is_bitvec_sort (mc->btor, sort))
    res = boolector_var (btor, sort, symbol);
  else
    res = boolector_array (btor, sort, symbol);
  BTOR_NEW (mc->mm, input);
  assert (input);
  input->id   = (int32_t) mc->inputs->count;
  input->node = res;
  bucket      = btor_hashptr_table_add (mc->inputs, boolector_copy (btor, res));
  assert (bucket);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = input;
  if (symbol)
    BTOR_MSG (boolector_get_btor_msg (btor),
              2,
              "declared input %d '%s' of width %d",
              input->id,
              symbol,
              boolector_get_width (btor, res));
  else
    BTOR_MSG (boolector_get_btor_msg (btor),
              2,
              "declared input %d of width %d",
              input->id,
              boolector_get_width (btor, res));
  return res;
}

BoolectorNode *
btor_mc_state (BtorMC *mc, BoolectorSort sort, const char *symbol)
{
  assert (mc);
  assert (mc->state == BTOR_NO_MC_STATE);
  assert (sort);
  assert (boolector_is_bitvec_sort (mc->btor, sort)
          || boolector_is_array_sort (mc->btor, sort));

  BtorPtrHashBucket *bucket;
  BtorMCstate *state;
  BoolectorNode *res;
  Btor *btor;

  btor = mc->btor;
  if (boolector_is_bitvec_sort (mc->btor, sort))
    res = boolector_var (btor, sort, symbol);
  else
    res = boolector_array (btor, sort, symbol);
  BTOR_NEW (mc->mm, state);
  assert (state);
  state->id   = (int32_t) mc->states->count;
  state->node = res;
  state->init = state->next = 0;
  bucket = btor_hashptr_table_add (mc->states, boolector_copy (btor, res));
  assert (bucket);
  assert (!bucket->data.as_ptr);
  bucket->data.as_ptr = state;
  if (symbol)
    BTOR_MSG (boolector_get_btor_msg (btor),
              2,
              "declared state %d '%s'",
              state->id,
              symbol);
  else
    BTOR_MSG (boolector_get_btor_msg (btor), 2, "declared state %d", state->id);
  return res;
}

/*------------------------------------------------------------------------*/

static BtorMCstate *
find_mc_state (BtorMC *mc, BoolectorNode *node)
{
  assert (mc);
  assert (node);

  BtorPtrHashBucket *bucket;
  BtorMCstate *res;

  bucket = btor_hashptr_table_get (mc->states, node);
  if (!bucket) return 0;
  res = bucket->data.as_ptr;
  assert (res->node == bucket->key);
  return res;
}

void
btor_mc_init (BtorMC *mc, BoolectorNode *node, BoolectorNode *init)
{
  assert (mc);
  assert (mc->state == BTOR_NO_MC_STATE);
  assert (node);

  Btor *btor;
  BtorMCstate *state;

  btor = mc->btor;

  assert (boolector_get_btor (node) == btor);
  assert (boolector_get_btor (init) == btor);
  /* Note: We allow constants to initialize arrays */
  assert (boolector_get_width (btor, node) == boolector_get_width (btor, init));
  assert (!boolector_is_array (btor, node)
          || boolector_get_sort (btor, node)
                 == boolector_get_sort (btor, init));

  state = find_mc_state (mc, node);
  assert (state);
  assert (state->node == node);
  assert (!state->init);
  state->init = boolector_copy (btor, init);
  BTOR_MSG (
      boolector_get_btor_msg (btor), 2, "adding INIT state %d", state->id);
  mc->initialized++;
}

void
btor_mc_next (BtorMC *mc, BoolectorNode *node, BoolectorNode *next)
{
  assert (mc);
  assert (mc->state == BTOR_NO_MC_STATE);

  Btor *btor;
  BtorMCstate *state;

  btor = mc->btor;

  assert (boolector_get_btor (node) == btor);
  assert (boolector_get_btor (next) == btor);
  assert (boolector_get_sort (btor, node) == boolector_get_sort (btor, next));

  state = find_mc_state (mc, node);
  assert (state);
  assert (state->node == node);
  assert (!state->next);
  state->next = boolector_copy (btor, next);
  BTOR_MSG (
      boolector_get_btor_msg (btor), 2, "adding NEXT state %d", state->id);
  mc->nextstates++;
}

/*------------------------------------------------------------------------*/

uint32_t
btor_mc_bad (BtorMC *mc, BoolectorNode *bad)
{
  assert (mc);
  assert (mc->state == BTOR_NO_MC_STATE);

  uint32_t res;
  Btor *btor;

  btor = mc->btor;

  assert (boolector_get_btor (bad) == btor);
  assert (boolector_get_width (btor, bad) == 1);
  assert (!boolector_is_array (btor, bad));

  res = BTOR_COUNT_STACK (mc->bad);
  (void) boolector_copy (btor, bad);
  BTOR_PUSH_STACK (mc->bad, bad);
  assert (res == BTOR_COUNT_STACK (mc->reached));
  BTOR_PUSH_STACK (mc->reached, -1);
  BTOR_MSG (boolector_get_btor_msg (btor), 2, "adding BAD property %d", res);
  return res;
}

uint32_t
btor_mc_constraint (BtorMC *mc, BoolectorNode *constraint)
{
  assert (mc);
  assert (mc->state == BTOR_NO_MC_STATE);

  uint32_t res;
  Btor *btor;

  btor = mc->btor;
  assert (boolector_get_btor (constraint) == btor);
  assert (!boolector_is_array (btor, constraint));
  assert (boolector_get_width (btor, constraint) == 1);

  res = BTOR_COUNT_STACK (mc->constraints);
  (void) boolector_copy (btor, constraint);
  BTOR_PUSH_STACK (mc->constraints, constraint);
  BTOR_MSG (boolector_get_btor_msg (btor),
            2,
            "adding environment CONSTRAINT %d",
            res);
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_mc_dump (BtorMC *mc, FILE *file)
{
  assert (mc);
  assert (file);

  BtorPtrHashTableIterator it;
  BtorDumpContext *bdc;
  uint32_t i;
  Btor *btor;

  btor = mc->btor;
  (void) boolector_simplify (btor);

  bdc = btor_dumpbtor_new_dump_context (btor);

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
    assert (btor_node_is_regular ((BtorNode *) state->node));
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

/*------------------------------------------------------------------------*/

static char *
timed_symbol (BtorMC *mc, char ch, BoolectorNode *node, int32_t time)
{
  assert (mc);
  assert (node);
  assert (btor_node_is_regular ((BtorNode *) node));
  assert (time >= 0);

  char *res, suffix[20];
  const char *symbol;
  uint32_t symlen, reslen;

  symbol = boolector_get_symbol (mc->btor, node);
  if (!symbol) return 0;
  sprintf (suffix, "%c%d", ch, time);
  symlen = strlen (symbol);
  reslen = symlen + strlen (suffix) + 1;
  res    = btor_mem_malloc (mc->mm, reslen);
  (void) strcpy (res, symbol);
  strcpy (res + symlen, suffix);
  return res;
}

static BoolectorNode *
new_var_or_array (BtorMC *mc, BoolectorNode *src, const char *symbol)
{
  uint32_t w;
  BoolectorNode *dst;
  BoolectorSort s, se, si;
  Btor *btor = mc->btor;
  Btor *fwd  = mc->forward;

  if (boolector_is_var (btor, src))
  {
    w   = boolector_get_width (btor, src);
    s   = boolector_bitvec_sort (fwd, w);
    dst = boolector_var (fwd, s, symbol);
    boolector_release_sort (fwd, s);
  }
  else
  {
    assert (boolector_is_array (btor, src));
    w   = boolector_get_index_width (btor, src);
    si  = boolector_bitvec_sort (fwd, w);
    w   = boolector_get_width (btor, src);
    se  = boolector_bitvec_sort (fwd, w);
    s   = boolector_array_sort (fwd, si, se);
    dst = boolector_array (fwd, s, symbol);
    boolector_release_sort (fwd, si);
    boolector_release_sort (fwd, se);
    boolector_release_sort (fwd, s);
  }
  return dst;
}

static void
initialize_inputs_of_frame (BtorMC *mc, BoolectorNodeMap *map, BtorMCFrame *f)
{
  Btor *btor;
  BoolectorNode *src, *dst;
  BtorPtrHashTableIterator it;
  char *sym;

#ifndef NDEBUG
  size_t i = 0;
  BtorMCInput *input;
#endif

  btor = mc->btor;

  BTOR_MSG (boolector_get_btor_msg (btor),
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
    assert (btor_node_is_regular ((BtorNode *) src));
#ifndef NDEBUG
    assert (input->node == src);
    assert (input->id >= 0);
    assert ((size_t) input->id == i);
#endif
    sym = timed_symbol (mc, '@', src, f->time);
    dst = new_var_or_array (mc, src, sym);
    btor_mem_freestr (mc->mm, sym);
    assert (BTOR_COUNT_STACK (f->inputs) == i++);
    BTOR_PUSH_STACK (f->inputs, dst);
    boolector_nodemap_map (map, src, dst);
  }
}

static void
initialize_states_of_frame (BtorMC *mc, BoolectorNodeMap *map, BtorMCFrame *f)
{
  Btor *btor, *fwd;
  BoolectorNode *src, *dst;
  BtorPtrHashTableIterator it;
  BtorMCstate *state;
  BtorMCFrame *p;
  char *sym;
  size_t i;

  assert (mc);
  assert (f);
  assert (f->time >= 0);

  btor = mc->btor;
  fwd  = mc->forward;

  BTOR_MSG (boolector_get_btor_msg (btor),
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
    assert (state->id >= 0);
    assert ((size_t) state->id == i);
    src = (BoolectorNode *) btor_iter_hashptr_next (&it);
    assert (src);
    assert (btor_node_is_regular ((BtorNode *) src));
    assert (state->node == src);

    if (!f->time && state->init)
    {
      dst = boolector_nodemap_substitute_node (mc->forward, map, state->init);
      dst = boolector_copy (mc->forward, dst);
      // special case: const initialization (constant array)
      if (boolector_is_array (btor, src) && boolector_is_const (btor, src))
      {
        BoolectorSort si =
            boolector_bitvec_sort (fwd, boolector_get_index_width (btor, src));
        BoolectorNode *param = boolector_param (fwd, si, 0);
        BoolectorNode *tmp   = boolector_fun (fwd, &param, 1, dst);
        // FIXME: this is a workaround to explicitly mark tmp as array
        ((BtorNode *) tmp)->is_array = 1;
        boolector_release_sort (fwd, si);
        boolector_release (fwd, dst);
        boolector_release (fwd, param);
        dst = tmp;
      }
    }
    else if (f->time > 0 && state->next)
    {
      p   = f - 1;
      dst = BTOR_PEEK_STACK (p->next, i);
      dst = boolector_copy (fwd, dst);
    }
    else
    {
      sym = timed_symbol (mc, '#', src, f->time);
      dst = new_var_or_array (mc, src, sym);
      btor_mem_freestr (mc->mm, sym);
    }
    assert (BTOR_COUNT_STACK (f->states) == i);
    BTOR_PUSH_STACK (f->states, dst);
    i += 1;
    boolector_nodemap_map (map, src, dst);
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
  int32_t nextstates;
  size_t i;
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
      dst = boolector_nodemap_substitute_node (mc->forward, map, src);
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
  BoolectorNode *src, *dst;
  uint32_t i;

  assert (mc);
  assert (map);
  assert (f);

  BTOR_MSG (boolector_get_btor_msg (mc->btor),
            2,
            "initializing %u environment constraints of frame %d",
            BTOR_COUNT_STACK (mc->constraints),
            f->time);

  for (i = 0; i < BTOR_COUNT_STACK (mc->constraints); i++)
  {
    src = BTOR_PEEK_STACK (mc->constraints, i);
    assert (src);
    dst = boolector_nodemap_substitute_node (mc->forward, map, src);
    boolector_assert (mc->forward, dst);
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
      dst = boolector_nodemap_substitute_node (mc->forward, map, src);
      dst = boolector_copy (mc->forward, dst);
    }
    else
      dst = 0;

    BTOR_PUSH_STACK (f->bad, dst);
  }
}

static void
initialize_new_forward_frame (BtorMC *mc)
{
  assert (mc);

  Btor *btor;
  BtorMCFrame frame, *f;
  BoolectorNodeMap *map;
  int32_t time;

  btor = mc->btor;

  time = BTOR_COUNT_STACK (mc->frames);
  BTOR_CLR (&frame);
  BTOR_PUSH_STACK (mc->frames, frame);
  f       = mc->frames.start + time;
  f->time = time;

  if (!mc->forward)
  {
    uint32_t v;
    BTOR_MSG (boolector_get_btor_msg (btor), 1, "new forward manager");
    mc->forward = boolector_new ();
    boolector_set_opt (mc->forward, BTOR_OPT_INCREMENTAL, 1);
    if (btor_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN))
      boolector_set_opt (mc->forward, BTOR_OPT_MODEL_GEN, 1);
    if ((v = btor_mc_get_opt (mc, BTOR_MC_OPT_VERBOSITY)))
      boolector_set_opt (mc->forward, BTOR_OPT_VERBOSITY, v);
  }

  BTOR_INIT_STACK (mc->mm, f->init);

  map = boolector_nodemap_new (mc->forward);

  initialize_inputs_of_frame (mc, map, f);
  initialize_states_of_frame (mc, map, f);
  initialize_next_state_functions_of_frame (mc, map, f);
  initialize_constraints_of_frame (mc, map, f);
  initialize_bad_state_properties_of_frame (mc, map, f);

  boolector_nodemap_delete (map);

  BTOR_MSG (boolector_get_btor_msg (btor),
            1,
            "initialized forward frame at bound k = %d",
            time);
}

static void
print_witness_at_time (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  bool is_bv;
  const char *default_sym, *sym, *value;
  char **indices = 0, **values = 0;
  uint32_t i, size, id;
  BtorPtrHashBucket *b;
  BtorMCInput *input;
  BtorMCstate *state;
  BoolectorNode *node_at_time;
  BtorMCFrame *frame;
  Btor *btor, *fwd;

  btor  = mc->btor;
  fwd   = mc->forward;
  is_bv = boolector_is_bitvec_sort (btor, boolector_get_sort (btor, node));
  frame = mc->frames.start + time;
  b     = btor_hashptr_table_get (mc->states, node);
  const bool is_state = (b != 0);
  if (b)
  {
    state        = b->data.as_ptr;
    id           = state->id;
    node_at_time = BTOR_PEEK_STACK (frame->states, id);
    default_sym  = "state";
  }
  else
  {
    b = btor_hashptr_table_get (mc->inputs, node);
    assert (b);
    input        = b->data.as_ptr;
    id           = input->id;
    node_at_time = BTOR_PEEK_STACK (frame->inputs, id);
    default_sym  = "input";
  }

  if (is_bv)
    value = boolector_bv_assignment (fwd, node_at_time);
  else
    boolector_array_assignment (fwd, node_at_time, &indices, &values, &size);

  sym = boolector_get_symbol (mc->btor, node);
  if (is_bv)
  {
    assert (value);
    printf ("%d %s", id, value);
    if (sym)
      printf (" %s", sym);
    else
      printf (" %s%d", default_sym, id);
    printf ("%c%d\n", is_state ? '#' : '@', time);
    boolector_free_bv_assignment (fwd, value);
  }
  else
  {
    for (i = 0; i < size; i++)
    {
      printf ("%d [%s] %s", id, indices[i], values[i]);
      if (sym)
        printf (" %s", sym);
      else
        printf (" %s%d", default_sym, id);
      printf ("@%d\n", time);
    }
    boolector_free_array_assignment (fwd, indices, values, size);
  }
}

static void
print_witness (BtorMC *mc, int32_t time)
{
  assert (time >= 0);

  size_t i;
  BtorMCstate *state;
  BoolectorNode *src;
  BtorPtrHashTableIterator it;
  bool full_trace;

  full_trace = btor_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN_FULL) == 1;

  printf ("sat\n");
  for (i = 0; i < BTOR_COUNT_STACK (mc->reached); i++)
  {
    if (BTOR_PEEK_STACK (mc->reached, i) == time) printf ("b%zu ", i);
  }
  printf ("\n");

  for (i = 0; i <= (size_t) time; i++)
  {
    if (i == 0 || full_trace)
    {
      printf ("#%zu\n", i);
      btor_iter_hashptr_init (&it, mc->states);
      while (btor_iter_hashptr_has_next (&it))
      {
        state = it.bucket->data.as_ptr;
        assert (state);
        src = (BoolectorNode *) btor_iter_hashptr_next (&it);
        if (!full_trace && state->init) continue;
        print_witness_at_time (mc, src, i);
      }
    }

    printf ("@%zu\n", i);
    btor_iter_hashptr_init (&it, mc->inputs);
    while (btor_iter_hashptr_has_next (&it))
    {
      src = (BoolectorNode *) btor_iter_hashptr_next (&it);
      print_witness_at_time (mc, src, i);
    }
  }
  printf (".\n");
  fflush (stdout);
}

static int32_t
check_last_forward_frame (BtorMC *mc)
{
  assert (mc);

  size_t i;
  int32_t k, res, satisfied;
  BtorMCFrame *f;
  BoolectorNode *bad;
  Btor *btor;

  btor = mc->btor;

  k = BTOR_COUNT_STACK (mc->frames) - 1;
  assert (k >= 0);
  f = mc->frames.top - 1;
  assert (f->time == k);

  BTOR_MSG (boolector_get_btor_msg (btor),
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
      BTOR_MSG (boolector_get_btor_msg (btor),
                1,
                "skipping checking bad state property %zu "
                "at bound %d reached before at %d",
                i,
                k,
                reached);
      continue;
    }
    BTOR_MSG (boolector_get_btor_msg (btor),
              1,
              "checking forward frame bad state property %zu at bound k = %d",
              i,
              k);
    boolector_assume (mc->forward, bad);
    res = boolector_sat (mc->forward);
    if (res == BOOLECTOR_SAT)
    {
      mc->state = BTOR_SAT_MC_STATE;
      BTOR_MSG (boolector_get_btor_msg (btor),
                1,
                "bad state property %zu at bound k = %d SATISFIABLE",
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
      BTOR_MSG (boolector_get_btor_msg (btor),
                1,
                "bad state property %zu at bound k = %d UNSATISFIABLE",
                i,
                k);
    }
    if (btor_mc_get_opt (mc, BTOR_MC_OPT_BTOR_STATS))
      boolector_print_stats (mc->forward);
  }

  if (satisfied && btor_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN))
    print_witness (mc, k);

  BTOR_MSG (boolector_get_btor_msg (btor),
            1,
            "found %d satisfiable bad state properties at bound k = %d",
            satisfied,
            k);

  return satisfied;
}

int32_t
btor_mc_bmc (BtorMC *mc, int32_t mink, int32_t maxk)
{
  assert (mc);

  int32_t k;
  Btor *btor;

  btor = mc->btor;

  mc_release_assignments (mc);

  BTOR_MSG (boolector_get_btor_msg (btor),
            1,
            "calling BMC on %u properties from bound %d "
            "up-to maximum bound k = %d",
            BTOR_COUNT_STACK (mc->bad),
            mink,
            maxk);

  BTOR_MSG (
      boolector_get_btor_msg (btor),
      1,
      "trace generation %s",
      btor_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN) ? "enabled" : "disabled");

  mc->state = BTOR_NO_MC_STATE;

  while ((k = BTOR_COUNT_STACK (mc->frames)) <= maxk)
  {
    if (mc->call_backs.starting_bound.fun)
    {
      mc->call_backs.starting_bound.fun (mc->call_backs.starting_bound.state,
                                         k);
    }

    initialize_new_forward_frame (mc);
    if (k < mink) continue;
    if (check_last_forward_frame (mc))
    {
      if (btor_mc_get_opt (mc, BTOR_MC_OPT_STOP_FIRST)
          || mc->num_reached == BTOR_COUNT_STACK (mc->bad) || k == maxk)
      {
        BTOR_MSG (boolector_get_btor_msg (btor),
                  2,
                  "entering SAT state at bound k=%d",
                  k);
        assert (k >= 0);
        return k;
      }
    }
  }

  BTOR_MSG (boolector_get_btor_msg (btor), 2, "entering UNSAT state");
  mc->state = BTOR_UNSAT_MC_STATE;

  return -1;
}

/*------------------------------------------------------------------------*/

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
  {
    if (*p == 'x') *p = '0';
  }
}

static BoolectorNode *
mc_model2const_mapper (Btor *btor, void *m2cmapper, BoolectorNode *node)
{
  assert (btor_node_is_regular ((BtorNode *) node));
  assert (m2cmapper);
  assert (node);

  BtorMCModel2ConstMapper *mapper;
  BoolectorNode *node_at_time, *res;
  const char *constbits;
  BtorPtrHashBucket *bucket;
  BtorMCFrame *frame;
  BtorMCInput *input;
  BtorMCstate *state;
  BtorMC *mc;
  char *bits;
  int32_t time;

  if (!boolector_is_var (btor, node)) return 0;

  mapper = m2cmapper;
  mc     = mapper->mc;
  assert (mc);
  assert (mc->btor == btor);
  assert (mc->btor == boolector_get_btor (node));
  time = mapper->time;

  assert (0 <= time && (size_t) time < BTOR_COUNT_STACK (mc->frames));
  frame = mc->frames.start + time;

  bucket = btor_hashptr_table_get (mc->inputs, node);

  if (bucket)
  {
    input = bucket->data.as_ptr;
    assert (input);
    assert (input->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->inputs, input->id);
  }
  else
  {
    bucket = btor_hashptr_table_get (mc->states, node);
    assert (bucket);
    state = bucket->data.as_ptr;
    assert (state);
    assert (state->node == node);
    node_at_time = BTOR_PEEK_STACK (frame->states, state->id);
  }
  assert (node_at_time);
  assert (boolector_get_btor (node_at_time) == mc->forward);
  constbits = boolector_bv_assignment (mc->forward, node_at_time);
  bits      = btor_mem_strdup (mc->mm, constbits);
  boolector_free_bv_assignment (mc->forward, constbits);
  zero_normalize_assignment (bits);
  res = boolector_const (btor, bits);
  btor_mem_freestr (mc->mm, bits);
  return res;
}

static BoolectorNode *
mc_model2const (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  BtorMCModel2ConstMapper mapper;
  BoolectorNodeMap *map;
  BtorMCFrame *f;
  assert (boolector_get_btor (node) == mc->btor);
  assert (0 <= time && (size_t) time < BTOR_COUNT_STACK (mc->frames));
  mapper.mc   = mc;
  mapper.time = time;
  f           = mc->frames.start + time;
  map         = get_mc_model2const_map (mc, f);
  return boolector_nodemap_extended_substitute_node (
      mc->btor, map, &mapper, mc_model2const_mapper, boolector_release, node);
}

char *
btor_mc_assignment (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  assert (mc);
  assert (mc->state == BTOR_SAT_MC_STATE);
  assert (btor_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN));
  assert (node);
  assert (BTOR_IMPORT_BOOLECTOR_NODE (node)->ext_refs);
  assert (boolector_get_btor (node) == mc->btor);
  assert (time >= 0);
  assert ((size_t) time < BTOR_COUNT_STACK (mc->frames));

  BoolectorNode *node_at_time, *const_node;
  const char *bits_owned_by_forward, *bits;
  BtorPtrHashBucket *bucket;
  BtorMCInput *input;
  BtorMCstate *state;
  BtorMCFrame *frame;
  char *res;
  Btor *btor;

  btor = mc->btor;

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
  else if ((bucket = btor_hashptr_table_get (mc->states, node)))
  {
    state = bucket->data.as_ptr;
    assert (state);
    assert (state->node == node);
    frame        = mc->frames.start + time;
    node_at_time = BTOR_PEEK_STACK (frame->states, state->id);
    assert (node_at_time);
    bits_owned_by_forward = boolector_bv_assignment (mc->forward, node_at_time);
    res                   = btor_mem_strdup (mc->mm, bits_owned_by_forward);
    boolector_free_bv_assignment (mc->forward, bits_owned_by_forward);
  }
  else
  {
    const_node = mc_model2const (mc, node, time);
    assert (const_node);
    assert (boolector_is_const (btor, const_node));
    assert (boolector_get_btor (const_node) == btor);
    bits = boolector_get_bits (btor, const_node);
    res  = btor_mem_strdup (mc->mm, bits);
    boolector_free_bits (btor, bits);
  }

  return res;
}

void
btor_mc_free_assignment (BtorMC *mc, char *assignment)
{
  assert (mc);
  assert (assignment);
  btor_mem_freestr (mc->mm, assignment);
}

/*------------------------------------------------------------------------*/

int32_t
btor_mc_reached_bad_at_bound (BtorMC *mc, int32_t badidx)
{
  assert (mc);
  assert (mc->state != BTOR_NO_MC_STATE);
  assert (!btor_mc_get_opt (mc, BTOR_MC_OPT_STOP_FIRST));
  assert (badidx >= 0);
  assert ((size_t) badidx < BTOR_COUNT_STACK (mc->bad));
  return BTOR_PEEK_STACK (mc->reached, badidx);
}

void
btor_mc_set_reached_at_bound_call_back (BtorMC *mc,
                                        void *state,
                                        BtorMCReachedAtBound fun)
{
  assert (mc);
  assert (state);
  assert (fun);
  mc->call_backs.reached_at_bound.state = state;
  mc->call_backs.reached_at_bound.fun   = fun;
}

/*------------------------------------------------------------------------*/

void
btor_mc_set_starting_bound_call_back (BtorMC *mc,
                                      void *state,
                                      BtorMCStartingBound fun)
{
  assert (mc);
  assert (state);
  assert (fun);
  mc->call_backs.starting_bound.state = state;
  mc->call_backs.starting_bound.fun   = fun;
}

/*------------------------------------------------------------------------*/
