/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
#include "utils/btorhash.h"
#include "utils/btoriter.h"
#include "utils/btorutil.h"

/* heuristic: minimum depth to the inputs
 *            (considering the whole formula or the bv skeleton, only) */
static void
compute_scores_aux_min_dep (Btor *btor, BtorNodePtrStack *nodes)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (nodes);

  int i, j, min_depth;
  BtorCoreSolver *slv;
  BtorNodePtrStack stack, unmark_stack;
  BtorNode *cur, *e;
  BtorPtrHashTable *score;
  BtorPtrHashBucket *b;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  slv = BTOR_CORE_SOLVER (btor);

  if (!slv->score)
    slv->score = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);

  score = slv->score;

  for (j = 0; j < BTOR_COUNT_STACK (*nodes); j++)
  {
    cur = BTOR_PEEK_STACK (*nodes, j);
    BTOR_PUSH_STACK (btor->mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark == 2) continue;

      if (cur->aux_mark == 0)
      {
        cur->aux_mark = 1;
        BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);
        BTOR_PUSH_STACK (btor->mm, stack, cur);

        if (cur->arity == 0)
        {
          if (!(b = btor_find_in_ptr_hash_table (score, cur)))
            b = btor_insert_in_ptr_hash_table (score,
                                               btor_copy_exp (btor, cur));
          b->data.asInt = 1;
          cur->aux_mark = 2;
          continue;
        }

        for (i = 0; i < cur->arity; i++)
          BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
      }
      else
      {
        assert (cur->aux_mark == 1);
        assert (cur->arity > 0);
        assert (!BTOR_IS_UF_NODE (cur));
        cur->aux_mark = 2;

        min_depth = -1;
        for (i = 0; i < cur->arity; i++)
        {
          e = BTOR_REAL_ADDR_NODE (cur->e[i]);
          b = btor_find_in_ptr_hash_table (score, e);
          assert (b);
          if (min_depth == -1 || b->data.asInt < min_depth)
            min_depth = b->data.asInt;
        }
        assert (min_depth >= 0);
        if (!(b = btor_find_in_ptr_hash_table (score, cur)))
          b = btor_insert_in_ptr_hash_table (score, btor_copy_exp (btor, cur));
        b->data.asInt = min_depth + 1;
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

/* heuristic: minimum number of unique applies on a path to the inputs
 *            (considering the whole formula, or the bv skeleton only) */
static void
compute_scores_aux_min_app (Btor *btor, BtorNodePtrStack *nodes)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (nodes);

  double delta;
  int i, j, k;
  BtorCoreSolver *slv;
  BtorNode *cur, *e;
  BtorNodePtrStack stack, unmark_stack;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *in, *t, *min_t;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  slv = BTOR_CORE_SOLVER (btor);

  qsort (nodes->start,
         BTOR_COUNT_STACK (*nodes),
         sizeof (BtorNode *),
         btor_cmp_exp_by_id_qsort_asc);

  /* compute score */
  for (k = 0; k < BTOR_COUNT_STACK (*nodes); k++)
  {
    cur = BTOR_PEEK_STACK (*nodes, k);
    b   = btor_find_in_ptr_hash_table (slv->score, cur);
    assert (b);
    assert (!b->data.asPtr);
    b->data.asPtr =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    in = b->data.asPtr;

    if (!cur->parameterized && BTOR_IS_AND_NODE (cur))
    {
      /* choose min path */
      min_t = 0;
      for (i = 0; i < cur->arity; i++)
      {
        e = BTOR_REAL_ADDR_NODE (cur->e[i]);
        b = btor_find_in_ptr_hash_table (slv->score, e);
        assert (b);
        t = (BtorPtrHashTable *) b->data.asPtr;
        assert (t);
        if (!min_t || t->count < min_t->count) min_t = t;
      }
      assert (min_t);
      btor_init_node_hash_table_iterator (&it, min_t);
      while (btor_has_next_node_hash_table_iterator (&it))
      {
        e = btor_next_node_hash_table_iterator (&it);
        assert (!btor_find_in_ptr_hash_table (in, e));
        btor_insert_in_ptr_hash_table (in, btor_copy_exp (btor, e));
      }
    }
    else
    {
      for (i = 0; i < cur->arity; i++)
      {
        e = BTOR_REAL_ADDR_NODE (cur->e[i]);
        b = btor_find_in_ptr_hash_table (slv->score, e);
        if (b && (t = b->data.asPtr))
        {
          /* merge tables */
          delta = btor_time_stamp ();
          btor_init_node_hash_table_iterator (&it, t);
          while (btor_has_next_node_hash_table_iterator (&it))
          {
            e = btor_next_node_hash_table_iterator (&it);
            if (!btor_find_in_ptr_hash_table (in, e))
              btor_insert_in_ptr_hash_table (in, btor_copy_exp (btor, e));
          }
          slv->time.search_init_apps_compute_scores_merge_applies +=
              btor_time_stamp () - delta;
        }
        else
        {
          /* search unique applies */
          BTOR_PUSH_STACK (btor->mm, stack, e);
          while (!BTOR_EMPTY_STACK (stack))
          {
            e = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
            if (e->aux_mark) continue;
            e->aux_mark = 1;
            BTOR_PUSH_STACK (btor->mm, unmark_stack, e);
            if (!e->parameterized && BTOR_IS_APPLY_NODE (e)
                && !btor_find_in_ptr_hash_table (in, e))
              btor_insert_in_ptr_hash_table (in, btor_copy_exp (btor, e));
            for (j = 0; j < e->arity; j++)
              BTOR_PUSH_STACK (btor->mm, stack, e->e[j]);
          }
          while (!BTOR_EMPTY_STACK (unmark_stack))
            BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
        }
      }
    }
  }

  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

static void
compute_scores_aux (Btor *btor, BtorNodePtrStack *nodes)
{
  int h;

  h = btor->options.just_heuristic.val;
  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
    compute_scores_aux_min_app (btor, nodes);
  else if (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
    compute_scores_aux_min_dep (btor, nodes);
}

void
btor_compute_scores (Btor *btor)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  int i;
  double start;
  BtorCoreSolver *slv;
  BtorNode *cur, *e;
  BtorHashTableIterator it;
  BtorNodePtrStack stack, unmark_stack, nodes;

  /* Collect all nodes we actually need the score for.
   * If just is enabled, we only need the children of AND nodes. If dual prop
   * is enabled, we only need APPLY nodes (BV var nodes always have score 0 and
   * are treated as such in compare_scores).
   * -> see btor_compute_scores_dual_prop */

  start = btor_time_stamp ();
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (nodes);

  slv = BTOR_CORE_SOLVER (btor);

  if (!slv->score)
    slv->score = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);

  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
      if (cur->aux_mark) continue;
      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);
      for (i = 0; i < cur->arity; i++)
      {
        e = BTOR_REAL_ADDR_NODE (cur->e[i]);
        if (!cur->parameterized && BTOR_IS_AND_NODE (cur)
            && !btor_find_in_ptr_hash_table (slv->score, e))
        {
          btor_insert_in_ptr_hash_table (slv->score, btor_copy_exp (btor, e));
          /* push onto working stack */
          BTOR_PUSH_STACK (btor->mm, nodes, e);
        }
        BTOR_PUSH_STACK (btor->mm, stack, e);
      }
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);

  compute_scores_aux (btor, &nodes);

  BTOR_RELEASE_STACK (btor->mm, nodes);

  slv->time.search_init_apps_compute_scores += btor_time_stamp () - start;
}

void
btor_compute_scores_dual_prop (Btor *btor)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  int i;
  double start;
  BtorCoreSolver *slv;
  BtorNode *cur;
  BtorNodePtrStack stack, unmark_stack, nodes;
  BtorHashTableIterator it;

  start = btor_time_stamp ();

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  slv = BTOR_CORE_SOLVER (btor);

  /* Collect all nodes we actually need the score for.
   * If just is enabled, we only need the children of AND nodes. If dual prop
   * is enabled, we only need APPLY nodes (BV var nodes always have score 0 and
   * are treated as such in compare_scores).
   * -> see btor_compute_scores */

  BTOR_INIT_STACK (nodes);

  if (!slv->score)
    slv->score = btor_new_ptr_hash_table (btor->mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect applies in bv skeleton */
  btor_init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->assumptions);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
      if (cur->aux_mark) continue;
      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_FEQ_NODE (cur)) continue;

      if (BTOR_IS_APPLY_NODE (cur))
      {
        assert (!cur->parameterized);
        if (!btor_find_in_ptr_hash_table (slv->score, cur))
        {
          btor_insert_in_ptr_hash_table (slv->score, btor_copy_exp (btor, cur));
          /* push onto working stack */
          BTOR_PUSH_STACK (btor->mm, nodes, cur);
        }
        continue;
      }

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;
  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);

  /* compute scores from applies downwards */
  compute_scores_aux (btor, &nodes);

  BTOR_RELEASE_STACK (btor->mm, nodes);

  slv->time.search_init_apps_compute_scores += btor_time_stamp () - start;
}

int
btor_compare_scores (Btor *btor, BtorNode *a, BtorNode *b)
{
  assert (btor);
  assert (a);
  assert (b);

  int h, sa, sb;
  BtorCoreSolver *slv;
  BtorPtrHashBucket *bucket;

  slv = BTOR_CORE_SOLVER (btor);

  h  = btor->options.just_heuristic.val;
  a  = BTOR_REAL_ADDR_NODE (a);
  b  = BTOR_REAL_ADDR_NODE (b);
  sa = sb = 0;

  if (!slv->score) return 0;

  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
  {
    if (BTOR_IS_BV_VAR_NODE (a))
      sa = 0;
    else
    {
      bucket = btor_find_in_ptr_hash_table (slv->score, a);
      assert (bucket);
      sa = ((BtorPtrHashTable *) bucket->data.asPtr)->count;
    }

    if (BTOR_IS_BV_VAR_NODE (b))
      sb = 0;
    else
    {
      bucket = btor_find_in_ptr_hash_table (slv->score, b);
      assert (bucket);
      sb = ((BtorPtrHashTable *) bucket->data.asPtr)->count;
    }
  }
  else if (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
  {
    bucket = btor_find_in_ptr_hash_table (slv->score, a);
    assert (bucket);
    sa = bucket->data.asInt;

    bucket = btor_find_in_ptr_hash_table (slv->score, b);
    assert (bucket);
    sb = bucket->data.asInt;
  }

  return sa < sb;
}

int
btor_compare_scores_qsort (const void *p1, const void *p2)
{
  int h, sa, sb;
  BtorCoreSolver *slv;
  Btor *btor;
  BtorNode *a, *b;
  BtorPtrHashBucket *bucket;

  sa = sb = 0;
  a       = *((BtorNode **) p1);
  b       = *((BtorNode **) p2);
  assert (a->btor == b->btor);
  btor = a->btor;
  slv  = BTOR_CORE_SOLVER (btor);

  h = btor->options.just_heuristic.val;

  if (!slv->score) return 0;

  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
  {
    if (BTOR_IS_BV_VAR_NODE (a) || BTOR_IS_FEQ_NODE (a))
      sa = 0;
    else
    {
      bucket = btor_find_in_ptr_hash_table (slv->score, a);
      assert (bucket);
      assert (bucket->data.asPtr);
      sa = ((BtorPtrHashTable *) bucket->data.asPtr)->count;
    }

    if (BTOR_IS_BV_VAR_NODE (b) || BTOR_IS_FEQ_NODE (b))
      sb = 0;
    else
    {
      bucket = btor_find_in_ptr_hash_table (slv->score, b);
      assert (bucket);
      assert (bucket->data.asPtr);
      sb = ((BtorPtrHashTable *) bucket->data.asPtr)->count;
    }
  }
  else if (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
  {
    bucket = btor_find_in_ptr_hash_table (slv->score, a);
    assert (bucket);
    sa = bucket->data.asInt;

    bucket = btor_find_in_ptr_hash_table (slv->score, b);
    assert (bucket);
    sb = bucket->data.asInt;
  }

  if (sa < sb) return 1;
  if (sa > sb) return -1;
  return 0;
}
