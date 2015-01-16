/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
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
#include "btorhash.h"
#include "btoriter.h"
#include "btorutil.h"

static void
compute_score_node_min_dep (Btor *btor, BtorPtrHashTable *score, BtorNode *cur)
{
  int i, min_depth;
  BtorNode *e;
  BtorPtrHashBucket *b;

  min_depth = -1;
  for (i = 0; i < cur->arity; i++)
  {
    e = BTOR_REAL_ADDR_NODE (cur->e[i]);
    b = btor_find_in_ptr_hash_table (score, e);
    assert (b);
    if (min_depth == -1 || b->data.asInt < min_depth) min_depth = b->data.asInt;
  }

  assert (min_depth >= 0);
  assert (!btor_find_in_ptr_hash_table (score, cur));
  btor_insert_in_ptr_hash_table (score, btor_copy_exp (btor, cur))->data.asInt =
      min_depth + 1;
}

// TODO get rid of score_depth
/* heuristic: minimum depth to the inputs
 *            (considering the whole formula or the bv skeleton, only) */
static void
compute_scores_aux_min_dep (Btor *btor, BtorHashTableIterator *it)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  int i, h;
  BtorNodePtrStack stack, unmark_stack;
  BtorNode *cur;
  BtorPtrHashTable *score;
  BtorPtrHashBucket *b;

  if (!(h = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC))) return;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  if (!btor->score_depth)
    btor->score_depth =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  score = btor->score_depth;

  while (has_next_node_hash_table_iterator (it))
  {
    cur = next_node_hash_table_iterator (it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark == 2 || btor_find_in_ptr_hash_table (score, cur))
        continue;

      if (cur->aux_mark == 0)
      {
        cur->aux_mark = 1;
        BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);
        BTOR_PUSH_STACK (btor->mm, stack, cur);

        if (cur->arity == 0)
        {
          assert (!btor_find_in_ptr_hash_table (score, cur));
          b = btor_insert_in_ptr_hash_table (score, btor_copy_exp (btor, cur));
          b->data.asInt = 1;
          continue;
        }

        for (i = 0; i < cur->arity; i++)
          BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
      }
      else
      {
        assert (cur->aux_mark == 1);
        assert (cur->arity > 0);
        assert (h != BTOR_JUST_HEUR_BRANCH_MIN_DEP || !BTOR_IS_UF_NODE (cur));
        cur->aux_mark = 2;

        compute_score_node_min_dep (btor, score, cur);
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
compute_scores_aux_min_app (Btor *btor, BtorHashTableIterator *it)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));
  assert (it);

  double delta;
  int i, j, k, h;
  BtorNode *cur, *e;
  BtorNodePtrStack stack, unmark_stack, score;
  BtorHashTableIterator hit;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *marked, *in, *t, *min_t;

  if (!(h = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC))) return;

  if (!btor->score)
    btor->score = btor_new_ptr_hash_table (btor->mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  marked = btor_new_ptr_hash_table (btor->mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (score);

  /* Collect all children of AND nodes (the only nodes we actually later
   * need the score for). Note: we need 2 passes, first to mark all children
   * of AND nodes, second to determine their post-order (dfs). This can NOT
   * be done within one pass! */

  while (has_next_node_hash_table_iterator (it))
  {
    cur = next_node_hash_table_iterator (it);
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
            && !btor_find_in_ptr_hash_table (btor->score, e))
        {
          btor_insert_in_ptr_hash_table (btor->score, btor_copy_exp (btor, e));
          /* push onto working stack */
          BTOR_PUSH_STACK (btor->mm, score, e);
        }
        BTOR_PUSH_STACK (btor->mm, stack, e);
      }
    }
  }
  qsort (score.start,
         BTOR_COUNT_STACK (score),
         sizeof (BtorNode *),
         btor_cmp_exp_by_id_qsort_asc);

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  for (k = 0; k < BTOR_COUNT_STACK (score); k++)
  {
    cur = BTOR_PEEK_STACK (score, k);
    b   = btor_find_in_ptr_hash_table (btor->score, cur);
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
        b = btor_find_in_ptr_hash_table (btor->score, e);
        assert (b);
        t = (BtorPtrHashTable *) b->data.asPtr;
        assert (t);
        if (!min_t || t->count < min_t->count) min_t = t;
      }
      assert (min_t);
      init_node_hash_table_iterator (&hit, min_t);
      while (has_next_node_hash_table_iterator (&hit))
      {
        e = next_node_hash_table_iterator (&hit);
        assert (!btor_find_in_ptr_hash_table (in, e));
        btor_insert_in_ptr_hash_table (in, btor_copy_exp (btor, e));
      }
    }
    else
    {
      for (i = 0; i < cur->arity; i++)
      {
        e = BTOR_REAL_ADDR_NODE (cur->e[i]);
        b = btor_find_in_ptr_hash_table (btor->score, e);
        if (b && (t = b->data.asPtr))
        {
          /* merge tables */
          delta = btor_time_stamp ();
          init_node_hash_table_iterator (&hit, t);
          while (has_next_node_hash_table_iterator (&hit))
          {
            e = next_node_hash_table_iterator (&hit);
            if (!btor_find_in_ptr_hash_table (in, e))
              btor_insert_in_ptr_hash_table (in, btor_copy_exp (btor, e));
          }
          btor->time.search_init_apps_compute_scores_merge_applies +=
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
  BTOR_RELEASE_STACK (btor->mm, score);

  btor_delete_ptr_hash_table (marked);
}

static void
compute_scores_aux (Btor *btor, BtorHashTableIterator *it)
{
  int h;

  if (!(h = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC))) return;

  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
    compute_scores_aux_min_app (btor, it);
  else if (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
    compute_scores_aux_min_dep (btor, it);
}

void
btor_compute_scores (Btor *btor)
{
  assert (btor);

  BtorHashTableIterator it;

  init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->assumptions);
  compute_scores_aux (btor, &it);
}

void
btor_compute_scores_dual_prop (Btor *btor)
{
  assert (btor);
  assert (check_id_table_aux_mark_unset_dbg (btor));

  int i, h;
  BtorNode *cur;
  BtorNodePtrStack stack, unmark_stack;
  BtorPtrHashTable *applies, *t;
  BtorHashTableIterator it, iit;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  applies = btor_new_ptr_hash_table (btor->mm,
                                     (BtorHashPtr) btor_hash_exp_by_id,
                                     (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect applies in bv skeleton */
  init_node_hash_table_iterator (&it, btor->synthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->assumptions);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (btor->mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark) continue;

      cur->aux_mark = 1;
      BTOR_PUSH_STACK (btor->mm, unmark_stack, cur);

      if (BTOR_IS_APPLY_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur))
      {
        assert (!btor_find_in_ptr_hash_table (applies, cur));
        btor_insert_in_ptr_hash_table (applies, cur);
        continue;
      }

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (btor->mm, stack, cur->e[i]);
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->aux_mark = 0;

  /* compute scores from applies downwards */
  init_node_hash_table_iterator (&it, applies);
  compute_scores_aux (btor, &it);

  /* cleanup */
  h = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC);
  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
  {
    init_node_hash_table_iterator (&it, btor->score);
    while (has_next_hash_table_iterator (&it))
    {
      t   = (BtorPtrHashTable *) it.bucket->data.asPtr;
      cur = next_node_hash_table_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      if (!BTOR_IS_BV_VAR_NODE (cur) && !BTOR_IS_APPLY_NODE (cur))
      {
        btor_release_exp (btor, cur);
        init_node_hash_table_iterator (&iit, t);
        while (has_next_node_hash_table_iterator (&iit))
          btor_release_exp (btor, next_node_hash_table_iterator (&iit));
        btor_delete_ptr_hash_table (t);
        btor_remove_from_ptr_hash_table (btor->score, cur, 0, 0);
      }
    }
  }
  btor_delete_ptr_hash_table (applies);
  BTOR_RELEASE_STACK (btor->mm, stack);
  BTOR_RELEASE_STACK (btor->mm, unmark_stack);
}

int
btor_compare_scores (Btor *btor, BtorNode *a, BtorNode *b)
{
  assert (btor);
  assert (a);
  assert (b);

  int h, sa, sb;
  BtorPtrHashBucket *bucket;

  h  = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC);
  a  = BTOR_REAL_ADDR_NODE (a);
  b  = BTOR_REAL_ADDR_NODE (b);
  sa = sb = 0;

  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
  {
    if (!btor->score) return 0;

    bucket = btor_find_in_ptr_hash_table (btor->score, a);
    assert (bucket);
    sa = ((BtorPtrHashTable *) bucket->data.asPtr)->count;

    bucket = btor_find_in_ptr_hash_table (btor->score, b);
    assert (bucket);
    sb = ((BtorPtrHashTable *) bucket->data.asPtr)->count;
  }
  else if (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
  {
    if (!btor->score_depth) return 0;

    bucket = btor_find_in_ptr_hash_table (btor->score_depth, a);
    assert (bucket);
    sa = bucket->data.asInt;

    bucket = btor_find_in_ptr_hash_table (btor->score_depth, b);
    assert (bucket);
    sb = bucket->data.asInt;
  }

  return sa < sb;
}

int
btor_compare_scores_qsort (const void *p1, const void *p2)
{
  int h, sa, sb;
  Btor *btor;
  BtorNode *a, *b;
  BtorPtrHashBucket *bucket;

  sa = sb = 0;
  a       = *((BtorNode **) p1);
  b       = *((BtorNode **) p2);
  assert (a->btor == b->btor);
  btor = a->btor;

  h = btor_get_opt_val (btor, BTOR_OPT_JUST_HEURISTIC);

  if (h == BTOR_JUST_HEUR_BRANCH_MIN_APP)
  {
    if (!btor->score) return 0;

    bucket = btor_find_in_ptr_hash_table (btor->score, a);
    assert (bucket);
    sa = ((BtorPtrHashTable *) bucket->data.asPtr)->count;

    bucket = btor_find_in_ptr_hash_table (btor->score, b);
    assert (bucket);
    sb = ((BtorPtrHashTable *) bucket->data.asPtr)->count;
  }
  else if (h == BTOR_JUST_HEUR_BRANCH_MIN_DEP)
  {
    if (!btor->score_depth) return 0;

    bucket = btor_find_in_ptr_hash_table (btor->score_depth, a);
    assert (bucket);
    sa = bucket->data.asInt;

    bucket = btor_find_in_ptr_hash_table (btor->score_depth, b);
    assert (bucket);
    sb = bucket->data.asInt;
  }

  if (sa < sb) return 1;
  if (sa > sb) return -1;
  return 0;
}
