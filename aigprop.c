/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "aigprop.h"
#include "btorclone.h"
#include "utils/btorhash.h"
#include "utils/btorinthash.h"
#include "utils/btoriter.h"
#include "utils/btorstack.h"

static int
get_assignment_aig (BtorPtrHashTable *model, BtorAIG *aig)
{
  assert (model);
  assert (aig);
  assert (btor_find_in_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig)));

  int res;

  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;
  if (BTOR_REAL_ADDR_AIG (aig)->cnf_id == 0) return 0;

  res =
      btor_find_in_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig))->data.asInt;
  if (BTOR_IS_INVERTED_AIG (aig)) res *= -1;
  return res;
}

static void
recursively_compute_assignment (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (aprop->model);
  assert (aig);

  BtorAIG *cur, *real_cur, *left, *right;
  BtorAIGPtrStack stack;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  mm = aprop->amgr->mm;

  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (mm);

  if (!BTOR_IS_CONST_AIG (aig)) BTOR_PUSH_STACK (mm, stack, aig);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);
    assert (!BTOR_IS_CONST_AIG (real_cur));
    if (btor_find_in_ptr_hash_table (aprop->model, real_cur)) continue;

    if (BTOR_IS_VAR_AIG (real_cur))
    {
      /* initialize with false */
      btor_insert_in_ptr_hash_table (aprop->model,
                                     btor_copy_aig (aprop->amgr, real_cur))
          ->data.asInt = -1;
    }
    else
    {
      assert (BTOR_IS_AND_AIG (real_cur));
      left  = BTOR_LEFT_CHILD_AIG (aprop->amgr, real_cur);
      right = BTOR_RIGHT_CHILD_AIG (aprop->amgr, real_cur);

      if (!btor_contains_int_hash_table (cache, real_cur->id))
      {
        assert (BTOR_IS_CONST_AIG (left)
                || !btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (left)->id));
        assert (BTOR_IS_CONST_AIG (right)
                || !btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (right)->id));

        BTOR_PUSH_STACK (mm, stack, cur);
        if (!BTOR_IS_CONST_AIG (left)) BTOR_PUSH_STACK (mm, stack, left);
        if (!BTOR_IS_CONST_AIG (right)) BTOR_PUSH_STACK (mm, stack, right);
        btor_add_int_hash_table (cache, real_cur->id);
      }
      else
      {
        if (get_assignment_aig (aprop->model, left) < 0
            || get_assignment_aig (aprop->model, right) < 0)
          btor_insert_in_ptr_hash_table (aprop->model,
                                         btor_copy_aig (aprop->amgr, real_cur))
              ->data.asInt = -1;
        else
          btor_insert_in_ptr_hash_table (aprop->model,
                                         btor_copy_aig (aprop->amgr, real_cur))
              ->data.asInt = 1;
      }
    }
  }

  btor_free_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, stack);
}

void
aigprop_generate_model (AIGProp *aprop)
{
  assert (aprop);
  assert (aprop->roots);
  assert (aprop->model);

  BtorHashTableIterator it;

  btor_init_hash_table_iterator (&it, aprop->roots);
  while (btor_has_next_hash_table_iterator (&it))
    recursively_compute_assignment (aprop, btor_next_hash_table_iterator (&it));
}

static void
move (AIGProp *aprop)
{
  assert (aprop);
  assert (aprop->roots);
  assert (aprop->model);

  // TODO
}

/* score
 *
 * score (aigvar, A) = A (aigvar)
 * score (BTOR_CONST_AIG_TRUE, A) = 1.0
 * score (BTOR_CONST_AIG_FALSE, A) = 0.0
 * score (aig0 /\ aig1, A) = 1/2 * (score (aig0) + score (aig1), A)
 * score (-(-aig0 /\ -aig1), A) = max (score (-aig0), score (-aig1), A)
 */
static double
compute_sls_score_aig (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (aig);

  double res, s0, s1;
  BtorPtrHashBucket *b;
  BtorAIGPtrStack stack;
  BtorIntHashTable *cache;
  BtorAIG *cur, *real_cur, *left, *right;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int a;
#endif

  mm = aprop->amgr->mm;

  res = 0.0;

  if ((b = btor_find_in_ptr_hash_table (aprop->score, aig)))
    return b->data.asDbl;

  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (mm);

  BTOR_PUSH_STACK (mm, stack, aig);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (BTOR_IS_CONST_AIG (real_cur)) continue;
    if (btor_find_in_ptr_hash_table (aprop->score, cur)) continue;

    if (!btor_contains_int_hash_table (cache, real_cur->id))
    {
      btor_add_int_hash_table (cache, real_cur->id);
      assert (BTOR_IS_VAR_AIG (real_cur) || BTOR_IS_AND_AIG (real_cur));
      BTOR_PUSH_STACK (mm, stack, cur);
      if (BTOR_IS_AND_AIG (real_cur))
      {
        left  = BTOR_LEFT_CHILD_AIG (aprop->amgr, real_cur);
        right = BTOR_RIGHT_CHILD_AIG (aprop->amgr, real_cur);
        assert (BTOR_IS_CONST_AIG (left)
                || !btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (left)->id));
        assert (BTOR_IS_CONST_AIG (right)
                || !btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (right)->id));
        if (!BTOR_IS_CONST_AIG (left)) BTOR_PUSH_STACK (mm, stack, left);
        if (!BTOR_IS_CONST_AIG (right)) BTOR_PUSH_STACK (mm, stack, right);
      }
    }
    else
    {
#ifndef NDEBUG
      a = get_assignment_aig (aprop->model, cur);
      assert (a);
      printf ("assignment cur:  %d\n", a < 0 ? 0 : 1);
#endif
      if (BTOR_IS_VAR_AIG (real_cur))
      {
        assert (get_assignment_aig (aprop->model, cur) != 0);
        res = get_assignment_aig (aprop->model, cur) < 0 ? 0.0 : 1.0;
      }
      else
      {
        assert (BTOR_IS_AND_AIG (real_cur));
        left  = BTOR_LEFT_CHILD_AIG (aprop->amgr, real_cur);
        right = BTOR_RIGHT_CHILD_AIG (aprop->amgr, real_cur);
        assert (BTOR_IS_CONST_AIG (left)
                || btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (left)->id));
        assert (BTOR_IS_CONST_AIG (right)
                || btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (right)->id));
        if (BTOR_IS_INVERTED_AIG (cur))
        {
          assert (BTOR_IS_CONST_AIG (left)
                  || btor_find_in_ptr_hash_table (aprop->score,
                                                  BTOR_INVERT_AIG (left)));
          assert (BTOR_IS_CONST_AIG (right)
                  || btor_find_in_ptr_hash_table (aprop->score,
                                                  BTOR_INVERT_AIG (right)));

          s0 = BTOR_IS_CONST_AIG (left)
                   ? (left == BTOR_AIG_TRUE ? 0.0 : 1.0)
                   : btor_find_in_ptr_hash_table (aprop->score,
                                                  BTOR_INVERT_AIG (left))
                         ->data.asDbl;
          s1 = BTOR_IS_CONST_AIG (right)
                   ? (right == BTOR_AIG_TRUE ? 0.0 : 1.0)
                   : btor_find_in_ptr_hash_table (aprop->score,
                                                  BTOR_INVERT_AIG (right))
                         ->data.asDbl;
#ifndef NDEBUG
          a = get_assignment_aig (aprop->model, left);
          assert (a);
          printf ("assignment aig0: %d\n", a < 0 ? 0 : 1);
          a = get_assignment_aig (aprop->model, right);
          assert (a);
          printf ("assignment aig1: %d\n", a < 0 ? 0 : 1);
          printf ("score      aig0: %f\n", s0);
          printf ("score      aig1: %f\n", s1);
#endif
          res = s0 > s1 ? s0 : s1;
        }
        else
        {
          assert (BTOR_IS_CONST_AIG (left)
                  || btor_find_in_ptr_hash_table (aprop->score, left));
          assert (BTOR_IS_CONST_AIG (right)
                  || btor_find_in_ptr_hash_table (aprop->score, right));

          s0 = BTOR_IS_CONST_AIG (left)
                   ? (left == BTOR_AIG_TRUE ? 1.0 : 0.0)
                   : btor_find_in_ptr_hash_table (aprop->score, left)
                         ->data.asDbl;
          s1 = BTOR_IS_CONST_AIG (right)
                   ? (right == BTOR_AIG_TRUE ? 1.0 : 0.0)
                   : btor_find_in_ptr_hash_table (aprop->score, right)
                         ->data.asDbl;
#ifndef NDEBUG
          a = get_assignment_aig (aprop->model, left);
          assert (a);
          printf ("assignment aig0: %d\n", a < 0 ? 0 : 1);
          a = get_assignment_aig (aprop->model, right);
          assert (a);
          printf ("assignment aig1: %d\n", a < 0 ? 0 : 1);
          printf ("score      aig0: %f\n", s0);
          printf ("score      aig1: %f\n", s1);
#endif
          res = (s0 + s1) / 2.0;
          /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
             choose minimum (else it might again result in 1.0) */
          if (res == 1.0 && (s0 < 1.0 || s1 < 1.0)) res = s0 < s1 ? s0 : s1;
        }
      }
#ifndef NDEBUG
      printf ("score cur      : %f\n", res);
#endif
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
  btor_free_int_hash_table (cache);
  assert (btor_find_in_ptr_hash_table (aprop->score, aig));
  assert (res == btor_find_in_ptr_hash_table (aprop->score, aig)->data.asDbl);
  return res;
}

static void
compute_scores (AIGProp *aprop)
{
  assert (aprop);

  BtorAIGPtrStack stack;
  BtorIntHashTable *cache;
  BtorAIG *cur, *real_cur, *left, *right;
  BtorHashTableIterator it;
  BtorMemMgr *mm;

  mm = aprop->amgr->mm;

  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (mm);

  /* collect roots */
  btor_init_node_hash_table_iterator (&it, aprop->roots);
  while (btor_has_next_hash_table_iterator (&it))
    BTOR_PUSH_STACK (mm, stack, btor_next_hash_table_iterator (&it));

  /* compute scores */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (BTOR_IS_CONST_AIG (real_cur)) continue;
    if (btor_find_in_ptr_hash_table (aprop->score, cur)) continue;

    if (!btor_contains_int_hash_table (cache, real_cur->id))
    {
      btor_add_int_hash_table (cache, real_cur->id);
      assert (BTOR_IS_VAR_AIG (real_cur) || BTOR_IS_AND_AIG (real_cur));
      BTOR_PUSH_STACK (mm, stack, cur);
      if (BTOR_IS_AND_AIG (real_cur))
      {
        left  = BTOR_LEFT_CHILD_AIG (aprop->amgr, real_cur);
        right = BTOR_RIGHT_CHILD_AIG (aprop->amgr, real_cur);
        assert (BTOR_IS_CONST_AIG (left)
                || !btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (left)->id));
        assert (BTOR_IS_CONST_AIG (right)
                || !btor_contains_int_hash_table (
                       cache, BTOR_REAL_ADDR_NODE (right)->id));
        if (!BTOR_IS_CONST_AIG (left)) BTOR_PUSH_STACK (mm, stack, left);
        if (!BTOR_IS_CONST_AIG (right)) BTOR_PUSH_STACK (mm, stack, right);
      }
    }
    else
    {
      compute_sls_score_aig (aprop, cur);
      compute_sls_score_aig (aprop, BTOR_INVERT_AIG (cur));
    }
  }

  /* cleanup */
  BTOR_RELEASE_STACK (mm, stack);
  btor_free_int_hash_table (cache);
}

int
aigprop_sat (AIGProp *aprop)
{
  assert (aprop);

  printf ("asdf\n");
  compute_scores (aprop);
  // TODO
  return 0;
}

static void *
clone_key_as_aig (BtorMemMgr *mm, const void *cloned_amgr, const void *key)
{
  assert (cloned_amgr);
  assert (key);

  BtorAIG *aig, *cloned_aig;
  BtorAIGMgr *camgr;

  (void) mm;

  aig        = (BtorAIG *) key;
  camgr      = (BtorAIGMgr *) cloned_amgr;
  cloned_aig = BTOR_GET_AIG_BY_ID (camgr, BTOR_REAL_ADDR_AIG (aig)->id);
  assert (cloned_aig);
  if (BTOR_IS_INVERTED_AIG (aig)) cloned_aig = BTOR_INVERT_AIG (cloned_aig);
  return cloned_aig;
}

AIGProp *
aigprop_clone_aigprop (BtorAIGMgr *clone, AIGProp *aprop)
{
  assert (clone);
  assert (aprop);

  AIGProp *res;

  BTOR_CNEW (clone->mm, res);
  res->amgr  = clone;
  res->roots = btor_clone_ptr_hash_table (clone->mm,
                                          aprop->roots,
                                          clone_key_as_aig,
                                          btor_clone_data_as_int,
                                          clone,
                                          0);
  res->score = btor_clone_ptr_hash_table (clone->mm,
                                          aprop->score,
                                          clone_key_as_aig,
                                          btor_clone_data_as_dbl,
                                          clone,
                                          0);
  res->model = btor_clone_ptr_hash_table (clone->mm,
                                          aprop->model,
                                          clone_key_as_aig,
                                          btor_clone_data_as_int,
                                          clone,
                                          0);
  return res;
}

AIGProp *
aigprop_new_aigprop (BtorAIGMgr *amgr)
{
  assert (amgr);

  AIGProp *res;

  BTOR_CNEW (amgr->mm, res);
  res->amgr = amgr;

  return res;
}
