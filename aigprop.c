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

#define AIGPROPLOG(level, fmt, args...) \
  do                                    \
  {                                     \
    if (aprop->loglevel < level) break; \
    msg (fmt, ##args);                  \
  } while (0)

void
msg (char *fmt, ...)
{
  va_list msg;

  fputs ("[aigprop] ", stdout);
  va_start (msg, fmt);
  vfprintf (stdout, fmt, msg);
  va_end (msg);
  fputc ('\n', stdout);
  fflush (stdout);
}

static int
get_assignment_aig (BtorPtrHashTable *model, BtorAIG *aig)
{
  assert (model);
  assert (aig);
  assert (btor_find_in_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig)));

  int res;

  if (aig == BTOR_AIG_TRUE) return 1;
  if (aig == BTOR_AIG_FALSE) return -1;

  res =
      btor_find_in_ptr_hash_table (model, BTOR_REAL_ADDR_AIG (aig))->data.asInt;
  if (BTOR_IS_INVERTED_AIG (aig)) res *= -1;
  return res;
}

bool
check_roots_mark_unset_dbg (BtorPtrHashTable *roots)
{
  assert (roots);

  BtorHashTableIterator it;

  btor_init_hash_table_iterator (&it, roots);
  while (btor_has_next_hash_table_iterator (&it))
    if (((BtorAIG *) btor_next_hash_table_iterator (&it))->mark) return false;
  return true;
}

static void
reset_cone (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (check_roots_mark_unset_dbg (aprop->roots));

  int i;
  BtorAIG *cur, *child;
  BtorHashTableIterator it;
  BtorPtrHashBucket *b;
  BtorAIGPtrStack stack, unmark_stack;
  BtorMemMgr *mm;

  if (BTOR_IS_CONST_AIG (aig)) return;

  mm = aprop->amgr->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  assert (btor_find_in_ptr_hash_table (aprop->model, aig));
  assert (btor_find_in_ptr_hash_table (aprop->model, BTOR_INVERT_AIG (aig)));
  btor_remove_from_ptr_hash_table (
      aprop->model, BTOR_REAL_ADDR_AIG (aig), 0, 0);

  btor_init_hash_table_iterator (&it, aprop->roots);
  while (btor_has_next_hash_table_iterator (&it))
    BTOR_PUSH_STACK (mm, stack, btor_next_hash_table_iterator (&it));

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (!BTOR_IS_CONST_AIG (cur));
    assert (BTOR_IS_REGULAR_AIG (cur));
    if (cur->mark == 2) continue;
    if (cur->mark == 0)
    {
      cur->mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur);
      if (BTOR_IS_VAR_AIG (cur))
      {
        cur->mark = 2;
        continue;
      }
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = 0; i < 2; i++)
      {
        child = BTOR_GET_AIG_BY_ID (aprop->amgr, cur->children[i]);
        if (!BTOR_IS_CONST_AIG (child)) BTOR_PUSH_STACK (mm, stack, child);
      }
    }
    else
    {
      assert (cur->mark == 1);
      assert (btor_find_in_ptr_hash_table (aprop->model, cur));
      cur->mark = 2;
      for (i = 0; i < 2; i++)
      {
        child = BTOR_GET_AIG_BY_ID (aprop->amgr, cur->children[i]);
        if (!(b = btor_find_in_ptr_hash_table (aprop->model, child)))
        {
          /* reset previous assignment */
          assert (btor_find_in_ptr_hash_table (aprop->model, cur));
          btor_remove_from_ptr_hash_table (aprop->model, cur, 0, 0);
          btor_release_aig (aprop->amgr, cur);
          /* reset previous score */
          assert (btor_find_in_ptr_hash_table (aprop->score, cur));
          btor_remove_from_ptr_hash_table (aprop->score, cur, 0, 0);
          assert (btor_find_in_ptr_hash_table (aprop->score,
                                               BTOR_INVERT_NODE (cur)));
          btor_remove_from_ptr_hash_table (
              aprop->score, BTOR_INVERT_NODE (cur), 0, 0);
          break;
        }
      }
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static void
update_cone (AIGProp *aprop, BtorAIG *aig, int assignment)
{
  assert (aprop);
  assert (aig);
  assert (assignment == 1 || assignment == -1);

  BtorAIG *real_aig;
  int real_ass;

  reset_cone (aprop, aig);
  real_aig = BTOR_REAL_ADDR_AIG (aig);
  real_ass = BTOR_IS_INVERTED_AIG (aig) ? -assignment : assignment;
  btor_insert_in_ptr_hash_table (aprop->model,
                                 btor_copy_aig (aprop->amgr, real_aig))
      ->data.asInt = real_ass;
  aigprop_generate_model (aprop, 0);
}

static void
recursively_compute_assignment (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (aprop->model);
  assert (aig);

  int aleft, aright;
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
        BTOR_PUSH_STACK (mm, stack, cur);
        if (!BTOR_IS_CONST_AIG (left)
            && !btor_contains_int_hash_table (cache,
                                              BTOR_REAL_ADDR_NODE (left)->id))
          BTOR_PUSH_STACK (mm, stack, left);
        if (!BTOR_IS_CONST_AIG (right)
            && !btor_contains_int_hash_table (cache,
                                              BTOR_REAL_ADDR_NODE (right)->id))
          BTOR_PUSH_STACK (mm, stack, right);
        btor_add_int_hash_table (cache, real_cur->id);
      }
      else
      {
        aleft = get_assignment_aig (aprop->model, left);
        assert (aleft);
        aright = get_assignment_aig (aprop->model, right);
        assert (aright);
        if (aleft < 0 || aright < 0)
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
aigprop_delete_model (AIGProp *aprop)
{
  assert (aprop);

  BtorHashTableIterator it;

  if (!aprop->model) return;

  btor_init_hash_table_iterator (&it, aprop->model);
  while (btor_has_next_hash_table_iterator (&it))
    btor_release_aig (aprop->amgr, btor_next_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (aprop->model);
  aprop->model = 0;
}

void
aigprop_init_model (AIGProp *aprop)
{
  assert (aprop);

  if (aprop->model) aigprop_delete_model (aprop);
  aprop->model = btor_new_ptr_hash_table (aprop->amgr->mm,
                                          (BtorHashPtr) btor_hash_aig_by_id,
                                          (BtorCmpPtr) btor_compare_aig_by_id);
}

void
aigprop_generate_model (AIGProp *aprop, int reset)
{
  assert (aprop);
  assert (aprop->roots);

  BtorHashTableIterator it;

  if (reset) aigprop_init_model (aprop);

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

#define AIGPROP_COMPUTE_SCORE_AIG_AND(cur, left, right, s0, s1, res)          \
  do                                                                          \
  {                                                                           \
    assert (BTOR_IS_CONST_AIG (left)                                          \
            || btor_find_in_ptr_hash_table (aprop->score, left));             \
    assert (BTOR_IS_CONST_AIG (right)                                         \
            || btor_find_in_ptr_hash_table (aprop->score, right));            \
    s0 = BTOR_IS_CONST_AIG (left)                                             \
             ? (left == BTOR_AIG_TRUE ? 1.0 : 0.0)                            \
             : btor_find_in_ptr_hash_table (aprop->score, left)->data.asDbl;  \
    s1 = BTOR_IS_CONST_AIG (right)                                            \
             ? (right == BTOR_AIG_TRUE ? 1.0 : 0.0)                           \
             : btor_find_in_ptr_hash_table (aprop->score, right)->data.asDbl; \
    res = (s0 + s1) / 2.0;                                                    \
    /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->                       \
       choose minimum (else it might again result in 1.0) */                  \
    if (res == 1.0 && (s0 < 1.0 || s1 < 1.0)) res = s0 < s1 ? s0 : s1;        \
  } while (0)

#define AIGPROP_COMPUTE_SCORE_AIG_OR(cur, left, right, s0, s1, res)           \
  do                                                                          \
  {                                                                           \
    assert (BTOR_IS_CONST_AIG (left)                                          \
            || btor_find_in_ptr_hash_table (aprop->score,                     \
                                            BTOR_INVERT_AIG (left)));         \
    assert (BTOR_IS_CONST_AIG (right)                                         \
            || btor_find_in_ptr_hash_table (aprop->score,                     \
                                            BTOR_INVERT_AIG (right)));        \
    s0 = BTOR_IS_CONST_AIG (left) ? (left == BTOR_AIG_TRUE ? 0.0 : 1.0)       \
                                  : btor_find_in_ptr_hash_table (             \
                                        aprop->score, BTOR_INVERT_AIG (left)) \
                                        ->data.asDbl;                         \
    s1 = BTOR_IS_CONST_AIG (right)                                            \
             ? (right == BTOR_AIG_TRUE ? 0.0 : 1.0)                           \
             : btor_find_in_ptr_hash_table (aprop->score,                     \
                                            BTOR_INVERT_AIG (right))          \
                   ->data.asDbl;                                              \
    res = s0 > s1 ? s0 : s1;                                                  \
  } while (0)

#define AIGPROP_LOG_COMPUTE_SCORE_AIG(cur, left, right, s0, s1, res) \
  do                                                                 \
  {                                                                  \
    a = get_assignment_aig (aprop->model, left);                     \
    assert (a);                                                      \
    AIGPROPLOG (2, "assignment aig0: %d", a < 0 ? 0 : 1);            \
    a = get_assignment_aig (aprop->model, right);                    \
    assert (a);                                                      \
    AIGPROPLOG (2, "assignment aig1: %d", a < 0 ? 0 : 1);            \
    AIGPROPLOG (2, "score      aig0: %f", s0);                       \
    AIGPROPLOG (2, "score      aig1: %f", s1);                       \
    AIGPROPLOG (2,                                                   \
                "score cur (%s%d): %f",                              \
                BTOR_IS_INVERTED_AIG (cur) ? "-" : "",               \
                real_cur->id,                                        \
                a < 0 ? 0 : 1,                                       \
                res);                                                \
  } while (0)

static double
compute_score_aig (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (check_roots_mark_unset_dbg (aprop->roots));
  assert (!BTOR_IS_CONST_AIG (aig));

  double res, invres, s0, s1, invs0, invs1;
  BtorPtrHashBucket *b;
  BtorAIGPtrStack stack, unmark_stack;
  BtorAIG *cur, *real_cur, *left, *right;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int a;
#endif

  if ((b = btor_find_in_ptr_hash_table (aprop->score, aig)))
    return b->data.asDbl;

  mm  = aprop->amgr->mm;
  res = 0.0;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (mm, stack, aig);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (BTOR_IS_CONST_AIG (real_cur)) continue;
    if (btor_find_in_ptr_hash_table (aprop->score, cur)) continue;
    if (real_cur->mark == 2) continue;

    if (real_cur->mark == 0)
    {
      real_cur->mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, real_cur);
      assert (BTOR_IS_VAR_AIG (real_cur) || BTOR_IS_AND_AIG (real_cur));
      BTOR_PUSH_STACK (mm, stack, cur);
      if (BTOR_IS_AND_AIG (real_cur))
      {
        left  = BTOR_LEFT_CHILD_AIG (aprop->amgr, real_cur);
        right = BTOR_RIGHT_CHILD_AIG (aprop->amgr, real_cur);
        if (!BTOR_IS_CONST_AIG (left)) BTOR_PUSH_STACK (mm, stack, left);
        if (!BTOR_IS_CONST_AIG (right)) BTOR_PUSH_STACK (mm, stack, right);
      }
    }
    else
    {
      assert (real_cur->mark == 1);
      real_cur->mark = 2;
      assert (get_assignment_aig (aprop->model, cur) != 0);
#ifndef NDEBUG
      a = get_assignment_aig (aprop->model, cur);
      assert (a);
      AIGPROPLOG (2, "**");
      AIGPROPLOG (2,
                  "assignment cur (%s%d):  %d",
                  BTOR_IS_INVERTED_AIG (cur) ? "-" : "",
                  real_cur->id,
                  a < 0 ? 0 : 1);
#endif
      if (BTOR_IS_VAR_AIG (real_cur))
      {
        res = get_assignment_aig (aprop->model, cur) < 0 ? 0.0 : 1.0;
      }
      else
      {
        assert (BTOR_IS_AND_AIG (real_cur));
        left  = BTOR_LEFT_CHILD_AIG (aprop->amgr, real_cur);
        right = BTOR_RIGHT_CHILD_AIG (aprop->amgr, real_cur);
        if (BTOR_IS_INVERTED_AIG (cur))
        {
          AIGPROP_COMPUTE_SCORE_AIG_OR (cur, left, right, s0, s1, res);
          AIGPROP_COMPUTE_SCORE_AIG_AND (
              BTOR_INVERT_AIG (cur), left, right, invs0, invs1, invres);
#ifndef NDEBUG
          AIGPROP_LOG_COMPUTE_SCORE_AIG (cur,
                                         BTOR_INVERT_AIG (left),
                                         BTOR_INVERT_AIG (right),
                                         s0,
                                         s1,
                                         res);
          AIGPROP_LOG_COMPUTE_SCORE_AIG (
              BTOR_INVERT_AIG (cur), left, right, invs0, invs1, invres);
#endif
        }
        else
        {
          AIGPROP_COMPUTE_SCORE_AIG_AND (cur, left, right, s0, s1, res);
          AIGPROP_COMPUTE_SCORE_AIG_OR (
              BTOR_INVERT_AIG (cur), left, right, invs0, invs1, invres);
#ifndef NDEBUG
          AIGPROP_LOG_COMPUTE_SCORE_AIG (cur, left, right, s0, s1, res);
          AIGPROP_LOG_COMPUTE_SCORE_AIG (BTOR_INVERT_AIG (cur),
                                         BTOR_INVERT_AIG (left),
                                         BTOR_INVERT_AIG (right),
                                         invs0,
                                         invs1,
                                         invres);
#endif
        }
      }
      assert (!btor_find_in_ptr_hash_table (aprop->score, cur));
      assert (
          !btor_find_in_ptr_hash_table (aprop->score, BTOR_INVERT_NODE (cur)));
      b             = btor_insert_in_ptr_hash_table (aprop->score, cur);
      b->data.asDbl = res;
      b = btor_insert_in_ptr_hash_table (aprop->score, BTOR_INVERT_NODE (cur));
      b->data.asDbl = invres;
      assert (btor_find_in_ptr_hash_table (aprop->score, cur));
      assert (
          btor_find_in_ptr_hash_table (aprop->score, BTOR_INVERT_NODE (cur)));
    }
  }

  /* cleanup */
  while (!BTOR_EMPTY_STACK (unmark_stack))
    BTOR_POP_STACK (unmark_stack)->mark = 0;

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);

  assert (btor_find_in_ptr_hash_table (aprop->score, aig));
  assert (res == btor_find_in_ptr_hash_table (aprop->score, aig)->data.asDbl);
  return res;
}

static void
compute_scores (AIGProp *aprop)
{
  assert (aprop);
  assert (aprop->roots);
  assert (aprop->model);

  BtorAIGPtrStack stack;
  BtorIntHashTable *cache;
  BtorAIG *cur, *real_cur, *left, *right;
  BtorHashTableIterator it;
  BtorMemMgr *mm;

  AIGPROPLOG (2, "*** compute scores");

  mm = aprop->amgr->mm;

  BTOR_INIT_STACK (stack);
  cache = btor_new_int_hash_table (mm);

  if (!aprop->score)
    aprop->score =
        btor_new_ptr_hash_table (aprop->amgr->mm,
                                 (BtorHashPtr) btor_hash_aig_by_id,
                                 (BtorCmpPtr) btor_compare_aig_by_id);

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
        if (!BTOR_IS_CONST_AIG (left)
            && !btor_contains_int_hash_table (cache,
                                              BTOR_REAL_ADDR_NODE (left)->id))
          BTOR_PUSH_STACK (mm, stack, left);
        if (!BTOR_IS_CONST_AIG (right)
            && !btor_contains_int_hash_table (cache,
                                              BTOR_REAL_ADDR_NODE (right)->id))
          BTOR_PUSH_STACK (mm, stack, right);
      }
    }
    else
    {
      compute_score_aig (aprop, cur);
      compute_score_aig (aprop, BTOR_INVERT_AIG (cur));
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
