/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "aigprop.h"
#include "btorclone.h"
#include "btorcore.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#include <math.h>

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

#define AIGPROP_MAXSTEPS_CFACT 100
#define AIGPROP_MAXSTEPS(i) \
  (AIGPROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define AIGPROP_SELECT_CFACT 20

/*------------------------------------------------------------------------*/

int32_t
aigprop_get_assignment_aig (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);

  int32_t res;
  int32_t id;

  if (btor_aig_is_true (aig)) return 1;
  if (btor_aig_is_false (aig)) return -1;

  id = btor_aig_get_id (BTOR_REAL_ADDR_AIG (aig));
  assert (btor_hashint_map_get (aprop->model, id));
  res = btor_hashint_map_get (aprop->model, id)->as_int;
  res = BTOR_IS_INVERTED_AIG (aig) ? -res : res;
  return res;
}

/*------------------------------------------------------------------------*/

/* score
 *
 * score (aigvar, A) = A (aigvar)
 * score (BTOR_CONST_AIG_TRUE, A) = 1.0
 * score (BTOR_CONST_AIG_FALSE, A) = 0.0
 * score (aig0 /\ aig1, A) = 1/2 * (score (aig0) + score (aig1), A)
 * score (-(-aig0 /\ -aig1), A) = max (score (-aig0), score (-aig1), A)
 */

#define AIGPROP_LOG_COMPUTE_SCORE_AIG(cur, left, right, s0, s1, res) \
  do                                                                 \
  {                                                                  \
    a = aigprop_get_assignment_aig (aprop, left);                    \
    assert (a);                                                      \
    AIGPROPLOG (3,                                                   \
                "        assignment aig0 (%s%d): %d",                \
                BTOR_IS_INVERTED_AIG (left) ? "-" : "",              \
                BTOR_REAL_ADDR_AIG (left)->id,                       \
                a < 0 ? 0 : 1);                                      \
    a = aigprop_get_assignment_aig (aprop, right);                   \
    assert (a);                                                      \
    AIGPROPLOG (3,                                                   \
                "        assignment aig1 (%s%d): %d",                \
                BTOR_IS_INVERTED_AIG (right) ? "-" : "",             \
                BTOR_REAL_ADDR_AIG (right)->id,                      \
                a < 0 ? 0 : 1);                                      \
    AIGPROPLOG (3,                                                   \
                "        score      aig0 (%s%d): %f%s",              \
                BTOR_IS_INVERTED_AIG (left) ? "-" : "",              \
                BTOR_REAL_ADDR_AIG (left)->id,                       \
                s0,                                                  \
                s0 < 1.0 ? " (< 1.0)" : "");                         \
    AIGPROPLOG (3,                                                   \
                "        score      aig1 (%s%d): %f%s",              \
                BTOR_IS_INVERTED_AIG (right) ? "-" : "",             \
                BTOR_REAL_ADDR_AIG (right)->id,                      \
                s1,                                                  \
                s1 < 1.0 ? " (< 1.0)" : "");                         \
    AIGPROPLOG (3,                                                   \
                "      * score cur (%s%d): %f%s",                    \
                BTOR_IS_INVERTED_AIG (cur) ? "-" : "",               \
                real_cur->id,                                        \
                res,                                                 \
                res < 1.0 ? " (< 1.0)" : "");                        \
  } while (0)

static double
compute_score_aig (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (!btor_aig_is_const (aig));

  int32_t curid, leftid, rightid;
  double res, sleft, sright;
  BtorAIGPtrStack stack;
  BtorAIG *cur, *real_cur, *left, *right;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;
#ifndef NDEBUG
  int32_t a;
#endif

  curid = btor_aig_get_id (aig);
  if (btor_hashint_map_contains (aprop->score, curid))
    return btor_hashint_map_get (aprop->score, curid)->as_dbl;

  mm  = aprop->amgr->btor->mm;
  res = 0.0;

  BTOR_INIT_STACK (mm, stack);
  mark = btor_hashint_map_new (mm);

  BTOR_PUSH_STACK (stack, aig);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (btor_aig_is_const (real_cur)) continue;

    curid = btor_aig_get_id (cur);
    if (btor_hashint_map_contains (aprop->score, curid)) continue;

    d = btor_hashint_map_get (mark, real_cur->id);
    if (d && d->as_int == 1) continue;

    if (!d)
    {
      btor_hashint_map_add (mark, real_cur->id);
      assert (btor_aig_is_var (real_cur) || btor_aig_is_and (real_cur));
      BTOR_PUSH_STACK (stack, cur);
      if (btor_aig_is_and (real_cur))
      {
        left  = btor_aig_get_left_child (aprop->amgr, real_cur);
        right = btor_aig_get_right_child (aprop->amgr, real_cur);
        if (!btor_aig_is_const (left)) BTOR_PUSH_STACK (stack, left);
        if (!btor_aig_is_const (right)) BTOR_PUSH_STACK (stack, right);
      }
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;
      assert (aigprop_get_assignment_aig (aprop, cur) != 0);
#ifndef NDEBUG
      a = aigprop_get_assignment_aig (aprop, cur);
      assert (a);
      AIGPROPLOG (3, "");
      AIGPROPLOG (3,
                  "  ** assignment cur (%s%d): %d",
                  BTOR_IS_INVERTED_AIG (cur) ? "-" : "",
                  real_cur->id,
                  a < 0 ? 0 : 1);
#endif
      assert (!btor_hashint_map_contains (aprop->score, curid));
      assert (!btor_hashint_map_contains (aprop->score, -curid));

      if (btor_aig_is_var (real_cur))
      {
        res = aigprop_get_assignment_aig (aprop, cur) < 0 ? 0.0 : 1.0;
        AIGPROPLOG (3,
                    "        * score cur (%s%d): %f",
                    BTOR_IS_INVERTED_AIG (cur) ? "-" : "",
                    real_cur->id,
                    res);
        AIGPROPLOG (3,
                    "        * score cur (%s%d): %f",
                    BTOR_IS_INVERTED_AIG (cur) ? "" : "-",
                    real_cur->id,
                    res == 0.0 ? 1.0 : 0.0);
        btor_hashint_map_add (aprop->score, curid)->as_dbl = res;
        btor_hashint_map_add (aprop->score, -curid)->as_dbl =
            res == 0.0 ? 1.0 : 0.0;
      }
      else
      {
        assert (btor_aig_is_and (real_cur));

        left    = btor_aig_get_left_child (aprop->amgr, real_cur);
        right   = btor_aig_get_right_child (aprop->amgr, real_cur);
        leftid  = btor_aig_get_id (left);
        rightid = btor_aig_get_id (right);

        assert (btor_aig_is_const (left)
                || btor_hashint_map_contains (aprop->score, leftid));
        assert (btor_aig_is_const (right)
                || btor_hashint_map_contains (aprop->score, rightid));
        assert (btor_aig_is_const (left)
                || btor_hashint_map_contains (aprop->score, -leftid));
        assert (btor_aig_is_const (right)
                || btor_hashint_map_contains (aprop->score, -rightid));

        sleft = btor_aig_is_const (left)
                    ? (btor_aig_is_true (left) ? 1.0 : 0.0)
                    : btor_hashint_map_get (aprop->score, leftid)->as_dbl;
        sright = btor_aig_is_const (right)
                     ? (btor_aig_is_true (right) ? 1.0 : 0.0)
                     : btor_hashint_map_get (aprop->score, rightid)->as_dbl;
        res = (sleft + sright) / 2.0;
        /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
           choose minimum (else it might again result in 1.0) */
        if (res == 1.0 && (sleft < 1.0 || sright < 1.0))
          res = sleft < sright ? sleft : sright;
        assert (res >= 0.0 && res <= 1.0);
        btor_hashint_map_add (aprop->score, real_cur->id)->as_dbl = res;
#ifndef NDEBUG
        AIGPROP_LOG_COMPUTE_SCORE_AIG (
            real_cur, left, right, sleft, sright, res);
#endif
        sleft = btor_aig_is_const (left)
                    ? (btor_aig_is_true (left) ? 0.0 : 1.0)
                    : btor_hashint_map_get (aprop->score, -leftid)->as_dbl;
        sright = btor_aig_is_const (right)
                     ? (btor_aig_is_true (right) ? 0.0 : 1.0)
                     : btor_hashint_map_get (aprop->score, -rightid)->as_dbl;
        res = sleft > sright ? sleft : sright;
        assert (res >= 0.0 && res <= 1.0);
        btor_hashint_map_add (aprop->score, -real_cur->id)->as_dbl = res;
#ifndef NDEBUG
        AIGPROP_LOG_COMPUTE_SCORE_AIG (BTOR_INVERT_AIG (real_cur),
                                       BTOR_INVERT_AIG (left),
                                       BTOR_INVERT_AIG (right),
                                       sleft,
                                       sright,
                                       res);
#endif
      }
      assert (btor_hashint_map_contains (aprop->score, curid));
      assert (btor_hashint_map_contains (aprop->score, -curid));
    }
  }

  btor_hashint_map_delete (mark);
  BTOR_RELEASE_STACK (stack);

  assert (btor_hashint_map_contains (aprop->score, btor_aig_get_id (aig)));
  assert (btor_hashint_map_contains (aprop->score, -btor_aig_get_id (aig)));
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
  BtorIntHashTableIterator it;
  BtorMemMgr *mm;

  AIGPROPLOG (3, "*** compute scores");

  mm = aprop->amgr->btor->mm;

  BTOR_INIT_STACK (mm, stack);
  cache = btor_hashint_table_new (mm);

  if (!aprop->score) aprop->score = btor_hashint_map_new (mm);

  /* collect roots */
  btor_iter_hashint_init (&it, aprop->roots);
  while (btor_iter_hashint_has_next (&it))
    BTOR_PUSH_STACK (
        stack, btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it)));

  /* compute scores */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);

    if (btor_aig_is_const (real_cur)) continue;
    if (btor_hashint_map_contains (aprop->score, btor_aig_get_id (cur)))
      continue;

    if (!btor_hashint_table_contains (cache, real_cur->id))
    {
      btor_hashint_table_add (cache, real_cur->id);
      assert (btor_aig_is_var (real_cur) || btor_aig_is_and (real_cur));
      BTOR_PUSH_STACK (stack, cur);
      if (btor_aig_is_and (real_cur))
      {
        left  = btor_aig_get_left_child (aprop->amgr, real_cur);
        right = btor_aig_get_right_child (aprop->amgr, real_cur);
        if (!btor_aig_is_const (left)
            && !btor_hashint_table_contains (cache,
                                             BTOR_REAL_ADDR_AIG (left)->id))
          BTOR_PUSH_STACK (stack, left);
        if (!btor_aig_is_const (right)
            && !btor_hashint_table_contains (cache,
                                             BTOR_REAL_ADDR_AIG (right)->id))
          BTOR_PUSH_STACK (stack, right);
      }
    }
    else
    {
      compute_score_aig (aprop, cur);
    }
  }

  /* cleanup */
  BTOR_RELEASE_STACK (stack);
  btor_hashint_table_delete (cache);
}

/*------------------------------------------------------------------------*/

static void
recursively_compute_assignment (AIGProp *aprop, BtorAIG *aig)
{
  assert (aprop);
  assert (aprop->model);
  assert (aig);

  int32_t aleft, aright;
  BtorAIG *cur, *real_cur, *left, *right;
  BtorAIGPtrStack stack;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  if (btor_aig_is_const (aig)) return;

  mm = aprop->amgr->btor->mm;

  cache = btor_hashint_table_new (mm);
  BTOR_INIT_STACK (mm, stack);
  BTOR_PUSH_STACK (stack, aig);

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_AIG (cur);
    assert (!btor_aig_is_const (real_cur));
    if (btor_hashint_map_contains (aprop->model, real_cur->id)) continue;

    if (btor_aig_is_var (real_cur))
    {
      /* initialize with false */
      btor_hashint_map_add (aprop->model, real_cur->id)->as_int = -1;
    }
    else
    {
      assert (btor_aig_is_and (real_cur));
      left  = btor_aig_get_left_child (aprop->amgr, real_cur);
      right = btor_aig_get_right_child (aprop->amgr, real_cur);

      if (!btor_hashint_table_contains (cache, real_cur->id))
      {
        btor_hashint_table_add (cache, real_cur->id);
        BTOR_PUSH_STACK (stack, cur);
        if (!btor_aig_is_const (left)
            && !btor_hashint_table_contains (cache,
                                             BTOR_REAL_ADDR_AIG (left)->id))
          BTOR_PUSH_STACK (stack, left);
        if (!btor_aig_is_const (right)
            && !btor_hashint_table_contains (cache,
                                             BTOR_REAL_ADDR_AIG (right)->id))
          BTOR_PUSH_STACK (stack, right);
      }
      else
      {
        aleft = aigprop_get_assignment_aig (aprop, left);
        assert (aleft);
        aright = aigprop_get_assignment_aig (aprop, right);
        assert (aright);
        if (aleft < 0 || aright < 0)
          btor_hashint_map_add (aprop->model, real_cur->id)->as_int = -1;
        else
          btor_hashint_map_add (aprop->model, real_cur->id)->as_int = 1;
      }
    }
  }

  btor_hashint_table_delete (cache);
  BTOR_RELEASE_STACK (stack);
}

void
aigprop_delete_model (AIGProp *aprop)
{
  assert (aprop);

  if (!aprop->model) return;
  btor_hashint_map_delete (aprop->model);
  aprop->model = 0;
}

void
aigprop_init_model (AIGProp *aprop)
{
  assert (aprop);

  if (aprop->model) aigprop_delete_model (aprop);
  aprop->model = btor_hashint_map_new (aprop->amgr->btor->mm);
}

void
aigprop_generate_model (AIGProp *aprop, bool reset)
{
  assert (aprop);
  assert (aprop->roots);

  BtorIntHashTableIterator it;

  if (reset) aigprop_init_model (aprop);

  btor_iter_hashint_init (&it, aprop->roots);
  while (btor_iter_hashint_has_next (&it))
    recursively_compute_assignment (
        aprop, btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it)));
}

/*------------------------------------------------------------------------*/

static inline void
update_unsatroots_table (AIGProp *aprop, BtorAIG *aig, int32_t assignment)
{
  assert (aprop);
  assert (aig);
  assert (!btor_aig_is_const (aig));
  assert (
      btor_hashint_table_contains (aprop->roots, btor_aig_get_id (aig))
      || btor_hashint_table_contains (aprop->roots, -btor_aig_get_id (aig)));
  assert (aigprop_get_assignment_aig (aprop, aig) != assignment);
  assert (assignment == 1 || assignment == -1);

  uint32_t id;

  id = btor_aig_get_id (aig);

  if (btor_hashint_map_contains (aprop->unsatroots, id))
  {
    btor_hashint_map_remove (aprop->unsatroots, id, 0);
    assert (aigprop_get_assignment_aig (aprop, aig) == -1);
    assert (assignment == 1);
  }
  else if (btor_hashint_map_contains (aprop->unsatroots, -id))
  {
    btor_hashint_map_remove (aprop->unsatroots, -id, 0);
    assert (aigprop_get_assignment_aig (aprop, BTOR_INVERT_AIG (aig)) == -1);
    assert (assignment == -1);
  }
  else if (assignment == -1)
  {
    btor_hashint_map_add (aprop->unsatroots, id);
    assert (aigprop_get_assignment_aig (aprop, aig) == 1);
  }
  else
  {
    btor_hashint_map_add (aprop->unsatroots, -id);
    assert (aigprop_get_assignment_aig (aprop, BTOR_INVERT_AIG (aig)) == 1);
  }
}

static void
update_cone (AIGProp *aprop, BtorAIG *aig, int32_t assignment)
{
  assert (aprop);
  assert (aig);
  assert (BTOR_IS_REGULAR_AIG (aig));
  assert (btor_aig_is_var (aig));
  assert (assignment == 1 || assignment == -1);

  int32_t aleft, aright, ass, leftid, rightid;
  uint32_t i;
  double start, delta, sleft, sright, s;
  BtorIntHashTable *cache;
  BtorHashTableData *d;
  BtorAIGPtrStack stack, cone;
  BtorIntStack *parents;
  BtorAIG *cur, *left, *right;
  BtorMemMgr *mm;

  start = btor_util_time_stamp ();

  mm = aprop->amgr->btor->mm;

#ifndef NDEBUG
  BtorIntHashTableIterator it;
  BtorAIG *root;
  btor_iter_hashint_init (&it, aprop->roots);
  while (btor_iter_hashint_has_next (&it))
  {
    root = btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it));
    assert (!btor_aig_is_false (root));
    if ((!BTOR_IS_INVERTED_AIG (root)
         && aigprop_get_assignment_aig (aprop, BTOR_REAL_ADDR_AIG (root)) == -1)
        || (BTOR_IS_INVERTED_AIG (root)
            && aigprop_get_assignment_aig (aprop, BTOR_REAL_ADDR_AIG (root))
                   == 1))
    {
      assert (btor_hashint_map_contains (aprop->unsatroots,
                                         btor_aig_get_id (root)));
    }
    else if ((!BTOR_IS_INVERTED_AIG (root)
              && aigprop_get_assignment_aig (aprop, BTOR_REAL_ADDR_AIG (root))
                     == 1)
             || (BTOR_IS_INVERTED_AIG (root)
                 && aigprop_get_assignment_aig (aprop,
                                                BTOR_REAL_ADDR_AIG (root))
                        == -1))
    {
      assert (!btor_hashint_map_contains (aprop->unsatroots,
                                          btor_aig_get_id (root)));
    }
  }
#endif

  /* reset cone ----------------------------------------------------------- */

  BTOR_INIT_STACK (mm, cone);
  BTOR_INIT_STACK (mm, stack);
  cache = btor_hashint_table_new (mm);
  BTOR_PUSH_STACK (stack, aig);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_AIG (cur));
    if (btor_hashint_table_contains (cache, cur->id)) continue;
    btor_hashint_table_add (cache, cur->id);
    if (cur != aig) BTOR_PUSH_STACK (cone, cur);
    assert (btor_hashint_map_contains (aprop->parents, cur->id));
    parents = btor_hashint_map_get (aprop->parents, cur->id)->as_ptr;
    for (i = 0; i < BTOR_COUNT_STACK (*parents); i++)
      BTOR_PUSH_STACK (
          stack,
          btor_aig_get_by_id (aprop->amgr, BTOR_PEEK_STACK (*parents, i)));
  }
  BTOR_RELEASE_STACK (stack);
  btor_hashint_table_delete (cache);

  aprop->time.update_cone_reset += btor_util_time_stamp () - start;

  /* update assignment and score of 'aig' --------------------------------- */
  /* update model */
  d = btor_hashint_map_get (aprop->model, aig->id);
  assert (d);
  /* update unsatroots table */
  if (d->as_int != assignment
      && (btor_hashint_table_contains (aprop->roots, aig->id)
          || btor_hashint_table_contains (aprop->roots, -aig->id)))
    update_unsatroots_table (aprop, aig, assignment);
  d->as_int = assignment;

  /* update score */
  if (aprop->score)
  {
    d         = btor_hashint_map_get (aprop->score, aig->id);
    d->as_dbl = assignment < 0 ? 0.0 : 1.0;
    d         = btor_hashint_map_get (aprop->score, -aig->id);
    d->as_dbl = assignment < 0 ? 1.0 : 0.0;
  }

  qsort (cone.start,
         BTOR_COUNT_STACK (cone),
         sizeof (BtorAIG *),
         btor_compare_aig_by_id_qsort_asc);

  /* update model of cone ------------------------------------------------- */

  delta = btor_util_time_stamp ();

  for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
  {
    cur = BTOR_PEEK_STACK (cone, i);
    assert (BTOR_IS_REGULAR_AIG (cur));
    assert (btor_aig_is_and (cur));
    assert (btor_hashint_map_contains (aprop->model, cur->id));

    left  = btor_aig_get_left_child (aprop->amgr, cur);
    right = btor_aig_get_right_child (aprop->amgr, cur);
    aleft = aigprop_get_assignment_aig (aprop, left);
    assert (aleft);
    aright = aigprop_get_assignment_aig (aprop, right);
    assert (aright);
    ass = aleft < 0 || aright < 0 ? -1 : 1;
    d   = btor_hashint_map_get (aprop->model, cur->id);
    assert (d);
    /* update unsatroots table */
    if (d->as_int != ass
        && (btor_hashint_table_contains (aprop->roots, cur->id)
            || btor_hashint_table_contains (aprop->roots, -cur->id)))
      update_unsatroots_table (aprop, cur, ass);
    d->as_int = ass;
  }

  aprop->time.update_cone_model_gen += btor_util_time_stamp () - delta;
  delta = btor_util_time_stamp ();

  /* update score of cone ------------------------------------------------- */

  if (aprop->score)
  {
    delta = btor_util_time_stamp ();
    for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
    {
      cur = BTOR_PEEK_STACK (cone, i);
      assert (BTOR_IS_REGULAR_AIG (cur));
      assert (btor_aig_is_and (cur));
      assert (btor_hashint_map_contains (aprop->score, cur->id));
      assert (btor_hashint_map_contains (aprop->score, -cur->id));

      left    = btor_aig_get_left_child (aprop->amgr, cur);
      right   = btor_aig_get_right_child (aprop->amgr, cur);
      leftid  = btor_aig_get_id (left);
      rightid = btor_aig_get_id (right);

      sleft = btor_aig_is_const (left)
                  ? (btor_aig_is_true (left) ? 1.0 : 0.0)
                  : btor_hashint_map_get (aprop->score, leftid)->as_dbl;
      sright = btor_aig_is_const (right)
                   ? (btor_aig_is_true (right) ? 1.0 : 0.0)
                   : btor_hashint_map_get (aprop->score, rightid)->as_dbl;
      s = (sleft + sright) / 2.0;
      /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
         choose minimum (else it might again result in 1.0) */
      if (s == 1.0 && (sleft < 1.0 || sright < 1.0))
        s = sleft < sright ? sleft : sright;
      assert (s >= 0.0 && s <= 1.0);
      btor_hashint_map_get (aprop->score, cur->id)->as_dbl = s;

      sleft = btor_aig_is_const (left)
                  ? (btor_aig_is_true (left) ? 0.0 : 1.0)
                  : btor_hashint_map_get (aprop->score, -leftid)->as_dbl;
      sright = btor_aig_is_const (right)
                   ? (btor_aig_is_true (right) ? 1.0 : 0.0)
                   : btor_hashint_map_get (aprop->score, -rightid)->as_dbl;
      s = sleft > sright ? sleft : sright;
      assert (s >= 0.0 && s <= 1.0);
      btor_hashint_map_get (aprop->score, -cur->id)->as_dbl = s;
    }
    aprop->time.update_cone_compute_score += btor_util_time_stamp () - delta;
  }

  BTOR_RELEASE_STACK (cone);

#ifndef NDEBUG
  btor_iter_hashint_init (&it, aprop->roots);
  while (btor_iter_hashint_has_next (&it))
  {
    root = btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it));
    if ((!BTOR_IS_INVERTED_AIG (root)
         && aigprop_get_assignment_aig (aprop, BTOR_REAL_ADDR_AIG (root)) == -1)
        || (BTOR_IS_INVERTED_AIG (root)
            && aigprop_get_assignment_aig (aprop, BTOR_REAL_ADDR_AIG (root))
                   == 1))
    {
      assert (btor_hashint_map_contains (aprop->unsatroots,
                                         btor_aig_get_id (root)));
    }
    else if ((!BTOR_IS_INVERTED_AIG (root)
              && aigprop_get_assignment_aig (aprop, BTOR_REAL_ADDR_AIG (root))
                     == 1)
             || (BTOR_IS_INVERTED_AIG (root)
                 && aigprop_get_assignment_aig (aprop,
                                                BTOR_REAL_ADDR_AIG (root))
                        == -1))
    {
      assert (!btor_hashint_map_contains (aprop->unsatroots,
                                          btor_aig_get_id (root)));
    }
  }
#endif

  aprop->time.update_cone += btor_util_time_stamp () - start;
}

/*------------------------------------------------------------------------*/

static BtorAIG *
select_root (AIGProp *aprop, uint32_t nmoves)
{
  assert (aprop);
  assert (aprop->unsatroots);
  assert (aprop->score);

  BtorAIG *res, *cur;
  BtorIntHashTableIterator it;
  BtorMemMgr *mm;

  mm  = aprop->amgr->btor->mm;
  res = 0;

  if (aprop->use_bandit)
  {
    int32_t *selected;
    double value, max_value, score;
    BtorHashTableData *d;

    max_value = 0.0;
    btor_iter_hashint_init (&it, aprop->unsatroots);
    while (btor_iter_hashint_has_next (&it))
    {
      selected = &aprop->unsatroots->data[it.cur_pos].as_int;
      cur      = btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it));
      assert (aigprop_get_assignment_aig (aprop, cur) != 1);
      assert (!btor_aig_is_const (cur));
      d = btor_hashint_map_get (aprop->score, btor_aig_get_id (cur));
      assert (d);
      score = d->as_dbl;
      assert (score < 1.0);
      if (!res)
      {
        res = cur;
        *selected += 1;
        continue;
      }
      value = score + AIGPROP_SELECT_CFACT * sqrt (log (*selected) / nmoves);
      if (value > max_value)
      {
        res       = cur;
        max_value = value;
        *selected *= 1;
      }
    }
  }
  else
  {
    uint32_t r;
    BtorAIGPtrStack stack;
    BTOR_INIT_STACK (mm, stack);
    btor_iter_hashint_init (&it, aprop->unsatroots);
    while (btor_iter_hashint_has_next (&it))
    {
      cur = btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it));
      assert (aigprop_get_assignment_aig (aprop, cur) != 1);
      assert (!btor_aig_is_const (cur));
      BTOR_PUSH_STACK (stack, cur);
    }
    assert (BTOR_COUNT_STACK (stack));
    r   = btor_rng_pick_rand (&aprop->rng, 0, BTOR_COUNT_STACK (stack) - 1);
    res = stack.start[r];
    BTOR_RELEASE_STACK (stack);
  }

  assert (res);

  AIGPROPLOG (1, "");
  AIGPROPLOG (1,
              "*** select root: %s%d",
              BTOR_IS_INVERTED_AIG (res) ? "-" : "",
              BTOR_REAL_ADDR_AIG (res)->id);
  return res;
}

static void
select_move (AIGProp *aprop,
             BtorAIG *root,
             BtorAIG **input,
             int32_t *assignment)
{
  assert (aprop);
  assert (root);
  assert (!btor_aig_is_const (root));
  assert (input);
  assert (assignment);

  int32_t i, asscur, ass[2], assnew;
  uint32_t eidx;
  BtorAIG *cur, *real_cur, *c[2];
  BtorHashTableData *d;

  *input      = 0;
  *assignment = 0;

  cur    = root;
  asscur = 1;

  if (btor_aig_is_var (BTOR_REAL_ADDR_AIG (cur)))
  {
    *input      = BTOR_REAL_ADDR_AIG (cur);
    *assignment = BTOR_IS_INVERTED_AIG (cur) ? -asscur : asscur;
  }
  else
  {
    for (;;)
    {
      real_cur = BTOR_REAL_ADDR_AIG (cur);
      assert (btor_aig_is_and (real_cur));
      asscur = BTOR_IS_INVERTED_AIG (cur) ? -asscur : asscur;
      c[0]   = btor_aig_get_by_id (aprop->amgr, real_cur->children[0]);
      c[1]   = btor_aig_get_by_id (aprop->amgr, real_cur->children[1]);

      /* conflict */
      if (btor_aig_is_and (real_cur) && btor_aig_is_const (c[0])
          && btor_aig_is_const (c[1]))
        break;

      /* select path and determine path assignment */
      if (btor_aig_is_const (c[0]))
        eidx = 1;
      else if (btor_aig_is_const (c[1]))
        eidx = 0;
      else
      {
        /* choose 0-branch if exactly one branch is 0,
         * else choose randomly */
        for (i = 0; i < 2; i++)
        {
          assert (btor_hashint_map_get (aprop->model,
                                        BTOR_REAL_ADDR_AIG (c[i])->id));
          d = btor_hashint_map_get (aprop->model,
                                    BTOR_REAL_ADDR_AIG (c[i])->id);
          assert (d);
          ass[i] = BTOR_IS_INVERTED_AIG (c[i]) ? -d->as_int : d->as_int;
        }
        if (ass[0] == -1 && ass[1] == 1)
          eidx = 0;
        else if (ass[0] == 1 && ass[1] == -1)
          eidx = 1;
        else
          eidx = btor_rng_pick_rand (&aprop->rng, 0, 1);
      }
      if (asscur == 1)
        assnew = 1;
      else if (ass[eidx ? 0 : 1] == 1)
        assnew = -1;
      else
      {
        assnew = btor_rng_pick_rand (&aprop->rng, 0, 1);
        if (!assnew) assnew = -1;
      }

      cur    = c[eidx];
      asscur = assnew;

      if (btor_aig_is_var (BTOR_REAL_ADDR_AIG (cur)))
      {
        *input      = BTOR_REAL_ADDR_AIG (cur);
        *assignment = BTOR_IS_INVERTED_AIG (cur) ? -asscur : asscur;
        break;
      }
    }
  }
}

static int32_t
move (AIGProp *aprop, uint32_t nmoves)
{
  assert (aprop);
  assert (aprop->roots);
  assert (aprop->unsatroots);
  assert (aprop->model);

  int32_t assignment;
  BtorAIG *root, *input;

  /* roots contain false AIG -> unsat */
  if (!(root = select_root (aprop, nmoves))) return 0;

  select_move (aprop, root, &input, &assignment);

  AIGPROPLOG (1, "");
  AIGPROPLOG (1, "*** move");
#ifndef NDEBUG
  int32_t a = aigprop_get_assignment_aig (aprop, input);
  AIGPROPLOG (1,
              "    * input: %s%d",
              BTOR_IS_INVERTED_AIG (input) ? "-" : "",
              BTOR_REAL_ADDR_AIG (input)->id);
  AIGPROPLOG (1, "      prev. assignment: %d", a);
  AIGPROPLOG (1, "      new   assignment: %d", assignment);
#endif

  update_cone (aprop, input, assignment);
  aprop->stats.moves += 1;
  return 1;
}

/*------------------------------------------------------------------------*/

// TODO termination callback?
int32_t
aigprop_sat (AIGProp *aprop, BtorIntHashTable *roots)
{
  assert (aprop);
  assert (roots);

  double start;
  int32_t i, j, max_steps, sat_result, rootid, childid;
  uint32_t nmoves;
  BtorMemMgr *mm;
  BtorIntHashTable *cache;
  BtorIntHashTableIterator it;
  BtorHashTableData *d;
  BtorAIGPtrStack stack;
  BtorIntStack *childparents;
  BtorAIG *root, *cur, *child;

  start      = btor_util_time_stamp ();
  sat_result = AIGPROP_UNKNOWN;
  nmoves     = 0;

  mm           = aprop->amgr->btor->mm;
  aprop->roots = roots;

  /* collect parents (for cone computation) */
  BTOR_INIT_STACK (mm, stack);
  cache = btor_hashint_map_new (mm);
  assert (!aprop->parents);
  aprop->parents = btor_hashint_map_new (mm);

  btor_iter_hashint_init (&it, roots);
  while (btor_iter_hashint_has_next (&it))
  {
    cur = btor_aig_get_by_id (aprop->amgr, btor_iter_hashint_next (&it));
    if (btor_aig_is_const (cur)) continue;
    BTOR_PUSH_STACK (stack, cur);
  }

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_AIG (BTOR_POP_STACK (stack));
    assert (!btor_aig_is_const (cur));

    if ((d = btor_hashint_map_get (cache, cur->id)) && d->as_int == 1) continue;

    if (!d)
    {
      btor_hashint_map_add (cache, cur->id);
      BTOR_PUSH_STACK (stack, cur);
      BTOR_NEW (mm, childparents);
      BTOR_INIT_STACK (mm, *childparents);
      btor_hashint_map_add (aprop->parents, cur->id)->as_ptr = childparents;
      if (btor_aig_is_and (cur))
      {
        for (i = 0; i < 2; i++)
        {
          child = btor_aig_get_by_id (aprop->amgr, cur->children[i]);
          if (!btor_aig_is_const (child)) BTOR_PUSH_STACK (stack, child);
        }
      }
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;
      if (btor_aig_is_var (cur)) continue;
      for (i = 0; i < 2; i++)
      {
        if (btor_aig_is_const (
                btor_aig_get_by_id (aprop->amgr, cur->children[i])))
          continue;
        childid = cur->children[i] < 0 ? -cur->children[i] : cur->children[i];
        assert (btor_hashint_map_contains (aprop->parents, childid));
        childparents = btor_hashint_map_get (aprop->parents, childid)->as_ptr;
        assert (childparents);
        BTOR_PUSH_STACK (*childparents, cur->id);
      }
    }
  }
  btor_hashint_map_delete (cache);
  BTOR_RELEASE_STACK (stack);

  /* generate initial model, all inputs are initialized with false */
  aigprop_generate_model (aprop, true);

  for (;;)
  {
    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert (!aprop->unsatroots);
    aprop->unsatroots = btor_hashint_map_new (mm);
    btor_iter_hashint_init (&it, roots);
    while (btor_iter_hashint_has_next (&it))
    {
      rootid = btor_iter_hashint_next (&it);
      root   = btor_aig_get_by_id (aprop->amgr, rootid);
      if (btor_aig_is_true (root)) continue;
      if (btor_aig_is_false (root)) goto UNSAT;
      if (btor_hashint_table_contains (aprop->roots, -rootid)) goto UNSAT;
      assert (aigprop_get_assignment_aig (aprop, root));
      if (!btor_hashint_map_contains (aprop->unsatroots, rootid)
          && aigprop_get_assignment_aig (aprop, root) == -1)
        btor_hashint_map_add (aprop->unsatroots, rootid);
    }

    /* compute initial score */
    compute_scores (aprop);

    if (!aprop->unsatroots->count) goto SAT;

    for (j = 0, max_steps = AIGPROP_MAXSTEPS (aprop->stats.restarts + 1);
         !aprop->use_restarts || j < max_steps;
         j++)
    {
      if (!(move (aprop, nmoves))) goto UNSAT;
      nmoves += 1;
      if (!aprop->unsatroots->count) goto SAT;
    }

    /* restart */
    aigprop_generate_model (aprop, true);
    btor_hashint_map_delete (aprop->score);
    aprop->score = 0;
    btor_hashint_map_delete (aprop->unsatroots);
    aprop->unsatroots = 0;
    aprop->stats.restarts += 1;
  }
SAT:
  sat_result = AIGPROP_SAT;
  goto DONE;
UNSAT:
  sat_result = AIGPROP_UNSAT;
DONE:
  btor_iter_hashint_init (&it, aprop->parents);
  while (btor_iter_hashint_has_next (&it))
  {
    childparents = btor_iter_hashint_next_data (&it)->as_ptr;
    assert (childparents);
    BTOR_RELEASE_STACK (*childparents);
    BTOR_DELETE (mm, childparents);
  }
  btor_hashint_map_delete (aprop->parents);
  aprop->parents = 0;
  if (aprop->unsatroots) btor_hashint_map_delete (aprop->unsatroots);
  aprop->unsatroots = 0;
  aprop->roots      = 0;
  if (aprop->score) btor_hashint_map_delete (aprop->score);
  aprop->score = 0;

  aprop->time.sat += btor_util_time_stamp () - start;
  return sat_result;
}

AIGProp *
aigprop_clone_aigprop (BtorAIGMgr *clone, AIGProp *aprop)
{
  assert (clone);

  AIGProp *res;
  BtorMemMgr *mm;

  if (!aprop) return 0;

  mm = clone->btor->mm;

  BTOR_CNEW (mm, res);
  memcpy (res, aprop, sizeof (AIGProp));
  res->amgr = clone;
  res->unsatroots =
      btor_hashint_map_clone (mm, aprop->unsatroots, btor_clone_data_as_int, 0);
  res->score =
      btor_hashint_map_clone (mm, aprop->score, btor_clone_data_as_dbl, 0);
  res->model =
      btor_hashint_map_clone (mm, aprop->model, btor_clone_data_as_int, 0);
  return res;
}

AIGProp *
aigprop_new_aigprop (BtorAIGMgr *amgr,
                     uint32_t loglevel,
                     uint32_t seed,
                     uint32_t use_restarts,
                     uint32_t use_bandit)
{
  assert (amgr);

  AIGProp *res;

  BTOR_CNEW (amgr->btor->mm, res);
  res->amgr = amgr;
  btor_rng_init (&res->rng, seed);
  res->loglevel     = loglevel;
  res->seed         = seed;
  res->use_restarts = use_restarts;
  res->use_bandit   = use_bandit;

  return res;
}

void
aigprop_delete_aigprop (AIGProp *aprop)
{
  assert (aprop);

  if (aprop->unsatroots) btor_hashint_map_delete (aprop->unsatroots);
  if (aprop->score) btor_hashint_map_delete (aprop->score);
  if (aprop->model) btor_hashint_map_delete (aprop->model);
  BTOR_DELETE (aprop->amgr->btor->mm, aprop);
}

#if 0
void
aigprop_print_stats (AIGProp * aprop)
{
  assert (aprop);
  msg ("");
  msg ("restarts: %d", aprop->stats.restarts);
  msg ("moves: %d", aprop->stats.moves);
}

void
aigprop_print_time_stats (AIGProp * aprop)
{
  assert (aprop);
  msg ("");
  msg ("%.2f seconds for sat call (AIG propagation)", aprop->time.sat);
}
#endif
