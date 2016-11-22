/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvpropsls.h"

#include "btorprintmodel.h"
#include "utils/btorexpiter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

#define BTOR_SLS_SCORE_CFACT 0.5     /* same as in Z3 (c1) */
#define BTOR_SLS_SCORE_F_CFACT 0.025 /* same as in Z3 (c3) */

static int
hamming_distance (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int res;
  BtorBitVector *bv, *bvdec = 0, *zero, *ones, *tmp;

  zero = btor_new_bv (btor->mm, bv1->width);
  ones = btor_ones_bv (btor->mm, bv1->width);
  bv   = btor_xor_bv (btor->mm, bv1, bv2);
  for (res = 0; !btor_is_zero_bv (bv); res++)
  {
    bvdec = btor_add_bv (btor->mm, bv, ones);
    tmp   = bv;
    bv    = btor_and_bv (btor->mm, bv, bvdec);
    btor_free_bv (btor->mm, tmp);
    btor_free_bv (btor->mm, bvdec);
  }
  btor_free_bv (btor->mm, bv);
  btor_free_bv (btor->mm, ones);
  btor_free_bv (btor->mm, zero);
  return res;
}

// TODO find a better heuristic this might be too expensive
// this is not necessarily the actual minimum, but the minimum if you flip
// bits in bv1 s.t. bv1 < bv2 (if bv2 is 0, we need to flip 1 bit in bv2, too)
static int
min_flip (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int i, res;
  BtorBitVector *tmp;

  if (btor_is_zero_bv (bv2))
    res = hamming_distance (btor, bv1, bv2) + 1;
  else
  {
    tmp = btor_copy_bv (btor->mm, bv1);
    for (res = 1, i = tmp->width - 1; i >= 0; i--)
    {
      if (!btor_get_bit_bv (tmp, i)) continue;
      res += 1;
      btor_set_bit_bv (tmp, i, 0);
      if (btor_compare_bv (tmp, bv2) < 0) break;
    }
    if (btor_is_zero_bv (bv2)) res += 1;
    btor_free_bv (btor->mm, tmp);
  }
  return res;
}

static int
min_flip_inv (Btor *btor, BtorBitVector *bv1, BtorBitVector *bv2)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bv1->len == bv2->len);

  int i, res;
  BtorBitVector *tmp;

  tmp = btor_copy_bv (btor->mm, bv1);
  for (res = 1, i = tmp->width - 1; i >= 0; i--)
  {
    if (btor_get_bit_bv (tmp, i)) continue;
    res += 1;
    btor_set_bit_bv (tmp, i, 1);
    if (btor_compare_bv (tmp, bv2) >= 0) break;
  }
  btor_free_bv (btor->mm, tmp);
  return res;
}

/* score
 *
 *  Boolean variable:
 *    s (e[1], A) = A (e[1])
 *
 *  bw m >= 1:
 *
 *    score (e0[bw] /\ e1[bw], A)    =
 *        1/2 * (score (e0[bw], A) + score (e1[bw], A))
 *
 *    score (-(-e0[bw] /\ ... /\ -e1[bw]), A) =
 *        max (score (-e0[bw], A), score (-e1[bw], A))
 *
 *    score (e0[bw] = e1[bw], A) =
 *        (A (e0) == A (e1))
 *      ? 1.0
 *      : c1 * (1 - (h (A(e0), A(e1)) / bw)
 *
 *    score (e0[bw] != e1[bw], A) =
 *        (A (e0) == A (e1) ? 0.0 : 1.0
 *
 *    s (e0[bw] < e1[bw], A) =
 *        (A (e0) < A (e1))
 *      ? 1.0
 *      : c1 * (1 - (min number of bits to flip s.t. e0[bw] < e1[bw]) / bw)
 */
static double
compute_sls_score_node (Btor *btor,
                        BtorIntHashTable *bv_model,
                        BtorIntHashTable *fun_model,
                        BtorIntHashTable *score,
                        BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (exp);
  assert (btor_get_exp_width (btor, exp) == 1);

  double res, s0, s1;
  BtorNode *real_exp;
  BtorBitVector *bv0, *bv1;
#ifndef NBTORLOG
  BtorMemMgr *mm;
  char *a0, *a1;
  mm = btor->mm;
#endif

  res      = 0.0;
  real_exp = BTOR_REAL_ADDR_NODE (exp);

  BTORLOG (3, "");
  BTORLOG (3, "*** compute sls score for: %s", node2string (exp));

  if (btor_is_and_node (real_exp))
  {
    /* OR --------------------------------------------------------- */
    if (BTOR_IS_INVERTED_NODE (exp))
    {
      assert (btor_contains_int_hash_map (score,
                                          -btor_exp_get_id ((real_exp->e[0]))));
      assert (btor_contains_int_hash_map (score,
                                          -btor_exp_get_id ((real_exp->e[1]))));
      s0 = btor_get_int_hash_map (score, -btor_exp_get_id ((real_exp->e[0])))
               ->as_dbl;
      s1 = btor_get_int_hash_map (score, -btor_exp_get_id ((real_exp->e[1])))
               ->as_dbl;
#ifndef NBTORLOG
      if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
      {
        a0 = (char *) btor_get_bv_model_str_aux (
            btor, bv_model, fun_model, BTOR_INVERT_NODE (real_exp->e[0]));
        a1 = (char *) btor_get_bv_model_str_aux (
            btor, bv_model, fun_model, BTOR_INVERT_NODE (real_exp->e[1]));
        BTORLOG (3, "      assignment e[0]: %s", a0);
        BTORLOG (3, "      assignment e[1]: %s", a1);
        btor_freestr (mm, a0);
        btor_freestr (mm, a1);
        BTORLOG (3, "      sls score e[0]: %f", s0);
        BTORLOG (3, "      sls score e[1]: %f", s1);
      }
#endif
      res = s0 > s1 ? s0 : s1;
    }
    /* AND -------------------------------------------------------- */
    else
    {
      assert (btor_contains_int_hash_map (score,
                                          btor_exp_get_id ((real_exp->e[0]))));
      assert (btor_contains_int_hash_map (score,
                                          btor_exp_get_id ((real_exp->e[1]))));
      s0 = btor_get_int_hash_map (score, btor_exp_get_id ((real_exp->e[0])))
               ->as_dbl;
      s1 = btor_get_int_hash_map (score, btor_exp_get_id ((real_exp->e[1])))
               ->as_dbl;
#ifndef NBTORLOG
      if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
      {
        a0 = (char *) btor_get_bv_model_str_aux (
            btor, bv_model, fun_model, real_exp->e[0]);
        a1 = (char *) btor_get_bv_model_str_aux (
            btor, bv_model, fun_model, real_exp->e[1]);
        BTORLOG (3, "      assignment e[0]: %s", a0);
        BTORLOG (3, "      assignment e[1]: %s", a1);
        btor_freestr (mm, a0);
        btor_freestr (mm, a1);
        BTORLOG (3, "      sls score e[0]: %f", s0);
        BTORLOG (3, "      sls score e[1]: %f", s1);
      }
#endif
      res = (s0 + s1) / 2.0;
      /* fix rounding errors (eg. (0.999+1.0)/2 = 1.0) ->
         choose minimum (else it might again result in 1.0) */
      if (res == 1.0 && (s0 < 1.0 || s1 < 1.0)) res = s0 < s1 ? s0 : s1;
    }
  }
  /* EQ --------------------------------------------------------- */
  else if (btor_is_bv_eq_node (real_exp))
  {
    bv0 = (BtorBitVector *) btor_get_bv_model_aux (
        btor, bv_model, fun_model, real_exp->e[0]);
    bv1 = (BtorBitVector *) btor_get_bv_model_aux (
        btor, bv_model, fun_model, real_exp->e[1]);
#ifndef NBTORLOG
    if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
    {
      a0 = (char *) btor_get_bv_model_str_aux (
          btor, bv_model, fun_model, real_exp->e[0]);
      a1 = (char *) btor_get_bv_model_str_aux (
          btor, bv_model, fun_model, real_exp->e[1]);
      BTORLOG (3, "      assignment e[0]: %s", a0);
      BTORLOG (3, "      assignment e[1]: %s", a1);
      btor_freestr (mm, a0);
      btor_freestr (mm, a1);
    }
#endif
    if (BTOR_IS_INVERTED_NODE (exp))
      res = !btor_compare_bv (bv0, bv1) ? 0.0 : 1.0;
    else
      res = !btor_compare_bv (bv0, bv1)
                ? 1.0
                : BTOR_SLS_SCORE_CFACT
                      * (1.0
                         - hamming_distance (btor, bv0, bv1)
                               / (double) bv0->width);
  }
  /* ULT -------------------------------------------------------- */
  else if (btor_is_ult_node (real_exp))
  {
    bv0 = (BtorBitVector *) btor_get_bv_model_aux (
        btor, bv_model, fun_model, real_exp->e[0]);
    bv1 = (BtorBitVector *) btor_get_bv_model_aux (
        btor, bv_model, fun_model, real_exp->e[1]);
#ifndef NBTORLOG
    if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
    {
      a0 = (char *) btor_get_bv_model_str_aux (
          btor, bv_model, fun_model, real_exp->e[0]);
      a1 = (char *) btor_get_bv_model_str_aux (
          btor, bv_model, fun_model, real_exp->e[1]);
      BTORLOG (3, "      assignment e[0]: %s", a0);
      BTORLOG (3, "      assignment e[1]: %s", a1);
      btor_freestr (mm, a0);
      btor_freestr (mm, a1);
    }
#endif
    if (BTOR_IS_INVERTED_NODE (exp))
      res = btor_compare_bv (bv0, bv1) >= 0
                ? 1.0
                : BTOR_SLS_SCORE_CFACT
                      * (1.0
                         - min_flip_inv (btor, bv0, bv1) / (double) bv0->width);
    else
      res = btor_compare_bv (bv0, bv1) < 0
                ? 1.0
                : BTOR_SLS_SCORE_CFACT
                      * (1.0 - min_flip (btor, bv0, bv1) / (double) bv0->width);
  }
  /* other BOOLEAN ---------------------------------------------- */
  else
  {
    assert (btor_get_exp_width (btor, real_exp) == 1);
#ifndef NBTORLOG
    if (btor_get_opt (btor, BTOR_OPT_LOGLEVEL) >= 2)
    {
      a0 = (char *) btor_get_bv_model_str_aux (btor, bv_model, fun_model, exp);
      BTORLOG (3, "      assignment : %s", a0);
      btor_freestr (mm, a0);
    }
#endif
    res = ((BtorBitVector *) btor_get_bv_model_aux (
               btor, bv_model, fun_model, exp))
              ->bits[0];
  }

  BTORLOG (3, "      sls score : %f", res);
  return res;
}

static double
recursively_compute_sls_score_node (Btor *btor,
                                    BtorIntHashTable *bv_model,
                                    BtorIntHashTable *fun_model,
                                    BtorIntHashTable *score,
                                    BtorNode *exp)
{
  assert (btor);
  assert (bv_model);
  assert (fun_model);
  assert (score);
  assert (exp);

  int i;
  double res;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;

  res = 0.0;
  assert (btor_is_bv_eq_node (exp) || btor_is_ult_node (exp)
          || btor_get_exp_width (btor, exp) == 1);

  if (btor_contains_int_hash_map (score, btor_exp_get_id (exp)))
    return btor_get_int_hash_map (score, btor_exp_get_id (exp))->as_dbl;

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  mark = btor_new_int_hash_map (mm);

  BTOR_PUSH_STACK (mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    d        = btor_get_int_hash_map (mark, real_cur->id);

    if ((d && d->as_int == 1)
        || btor_get_int_hash_map (score, btor_exp_get_id (cur)))
      continue;

    if (!d)
    {
      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;

      if (btor_get_exp_width (btor, real_cur) != 1) continue;

      res = compute_sls_score_node (btor, bv_model, fun_model, score, cur);

      assert (!btor_contains_int_hash_map (score, btor_exp_get_id (cur)));
      btor_add_int_hash_map (score, btor_exp_get_id (cur))->as_dbl = res;
    }
  }

  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_int_hash_map (mark);

  assert (btor_contains_int_hash_map (score, btor_exp_get_id (exp)));
  assert (res == btor_get_int_hash_map (score, btor_exp_get_id (exp))->as_dbl);
  return res;
}

void
btor_propsls_compute_sls_scores (Btor *btor,
                                 BtorIntHashTable *bv_model,
                                 BtorIntHashTable *fun_model,
                                 BtorIntHashTable *score)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);
  assert (bv_model);
  assert (fun_model);
  assert (score);

  int i;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack stack;
  BtorPtrHashTableIterator pit;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorMemMgr *mm;

  BTORLOG (3, "");
  BTORLOG (3, "**** compute sls scores ***");

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  mark = btor_new_int_hash_map (mm);

  /* collect roots */
  btor_init_ptr_hash_table_iterator (&pit, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&pit, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&pit))
    BTOR_PUSH_STACK (mm, stack, btor_next_ptr_hash_table_iterator (&pit));

  /* compute score */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    d        = btor_get_int_hash_map (mark, real_cur->id);

    if ((d && d->as_int == 1)
        || btor_contains_int_hash_map (score, btor_exp_get_id (cur)))
      continue;

    if (!d)
    {
      btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
    else
    {
      assert (d->as_int == 0);
      d->as_int = 1;
      if (btor_get_exp_width (btor, real_cur) != 1) continue;
      (void) recursively_compute_sls_score_node (
          btor, bv_model, fun_model, score, cur);
      (void) recursively_compute_sls_score_node (
          btor, bv_model, fun_model, score, BTOR_INVERT_NODE (cur));
    }
  }

  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_int_hash_map (mark);
}

/*========================================================================*/

static inline void
update_roots_table (Btor *btor,
                    BtorIntHashTable *roots,
                    BtorNode *exp,
                    BtorBitVector *bv)
{
  assert (btor);
  assert (roots);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (bv);
  assert (btor_compare_bv (btor_get_bv_model (btor, exp), bv));

  (void) btor;

  /* exp: old assignment = 0, new assignment = 1 (bv = 1)
   *      -> satisfied, remove */
  if (btor_get_int_hash_map (roots, exp->id))
  {
    btor_remove_int_hash_map (roots, exp->id, 0);
    assert (btor_is_false_bv (btor_get_bv_model (btor, exp)));
    assert (btor_is_true_bv (bv));
  }
  /* -exp: old assignment = 0, new assignment = 1 (bv = 0)
   * -> satisfied, remove */
  else if (btor_get_int_hash_map (roots, -exp->id))
  {
    btor_remove_int_hash_map (roots, -exp->id, 0);
    assert (
        btor_is_false_bv (btor_get_bv_model (btor, BTOR_INVERT_NODE (exp))));
    assert (btor_is_false_bv (bv));
  }
  /* exp: old assignment = 1, new assignment = 0 (bv = 0)
   * -> unsatisfied, add */
  else if (btor_is_false_bv (bv))
  {
    btor_add_int_hash_map (roots, exp->id);
    assert (btor_is_true_bv (btor_get_bv_model (btor, exp)));
  }
  /* -exp: old assignment = 1, new assignment = 0 (bv = 1)
   * -> unsatisfied, add */
  else
  {
    assert (btor_is_true_bv (bv));
    btor_add_int_hash_map (roots, -exp->id);
    assert (btor_is_true_bv (btor_get_bv_model (btor, BTOR_INVERT_NODE (exp))));
  }
}

/* Note: 'roots' will only be updated if 'update_roots' is true.
 *         + PROP engine: always
 *         + SLS  engine: only if an actual move is performed
 *                        (not during neighborhood exploration, 'try_move')
 *       -> assertion code guarded with '#ifndef NDEBUG' is therefore
 *          always valid since 'roots' always maintains a valid state
 *          ('try_move' of the SLS engine is the only case where 'roots'
 *           might become globally invalid, i.e., when a tried move
 *           is not actually performed, however in that particular case
 *           we do not update 'roots') */
void
btor_propsls_update_cone (Btor *btor,
                          BtorIntHashTable *bv_model,
                          BtorIntHashTable *roots,
                          BtorIntHashTable *score,
                          BtorIntHashTable *exps,
                          bool update_roots,
                          uint64_t *stats_updates,
                          double *time_update_cone,
                          double *time_update_cone_reset,
                          double *time_update_cone_model_gen,
                          double *time_update_cone_compute_score)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);
  assert (bv_model);
  assert (roots);
  assert (exps);
  assert (exps->count);
  assert (btor_get_opt (btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_PROP
          || update_roots);
  assert (time_update_cone);
  assert (time_update_cone_reset);
  assert (time_update_cone_model_gen);

  double start, delta;
  uint32_t i, j;
  int32_t id;
  BtorNode *exp, *cur;
  BtorNodeIterator nit;
  BtorIntHashTableIterator iit;
  BtorHashTableData *d;
  BtorNodePtrStack stack, cone;
  BtorIntHashTable *cache;
  BtorBitVector *bv, *e[3], *ass;
  BtorMemMgr *mm;

  start = delta = btor_time_stamp ();

  mm = btor->mm;

#ifndef NDEBUG
  BtorPtrHashTableIterator pit;
  BtorNode *root;
  btor_init_ptr_hash_table_iterator (&pit, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&pit, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&pit))
  {
    root = btor_next_ptr_hash_table_iterator (&pit);
    assert (!btor_get_ptr_hash_table (btor->unsynthesized_constraints,
                                      BTOR_INVERT_NODE (root)));
    assert (
        !btor_get_ptr_hash_table (btor->assumptions, BTOR_INVERT_NODE (root)));
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (roots, btor_exp_get_id (root)));
    else
      assert (!btor_contains_int_hash_map (roots, btor_exp_get_id (root)));
  }
#endif

  /* reset cone ----------------------------------------------------------- */

  BTOR_INIT_STACK (cone);
  BTOR_INIT_STACK (stack);
  btor_init_int_hash_table_iterator (&iit, exps);
  while (btor_has_next_int_hash_table_iterator (&iit))
  {
    exp = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&iit));
    assert (BTOR_IS_REGULAR_NODE (exp));
    assert (btor_is_bv_var_node (exp));
    BTOR_PUSH_STACK (btor->mm, stack, exp);
  }
  cache = btor_new_int_hash_table (mm);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (btor_contains_int_hash_table (cache, cur->id)) continue;
    btor_add_int_hash_table (cache, cur->id);
    if (!btor_contains_int_hash_table (exps, cur->id))
      BTOR_PUSH_STACK (mm, cone, cur);
    *stats_updates += 1;

    /* push parents */
    btor_init_parent_iterator (&nit, cur);
    while (btor_has_next_parent_iterator (&nit))
      BTOR_PUSH_STACK (mm, stack, btor_next_parent_iterator (&nit));
  }
  BTOR_RELEASE_STACK (mm, stack);
  btor_delete_int_hash_table (cache);

  *time_update_cone_reset += btor_time_stamp () - delta;

  /* update assignment and score of exps ----------------------------------- */

  btor_init_int_hash_table_iterator (&iit, exps);
  while (btor_has_next_int_hash_table_iterator (&iit))
  {
    ass = (BtorBitVector *) exps->data[iit.cur_pos].as_ptr;
    exp = btor_get_node_by_id (btor, btor_next_int_hash_table_iterator (&iit));

    /* update model */
    d = btor_get_int_hash_map (bv_model, exp->id);
    assert (d);
    if (update_roots
        && (exp->constraint || btor_get_ptr_hash_table (btor->assumptions, exp)
            || btor_get_ptr_hash_table (btor->assumptions,
                                        BTOR_INVERT_NODE (exp)))
        && btor_compare_bv (d->as_ptr, ass))
    {
      /* old assignment != new assignment */
      update_roots_table (btor, roots, exp, ass);
    }
    btor_free_bv (mm, d->as_ptr);
    d->as_ptr = btor_copy_bv (mm, ass);
    if ((d = btor_get_int_hash_map (bv_model, -exp->id)))
    {
      btor_free_bv (mm, d->as_ptr);
      d->as_ptr = btor_not_bv (mm, ass);
    }

    /* update score */
    if (score && btor_get_exp_width (btor, exp) == 1)
    {
      assert (btor_contains_int_hash_map (score, btor_exp_get_id (exp)));
      btor_get_int_hash_map (score, btor_exp_get_id (exp))->as_dbl =
          compute_sls_score_node (btor, bv_model, btor->fun_model, score, exp);

      assert (btor_contains_int_hash_map (score, -btor_exp_get_id (exp)));
      btor_get_int_hash_map (score, -btor_exp_get_id (exp))->as_dbl =
          compute_sls_score_node (
              btor, bv_model, btor->fun_model, score, BTOR_INVERT_NODE (exp));
    }
  }

  qsort (cone.start,
         BTOR_COUNT_STACK (cone),
         sizeof (BtorNode *),
         btor_compare_exp_by_id_qsort_asc);

  /* update model of cone ------------------------------------------------- */

  delta = btor_time_stamp ();

  for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
  {
    cur = BTOR_PEEK_STACK (cone, i);
    assert (BTOR_IS_REGULAR_NODE (cur));
    for (j = 0; j < cur->arity; j++)
    {
      if (btor_is_bv_const_node (cur->e[j]))
      {
        e[j] = BTOR_IS_INVERTED_NODE (cur->e[j])
                   ? btor_copy_bv (mm, btor_const_get_invbits (cur->e[j]))
                   : btor_copy_bv (mm, btor_const_get_bits (cur->e[j]));
      }
      else
      {
        d = btor_get_int_hash_map (bv_model,
                                   BTOR_REAL_ADDR_NODE (cur->e[j])->id);
        /* Note: generate model enabled branch for ite (and does not
         * generate model for nodes in the branch, hence !b may happen */
        if (!d)
          e[j] = btor_recursively_compute_assignment (
              btor, bv_model, btor->fun_model, cur->e[j]);
        else
          e[j] = BTOR_IS_INVERTED_NODE (cur->e[j])
                     ? btor_not_bv (mm, d->as_ptr)
                     : btor_copy_bv (mm, d->as_ptr);
      }
    }
    switch (cur->kind)
    {
      case BTOR_ADD_NODE: bv = btor_add_bv (mm, e[0], e[1]); break;
      case BTOR_AND_NODE: bv = btor_and_bv (mm, e[0], e[1]); break;
      case BTOR_BV_EQ_NODE: bv = btor_eq_bv (mm, e[0], e[1]); break;
      case BTOR_ULT_NODE: bv = btor_ult_bv (mm, e[0], e[1]); break;
      case BTOR_SLL_NODE: bv = btor_sll_bv (mm, e[0], e[1]); break;
      case BTOR_SRL_NODE: bv = btor_srl_bv (mm, e[0], e[1]); break;
      case BTOR_MUL_NODE: bv = btor_mul_bv (mm, e[0], e[1]); break;
      case BTOR_UDIV_NODE: bv = btor_udiv_bv (mm, e[0], e[1]); break;
      case BTOR_UREM_NODE: bv = btor_urem_bv (mm, e[0], e[1]); break;
      case BTOR_CONCAT_NODE: bv = btor_concat_bv (mm, e[0], e[1]); break;
      case BTOR_SLICE_NODE:
        bv = btor_slice_bv (
            mm, e[0], btor_slice_get_upper (cur), btor_slice_get_lower (cur));
        break;
      default:
        assert (btor_is_cond_node (cur));
        bv = btor_is_true_bv (e[0]) ? btor_copy_bv (mm, e[1])
                                    : btor_copy_bv (mm, e[2]);
    }

    /* update assignment */

    d = btor_get_int_hash_map (bv_model, cur->id);

    /* update roots table */
    if (update_roots
        && (cur->constraint || btor_get_ptr_hash_table (btor->assumptions, cur)
            || btor_get_ptr_hash_table (btor->assumptions,
                                        BTOR_INVERT_NODE (cur))))
    {
      assert (d); /* must be contained, is root */
      /* old assignment != new assignment */
      if (btor_compare_bv (d->as_ptr, bv))
        update_roots_table (btor, roots, cur, bv);
    }

    /* update assignments */
    /* Note: generate model enabled branch for ite (and does not generate
     *       model for nodes in the branch, hence !b may happen */
    if (!d)
    {
      btor_copy_exp (btor, cur);
      btor_add_int_hash_map (bv_model, cur->id)->as_ptr = bv;
    }
    else
    {
      btor_free_bv (mm, d->as_ptr);
      d->as_ptr = bv;
    }

    if ((d = btor_get_int_hash_map (bv_model, -cur->id)))
    {
      btor_free_bv (mm, d->as_ptr);
      d->as_ptr = btor_not_bv (mm, bv);
    }
    /* cleanup */
    for (j = 0; j < cur->arity; j++) btor_free_bv (mm, e[j]);
  }
  *time_update_cone_model_gen += btor_time_stamp () - delta;

  /* update score of cone ------------------------------------------------- */

  if (score)
  {
    delta = btor_time_stamp ();
    for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
    {
      cur = BTOR_PEEK_STACK (cone, i);
      assert (BTOR_IS_REGULAR_NODE (cur));

      if (btor_get_exp_width (btor, cur) != 1) continue;

      id = btor_exp_get_id (cur);
      if (!btor_contains_int_hash_map (score, id))
      {
        /* not reachable from the roots */
        assert (!btor_contains_int_hash_map (score, -id));
        continue;
      }
      btor_get_int_hash_map (score, id)->as_dbl =
          compute_sls_score_node (btor, bv_model, btor->fun_model, score, cur);
      assert (btor_contains_int_hash_map (score, -id));
      btor_get_int_hash_map (score, -id)->as_dbl = compute_sls_score_node (
          btor, bv_model, btor->fun_model, score, BTOR_INVERT_NODE (cur));
    }
    *time_update_cone_compute_score += btor_time_stamp () - delta;
  }

  BTOR_RELEASE_STACK (mm, cone);

#ifndef NDEBUG
  btor_init_ptr_hash_table_iterator (&pit, btor->unsynthesized_constraints);
  btor_queue_ptr_hash_table_iterator (&pit, btor->assumptions);
  while (btor_has_next_ptr_hash_table_iterator (&pit))
  {
    root = btor_next_ptr_hash_table_iterator (&pit);
    if (btor_is_false_bv (btor_get_bv_model (btor, root)))
      assert (btor_contains_int_hash_map (roots, btor_exp_get_id (root)));
    else
      assert (!btor_contains_int_hash_map (roots, btor_exp_get_id (root)));
  }
#endif
  *time_update_cone += btor_time_stamp () - start;
}

/*========================================================================*/

static inline int
select_path_non_const (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (exp->arity <= 2);
  assert (!btor_is_bv_const_node (exp->e[0])
          || (exp->arity > 1 && !btor_is_bv_const_node (exp->e[1])));

  int i, eidx;

  for (i = 0, eidx = -1; i < exp->arity; i++)
    if (btor_is_bv_const_node (exp->e[i]))
    {
      eidx = i ? 0 : 1;
      break;
    }
  assert (exp->arity == 1 || !btor_is_bv_const_node (exp->e[i ? 0 : 1]));
  return eidx;
}

static inline int
select_path_random (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return (int) btor_pick_rand_rng (&btor->rng, 0, exp->arity - 1);
}

static inline int
select_path_add (Btor *btor,
                 BtorNode *add,
                 BtorBitVector *bvadd,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);

  (void) bvadd;
  (void) bve;

  int eidx;

  eidx = select_path_non_const (add);
  if (eidx == -1) eidx = select_path_random (btor, add);
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (add));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (add->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (add->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_and (Btor *btor,
                 BtorNode *and,
                 BtorBitVector *bvand,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);

  uint32_t opt;
  int i, eidx;
  BtorBitVector *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (and);

  if (eidx == -1)
  {
    opt = btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL);

    if (opt == BTOR_PROP_PATH_SEL_RANDOM)
    {
      eidx = select_path_random (btor, and);
    }
    else if (btor_get_exp_width (btor, and) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < and->arity; i++)
        if (btor_is_zero_bv (bve[i])) eidx = eidx == -1 ? i : -1;
      if (eidx == -1) eidx = select_path_random (btor, and);
    }
    else if (opt == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      /* 1) all bits set in bvand must be set in both inputs, but
       * 2) all bits NOT set in bvand can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < and->arity; i++)
      {
        tmp = btor_and_bv (mm, bvand, bve[i]);
        if (btor_compare_bv (tmp, bvand)) eidx = eidx == -1 ? i : -1;
        btor_free_bv (mm, tmp);
      }
    }
    if (eidx == -1) eidx = select_path_random (btor, and);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (and));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (and->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (and->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_eq (Btor *btor,
                BtorNode *eq,
                BtorBitVector *bveq,
                BtorBitVector **bve)
{
  assert (btor);
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bve);

  (void) bveq;
  (void) bve;

  int eidx;
  eidx = select_path_non_const (eq);
  if (eidx == -1) eidx = select_path_random (btor, eq);
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (eq));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (eq->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (eq->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_ult (Btor *btor,
                 BtorNode *ult,
                 BtorBitVector *bvult,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bve);

  int eidx;
  BtorBitVector *bvmax;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (ult);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax = btor_ones_bv (mm, bve[0]->width);
      if (btor_is_one_bv (bvult))
      {
        /* 1...1 < bve[1] */
        if (!btor_compare_bv (bve[0], bvmax)) eidx = 0;
        /* bve[0] < 0 */
        if (btor_is_zero_bv (bve[1])) eidx = eidx == -1 ? 1 : -1;
      }
      btor_free_bv (mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random (btor, ult);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (ult));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (ult->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (ult->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_sll (Btor *btor,
                 BtorNode *sll,
                 BtorBitVector *bvsll,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);

  int eidx;
  uint64_t i, j, shift;

  eidx = select_path_non_const (sll);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      shift = btor_bv_to_uint64_bv (bve[1]);
      /* bve[1] and number of LSB 0-bits in bvsll must match */
      for (i = 0; i < shift; i++)
        if (btor_get_bit_bv (bvsll, i))
        {
          eidx = 1;
          goto DONE;
        }
      /* bve[0] and bvsll (except for the bits shifted out) must match */
      for (i = 0, j = shift; i < bvsll->width - j; i++)
        if (btor_get_bit_bv (bve[0], i) != btor_get_bit_bv (bvsll, j + i))
        {
          eidx = eidx == -1 ? 0 : -1;
          break;
        }
    }
    if (eidx == -1) eidx = select_path_random (btor, sll);
  }
DONE:
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (sll));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (sll->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (sll->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_srl (Btor *btor,
                 BtorNode *srl,
                 BtorBitVector *bvsrl,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);

  int eidx;
  uint64_t i, j, shift;

  eidx = select_path_non_const (srl);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      shift = btor_bv_to_uint64_bv (bve[1]);
      /* bve[1] and number of MSB 0-bits in bvsrl must match */
      for (i = 0; i < shift; i++)
        if (btor_get_bit_bv (bvsrl, bvsrl->width - 1 - i))
        {
          eidx = 1;
          goto DONE;
        }
      /* bve[0] and bvsrl (except for the bits shifted out) must match */
      for (i = 0, j = shift; i < bvsrl->width - j; i++)
        if (btor_get_bit_bv (bve[0], bve[0]->width - 1 - i)
            != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
        {
          eidx = eidx == -1 ? 0 : -1;
          break;
        }
    }
    if (eidx == -1) eidx = select_path_random (btor, srl);
  }
DONE:
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (srl));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (srl->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (srl->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_mul (Btor *btor,
                 BtorNode *mul,
                 BtorBitVector *bvmul,
                 BtorBitVector **bve)
{
  assert (btor);
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);

  uint32_t ctz_bvmul;
  int eidx, lsbve0, lsbve1;
  bool iszerobve0, iszerobve1;

  eidx = select_path_non_const (mul);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      iszerobve0 = btor_is_zero_bv (bve[0]);
      iszerobve1 = btor_is_zero_bv (bve[1]);

      lsbve0 = btor_get_bit_bv (bve[0], 0);
      lsbve1 = btor_get_bit_bv (bve[1], 0);

      /* either bve[0] or bve[1] are 0 but bvmul > 0 */
      if ((iszerobve0 || iszerobve1) && !btor_is_zero_bv (bvmul))
      {
        if (iszerobve0) eidx = 0;
        if (iszerobve1) eidx = eidx == -1 ? 1 : -1;
      }
      /* bvmul is odd but either bve[0] or bve[1] are even */
      else if (btor_get_bit_bv (bvmul, 0) && (!lsbve0 || !lsbve1))
      {
        if (!lsbve0) eidx = 0;
        if (!lsbve1) eidx = eidx == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in bvmul < number of 0-LSBs in bve[0|1] */
      else
      {
        ctz_bvmul = btor_get_num_trailing_zeros_bv (bvmul);
        if (ctz_bvmul < btor_get_num_trailing_zeros_bv (bve[0])) eidx = 0;
        if (ctz_bvmul < btor_get_num_trailing_zeros_bv (bve[1]))
          eidx = eidx == -1 ? 1 : -1;
      }
    }
    if (eidx == -1) eidx = select_path_random (btor, mul);
  }
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (mul));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (mul->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (mul->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_udiv (Btor *btor,
                  BtorNode *udiv,
                  BtorBitVector *bvudiv,
                  BtorBitVector **bve)
{
  assert (btor);
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);

  int eidx;
  int cmp_udiv_max;
  BtorBitVector *bvmax, *up, *lo, *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (udiv);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax        = btor_ones_bv (mm, bve[0]->width);
      cmp_udiv_max = btor_compare_bv (bvudiv, bvmax);

      /* bve[0] / bve[1] = 1...1 -> choose e[1]
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        eidx = 1;
      else
      {
        /* 1...1 / e[0] = 0 -> choose e[0] */
        if (btor_is_zero_bv (bvudiv) && !btor_compare_bv (bve[0], bvmax))
          eidx = 0;
        /* bve[0] < bvudiv -> choose e[0] */
        else if (btor_compare_bv (bve[0], bvudiv) < 0)
          eidx = 0;
        else
        {
          up  = btor_udiv_bv (mm, bve[0], bvudiv);
          lo  = btor_inc_bv (mm, bvudiv);
          tmp = btor_udiv_bv (mm, bve[0], lo);
          btor_free_bv (mm, lo);
          lo = btor_inc_bv (mm, tmp);

          if (btor_compare_bv (lo, up) > 0) eidx = 0;
          btor_free_bv (mm, up);
          btor_free_bv (mm, lo);
          btor_free_bv (mm, tmp);
        }

        /* e[0] / 0 != 1...1 -> choose e[1] */
        if (btor_is_zero_bv (bve[1]) || btor_is_umulo_bv (mm, bve[1], bvudiv))
          eidx = eidx == -1 ? 1 : -1;
      }
      btor_free_bv (mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random (btor, udiv);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (udiv));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (udiv->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (udiv->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_urem (Btor *btor,
                  BtorNode *urem,
                  BtorBitVector *bvurem,
                  BtorBitVector **bve)
{
  assert (btor);
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);

  int eidx;
  BtorBitVector *bvmax, *sub, *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (urem);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax = btor_ones_bv (mm, bve[0]->width);
      sub   = btor_sub_bv (mm, bve[0], bvurem);
      tmp   = btor_dec_bv (mm, bve[0]);

      /* bvurem = 1...1 -> bve[0] = 1...1 and bve[1] = 0...0 */
      if (!btor_compare_bv (bvurem, bvmax))
      {
        if (!btor_is_zero_bv (bve[1])) eidx = 1;
        if (btor_compare_bv (bve[0], bvmax)) eidx = eidx == -1 ? 0 : -1;
      }
      /* bvurem > 0 and bve[1] = 1 */
      else if (!btor_is_zero_bv (bvurem) && btor_is_one_bv (bve[1]))
      {
        eidx = 1;
      }
      /* 0 < bve[1] <= bvurem */
      else if (!btor_is_zero_bv (bve[1])
               && btor_compare_bv (bve[1], bvurem) <= 0)
      {
        eidx = eidx == -1 ? 1 : -1;
      }
      /* bve[0] < bvurem or
       * bve[0] > bvurem and bve[0] - bvurem <= bvurem or
       *                 and bve[0] - 1 = bvurem */
      else if (btor_compare_bv (bve[0], bvurem) < 0
               || (btor_compare_bv (bve[0], bvurem) > 0
                   && (btor_compare_bv (sub, bvurem) <= 0
                       || !btor_compare_bv (tmp, bvurem))))
      {
        eidx = 0;
      }

      btor_free_bv (mm, tmp);
      btor_free_bv (mm, bvmax);
      btor_free_bv (mm, sub);
    }

    if (eidx == -1) eidx = select_path_random (btor, urem);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (urem));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (urem->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (urem->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_concat (Btor *btor,
                    BtorNode *concat,
                    BtorBitVector *bvconcat,
                    BtorBitVector **bve)
{
  assert (btor);
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);

  int eidx;
  BtorBitVector *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (concat);

  if (eidx == -1)
  {
    if (btor_get_opt (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      /* bve[0] o bve[1] = bvconcat
       * -> bve[0] resp. bve[1] must match with bvconcat */
      tmp = btor_slice_bv (
          mm, bvconcat, bvconcat->width - 1, bvconcat->width - bve[0]->width);
      if (btor_compare_bv (tmp, bve[0])) eidx = 0;
      btor_free_bv (mm, tmp);
      tmp = btor_slice_bv (mm, bvconcat, bve[1]->width - 1, 0);
      if (btor_compare_bv (tmp, bve[1])) eidx = eidx == -1 ? 1 : -1;
      btor_free_bv (mm, tmp);
    }

    if (eidx == -1) eidx = select_path_random (btor, concat);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (concat));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (concat->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, bve[1]);
  BTORLOG (2, "       e[1]: %s (%s)", node2string (concat->e[1]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static inline int
select_path_slice (Btor *btor,
                   BtorNode *slice,
                   BtorBitVector *bvslice,
                   BtorBitVector **bve)
{
  assert (btor);
  assert (slice);
  assert (BTOR_IS_REGULAR_NODE (slice));
  assert (bvslice);
  assert (bve);

  assert (!btor_is_bv_const_node (slice->e[0]));

  (void) btor;
  (void) slice;
  (void) bvslice;
  (void) bve;
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (slice));
  a = btor_bv_to_char_bv (mm, bve[0]);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (slice->e[0]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: 0");
#endif

  return 0;
}

static inline int
select_path_cond (Btor *btor,
                  BtorNode *cond,
                  BtorBitVector *bvcond,
                  BtorBitVector *bve0)
{
  assert (btor);
  assert (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);
  assert (cond);
  assert (BTOR_IS_REGULAR_NODE (cond));
  assert (bvcond);
  assert (bve0);

  bool e1const, e2const;
  int32_t eidx;
  uint32_t prob;

  (void) bvcond;

  if (btor_is_bv_const_node (cond->e[0]))
    eidx = cond->e[0] == btor->true_exp ? 1 : 2;
  else
  {
    e1const = btor_is_bv_const_node (cond->e[1]);
    e2const = btor_is_bv_const_node (cond->e[2]);

    /* flip condition
     *
     * if either the 'then' or 'else' branch is const
     * with probability BTOR_OPT_PROP_FLIP_COND_CONST_PROB,
     * which is dynamically updated (depending on the number
     * times this case has already bin encountered)
     *
     * else with probability BTOR_OPT_PROP_FLIP_COND_PROB,
     * which is constant and will not be updated */
    if (((e1const && btor_is_true_bv (bve0))
         || (e2const && btor_is_false_bv (bve0)))
        && btor_pick_with_prob_rng (
               &btor->rng,
               (prob =
                    btor_get_opt (btor, BTOR_OPT_PROP_PROB_FLIP_COND_CONST))))
    {
      eidx = 0;

      if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
      {
        BtorPropSolver *slv;
        slv = BTOR_PROP_SOLVER (btor);
        if (++slv->nflip_cond_const
            == btor_get_opt (btor, BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          slv->nflip_cond_const = 0;
          slv->flip_cond_const_prob_delta =
              prob == 0
                  ? 100
                  : (prob == 1000 ? -100 : slv->flip_cond_const_prob_delta);
          btor_set_opt (btor,
                        BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
                        prob + slv->flip_cond_const_prob_delta);
        }
      }
      else
      {
        BtorSLSSolver *slv;
        slv = BTOR_SLS_SOLVER (btor);
        if (++slv->prop_nflip_cond_const
            == btor_get_opt (btor, BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          slv->prop_nflip_cond_const = 0;
          slv->prop_flip_cond_const_prob_delta =
              prob == 0 ? 100
                        : (prob == 1000 ? -100
                                        : slv->prop_flip_cond_const_prob_delta);
          btor_set_opt (btor,
                        BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
                        prob + slv->prop_flip_cond_const_prob_delta);
        }
      }
    }
    else if (btor_pick_with_prob_rng (
                 &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_FLIP_COND)))
    {
      eidx = 0;
    }
    /* assume cond to be fixed and select enabled branch */
    else
    {
      eidx = btor_is_true_bv (bve0) ? 1 : 2;
    }
  }

#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;

  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", node2string (cond));
  a = btor_bv_to_char_bv (mm, bve0);
  BTORLOG (2, "       e[0]: %s (%s)", node2string (cond->e[0]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, btor_get_bv_model (btor, cond->e[1]));
  BTORLOG (2, "       e[1]: %s (%s)", node2string (cond->e[1]), a);
  btor_freestr (mm, a);
  a = btor_bv_to_char_bv (mm, btor_get_bv_model (btor, cond->e[2]));
  BTORLOG (2, "       e[2]: %s (%s)", node2string (cond->e[2]), a);
  btor_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

/*------------------------------------------------------------------------*/

#ifdef NDEBUG
static inline BtorBitVector *inv_slice_bv (Btor *,
                                           BtorNode *,
                                           BtorBitVector *,
                                           BtorBitVector *);
#endif

static inline BtorBitVector *
cons_add_bv (Btor *btor,
             BtorNode *add,
             BtorBitVector *bvadd,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);
  assert (bve->width == bvadd->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (add->e[eidx]));

  (void) add;
  (void) bve;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_add++;
#endif
  return btor_new_random_bv (btor->mm, &btor->rng, bvadd->width);
}

static inline BtorBitVector *
cons_and_bv (Btor *btor,
             BtorNode *and,
             BtorBitVector *bvand,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);
  assert (bve->width == bvand->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (and->e[eidx]));

  uint32_t i;
  BtorBitVector *res;
  BtorUIntStack dcbits;
  bool b;

  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_and++;
#endif
  b = btor_pick_with_prob_rng (
      &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_AND_FLIP));
  BTOR_INIT_STACK (dcbits);

  res = btor_copy_bv (btor->mm, btor_get_bv_model (btor, and->e[eidx]));

  /* bve & res = bvand
   * -> all bits set in bvand must be set in res
   * -> all bits not set in bvand are chosen to be set randomly */
  for (i = 0; i < bvand->width; i++)
  {
    if (btor_get_bit_bv (bvand, i))
      btor_set_bit_bv (res, i, 1);
    else if (b)
      BTOR_PUSH_STACK (btor->mm, dcbits, i);
    else
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

  if (b && BTOR_COUNT_STACK (dcbits))
    btor_flip_bit_bv (
        res,
        BTOR_PEEK_STACK (
            dcbits,
            btor_pick_rand_rng (&btor->rng, 0, BTOR_COUNT_STACK (dcbits) - 1)));

  BTOR_RELEASE_STACK (btor->mm, dcbits);
  return res;
}

static inline BtorBitVector *
cons_eq_bv (
    Btor *btor, BtorNode *eq, BtorBitVector *bveq, BtorBitVector *bve, int eidx)
{
  assert (btor);
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bveq->width == 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (eq->e[eidx]));

  (void) bveq;

  BtorBitVector *res;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_eq++;
#endif

  if (btor_pick_with_prob_rng (&btor->rng,
                               btor_get_opt (btor, BTOR_OPT_PROP_PROB_EQ_FLIP)))
  {
    res = btor_copy_bv (btor->mm, btor_get_bv_model (btor, eq->e[eidx]));
    btor_flip_bit_bv (res, btor_pick_rand_rng (&btor->rng, 0, res->width - 1));
  }
  else
  {
    res = btor_new_random_bv (btor->mm, &btor->rng, bve->width);
  }
  return res;
}

static inline BtorBitVector *
cons_ult_bv (Btor *btor,
             BtorNode *ult,
             BtorBitVector *bvult,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bvult->width == 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BtorBitVector *bvmax, *zero, *tmp, *res;
  BtorMemMgr *mm;

  (void) ult;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_ult++;
#endif
  mm    = btor->mm;
  bw    = bve->width;
  isult = !btor_is_zero_bv (bvult);
  zero  = btor_new_bv (mm, bw);
  bvmax = btor_ones_bv (mm, bw);

  if (eidx && isult)
  {
    /* bve < res = 1  ->  res > 0 */
    tmp = btor_one_bv (mm, bw);
    res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
    btor_free_bv (mm, tmp);
  }
  else if (!eidx && isult)
  {
    /* res < bve = 1  ->  0 <= res < 1...1 */
    tmp = btor_dec_bv (mm, bvmax);
    res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, tmp);
    btor_free_bv (mm, tmp);
  }
  else
  {
    res = btor_new_random_bv (mm, &btor->rng, bw);
  }

  btor_free_bv (mm, bvmax);
  btor_free_bv (mm, zero);

  return res;
}

static inline BtorBitVector *
cons_sll_bv (Btor *btor,
             BtorNode *sll,
             BtorBitVector *bvsll,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsll->width);
  assert (eidx || btor_log_2_util (bvsll->width) == bve->width);
  assert (!btor_is_bv_const_node (sll->e[eidx]));

  uint32_t i, s, bw, sbw, ctz_bvsll;
  BtorBitVector *res, *from, *to, *shift;
  BtorMemMgr *mm;

  (void) sll;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_sll++;
#endif
  mm  = btor->mm;
  bw  = bvsll->width;
  sbw = btor_log_2_util (bw);

  ctz_bvsll = btor_get_num_trailing_zeros_bv (bvsll);
  from      = btor_new_bv (mm, sbw);
  to = btor_uint64_to_bv (mm, ctz_bvsll == bw ? ctz_bvsll - 1 : ctz_bvsll, sbw);
  shift = btor_new_random_range_bv (mm, &btor->rng, sbw, from, to);
  btor_free_bv (mm, from);
  btor_free_bv (mm, to);

  if (eidx)
  {
    res = shift;
  }
  else
  {
    s   = btor_bv_to_uint64_bv (shift);
    res = btor_srl_bv (mm, bvsll, shift);
    for (i = 0; i < s; i++)
      btor_set_bit_bv (res, bw - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
    btor_free_bv (mm, shift);
  }

  return res;
}

static inline BtorBitVector *
cons_srl_bv (Btor *btor,
             BtorNode *srl,
             BtorBitVector *bvsrl,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsrl->width);
  assert (eidx || btor_log_2_util (bvsrl->width) == bve->width);
  assert (!btor_is_bv_const_node (srl->e[eidx]));

  uint32_t i, s, bw, sbw;
  BtorBitVector *res, *from, *to, *shift;
  BtorMemMgr *mm;

  (void) srl;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_srl++;
#endif
  mm  = btor->mm;
  bw  = bvsrl->width;
  sbw = btor_log_2_util (bw);

  for (i = 0; i < bw; i++)
    if (btor_get_bit_bv (bvsrl, bw - 1 - i)) break;

  from  = btor_new_bv (mm, sbw);
  to    = btor_uint64_to_bv (mm, i == bw ? i - 1 : i, sbw);
  shift = btor_new_random_range_bv (mm, &btor->rng, sbw, from, to);
  btor_free_bv (mm, from);
  btor_free_bv (mm, to);

  if (eidx)
  {
    res = shift;
  }
  else
  {
    s   = btor_bv_to_uint64_bv (shift);
    res = btor_srl_bv (mm, bvsrl, shift);
    for (i = 0; i < s; i++)
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
    btor_free_bv (mm, shift);
  }

  return res;
}

static inline BtorBitVector *
cons_mul_bv (Btor *btor,
             BtorNode *mul,
             BtorBitVector *bvmul,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);
  assert (bve->width == bvmul->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (mul->e[eidx]));

  uint32_t r, bw, ctz_res, ctz_bvmul;
  BtorBitVector *res, *tmp;
  BtorMemMgr *mm;

  (void) mul;
  (void) bve;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_mul++;
#endif
  mm  = btor->mm;
  bw  = bvmul->width;
  res = btor_new_random_bv (mm, &btor->rng, bw);
  if (!btor_is_zero_bv (bvmul))
  {
    if (btor_is_zero_bv (res))
    {
      btor_free_bv (mm, res);
      res = btor_new_random_bv (mm, &btor->rng, bw);
    }
    /* bvmul odd -> choose odd value > 0 */
    if (btor_get_bit_bv (bvmul, 0))
    {
      if (!btor_get_bit_bv (res, 0)) btor_set_bit_bv (res, 0, 1);
    }
    /* bvmul even -> choose random value > 0
     *               with number of 0-LSBs in res less or equal
     *               than in bvmul */
    else
    {
      ctz_bvmul = btor_get_num_trailing_zeros_bv (bvmul);
      /* choose res as 2^n with ctz(bvmul) >= ctz(res) with prob 0.1 */
      if (btor_pick_with_prob_rng (&btor->rng, 100))
      {
        btor_free_bv (mm, res);
        res = btor_new_bv (mm, bw);
        btor_set_bit_bv (
            res, btor_pick_rand_rng (&btor->rng, 0, ctz_bvmul - 1), 1);
      }
      /* choose res as bvmul / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (btor_pick_with_prob_rng (&btor->rng, 100))
      {
        btor_free_bv (mm, res);
        if ((r = btor_pick_rand_rng (&btor->rng, 0, ctz_bvmul)))
        {
          tmp = btor_slice_bv (mm, bvmul, bw - 1, r);
          res = btor_uext_bv (mm, tmp, r);
          btor_free_bv (mm, tmp);
        }
        else
        {
          res = btor_copy_bv (mm, bvmul);
        }
      }
      /* choose random value with ctz(bvmul) >= ctz(res) with prob 0.8 */
      else
      {
        ctz_res = btor_get_num_trailing_zeros_bv (res);
        if (ctz_res > ctz_bvmul)
          btor_set_bit_bv (
              res, btor_pick_rand_rng (&btor->rng, 0, ctz_bvmul - 1), 1);
      }
    }
  }

  return res;
}

static inline BtorBitVector *
cons_udiv_bv (Btor *btor,
              BtorNode *udiv,
              BtorBitVector *bvudiv,
              BtorBitVector *bve,
              int eidx)
{
  assert (btor);
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (udiv->e[eidx]));

  uint32_t bw;
  BtorBitVector *res, *tmp, *tmpbve, *zero, *one, *bvmax;
  BtorMemMgr *mm;

  mm    = btor->mm;
  bw    = bvudiv->width;
  zero  = btor_new_bv (mm, bw);
  one   = btor_one_bv (mm, bw);
  bvmax = btor_ones_bv (mm, bw);

  (void) udiv;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_udiv++;
#endif
  if (eidx)
  {
    /* -> bvudiv = 1...1 then res = 0 or res = 1
     * -> else choose res s.t. res * bvudiv does not overflow */
    if (!btor_compare_bv (bvudiv, bvmax))
      res = btor_uint64_to_bv (mm, btor_pick_rand_rng (&btor->rng, 0, 1), bw);
    else
    {
      res = btor_new_random_range_bv (mm, &btor->rng, bw, one, bvmax);
      while (btor_is_umulo_bv (mm, res, bvudiv))
      {
        tmp = btor_sub_bv (mm, res, one);
        btor_free_bv (mm, res);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);
        btor_free_bv (mm, tmp);
      }
    }
  }
  else
  {
    /* -> bvudiv = 0 then res < 1...1
     * -> bvudiv = 1...1 then choose random res
     * -> else choose tmpbve s.t. res = tmpbve * bvudiv does not overflow */
    if (btor_is_zero_bv (bvudiv))
    {
      tmp = btor_dec_bv (mm, bvmax);
      res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, tmp);
      btor_free_bv (mm, tmp);
    }
    else if (!btor_compare_bv (bvudiv, bvmax))
    {
      res = btor_new_random_bv (mm, &btor->rng, bw);
    }
    else
    {
      tmpbve = btor_new_random_range_bv (mm, &btor->rng, bw, one, bvmax);
      while (btor_is_umulo_bv (mm, tmpbve, bvudiv))
      {
        tmp = btor_sub_bv (mm, tmpbve, one);
        btor_free_bv (mm, tmpbve);
        tmpbve = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);
        btor_free_bv (mm, tmp);
      }
      res = btor_mul_bv (mm, tmpbve, bvudiv);
      btor_free_bv (mm, tmpbve);
    }
  }

  btor_free_bv (mm, one);
  btor_free_bv (mm, zero);
  btor_free_bv (mm, bvmax);
  return res;
}

static inline BtorBitVector *
cons_urem_bv (Btor *btor,
              BtorNode *urem,
              BtorBitVector *bvurem,
              BtorBitVector *bve,
              int eidx)
{
  assert (btor);
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);
  assert (bve->width == bvurem->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (urem->e[eidx]));

  uint32_t bw;
  BtorBitVector *res, *bvmax, *tmp;
  BtorMemMgr *mm;

  (void) urem;
  (void) bve;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_urem++;
#endif
  mm    = btor->mm;
  bw    = bvurem->width;
  bvmax = btor_ones_bv (mm, bw);

  if (eidx)
  {
    /* bvurem = 1...1  ->  res = 0 */
    if (!btor_compare_bv (bvurem, bvmax))
    {
      res = btor_new_bv (mm, bw);
    }
    /* else res > bvurem */
    else
    {
      tmp = btor_inc_bv (mm, bvurem);
      res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
      btor_free_bv (mm, tmp);
    }
  }
  else
  {
    /* bvurem = 1...1  ->  res = 1...1 */
    if (!btor_compare_bv (bvurem, bvmax))
    {
      res = btor_copy_bv (mm, bvmax);
    }
    /* else res >= bvurem */
    else
    {
      res = btor_new_random_range_bv (mm, &btor->rng, bw, bvurem, bvmax);
    }
  }

  btor_free_bv (mm, bvmax);
  return res;
}

static inline BtorBitVector *
cons_concat_bv (Btor *btor,
                BtorNode *concat,
                BtorBitVector *bvconcat,
                BtorBitVector *bve,
                int eidx)
{
  assert (btor);
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (concat->e[eidx]));

  int32_t idx;
  uint32_t r;
  BtorBitVector *res;
  const BtorBitVector *bvcur;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_concat++;
#endif

  idx = eidx ? 0 : 1;

  /* If one operand is const, with BTOR_OPT_CONC_FLIP_PROB
   * either slice bits out of current assignment and flip max. one bit
   * randomly, or slice bits out of given assignment 'bve'.
   */

  if (btor_is_bv_const_node (concat->e[idx])
      && btor_pick_with_prob_rng (
             &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_CONC_FLIP)))
  {
    bvcur = btor_get_bv_model (btor, concat);
    res =
        eidx ? btor_slice_bv (
                   btor->mm, bvcur, bvconcat->width - bve->width - 1, 0)
             : btor_slice_bv (btor->mm, bvcur, bvconcat->width - 1, bve->width);
    r = btor_pick_rand_rng (&btor->rng, 0, res->width);
    if (r) btor_flip_bit_bv (res, r - 1);
  }
  else
  {
    res = eidx ? btor_slice_bv (
                     btor->mm, bvconcat, bvconcat->width - bve->width - 1, 0)
               : btor_slice_bv (
                     btor->mm, bvconcat, bvconcat->width - 1, bve->width);
  }
  return res;
}

static inline BtorBitVector *
cons_slice_bv (Btor *btor,
               BtorNode *slice,
               BtorBitVector *bvslice,
               BtorBitVector *bve)
{
#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.cons_slice++;
#endif
  return inv_slice_bv (btor, slice, bvslice, bve);
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static inline void
check_result_binary_dbg (Btor *btor,
                         BtorBitVector *(*fun) (BtorMemMgr *,
                                                const BtorBitVector *,
                                                const BtorBitVector *),
                         BtorNode *exp,
                         BtorBitVector *bve,
                         BtorBitVector *bvexp,
                         BtorBitVector *res,
                         int eidx,
                         char *op)
{
  assert (btor);
  assert (fun);
  assert (exp);
  assert (bve);
  assert (bvexp);
  assert (res);
  assert (op);

  (void) exp;
  (void) op;

  BtorBitVector *tmp;
  char *sbve, *sbvexp, *sres;

  tmp = eidx ? fun (btor->mm, bve, res) : fun (btor->mm, res, bve);
  assert (!btor_compare_bv (tmp, bvexp));
  sbvexp = btor_bv_to_char_bv (btor->mm, bvexp);
  sbve   = btor_bv_to_char_bv (btor->mm, bve);
  sres   = btor_bv_to_char_bv (btor->mm, res);
  BTORLOG (3,
           "prop (e[%d]): %s: %s := %s %s %s",
           eidx,
           node2string (exp),
           sbvexp,
           eidx ? sbve : sres,
           op,
           eidx ? sres : sbve);
  btor_free_bv (btor->mm, tmp);
  btor_freestr (btor->mm, sbvexp);
  btor_freestr (btor->mm, sbve);
  btor_freestr (btor->mm, sres);
}
#endif

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_add_bv (Btor *btor,
            BtorNode *add,
            BtorBitVector *bvadd,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (add);
  assert (BTOR_IS_REGULAR_NODE (add));
  assert (bvadd);
  assert (bve);
  assert (bve->width == bvadd->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (add->e[eidx]));

  BtorBitVector *res;

  (void) add;
  (void) eidx;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_add++;
#endif

  /* res + bve = bve + res = bvadd -> res = bvadd - bve */
  res = btor_sub_bv (btor->mm, bvadd, bve);
#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_add_bv, add, bve, bvadd, res, eidx, "+");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_and_bv (Btor *btor,
            BtorNode *and,
            BtorBitVector *bvand,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (and);
  assert (BTOR_IS_REGULAR_NODE (and));
  assert (bvand);
  assert (bve);
  assert (bve->width == bvand->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (and->e[eidx]));

  uint32_t i;
  int bitand, bite;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
  BtorUIntStack dcbits;
  bool b;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_and++;
#endif

  mm = btor->mm;
  e  = and->e[eidx ? 0 : 1];
  assert (e);

  b = btor_pick_with_prob_rng (
      &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_AND_FLIP));
  BTOR_INIT_STACK (dcbits);

  res = btor_copy_bv (mm, btor_get_bv_model (btor, and->e[eidx]));
  assert (res);

  for (i = 0; i < bvand->width; i++)
  {
    bitand = btor_get_bit_bv (bvand, i);
    bite   = btor_get_bit_bv (bve, i);

    /* CONFLICT: all bits set in bvand, must be set in bve -------------- */
    if (bitand&&!bite)
    {
      btor_free_bv (mm, res);
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = btor_propsls_non_rec_conf (btor, bve, bvand, eidx, "AND");
      }
      else
      {
        res = cons_and_bv (btor, and, bvand, bve, eidx);
        btor_propsls_rec_conf (btor);
      }
      goto DONE;
    }
    /* ^^--------------------------------------------------------------^^ */

    /* res & bve = bve & res = bvand
     * -> all bits set in bvand and bve must be set in res
     * -> all bits not set in bvand but set in bve must not be set in res
     * -> all bits not set in bve can be chosen to be set randomly */
    if (bitand)
      btor_set_bit_bv (res, i, 1);
    else if (bite)
      btor_set_bit_bv (res, i, 0);
    else if (b)
      BTOR_PUSH_STACK (mm, dcbits, i);
    else
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

  if (b && BTOR_COUNT_STACK (dcbits))
    btor_flip_bit_bv (
        res,
        BTOR_PEEK_STACK (
            dcbits,
            btor_pick_rand_rng (&btor->rng, 0, BTOR_COUNT_STACK (dcbits) - 1)));

#ifndef NDEBUG
  check_result_binary_dbg (
      btor, btor_and_bv, and, bve, bvand, res, eidx, "AND");
#endif

DONE:
  BTOR_RELEASE_STACK (mm, dcbits);
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_eq_bv (
    Btor *btor, BtorNode *eq, BtorBitVector *bveq, BtorBitVector *bve, int eidx)
{
  assert (btor);
  assert (eq);
  assert (BTOR_IS_REGULAR_NODE (eq));
  assert (bveq);
  assert (bveq->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (eq->e[eidx]));

  BtorBitVector *res;
  BtorMemMgr *mm;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_eq++;
#endif

  mm = btor->mm;

  /* res != bveq -> choose random res != bveq */
  if (btor_is_zero_bv (bveq))
  {
    if (btor_pick_with_prob_rng (
            &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_EQ_FLIP)))
    {
      res = 0;
      do
      {
        if (res) btor_free_bv (btor->mm, res);
        res = btor_copy_bv (btor->mm, btor_get_bv_model (btor, eq->e[eidx]));
        btor_flip_bit_bv (res,
                          btor_pick_rand_rng (&btor->rng, 0, res->width - 1));
      } while (!btor_compare_bv (res, bve));
    }
    else
    {
      res = 0;
      do
      {
        if (res) btor_free_bv (mm, res);
        res = btor_new_random_bv (mm, &btor->rng, bve->width);
      } while (!btor_compare_bv (res, bve));
    }
  }
  /* res = bveq */
  else
    res = btor_copy_bv (mm, bve);

#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_eq_bv, eq, bve, bveq, res, eidx, "=");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_ult_bv (Btor *btor,
            BtorNode *ult,
            BtorBitVector *bvult,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (ult);
  assert (BTOR_IS_REGULAR_NODE (ult));
  assert (bvult);
  assert (bvult->width = 1);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *zero, *one, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_ult++;
#endif
  mm = btor->mm;
  e  = ult->e[eidx ? 0 : 1];
  assert (e);

  zero  = btor_new_bv (mm, bve->width);
  one   = btor_one_bv (mm, bve->width);
  bvmax = btor_ones_bv (mm, bve->width);
  isult = !btor_is_zero_bv (bvult);
  bw    = bve->width;

  res = 0;

  if (eidx)
  {
    /* CONFLICT: 1...1 < e[1] ------------------------------------------- */
    if (!btor_compare_bv (bve, bvmax) && isult)
    {
    BVULT_CONF:
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = btor_propsls_non_rec_conf (btor, bve, bvult, eidx, "<");
      }
      else
      {
        res = cons_ult_bv (btor, ult, bvult, bve, eidx);
        btor_propsls_rec_conf (btor);
      }
#ifndef NDEBUG
      is_inv = false;
#endif
    }
    /* ^^---------------------------------------------------------------^^ */
    else
    {
      /* bve >= e[1] */
      if (!isult)
        res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, bve);
      /* bve < e[1] */
      else
      {
        tmp = btor_add_bv (mm, bve, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
        btor_free_bv (mm, tmp);
      }
    }
  }
  else
  {
    /* CONFLICT: e[0] < 0 ----------------------------------------------- */
    if (btor_is_zero_bv (bve) && isult)
    {
      goto BVULT_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      /* e[0] >= bve */
      if (!isult)
        res = btor_new_random_range_bv (mm, &btor->rng, bw, bve, bvmax);
      /* e[0] < bve */
      else
      {
        tmp = btor_sub_bv (mm, bve, one);
        res = btor_new_random_range_bv (mm, &btor->rng, bw, zero, tmp);
        btor_free_bv (mm, tmp);
      }
    }
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_ult_bv, ult, bve, bvult, res, eidx, "<");
#endif
  btor_free_bv (mm, zero);
  btor_free_bv (mm, one);
  btor_free_bv (mm, bvmax);
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_sll_bv (Btor *btor,
            BtorNode *sll,
            BtorBitVector *bvsll,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (sll);
  assert (BTOR_IS_REGULAR_NODE (sll));
  assert (bvsll);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsll->width);
  assert (eidx || btor_log_2_util (bvsll->width) == bve->width);
  assert (!btor_is_bv_const_node (sll->e[eidx]));

  uint32_t i, j, ctz_bve, ctz_bvsll, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *tmp, *bvmax;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_sll++;
#endif
  mm = btor->mm;
  e  = sll->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* bve << e[1] = bvsll
   * -> identify possible shift value via zero LSB in bvsll
   *    (considering zero LSB in bve) */
  if (eidx)
  {
    sbw = btor_log_2_util (bvsll->width);

    /* 0...0 << e[1] = 0...0 -> choose res randomly */
    if (btor_is_zero_bv (bve) && btor_is_zero_bv (bvsll))
    {
      res = btor_new_random_bv (mm, &btor->rng, sbw);
    }
    /* -> ctz(bve) > ctz (bvsll) -> conflict
     * -> shift = ctz(bvsll) - ctz(bve)
     *      -> if bvsll = 0 choose shift <= res < bw
     *      -> else res = shift
     *           + if all remaining shifted bits match
     *	   + and if res < bw
     * -> else conflict  */
    else
    {
      ctz_bve   = btor_get_num_trailing_zeros_bv (bve);
      ctz_bvsll = btor_get_num_trailing_zeros_bv (bvsll);
      if (ctz_bve <= ctz_bvsll)
      {
        shift = ctz_bvsll - ctz_bve;

        /* CONFLICT: do not allow shift by bw ----------------------- */
        if (shift > bvsll->width - 1)
        {
          assert (btor_is_zero_bv (bvsll));
        BVSLL_CONF:
          /* check for non-recoverable conflict */
          if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
              && btor_is_bv_const_node (e))
          {
            res = btor_propsls_non_rec_conf (btor, bve, bvsll, eidx, "<<");
          }
          else
          {
            res = cons_sll_bv (btor, sll, bvsll, bve, eidx);
            btor_propsls_rec_conf (btor);
          }
#ifndef NDEBUG
          is_inv = false;
#endif
        }
        /* ^^------------------------------------------------------^^ */
        /* x...x0 << e[1] = 0...0
         * -> choose random shift <= res < bw */
        else if (btor_is_zero_bv (bvsll))
        {
          bvmax = btor_ones_bv (mm, sbw);
          tmp   = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
          res   = btor_new_random_range_bv (mm, &btor->rng, sbw, tmp, bvmax);
          btor_free_bv (mm, bvmax);
          btor_free_bv (mm, tmp);
        }
        else
        {
          /* CONFLICT: shifted bits must match -------------------- */
          for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
          {
            if (btor_get_bit_bv (bve, i) != btor_get_bit_bv (bvsll, j + i))
              goto BVSLL_CONF;
          }
          /* ^^--------------------------------------------------^^ */

          res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSLL_CONF;
      }
    }
  }
  /* e[0] << bve = bvsll
   * -> e[0] = bvsll >> bve
   *    set irrelevant MSBs (the ones that get shifted out) randomly */
  else
  {
    /* using uint64_t here is no problem
     * (max bit width currently handled by Boolector is INT_MAX) */
    shift = btor_bv_to_uint64_bv (bve);

    /* CONFLICT: the LSBs shifted must be zero -------------------------- */
    if (btor_get_num_trailing_zeros_bv (bvsll) < shift) goto BVSLL_CONF;
    /* ^^--------------------------------------------------------------^^ */

    res = btor_srl_bv (mm, bvsll, bve);
    for (i = 0; i < shift; i++)
      btor_set_bit_bv (
          res, res->width - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_sll_bv, sll, bve, bvsll, res, eidx, "<<");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_srl_bv (Btor *btor,
            BtorNode *srl,
            BtorBitVector *bvsrl,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (srl);
  assert (BTOR_IS_REGULAR_NODE (srl));
  assert (bvsrl);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || bve->width == bvsrl->width);
  assert (eidx || btor_log_2_util (bvsrl->width) == bve->width);
  assert (!btor_is_bv_const_node (srl->e[eidx]));

  uint32_t i, j, clz_bve, clz_bvsrl, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_srl++;
#endif
  mm = btor->mm;
  e  = srl->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* bve >> e[1] = bvsll
   * -> identify possible shift value via zero MSBs in bvsll
   *    (considering zero MSBs in bve) */
  if (eidx)
  {
    sbw = btor_log_2_util (bvsrl->width);

    /* 0...0 >> e[1] = 0...0 -> choose random res */
    if (btor_is_zero_bv (bve) && btor_is_zero_bv (bvsrl))
    {
      res = btor_new_random_bv (mm, &btor->rng, sbw);
    }
    /* clz(bve) > clz(bvsrl) -> conflict
     * -> shift = clz(bvsrl) - clz(bve)
     *      -> if bvsrl = 0 choose shift <= res < bw
     *      -> else res = shift
     *           + if all remaining shifted bits match
     *           + and if res < bw
     * -> else conflict */
    else
    {
      clz_bve   = btor_get_num_leading_zeros_bv (bve);
      clz_bvsrl = btor_get_num_leading_zeros_bv (bvsrl);
      if (clz_bve <= clz_bvsrl)
      {
        shift = clz_bvsrl - clz_bve;

        /* CONFLICT: do not allow shift by bw ----------------------- */
        if (shift > bvsrl->width - 1)
        {
          assert (btor_is_zero_bv (bvsrl));
        BVSRL_CONF:
          /* check for non-recoverable conflict */
          if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
              && btor_is_bv_const_node (e))
          {
            res = btor_propsls_non_rec_conf (btor, bve, bvsrl, eidx, ">>");
          }
          else
          {
            res = cons_srl_bv (btor, srl, bvsrl, bve, eidx);
            btor_propsls_rec_conf (btor);
          }
#ifndef NDEBUG
          is_inv = false;
#endif
        }
        /* ^^------------------------------------------------------^^ */
        /* x...x0 >> e[1] = 0...0
         * -> choose random shift <= res < bw */
        else if (btor_is_zero_bv (bvsrl))
        {
          bvmax = btor_ones_bv (mm, sbw);
          tmp   = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
          res   = btor_new_random_range_bv (mm, &btor->rng, sbw, tmp, bvmax);
          btor_free_bv (mm, bvmax);
          btor_free_bv (mm, tmp);
        }
        else
        {
          /* CONFLICT: shifted bits must match -------------------- */
          for (i = 0, j = shift, res = 0; i < bve->width - j; i++)
          {
            if (btor_get_bit_bv (bve, bve->width - 1 - i)
                != btor_get_bit_bv (bvsrl, bvsrl->width - 1 - (j + i)))
              goto BVSRL_CONF;
          }
          /* ^^--------------------------------------------------^^ */

          res = btor_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSRL_CONF;
      }
    }
  }
  /* e[0] >> bve = bvsll
   * -> e[0] = bvsll << bve
   *    set irrelevant LSBs (the ones that get shifted out) randomly */
  else
  {
    /* cast is no problem (max bit width handled by Boolector is INT_MAX) */
    shift = (int) btor_bv_to_uint64_bv (bve);

    /* CONFLICT: the MSBs shifted must be zero -------------------------- */
    if (btor_get_num_leading_zeros_bv (bvsrl) < shift) goto BVSRL_CONF;
    /* ^^--------------------------------------------------------------^^ */

    res = btor_sll_bv (mm, bvsrl, bve);
    for (i = 0; i < shift; i++)
      btor_set_bit_bv (res, i, btor_pick_rand_rng (&btor->rng, 0, 1));
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_srl_bv, srl, bve, bvsrl, res, eidx, ">>");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_mul_bv (Btor *btor,
            BtorNode *mul,
            BtorBitVector *bvmul,
            BtorBitVector *bve,
            int eidx)
{
  assert (btor);
  assert (mul);
  assert (BTOR_IS_REGULAR_NODE (mul));
  assert (bvmul);
  assert (bve);
  assert (bve->width == bvmul->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (mul->e[eidx]));

  int lsbve, lsbvmul, ispow2_bve;
  uint32_t i, j, bw;
  BtorBitVector *res, *inv, *tmp, *tmp2;
  BtorMemMgr *mm;
  BtorNode *e;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_mul++;
#endif
  mm = btor->mm;
  e  = mul->e[eidx ? 0 : 1];
  assert (e);
  bw = bvmul->width;

  res = 0;

  /* bve * res = bvmul
   *
   * -> if bve = 0: * bvmul = 0 -> choose random value for res
   *                * bvmul > 0 -> conflict
   *
   * -> if bvmul odd and bve even -> conflict
   *
   * -> if bve odd -> determine res via modular inverse (extended euklid)
   *		      (unique solution)
   *
   * -> else if bve is even (non-unique, multiple solutions possible!)
   *      * bve = 2^n: + if number of 0-LSBs in bvmul < n -> conflict
   *                   + else res = bvmul >> n
   *                     (with all bits shifted in randomly set to 0 or 1)
   *      * else: bve = 2^n * m, m is odd
   *		  + if number of 0-LSBs in bvmul < n -> conflict
   *	          + else c' = bvmul >> n
   *	            (with all bits shifted in randomly set to 0 or 1)
   *		    -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
   */

  lsbve   = btor_get_bit_bv (bve, 0);
  lsbvmul = btor_get_bit_bv (bvmul, 0);

  /* bve = 0 -> if bvmul = 0 choose random value, else conflict */
  if (btor_is_zero_bv (bve))
  {
    if (btor_is_zero_bv (bvmul))
    {
      res = btor_new_random_bv (mm, &btor->rng, bw);
    }
    /* CONFLICT: bve = 0 but bvmul != 0 -------------------------------- */
    else
    {
    BVMUL_CONF:
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = btor_propsls_non_rec_conf (btor, bve, bvmul, eidx, "*");
      }
      else
      {
        res = cons_mul_bv (btor, mul, bvmul, bve, eidx);
        btor_propsls_rec_conf (btor);
      }
#ifndef NDEBUG
      is_inv = false;
#endif
    }
    /* ^^-------------------------------------------------------------^^ */
  }
  /* CONFLICT: bvmul odd and bve ----------------------------------------- */
  else if (lsbvmul && !lsbve)
  {
    goto BVMUL_CONF;
  }
  /* ^^-----------------------------------------------------------------^^ */
  else
  {
    /* bve odd
     * -> determine res via modular inverse (extended euklid)
     *    (unique solution) */
    if (lsbve)
    {
      inv = btor_mod_inverse_bv (mm, bve);
      res = btor_mul_bv (mm, inv, bvmul);
      btor_free_bv (mm, inv);
    }
    /* bve even
     * (non-unique, multiple solutions possible!)
     * if bve = 2^n: + if number of 0-LSBs in bvmul < n -> conflict
     *               + else res = bvmul >> n
     *                      (with all bits shifted in set randomly)
     * else: bve = 2^n * m, m is odd
     *       + if number of 0-LSBs in bvmul < n -> conflict
     *       + else c' = bvmul >> n (with all bits shifted in set randomly)
     *	      res = c' * m^-1 (with m^-1 the mod inverse of m) */
    else
    {
      if ((ispow2_bve = btor_power_of_two_bv (bve)) >= 0)
      {
        for (i = 0; i < bw; i++)
          if (btor_get_bit_bv (bvmul, i)) break;
        /* CONFLICT: number of 0-LSBs in bvmul < n (for bve = 2^n) -- */
        if (i < (uint32_t) ispow2_bve)
        {
          goto BVMUL_CONF;
        }
        /* ^^------------------------------------------------------^^ */
        /* res = bvmul >> n with all bits shifted in set randomly
         * (note: bw is not necessarily power of 2 -> do not use srl) */
        else
        {
          tmp = btor_slice_bv (mm, bvmul, bw - 1, ispow2_bve);
          res = btor_uext_bv (mm, tmp, ispow2_bve);
          assert (res->width == bw);
          for (i = 0; i < (uint32_t) ispow2_bve; i++)
            btor_set_bit_bv (
                res, bw - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
          btor_free_bv (mm, tmp);
        }
      }
      else
      {
        for (i = 0; i < bw; i++)
          if (btor_get_bit_bv (bvmul, i)) break;
        for (j = 0; j < bw; j++)
          if (btor_get_bit_bv (bve, j)) break;
        /* CONFLICT: number of 0-LSB in bvmul < number of 0-LSB in bve */
        if (i < j)
        {
          goto BVMUL_CONF;
        }
        /* ^^-------------------------------------------------------^^ */
        /* c' = bvmul >> n (with all bits shifted in set randomly)
         * (note: bw is not necessarily power of 2 -> do not use srl)
         * -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd) */
        else
        {
          tmp = btor_slice_bv (mm, bvmul, bw - 1, j);
          res = btor_uext_bv (mm, tmp, j);
          assert (res->width == bw);
          btor_free_bv (mm, tmp);

          tmp  = btor_slice_bv (mm, bve, bw - 1, j);
          tmp2 = btor_uext_bv (mm, tmp, j);
          assert (tmp2->width == bw);
          assert (btor_get_bit_bv (tmp2, 0));
          inv = btor_mod_inverse_bv (mm, tmp2);
          btor_free_bv (mm, tmp);
          btor_free_bv (mm, tmp2);
          tmp = res;
          res = btor_mul_bv (mm, tmp, inv);
          /* choose one of all possible values */
          for (i = 0; i < j; i++)
            btor_set_bit_bv (
                res, bw - 1 - i, btor_pick_rand_rng (&btor->rng, 0, 1));
          btor_free_bv (mm, tmp);
          btor_free_bv (mm, inv);
        }
      }
    }
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_mul_bv, mul, bve, bvmul, res, eidx, "*");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_udiv_bv (Btor *btor,
             BtorNode *udiv,
             BtorBitVector *bvudiv,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (udiv);
  assert (BTOR_IS_REGULAR_NODE (udiv));
  assert (bvudiv);
  assert (bve);
  assert (bve->width == bvudiv->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (udiv->e[eidx]));

  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *lo, *up, *one, *bvmax, *tmp;
  BtorMemMgr *mm;
  BtorRNG *rng;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_udiv++;
#endif
  mm  = btor->mm;
  rng = &btor->rng;
  e   = udiv->e[eidx ? 0 : 1];
  assert (e);
  bw = bve->width;

  one   = btor_one_bv (mm, bve->width);
  bvmax = btor_ones_bv (mm, bvudiv->width); /* 2^bw - 1 */

  res = 0;

  /* bve / e[1] = bvudiv
   *
   * -> if bvudiv = 2^bw - 1: + bve = bvudiv = 2^bw - 1 -> e[1] = 1 or e[1] = 0
   *                          + bve != bvudiv -> e[1] = 0
   * -> if bvudiv = 0 and 0 < bve < 2^bw - 1 choose random e[1] > bve
   *                  and bve = 0            choose random e[1] > 0
   *                  else conflict
   * -> if bve < bvudiv -> conflict
   * -> if bvudiv is a divisor of bve choose with 0.5 prob out of
   *      + e[1] = bvudiv / bve
   *      + choose bve s.t. bve / e[1] = bvudiv
   * -> else choose bve s.t. bve / e[1] = bvudiv  */
  if (eidx)
  {
    if (!btor_compare_bv (bvudiv, bvmax))
    {
      /* bve = bvudiv = 2^bw - 1 -> choose either e[1] = 0 or e[1] = 1
       * with prob 0.5 */
      if (!btor_compare_bv (bve, bvudiv)
          && btor_pick_with_prob_rng (&btor->rng, 500))
        res = btor_one_bv (mm, bw);
      /* bvudiv = 2^bw - 1 and bve != bvudiv -> e[1] = 0 */
      else
        res = btor_new_bv (mm, bw);
    }
    else if (btor_is_zero_bv (bvudiv))
    {
      /* bvudiv = 0 and bve = 0 -> choose random e[1] > 0 */
      if (btor_is_zero_bv (bve))
        res = btor_new_random_range_bv (mm, rng, bw, one, bvmax);
      /* bvudiv = 0 and 0 < bve < 2^bw - 1 -> choose random e[1] > bve */
      else if (btor_compare_bv (bve, bvmax))
      {
        tmp = btor_inc_bv (mm, bve);
        res = btor_new_random_range_bv (mm, rng, bw, tmp, bvmax);
        btor_free_bv (mm, tmp);
      }
      /* CONFLICT ----------------------------------------------------- */
      else
      {
      BVUDIV_CONF:
        /* check for non-recoverable conflict */
        if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
            && btor_is_bv_const_node (e))
        {
          res = btor_propsls_non_rec_conf (btor, bve, bvudiv, eidx, "/");
        }
        else
        {
          res = cons_udiv_bv (btor, udiv, bvudiv, bve, eidx);
          btor_propsls_rec_conf (btor);
        }
#ifndef NDEBUG
        is_inv = false;
#endif
      }
      /* ^^----------------------------------------------------------^^ */
    }
    /* CONFLICT: bve < bvudiv ------------------------------------------- */
    else if (btor_compare_bv (bve, bvudiv) < 0)
    {
      goto BVUDIV_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      /* if bvudiv is a divisor of bve, choose e[1] = bve / bvudiv
       * with prob = 0.5 and a bve s.t. bve / e[1] = bvudiv otherwise */
      tmp = btor_urem_bv (mm, bve, bvudiv);
      if (btor_is_zero_bv (tmp) && btor_pick_with_prob_rng (rng, 500))
      {
        btor_free_bv (mm, tmp);
        res = btor_udiv_bv (mm, bve, bvudiv);
      }
      else
      {
        /* choose e[1] out of all options that yield bve / e[1] = bvudiv
         * Note: udiv always truncates the results towards 0. */

        /* determine upper and lower bounds for e[1]:
         * up = bve / bvudiv
         * lo = bve / (bvudiv + 1) + 1
         * if lo > up -> conflict */
        btor_free_bv (mm, tmp);
        up  = btor_udiv_bv (mm, bve, bvudiv); /* upper bound */
        tmp = btor_inc_bv (mm, bvudiv);
        lo  = btor_udiv_bv (mm, bve, tmp); /* lower bound (excl.) */
        btor_free_bv (mm, tmp);
        tmp = lo;
        lo  = btor_inc_bv (mm, tmp); /* lower bound (incl.) */
        btor_free_bv (mm, tmp);

        /* CONFLICT: lo > up ---------------------------------------- */
        if (btor_compare_bv (lo, up) > 0)
        {
          btor_free_bv (mm, lo);
          btor_free_bv (mm, up);
          goto BVUDIV_CONF;
        }
        /* ^^------------------------------------------------------^^ */
        /* choose lo <= e[1] <= up */
        else
        {
          res = btor_new_random_range_bv (mm, rng, bw, lo, up);
          btor_free_bv (mm, lo);
          btor_free_bv (mm, up);
        }
      }
    }
  }

  /* e[0] / bve = bvudiv
   *
   * -> if bvudiv = 2^bw - 1 and bve = 1 e[0] = 2^bw-1
   *                         and bve = 0, choose random e[0] > 0
   *                         and bve > 0 -> conflict
   * -> if bve = 0 and bvudiv < 2^bw - 1 -> conflict
   * -> if bve * bvudiv does not overflow, choose with 0.5 prob out of
   *      + e[0] = bve * bvudiv
   *      + choose bve s.t. e[0] / bve = bvudiv
   * -> else choose bve s.t. e[0] / bve = bvudiv  */
  else
  {
    if (!btor_compare_bv (bvudiv, bvmax))
    {
      /* bvudiv = 2^bw-1 and bve = 1 -> e[0] = 2^bw-1 */
      if (!btor_compare_bv (bve, one)) res = btor_copy_bv (mm, bvmax);
      /* bvudiv = 2^bw - 1 and bve = 0 -> choose random e[0] */
      else if (btor_is_zero_bv (bve))
        res = btor_new_random_bv (mm, rng, bw);
      /* CONFLICT ---------------------------------------------------- */
      else
      {
        goto BVUDIV_CONF;
      }
      /* ^^---------------------------------------------------------^^ */
    }
    /* CONFLICT: bve = 0 and bvudiv < 2^bw - 1 ------------------------- */
    else if (btor_is_zero_bv (bve))
    {
      goto BVUDIV_CONF;
    }
    /* ^^-------------------------------------------------------------^^ */
    else
    {
      /* if bve * bvudiv does not overflow, choose e[0] = bve * bvudiv
       * with prob = 0.5 and a bve s.t. e[0] / bve = bvudiv otherwise */

      /* CONFLICT: overflow: bve * bvudiv ----------------------------- */
      if (btor_is_umulo_bv (mm, bve, bvudiv)) goto BVUDIV_CONF;
      /* ^^----------------------------------------------------------^^ */
      else
      {
        if (btor_pick_with_prob_rng (rng, 500))
          res = btor_mul_bv (mm, bve, bvudiv);
        else
        {
          /* choose e[0] out of all options that yield
           * e[0] / bve = bvudiv
           * Note: udiv always truncates the results towards 0. */

          /* determine upper and lower bounds for e[0]:
           * up = bve * (budiv + 1) - 1
           *	  if bve * (bvudiv + 1) does not overflow
           *	  else 2^bw - 1
           * lo = bve * bvudiv */
          lo  = btor_mul_bv (mm, bve, bvudiv);
          tmp = btor_inc_bv (mm, bvudiv);
          if (btor_is_umulo_bv (mm, bve, tmp))
          {
            btor_free_bv (mm, tmp);
            up = btor_copy_bv (mm, bvmax);
          }
          else
          {
            up = btor_mul_bv (mm, bve, tmp);
            btor_free_bv (mm, tmp);
            tmp = btor_dec_bv (mm, up);
            btor_free_bv (mm, up);
            up = tmp;
          }

          res = btor_new_random_range_bv (mm, &btor->rng, bve->width, lo, up);

          btor_free_bv (mm, up);
          btor_free_bv (mm, lo);
        }
      }
    }
  }

  btor_free_bv (mm, bvmax);
  btor_free_bv (mm, one);
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_udiv_bv, udiv, bve, bvudiv, res, eidx, "/");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_urem_bv (Btor *btor,
             BtorNode *urem,
             BtorBitVector *bvurem,
             BtorBitVector *bve,
             int eidx)
{
  assert (btor);
  assert (urem);
  assert (BTOR_IS_REGULAR_NODE (urem));
  assert (bvurem);
  assert (bve);
  assert (bve->width == bvurem->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (urem->e[eidx]));

  uint32_t bw, cnt;
  int cmp;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_urem++;
#endif
  mm = btor->mm;
  e  = urem->e[eidx ? 0 : 1];
  assert (e);

  bw = bvurem->width;

  bvmax = btor_ones_bv (mm, bw); /* 2^bw - 1 */
  one   = btor_one_bv (mm, bw);

  res = 0;

  /* bve % e[1] = bvurem
   * -> if bvurem = 1...1 -> bve = 1...1 and e[1] = 0...0, else conflict
   * -> if bve = bvurem, choose either e[1] = 0 or some e[1] > bvurem randomly
   * -> if bvurem > 0 and bvurem = bve - 1, conflict
   * -> if bve > bvurem, e[1] = ((bve - bvurem) / n) > bvurem, else conflict
   * -> if bve < bvurem, conflict */
  if (eidx)
  {
    /* bve % e[1] = 1...1 -> bve = 1...1, e[1] = 0 */
    if (!btor_compare_bv (bvurem, bvmax))
    {
      /* CONFLICT: bvurem = 1...1 but bve != 1...1 -------------------- */
      if (btor_compare_bv (bve, bvmax))
      {
      BVUREM_CONF:
        /* check for non-recoverable conflict */
        if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
            && btor_is_bv_const_node (e))
        {
          res = btor_propsls_non_rec_conf (btor, bve, bvurem, eidx, "%");
        }
        else
        {
          res = cons_urem_bv (btor, urem, bvurem, bve, eidx);
          btor_propsls_rec_conf (btor);
        }
#ifndef NDEBUG
        is_inv = false;
#endif
      }
      /* ^^----------------------------------------------------------^^ */
      else
      {
        res = btor_new_bv (mm, bw);
      }
    }
    else
    {
      cmp = btor_compare_bv (bve, bvurem);

      /* bve = bvurem, choose either e[1] = 0 or random e[1] > bvurem */
      if (cmp == 0)
      {
        /* choose e[1] = 0 with prob = 0.25*/
        if (btor_pick_with_prob_rng (&btor->rng, 250))
          res = btor_new_bv (mm, bw);
        /* bvurem < res <= 2^bw - 1 */
        else
        {
          tmp = btor_add_bv (mm, bvurem, one);
          res = btor_new_random_range_bv (mm, &btor->rng, bw, tmp, bvmax);
          btor_free_bv (mm, tmp);
        }
      }
      /* bve > bvurem, e[1] = (bve - bvurem) / n */
      else if (cmp > 0)
      {
        if (!btor_is_zero_bv (bvurem))
        {
          tmp = btor_dec_bv (mm, bve);
          /* CONFLICT: -------------------------------------------- */
          /* bvurem = bve - 1 -> bve % e[1] = bve - 1
           * -> not possible if bvurem > 0  */
          if (!btor_compare_bv (bvurem, tmp))
          {
            btor_free_bv (mm, tmp);
            goto BVUREM_CONF;
          }
          /* ^^--------------------------------------------------^^ */
          btor_free_bv (mm, tmp);
        }

        sub = btor_sub_bv (mm, bve, bvurem);

        /* CONFLICT: bve - bvurem <= bvurem ------------------------- */
        if (btor_compare_bv (sub, bvurem) <= 0)
        {
          btor_free_bv (mm, sub);
          goto BVUREM_CONF;
        }
        /* ^^------------------------------------------------------^^ */
        /* choose either n = 1 or 1 <= n < (bve - bvurem) / bvurem
         * with prob = 0.5 */
        else
        {
          if (btor_pick_with_prob_rng (&btor->rng, 500))
          {
            res = btor_copy_bv (mm, sub);
          }
          else
          {
            /* 1 <= n < (bve - bvurem) / bvurem (non-truncating)
             * (note: div truncates towards 0!) */

            /* bvurem = 0 -> 1 <= n <= bve */
            if (btor_is_zero_bv (bvurem))
            {
              up = btor_copy_bv (mm, bve);
            }
            /* e[1] > bvurem
             * -> (bve - bvurem) / n > bvurem
             * -> (bve - bvurem) / bvurem > n */
            else
            {
              tmp  = btor_urem_bv (mm, sub, bvurem);
              tmp2 = btor_udiv_bv (mm, sub, bvurem);
              if (btor_is_zero_bv (tmp))
              {
                /* (bve - bvurem) / bvurem is not truncated
                 * (remainder is 0), therefore the EXclusive
                 * upper bound
                 * -> up = (bve - bvurem) / bvurem - 1 */
                up = btor_sub_bv (mm, tmp2, one);
                btor_free_bv (mm, tmp2);
              }
              else
              {
                /* (bve - bvurem) / bvurem is truncated
                 * (remainder is not 0), therefore the INclusive
                 * upper bound
                 * -> up = (bve - bvurem) / bvurem */
                up = tmp2;
              }
              btor_free_bv (mm, tmp);
            }

            if (btor_is_zero_bv (up))
              res = btor_udiv_bv (mm, sub, one);
            else
            {
              /* choose 1 <= n <= up randomly
               * s.t (bve - bvurem) % n = 0 */
              n   = btor_new_random_range_bv (mm, &btor->rng, bw, one, up);
              tmp = btor_urem_bv (mm, sub, n);
              for (cnt = 0; cnt < bw && !btor_is_zero_bv (tmp); cnt++)
              {
                btor_free_bv (mm, n);
                btor_free_bv (mm, tmp);
                n   = btor_new_random_range_bv (mm, &btor->rng, bw, one, up);
                tmp = btor_urem_bv (mm, sub, n);
              }

              /* res = (bve - bvurem) / n */
              if (btor_is_zero_bv (tmp)) res = btor_udiv_bv (mm, sub, n);
              /* fallback: n = 1 */
              else
                res = btor_copy_bv (mm, sub);

              btor_free_bv (mm, n);
              btor_free_bv (mm, tmp);
            }
            btor_free_bv (mm, up);
          }
        }
        btor_free_bv (mm, sub);
      }
      /* CONFLICT: bve < bvurem --------------------------------------- */
      else
      {
        goto BVUREM_CONF;
      }
      /* ^^----------------------------------------------------------^^ */
    }
  }
  /* e[0] % bve = bvurem
   * -> if bve = 0, e[0] = bvurem
   * -> if bvurem = 1...1 and bve != 0, conflict
   * -> if bve <= bvurem, conflict
   * -> if bvurem > 0 and bve = 1, conflict
   * -> else choose either
   *      - e[0] = bvurem, or
   *      - e[0] = bve * n + b, with n s.t. (bve * n + b) does not overflow */
  else
  {
    /* bve = 0 -> e[0] = bvurem */
    if (btor_is_zero_bv (bve))
    {
    BVUREM_ZERO_0:
      res = btor_copy_bv (mm, bvurem);
    }
    /* CONFLICT: bvurem > 0 and bve = 1 --------------------------------- */
    else if (!btor_is_zero_bv (bvurem) && btor_is_one_bv (bve))
    {
      goto BVUREM_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    /* bvurem = 1...1 -> bve = 0, e[0] = 1...1 */
    else if (!btor_compare_bv (bvurem, bvmax))
    {
      /* CONFLICT: bve != 0 ------------------------------------------- */
      if (!btor_is_zero_bv (bve))
      {
        goto BVUREM_CONF;
      }
      /* ^^----------------------------------------------------------^^ */
      else
      {
        goto BVUREM_ZERO_0;
      }
    }
    else if (btor_compare_bv (bve, bvurem) > 0)
    {
      /* choose simplest solution (0 <= res < bve -> res = bvurem)
       * with prob 0.5 */
      if (btor_pick_with_prob_rng (&btor->rng, 500))
      {
      BVUREM_EQ_0:
        res = btor_copy_bv (mm, bvurem);
      }
      /* e[0] = bve * n + bvurem,
       * with n s.t. (bve * n + bvurem) does not overflow */
      else
      {
        tmp2 = btor_sub_bv (mm, bvmax, bve);

        /* overflow for n = 1 -> only simplest solution possible */
        if (btor_compare_bv (tmp2, bvurem) < 0)
        {
          btor_free_bv (mm, tmp2);
          goto BVUREM_EQ_0;
        }
        else
        {
          btor_free_bv (mm, tmp2);

          tmp = btor_copy_bv (mm, bvmax);
          n   = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);

          while (btor_is_umulo_bv (mm, bve, n))
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);
          }

          mul  = btor_mul_bv (mm, bve, n);
          tmp2 = btor_sub_bv (mm, bvmax, mul);

          if (btor_compare_bv (tmp2, bvurem) < 0)
          {
            btor_free_bv (mm, tmp);
            tmp = btor_sub_bv (mm, n, one);
            btor_free_bv (mm, n);
            n = btor_new_random_range_bv (mm, &btor->rng, bw, one, tmp);
            btor_free_bv (mm, mul);
            mul = btor_mul_bv (mm, bve, n);
          }

          res = btor_add_bv (mm, mul, bvurem);
          assert (btor_compare_bv (res, mul) >= 0);
          assert (btor_compare_bv (res, bvurem) >= 0);

          btor_free_bv (mm, tmp);
          btor_free_bv (mm, tmp2);
          btor_free_bv (mm, mul);
          btor_free_bv (mm, n);
        }
      }
    }
    /* CONFLICT: bve <= bvurem ------------------------------------------ */
    else
    {
      goto BVUREM_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
  }

  btor_free_bv (mm, one);
  btor_free_bv (mm, bvmax);

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_urem_bv, urem, bve, bvurem, res, eidx, "%");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_concat_bv (Btor *btor,
               BtorNode *concat,
               BtorBitVector *bvconcat,
               BtorBitVector *bve,
               int eidx)
{
  assert (btor);
  assert (concat);
  assert (BTOR_IS_REGULAR_NODE (concat));
  assert (bvconcat);
  assert (bve);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_is_bv_const_node (concat->e[eidx]));

  BtorNode *e;
  BtorBitVector *res, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_concat++;
#endif
  mm = btor->mm;
  e  = concat->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* bve o e[1] = bvconcat, slice e[1] out of the lower bits of bvconcat */
  if (eidx)
  {
    tmp = btor_slice_bv (
        mm, bvconcat, bvconcat->width - 1, bvconcat->width - bve->width);
    /* CONFLICT: bve bits do not match bvconcat ------------------------- */
    if (btor_compare_bv (tmp, bve))
    {
    BVCONCAT_CONF:
      /* check for non-recoverable conflict */
      if (btor_get_opt (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT)
          && btor_is_bv_const_node (e))
      {
        res = btor_propsls_non_rec_conf (btor, bve, bvconcat, eidx, "o");
      }
      else
      {
        res = cons_concat_bv (btor, concat, bvconcat, bve, eidx);
        btor_propsls_rec_conf (btor);
      }
#ifndef NDEBUG
      is_inv = false;
#endif
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      res = btor_slice_bv (mm, bvconcat, bvconcat->width - bve->width - 1, 0);
    }
  }
  /* e[0] o bve = bvconcat, slice e[0] out of the upper bits of bvconcat */
  else
  {
    tmp = btor_slice_bv (mm, bvconcat, bve->width - 1, 0);
    /* CONFLICT: bve bits do not match bvconcat ------------------------- */
    if (btor_compare_bv (tmp, bve))
    {
      goto BVCONCAT_CONF;
    }
    /* ^^--------------------------------------------------------------^^ */
    else
    {
      res = btor_slice_bv (mm, bvconcat, bvconcat->width - 1, bve->width);
    }
  }
  btor_free_bv (mm, tmp);
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_concat_bv, concat, bve, bvconcat, res, eidx, "o");
#endif
  return res;
}

#ifdef NDEBUG
static inline BtorBitVector *
#else
BtorBitVector *
#endif
inv_slice_bv (Btor *btor,
              BtorNode *slice,
              BtorBitVector *bvslice,
              BtorBitVector *bve)
{
  assert (btor);
  assert (slice);
  assert (BTOR_IS_REGULAR_NODE (slice));
  assert (bvslice);
  assert (!btor_is_bv_const_node (slice->e[0]));

  uint32_t i, upper, lower, rlower, rupper, rboth;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
  bool bkeep, bflip;

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP)
    BTOR_PROP_SOLVER (btor)->stats.inv_slice++;
#endif
  mm = btor->mm;
  e  = slice->e[0];
  assert (e);

  bflip = btor_pick_with_prob_rng (
      &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_SLICE_FLIP));

  bkeep = bflip ? true
                : btor_pick_with_prob_rng (
                      &btor->rng,
                      btor_get_opt (btor, BTOR_OPT_PROP_PROB_SLICE_KEEP_DC));

  upper = btor_slice_get_upper (slice);
  lower = btor_slice_get_lower (slice);

  res = btor_new_bv (mm, btor_get_exp_width (btor, e));

  /* keep previous value for don't care bits or set randomly with prob
   * BTOR_OPT_PROP_PROB_SLICE_KEEP_DC */
  for (i = 0; i < lower; i++)
    btor_set_bit_bv (res,
                     i,
                     bkeep ? btor_get_bit_bv (bve, i)
                           : (int) btor_pick_rand_rng (&btor->rng, 0, 1));

  /* set sliced bits to propagated value */
  for (i = lower; i <= upper; i++)
    btor_set_bit_bv (res, i, btor_get_bit_bv (bvslice, i - lower));

  /* keep previous value for don't care bits or set randomly with prob
   * BTOR_OPT_PROP_PROB_SLICE_KEEP_DC */
  for (i = upper + 1; i < res->width; i++)
    btor_set_bit_bv (res,
                     i,
                     bkeep ? btor_get_bit_bv (bve, i)
                           : (int) btor_pick_rand_rng (&btor->rng, 0, 1));

  if (bflip)
  {
    rboth = 0;
    if (lower)
    {
      rboth += 1;
      rlower = btor_pick_rand_rng (&btor->rng, 0, lower - 1);
    }
    if (upper + 1 < res->width)
    {
      rboth += 2;
      rupper = btor_pick_rand_rng (&btor->rng, upper + 1, res->width - 1);
    }
    switch (rboth)
    {
      case 3:
        assert (rupper >= upper + 1 && rupper < res->width);
        assert (rlower < lower);
        btor_flip_bit_bv (
            res, btor_pick_with_prob_rng (&btor->rng, 500) ? rupper : rlower);
        break;
      case 2:
        assert (rupper >= upper + 1 && rupper < res->width);
        btor_flip_bit_bv (res, rupper);
        break;
      case 1:
        assert (rlower < lower);
        btor_flip_bit_bv (res, rlower);
        break;
    }
  }

#ifndef NDEBUG
  BtorBitVector *tmpdbg = btor_slice_bv (mm, res, upper, lower);
  assert (!btor_compare_bv (tmpdbg, bvslice));
  btor_free_bv (mm, tmpdbg);

  char *sbvslice = btor_bv_to_char_bv (mm, bvslice);
  char *sres     = btor_bv_to_char_bv (mm, res);
  BTORLOG (3,
           "prop (xxxxx): %s: %s := %s[%d:%d]",
           node2string (slice),
           sbvslice,
           sres,
           lower,
           upper);
  btor_freestr (mm, sbvslice);
  btor_freestr (mm, sres);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

uint64_t
btor_propsls_select_move_prop (Btor *btor,
                               BtorNode *root,
                               BtorNode **input,
                               BtorBitVector **assignment)
{
  assert (btor);
  assert (root);
  assert (
      btor_bv_to_uint64_bv ((BtorBitVector *) btor_get_bv_model (btor, root))
      == 0);

  bool b;
  int32_t i, nconst, eidx, idx;
  uint64_t nprops;
  BtorNode *cur, *real_cur;
  BtorBitVector *bve[3], *bvcur, *bvenew, *tmp;
#ifndef NBTORLOG
  char *a;
#endif

  *input      = 0;
  *assignment = 0;
  nprops      = 0;

  cur   = root;
  bvcur = btor_one_bv (btor->mm, 1);

  for (;;)
  {
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_is_bv_var_node (cur))
    {
      *input      = real_cur;
      *assignment = BTOR_IS_INVERTED_NODE (cur)
                        ? btor_not_bv (btor->mm, bvcur)
                        : btor_copy_bv (btor->mm, bvcur);
      break;
    }
    else if (btor_is_bv_const_node (cur))
    {
      break;
    }
    else
    {
      nprops += 1;
      assert (!btor_is_bv_const_node (cur));

      if (BTOR_IS_INVERTED_NODE (cur))
      {
        tmp   = bvcur;
        bvcur = btor_not_bv (btor->mm, tmp);
        btor_free_bv (btor->mm, tmp);
      }

      /* check if all paths are const, if yes -> conflict */
      for (i = 0, nconst = 0; i < real_cur->arity; i++)
      {
        bve[i] = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[i]);
        if (btor_is_bv_const_node (real_cur->e[i])) nconst += 1;
      }
      if (nconst > real_cur->arity - 1) break;

#ifndef NBTORLOG
      a = btor_bv_to_char_bv (btor->mm, bvcur);
      BTORLOG (2, "");
      BTORLOG (2, "propagate: %s", a);
      btor_freestr (btor->mm, a);
#endif

      /* we either select a consistent or inverse value
       * as path assignment, depending on the given probability p
       * -> if b then inverse else consistent */
      b = btor_pick_with_prob_rng (
          &btor->rng, btor_get_opt (btor, BTOR_OPT_PROP_PROB_USE_INV_VALUE));

      /* select path and determine path assignment */
      switch (real_cur->kind)
      {
        case BTOR_ADD_NODE:
          eidx = select_path_add (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_add_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_add_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_AND_NODE:
          eidx = select_path_and (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_and_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_and_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_BV_EQ_NODE:
          eidx = select_path_eq (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_eq_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_eq_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_ULT_NODE:
          eidx = select_path_ult (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_ult_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_ult_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SLL_NODE:
          eidx = select_path_sll (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_sll_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_sll_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SRL_NODE:
          eidx = select_path_srl (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_srl_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_srl_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_MUL_NODE:
          eidx = select_path_mul (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_mul_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_mul_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_UDIV_NODE:
          eidx = select_path_udiv (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_udiv_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_UREM_NODE:
          eidx = select_path_urem (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_urem_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_urem_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_CONCAT_NODE:
          eidx = select_path_concat (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0);
          bvenew = b ? inv_concat_bv (btor, real_cur, bvcur, bve[idx], eidx)
                     : cons_concat_bv (btor, real_cur, bvcur, bve[idx], eidx);
          break;
        case BTOR_SLICE_NODE:
          eidx = select_path_slice (btor, real_cur, bvcur, bve);
          idx  = eidx ? 0 : 1;
          assert (eidx >= 0),
              bvenew = b ? inv_slice_bv (btor, real_cur, bvcur, bve[0])
                         : cons_slice_bv (btor, real_cur, bvcur, bve[0]);
          break;
        default:
          assert (btor_is_bv_cond_node (real_cur));
          /* either assume that cond is fixed and propagate bvenew
           * to enabled path, or flip condition */
          tmp  = (BtorBitVector *) btor_get_bv_model (btor, real_cur->e[0]);
          eidx = select_path_cond (btor, real_cur, bvcur, tmp);
          /* flip condition */
          if (eidx == 0) bvenew = btor_not_bv (btor->mm, tmp);
          /* else continue propagating current bvenew down */
          else
            bvenew = btor_copy_bv (btor->mm, bvcur);
      }

      if (!bvenew) break; /* non-recoverable conflict */

      cur = real_cur->e[eidx];
      btor_free_bv (btor->mm, bvcur);
      bvcur = bvenew;
    }
  }

  btor_free_bv (btor->mm, bvcur);

  return nprops;
}
