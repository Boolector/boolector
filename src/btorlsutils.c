/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorlsutils.h"

#include "btorbv.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btornode.h"
#include "btorslsutils.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static void
update_roots_table (Btor *btor,
                    BtorIntHashTable *roots,
                    BtorNode *exp,
                    BtorBitVector *bv)
{
  assert (btor);
  assert (roots);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (bv);
  assert (btor_bv_compare (btor_model_get_bv (btor, exp), bv));

  (void) btor;

  /* exp: old assignment = 0, new assignment = 1 (bv = 1)
   *      -> satisfied, remove */
  if (btor_hashint_map_get (roots, exp->id))
  {
    btor_hashint_map_remove (roots, exp->id, 0);
    assert (btor_bv_is_false (btor_model_get_bv (btor, exp)));
    assert (btor_bv_is_true (bv));
  }
  /* -exp: old assignment = 0, new assignment = 1 (bv = 0)
   * -> satisfied, remove */
  else if (btor_hashint_map_get (roots, -exp->id))
  {
    btor_hashint_map_remove (roots, -exp->id, 0);
    assert (
        btor_bv_is_false (btor_model_get_bv (btor, btor_node_invert (exp))));
    assert (btor_bv_is_false (bv));
  }
  /* exp: old assignment = 1, new assignment = 0 (bv = 0)
   * -> unsatisfied, add */
  else if (btor_bv_is_false (bv))
  {
    btor_hashint_map_add (roots, exp->id);
    assert (btor_bv_is_true (btor_model_get_bv (btor, exp)));
  }
  /* -exp: old assignment = 1, new assignment = 0 (bv = 1)
   * -> unsatisfied, add */
  else
  {
    assert (btor_bv_is_true (bv));
    btor_hashint_map_add (roots, -exp->id);
    assert (btor_bv_is_true (btor_model_get_bv (btor, btor_node_invert (exp))));
  }
}

/**
 * Update cone of influence.
 *
 * Note: 'roots' will only be updated if 'update_roots' is true.
 *         + PROP engine: always
 *         + SLS  engine: only if an actual move is performed
 *                        (not during neighborhood exploration, 'try_move')
 *       -> assertion code guarded with '#ifndef NDEBUG' is therefore
 *          always valid since 'roots' always maintains a valid state
 *          ('try_move' of the SLS engine is the only case where 'roots'
 *           might become globally invalid, i.e., when a tried move
 *           is not actually performed, however in that particular case
 *           we do not update 'roots')
 */
void
btor_lsutils_update_cone (Btor *btor,
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
  assert (btor_opt_get (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_PROP
          || btor_opt_get (btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_SLS);
  assert (bv_model);
  assert (roots);
  assert (exps);
  assert (exps->count);
  assert (btor_opt_get (btor, BTOR_OPT_ENGINE) != BTOR_ENGINE_PROP
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

  start = delta = btor_util_time_stamp ();

  mm = btor->mm;

#ifndef NDEBUG
  BtorPtrHashTableIterator pit;
  BtorNode *root;
  btor_iter_hashptr_init (&pit, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&pit, btor->assumptions);
  while (btor_iter_hashptr_has_next (&pit))
  {
    root = btor_iter_hashptr_next (&pit);
    assert (!btor_hashptr_table_get (btor->unsynthesized_constraints,
                                     btor_node_invert (root)));
    assert (
        !btor_hashptr_table_get (btor->assumptions, btor_node_invert (root)));
    if (btor_bv_is_false (btor_model_get_bv (btor, root)))
      assert (btor_hashint_map_contains (roots, btor_node_get_id (root)));
    else
      assert (!btor_hashint_map_contains (roots, btor_node_get_id (root)));
  }
#endif

  /* reset cone ----------------------------------------------------------- */

  BTOR_INIT_STACK (mm, cone);
  BTOR_INIT_STACK (mm, stack);
  btor_iter_hashint_init (&iit, exps);
  while (btor_iter_hashint_has_next (&iit))
  {
    exp = btor_node_get_by_id (btor, btor_iter_hashint_next (&iit));
    assert (btor_node_is_regular (exp));
    assert (btor_node_is_bv_var (exp));
    BTOR_PUSH_STACK (stack, exp);
  }
  cache = btor_hashint_table_new (mm);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (btor_node_is_regular (cur));
    if (btor_hashint_table_contains (cache, cur->id)) continue;
    btor_hashint_table_add (cache, cur->id);
    if (!btor_hashint_table_contains (exps, cur->id))
      BTOR_PUSH_STACK (cone, cur);
    *stats_updates += 1;

    /* push parents */
    btor_iter_parent_init (&nit, cur);
    while (btor_iter_parent_has_next (&nit))
      BTOR_PUSH_STACK (stack, btor_iter_parent_next (&nit));
  }
  BTOR_RELEASE_STACK (stack);
  btor_hashint_table_delete (cache);

  *time_update_cone_reset += btor_util_time_stamp () - delta;

  /* update assignment and score of exps ----------------------------------- */

  btor_iter_hashint_init (&iit, exps);
  while (btor_iter_hashint_has_next (&iit))
  {
    ass = (BtorBitVector *) exps->data[iit.cur_pos].as_ptr;
    exp = btor_node_get_by_id (btor, btor_iter_hashint_next (&iit));

    /* update model */
    d = btor_hashint_map_get (bv_model, exp->id);
    assert (d);
    if (update_roots
        && (exp->constraint || btor_hashptr_table_get (btor->assumptions, exp)
            || btor_hashptr_table_get (btor->assumptions,
                                       btor_node_invert (exp)))
        && btor_bv_compare (d->as_ptr, ass))
    {
      /* old assignment != new assignment */
      update_roots_table (btor, roots, exp, ass);
    }
    btor_bv_free (mm, d->as_ptr);
    d->as_ptr = btor_bv_copy (mm, ass);
    if ((d = btor_hashint_map_get (bv_model, -exp->id)))
    {
      btor_bv_free (mm, d->as_ptr);
      d->as_ptr = btor_bv_not (mm, ass);
    }

    /* update score */
    if (score && btor_node_bv_get_width (btor, exp) == 1)
    {
      assert (btor_hashint_map_contains (score, btor_node_get_id (exp)));
      btor_hashint_map_get (score, btor_node_get_id (exp))->as_dbl =
          btor_slsutils_compute_score_node (
              btor, bv_model, btor->fun_model, score, exp);

      assert (btor_hashint_map_contains (score, -btor_node_get_id (exp)));
      btor_hashint_map_get (score, -btor_node_get_id (exp))->as_dbl =
          btor_slsutils_compute_score_node (
              btor, bv_model, btor->fun_model, score, btor_node_invert (exp));
    }
  }

  qsort (cone.start,
         BTOR_COUNT_STACK (cone),
         sizeof (BtorNode *),
         btor_node_compare_by_id_qsort_asc);

  /* update model of cone ------------------------------------------------- */

  delta = btor_util_time_stamp ();

  for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
  {
    cur = BTOR_PEEK_STACK (cone, i);
    assert (btor_node_is_regular (cur));
    for (j = 0; j < cur->arity; j++)
    {
      if (btor_node_is_bv_const (cur->e[j]))
      {
        e[j] =
            btor_node_is_inverted (cur->e[j])
                ? btor_bv_copy (mm, btor_node_bv_const_get_invbits (cur->e[j]))
                : btor_bv_copy (mm, btor_node_bv_const_get_bits (cur->e[j]));
      }
      else
      {
        d = btor_hashint_map_get (bv_model,
                                  btor_node_real_addr (cur->e[j])->id);
        /* Note: generate model enabled branch for ite (and does not
         * generate model for nodes in the branch, hence !b may happen */
        if (!d)
          e[j] = btor_model_recursively_compute_assignment (
              btor, bv_model, btor->fun_model, cur->e[j]);
        else
          e[j] = btor_node_is_inverted (cur->e[j])
                     ? btor_bv_not (mm, d->as_ptr)
                     : btor_bv_copy (mm, d->as_ptr);
      }
    }
    switch (cur->kind)
    {
      case BTOR_BV_ADD_NODE: bv = btor_bv_add (mm, e[0], e[1]); break;
      case BTOR_BV_AND_NODE: bv = btor_bv_and (mm, e[0], e[1]); break;
      case BTOR_BV_EQ_NODE: bv = btor_bv_eq (mm, e[0], e[1]); break;
      case BTOR_BV_ULT_NODE: bv = btor_bv_ult (mm, e[0], e[1]); break;
      case BTOR_BV_SLL_NODE: bv = btor_bv_sll (mm, e[0], e[1]); break;
      case BTOR_BV_SRL_NODE: bv = btor_bv_srl (mm, e[0], e[1]); break;
      case BTOR_BV_MUL_NODE: bv = btor_bv_mul (mm, e[0], e[1]); break;
      case BTOR_BV_UDIV_NODE: bv = btor_bv_udiv (mm, e[0], e[1]); break;
      case BTOR_BV_UREM_NODE: bv = btor_bv_urem (mm, e[0], e[1]); break;
      case BTOR_BV_CONCAT_NODE: bv = btor_bv_concat (mm, e[0], e[1]); break;
      case BTOR_BV_SLICE_NODE:
        bv = btor_bv_slice (mm,
                            e[0],
                            btor_node_bv_slice_get_upper (cur),
                            btor_node_bv_slice_get_lower (cur));
        break;
      default:
        assert (btor_node_is_cond (cur));
        bv = btor_bv_is_true (e[0]) ? btor_bv_copy (mm, e[1])
                                    : btor_bv_copy (mm, e[2]);
    }

    /* update assignment */

    d = btor_hashint_map_get (bv_model, cur->id);

    /* update roots table */
    if (update_roots
        && (cur->constraint || btor_hashptr_table_get (btor->assumptions, cur)
            || btor_hashptr_table_get (btor->assumptions,
                                       btor_node_invert (cur))))
    {
      assert (d); /* must be contained, is root */
      /* old assignment != new assignment */
      if (btor_bv_compare (d->as_ptr, bv))
        update_roots_table (btor, roots, cur, bv);
    }

    /* update assignments */
    /* Note: generate model enabled branch for ite (and does not generate
     *       model for nodes in the branch, hence !b may happen */
    if (!d)
    {
      btor_node_copy (btor, cur);
      btor_hashint_map_add (bv_model, cur->id)->as_ptr = bv;
    }
    else
    {
      btor_bv_free (mm, d->as_ptr);
      d->as_ptr = bv;
    }

    if ((d = btor_hashint_map_get (bv_model, -cur->id)))
    {
      btor_bv_free (mm, d->as_ptr);
      d->as_ptr = btor_bv_not (mm, bv);
    }
    /* cleanup */
    for (j = 0; j < cur->arity; j++) btor_bv_free (mm, e[j]);
  }
  *time_update_cone_model_gen += btor_util_time_stamp () - delta;

  /* update score of cone ------------------------------------------------- */

  if (score)
  {
    delta = btor_util_time_stamp ();
    for (i = 0; i < BTOR_COUNT_STACK (cone); i++)
    {
      cur = BTOR_PEEK_STACK (cone, i);
      assert (btor_node_is_regular (cur));

      if (btor_node_bv_get_width (btor, cur) != 1) continue;

      id = btor_node_get_id (cur);
      if (!btor_hashint_map_contains (score, id))
      {
        /* not reachable from the roots */
        assert (!btor_hashint_map_contains (score, -id));
        continue;
      }
      btor_hashint_map_get (score, id)->as_dbl =
          btor_slsutils_compute_score_node (
              btor, bv_model, btor->fun_model, score, cur);
      assert (btor_hashint_map_contains (score, -id));
      btor_hashint_map_get (score, -id)->as_dbl =
          btor_slsutils_compute_score_node (
              btor, bv_model, btor->fun_model, score, btor_node_invert (cur));
    }
    *time_update_cone_compute_score += btor_util_time_stamp () - delta;
  }

  BTOR_RELEASE_STACK (cone);

#ifndef NDEBUG
  btor_iter_hashptr_init (&pit, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&pit, btor->assumptions);
  while (btor_iter_hashptr_has_next (&pit))
  {
    root = btor_iter_hashptr_next (&pit);
    if (btor_bv_is_false (btor_model_get_bv (btor, root)))
      assert (btor_hashint_map_contains (roots, btor_node_get_id (root)));
    else
      assert (!btor_hashint_map_contains (roots, btor_node_get_id (root)));
  }
#endif
  *time_update_cone += btor_util_time_stamp () - start;
}
