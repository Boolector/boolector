/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "normalizer/btornormquant.h"
#include "btorcore.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorstack.h"

static BtorNode *
create_skolem_ite (Btor *btor, BtorNode *ite, BtorIntHashTable *map)
{
  assert (BTOR_IS_REGULAR_NODE (ite));
  assert (BTOR_IS_BV_COND_NODE (ite));

  char buf[128];
  BtorParameterizedIterator p_it;
  BtorNodePtrStack params;
  BtorSortIdStack tsorts;
  BtorNode *param, *uf, *result;
  BtorSortId domain, funsort;
  BtorMemMgr *mm;
  BtorIntHashTableData *d;
  BtorSortUniqueTable *sorts;

  mm    = btor->mm;
  sorts = &btor->sorts_unique_table;

  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (tsorts);
  btor_init_parameterized_iterator (&p_it, btor, ite);
  while (btor_has_next_parameterized_iterator (&p_it))
  {
    param = btor_next_parameterized_iterator (&p_it);
    d     = btor_get_int_hash_map (map, param->id);
    assert (d);
    assert (d->as_ptr);
    param = d->as_ptr;
    BTOR_PUSH_STACK (mm, params, param);
    BTOR_PUSH_STACK (mm, tsorts, param->sort_id);
  }

  domain  = btor_tuple_sort (sorts, tsorts.start, BTOR_COUNT_STACK (tsorts));
  funsort = btor_fun_sort (sorts, domain, ite->sort_id);

  sprintf (buf, "ite_%d", ite->id);
  uf     = btor_uf_exp (btor, funsort, buf);
  result = btor_apply_exps (btor, BTOR_COUNT_STACK (params), params.start, uf);
  btor_release_sort (sorts, domain);
  btor_release_sort (sorts, funsort);
  btor_release_exp (btor, uf);
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, tsorts);
  BTOR_MSG (btor->msg, 1, "create fresh skolem constant %s", buf);
  return result;
}

static BtorNode *
normalize_quantifiers (Btor *btor, BtorNode *roots[], uint32_t num_roots)
{
  int32_t i, id;
  uint32_t j;
  BtorNode *cur, *cur_pol, *e_pol, *real_cur, *tmp, *result, **e;
  BtorNode *ite_var, *ite_cond, *ite_if, *ite_else, *ite_c1, *ite_c2, *ite_c3;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args, conds;
  BtorIntHashTable *map;
  BtorIntHashTableData *d;
  BtorNodeKind kind;

  mm  = btor->mm;
  map = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (conds);

  for (j = 0; j < num_roots; j++)
  {
    BTOR_PUSH_STACK (mm, visit, roots[j]);
    BTOR_PUSH_STACK (mm, visit, roots[j]);
  }

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    cur_pol  = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    if (BTOR_IS_AND_NODE (real_cur) || BTOR_IS_QUANTIFIER_NODE (real_cur))
      id = BTOR_GET_ID_NODE (cur_pol);
    else
      id = real_cur->id;

    //      if (real_cur->parents == 0)
    //      printf ("root: %s (%d)\n", node2string (cur), BTOR_IS_INVERTED_NODE
    //      (cur_pol)); else printf ("visit: %s (%d)\n", node2string (cur),
    //      BTOR_IS_INVERTED_NODE (cur_pol));
    d = btor_get_int_hash_map (map, id);

    if (!d)
    {
      btor_add_int_hash_map (map, id);

      // TODO: extra handling for bv_conds to eliminate them, we have to push
      // both phasesof cond
      BTOR_PUSH_STACK (mm, visit, cur_pol);
      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
      {
        if (BTOR_IS_AND_NODE (real_cur) || BTOR_IS_QUANTIFIER_NODE (real_cur))
          e_pol = BTOR_COND_INVERT_NODE (cur_pol, real_cur->e[i]);
        else
          e_pol = real_cur->e[i];
        BTOR_PUSH_STACK (mm, visit, e_pol);
        if (BTOR_IS_QUANTIFIER_NODE (real_cur)
            && BTOR_IS_INVERTED_NODE (cur_pol) && i == 1
            && !BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (real_cur->e[i])))
          BTOR_PUSH_STACK (mm, visit, BTOR_INVERT_NODE (real_cur->e[i]));
        else
          BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (BTOR_IS_PARAM_NODE (real_cur))
          result =
              btor_param_exp (btor, btor_get_exp_width (btor, real_cur), 0);
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (BTOR_IS_SLICE_NODE (real_cur))
      {
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      // TODO: do only for quantified conds (no lambdas)
      else if (BTOR_IS_BV_COND_NODE (real_cur)
               && BTOR_REAL_ADDR_NODE (real_cur->e[0])->quantifier_below)
      {
        result = create_skolem_ite (btor, real_cur, map);

#if 0

	      result = btor_param_exp (btor,
				     btor_get_exp_width (btor, real_cur), buf);
	      printf ("buf: %s\n", buf);
#endif
        /* save ite arguments for later */
        BTOR_PUSH_STACK (mm, conds, btor_copy_exp (btor, result));
        BTOR_PUSH_STACK (mm, conds, btor_copy_exp (btor, e[0]));
        BTOR_PUSH_STACK (mm, conds, btor_copy_exp (btor, e[1]));
        BTOR_PUSH_STACK (mm, conds, btor_copy_exp (btor, e[2]));
      }
      else
      {
        if (BTOR_IS_QUANTIFIER_NODE (real_cur) && BTOR_COUNT_STACK (conds) > 0)
        {
          /* add ite contraints to scope of quantifier */
          while (!BTOR_EMPTY_STACK (conds))
          {
            ite_else = BTOR_POP_STACK (conds);
            ite_if   = BTOR_POP_STACK (conds);
            ite_cond = BTOR_POP_STACK (conds);
            ite_var  = BTOR_POP_STACK (conds);

            tmp    = btor_eq_exp (btor, ite_var, ite_if);
            ite_c1 = btor_implies_exp (btor, ite_cond, tmp);
            btor_release_exp (btor, tmp);

            tmp    = btor_eq_exp (btor, ite_var, ite_else);
            ite_c2 = btor_implies_exp (btor, BTOR_INVERT_NODE (ite_cond), tmp);
            btor_release_exp (btor, tmp);

            ite_c3 = btor_and_exp (btor, ite_c1, ite_c2);
            btor_release_exp (btor, ite_c1);
            btor_release_exp (btor, ite_c2);

            tmp = btor_and_exp (btor, ite_c3, e[1]);
            btor_release_exp (btor, ite_c3);
            btor_release_exp (btor, e[1]);
#if 0
		      e[1] = btor_exists_exp (btor, ite_var, tmp);
		      btor_release_exp (btor, tmp);
#else
            e[1] = tmp;
#endif

            btor_release_exp (btor, ite_else);
            btor_release_exp (btor, ite_if);
            btor_release_exp (btor, ite_cond);
            btor_release_exp (btor, ite_var);
          }
        }

        if (BTOR_IS_QUANTIFIER_NODE (real_cur)
            && BTOR_IS_INVERTED_NODE (cur_pol))
        {
          /* flip quantification */
          kind = real_cur->kind == BTOR_FORALL_NODE ? BTOR_EXISTS_NODE
                                                    : BTOR_FORALL_NODE;
        }
        else
          kind = real_cur->kind;
        result = btor_create_exp (btor, kind, real_cur->arity, e);
      }

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      d->as_ptr = btor_copy_exp (btor, result);
    PUSH_RESULT:
      /* quantifiers are never negated (but flipped) */
      if (!BTOR_IS_QUANTIFIER_NODE (real_cur))
        result = BTOR_COND_INVERT_NODE (cur, result);
      //	  assert (!BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE
      //(result))
      //		  || !BTOR_IS_INVERTED_NODE (result));
      //	  printf ("  result: %s\n", node2string (result));
      BTOR_PUSH_STACK (mm, args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == num_roots);

  result = BTOR_POP_STACK (args);
  while (!BTOR_EMPTY_STACK (args))
  {
    cur = BTOR_POP_STACK (args);
    tmp = btor_and_exp (btor, result, cur);
    btor_release_exp (btor, result);
    btor_release_exp (btor, cur);
    result = tmp;
  }
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, conds);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_release_exp (btor, map->data[j].as_ptr);
  }
  btor_delete_int_hash_map (map);
  return result;
}

BtorNode *
btor_normalize_quantifiers_node (Btor *btor, BtorNode *root)
{
  return normalize_quantifiers (btor, &root, 1);
}

BtorNode *
btor_normalize_quantifiers (Btor *btor)
{
  assert (btor->synthesized_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);
  assert (btor->varsubst_constraints->count == 0);

  int32_t opt_simp_const;
  BtorNode *result, *root;
  BtorMemMgr *mm;
  BtorNodePtrStack roots;
  BtorHashTableIterator it;

  mm = btor->mm;

  /* we do not want simplification of constraints here as we need the
   * complete formula in nnf */
  opt_simp_const = btor_get_opt (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS);
  btor_set_opt (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, 0);
  // TODO (ma): check if all quants checked

  BTOR_INIT_STACK (roots);
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    root = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (mm, roots, root);
  }

  result = normalize_quantifiers (btor, roots.start, BTOR_COUNT_STACK (roots));
  BTOR_RELEASE_STACK (mm, roots);
  btor_set_opt (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, opt_simp_const);
  return result;
}
