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
  assert (btor_is_bv_cond_node (ite));

  char buf[128];
  uint32_t i;
  BtorNodePtrStack params, visit;
  BtorSortIdStack tsorts;
  BtorNode *param, *uf, *result, *cur;
  BtorSortId domain, funsort;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  BtorSortUniqueTable *sorts;

  mm    = btor->mm;
  sorts = &btor->sorts_unique_table;
  mark  = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (tsorts);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (mm, visit, ite);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (mark, cur->id) || !cur->parameterized)
      continue;

    if (btor_is_param_node (cur))
    {
      d = btor_get_int_hash_map (map, cur->id);
      assert (d);
      assert (d->as_ptr);
      param = d->as_ptr;
      BTOR_PUSH_STACK (mm, params, param);
      BTOR_PUSH_STACK (mm, tsorts, param->sort_id);
    }
    /* param of 'cur' is bound */
    else if (btor_is_quantifier_node (cur))
      btor_add_int_hash_table (mark, cur->e[0]->id);

    btor_add_int_hash_table (mark, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (mm, visit, cur->e[i]);
  }

  sprintf (buf, "ite_%d", ite->id);
  if (BTOR_EMPTY_STACK (params))
    result = btor_var_exp (btor, btor_get_exp_width (btor, ite), buf);
  else
  {
    domain  = btor_tuple_sort (sorts, tsorts.start, BTOR_COUNT_STACK (tsorts));
    funsort = btor_fun_sort (sorts, domain, ite->sort_id);
    uf      = btor_uf_exp (btor, funsort, buf);
    result =
        btor_apply_exps (btor, params.start, BTOR_COUNT_STACK (params), uf);
    btor_release_sort (sorts, domain);
    btor_release_sort (sorts, funsort);
    btor_release_exp (btor, uf);
  }

  btor_delete_int_hash_table (mark);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, tsorts);
  BTOR_MSG (btor->msg, 1, "create fresh skolem constant %s", buf);
  return result;
}

static BtorNode *
elim_quantified_ite (Btor *btor, BtorNode *roots[], uint32_t num_roots)
{
  int32_t i;
  uint32_t j;
  BtorNode *cur, *real_cur, *tmp, *result, **e;
  BtorNode *ite, *ite_if, *ite_else;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args, conds;
  BtorIntHashTable *map;
  BtorHashTableData *d;

  mm  = btor->mm;
  map = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (conds);

  for (j = 0; j < num_roots; j++) BTOR_PUSH_STACK (mm, visit, roots[j]);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    d        = btor_get_int_hash_map (map, real_cur->id);

    if (!d)
    {
      /* mark new scope of 'real_cur' */
      if (btor_is_quantifier_node (real_cur))
        BTOR_PUSH_STACK (mm, conds, real_cur);

      btor_add_int_hash_map (map, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_is_param_node (real_cur))
          result =
              btor_param_exp (btor, btor_get_exp_width (btor, real_cur), 0);
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      // TODO: do only for quantified conds (no lambdas)
      else if (btor_is_bv_cond_node (real_cur)
               && BTOR_REAL_ADDR_NODE (real_cur->e[0])->quantifier_below)
      {
        result = create_skolem_ite (btor, real_cur, map);

        tmp    = btor_eq_exp (btor, result, e[1]);
        ite_if = btor_implies_exp (btor, e[0], tmp);
        btor_release_exp (btor, tmp);

        tmp      = btor_eq_exp (btor, result, e[2]);
        ite_else = btor_implies_exp (btor, BTOR_INVERT_NODE (e[0]), tmp);
        btor_release_exp (btor, tmp);

        ite = btor_and_exp (btor, ite_if, ite_else);
        btor_release_exp (btor, ite_if);
        btor_release_exp (btor, ite_else);

        BTOR_PUSH_STACK (mm, conds, ite);
      }
      else
      {
        if (btor_is_quantifier_node (real_cur))
        {
          assert (!BTOR_EMPTY_STACK (conds));
          /* add ite contraints in scope of 'real_cur' to body of
           * quantifier */
          do
          {
            ite = BTOR_POP_STACK (conds);
            if (ite == real_cur) break;
            tmp = btor_and_exp (btor, ite, e[1]);
            btor_release_exp (btor, ite);
            btor_release_exp (btor, e[1]);
            e[1] = tmp;
          } while (!BTOR_EMPTY_STACK (conds));
        }
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      d->as_ptr = btor_copy_exp (btor, result);
    PUSH_RESULT:
      result = BTOR_COND_INVERT_NODE (cur, result);
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

  /* add remaining constraints to top level */
  while (!BTOR_EMPTY_STACK (conds))
  {
    tmp = BTOR_POP_STACK (conds);
    assert (!btor_is_quantifier_node (tmp));
    BTOR_PUSH_STACK (mm, args, tmp);
  }

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

static BtorNode *
normalize_quantifiers (Btor *btor,
                       BtorNode *roots[],
                       uint32_t num_roots,
                       BtorIntHashTable *node_map)
{
  int32_t i, id;
  uint32_t j;
  bool push_down;
  char *sym, *buf;
  size_t len;
  BtorNode *root, *cur, *cur_pol, *real_cur, *tmp, *result, **e;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, pols, args, conds, reset, vars;
  BtorIntHashTable *map;
  BtorHashTableData *d, data;
  BtorNodeKind kind;
  BtorSortUniqueTable *sorts;

  mm    = btor->mm;
  sorts = &btor->sorts_unique_table;
  map   = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (pols);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (conds);
  BTOR_INIT_STACK (reset);
  BTOR_INIT_STACK (vars);

  root = elim_quantified_ite (btor, roots, num_roots);

  BTOR_PUSH_STACK (mm, visit, root);
  BTOR_PUSH_STACK (mm, pols, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    assert (BTOR_COUNT_STACK (visit) == BTOR_COUNT_STACK (pols));
    cur     = BTOR_POP_STACK (visit);
    cur_pol = BTOR_POP_STACK (pols);
    assert (BTOR_REAL_ADDR_NODE (cur) == BTOR_REAL_ADDR_NODE (cur_pol));

    real_cur  = BTOR_REAL_ADDR_NODE (cur);
    push_down = ((btor_is_and_node (real_cur)
                  && btor_is_bool_sort (sorts, real_cur->sort_id))
                 || btor_is_quantifier_node (real_cur));

    id = push_down ? BTOR_GET_ID_NODE (cur_pol) : real_cur->id;
    d  = btor_get_int_hash_map (map, id);

    if (!d)
    {
      btor_add_int_hash_map (map, id);
      BTOR_PUSH_STACK (mm, visit, cur);
      BTOR_PUSH_STACK (mm, pols, cur_pol);
      if (push_down)
      {
        /* if quantifier gets negated we also need to negate the body */
        if (btor_is_quantifier_node (real_cur)
            && !btor_is_quantifier_node (real_cur->e[1]))
          BTOR_PUSH_STACK (
              mm, visit, BTOR_COND_INVERT_NODE (cur_pol, real_cur->e[1]));
        else
          BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);

        /* push negations down along and nodes and quantifiers */
        BTOR_PUSH_STACK (
            mm, pols, BTOR_COND_INVERT_NODE (cur_pol, real_cur->e[1]));
        if (btor_is_and_node (real_cur))
          BTOR_PUSH_STACK (
              mm, pols, BTOR_COND_INVERT_NODE (cur_pol, real_cur->e[0]));
        else
          BTOR_PUSH_STACK (mm, pols, real_cur->e[0]);
        continue;
      }
      for (i = real_cur->arity - 1; i >= 0; i--)
      {
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
        BTOR_PUSH_STACK (mm, pols, real_cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_is_param_node (real_cur))
        {
          sym = btor_get_symbol_exp (btor, real_cur);
          if (sym)
          {
            len = strlen (sym) + 3;
            BTOR_NEWN (mm, buf, len);
            sprintf (buf, "%s!0", sym);
          }
          else
            buf = 0;
          result =
              btor_param_exp (btor, btor_get_exp_width (btor, real_cur), buf);
          if (buf) BTOR_DELETEN (mm, buf, len);
        }
        else if (btor_is_bv_var_node (real_cur))
        {
          sym = btor_get_symbol_exp (btor, real_cur);
          if (sym)
          {
            len = strlen (sym) + 3;
            BTOR_NEWN (mm, buf, len);
            sprintf (buf, "%s!0", sym);
          }
          else
            buf = 0;
          result =
              btor_param_exp (btor, btor_get_exp_width (btor, real_cur), buf);
          if (buf) BTOR_DELETEN (mm, buf, len);
          BTOR_PUSH_STACK (mm, vars, result);
        }
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (btor_is_slice_node (real_cur))
      {
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      else
      {
        if (btor_is_quantifier_node (real_cur)
            && BTOR_IS_INVERTED_NODE (cur_pol))
        {
          /* flip quantification */
          kind = real_cur->kind == BTOR_FORALL_NODE ? BTOR_EXISTS_NODE
                                                    : BTOR_FORALL_NODE;
        }
        else
          kind = real_cur->kind;
        result = btor_create_exp (btor, kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      if (real_cur->parameterized)
        BTOR_PUSH_STACK (mm, reset, push_down ? cur_pol : real_cur);
      d->as_ptr = btor_copy_exp (btor, result);

      /* scope of 'real_cur' is closed remove all parameterized nodes from
       * cache that are in the scope of 'real_cur'. */
      // TODO (ma): this removes all parameterized nodes from the reset
      //		stack, which is not necessary. try to only remove
      //		parameterized nodes in the scope of real_cur
      if (btor_is_quantifier_node (real_cur))
      {
        while (!BTOR_EMPTY_STACK (reset))
        {
          tmp = BTOR_POP_STACK (reset);
          id  = BTOR_GET_ID_NODE (tmp);
          tmp = BTOR_REAL_ADDR_NODE (tmp);
          /* do not remove params other than real_cur->e[0] */
          if (btor_is_param_node (tmp) && tmp->id != real_cur->e[0]->id)
            continue;
          btor_remove_int_hash_map (map, id, &data);
          btor_release_exp (btor, data.as_ptr);
        }
      }

      if (node_map)
      {
        assert (!btor_contains_int_hash_map (node_map, real_cur->id));
        btor_add_int_hash_map (node_map, real_cur->id)->as_int =
            BTOR_REAL_ADDR_NODE (result)->id;
      }
    PUSH_RESULT:
      /* quantifiers are never negated (but flipped) */
      if (!btor_is_quantifier_node (real_cur))
        result = BTOR_COND_INVERT_NODE (cur, result);
      BTOR_PUSH_STACK (mm, args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_EMPTY_STACK (pols));
  assert (BTOR_COUNT_STACK (args) == 1);

  result = BTOR_POP_STACK (args);
  while (!BTOR_EMPTY_STACK (args))
  {
    cur = BTOR_POP_STACK (args);
    tmp = btor_and_exp (btor, result, cur);
    btor_release_exp (btor, result);
    btor_release_exp (btor, cur);
    result = tmp;
  }
  /* create outermost existential scope for bv vars */
  while (!BTOR_EMPTY_STACK (vars))
  {
    tmp = btor_exists_exp (btor, BTOR_POP_STACK (vars), result);
    btor_release_exp (btor, result);
    result = tmp;
  }
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, pols);
  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, conds);
  BTOR_RELEASE_STACK (mm, reset);
  BTOR_RELEASE_STACK (mm, vars);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_release_exp (btor, map->data[j].as_ptr);
  }
  btor_delete_int_hash_map (map);
  btor_release_exp (btor, root);
  return result;
}

BtorNode *
btor_normalize_quantifiers_node (Btor *btor,
                                 BtorNode *root,
                                 BtorIntHashTable *node_map)
{
  return normalize_quantifiers (btor, &root, 1, node_map);
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

  result =
      normalize_quantifiers (btor, roots.start, BTOR_COUNT_STACK (roots), 0);
  BTOR_RELEASE_STACK (mm, roots);
  btor_set_opt (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, opt_simp_const);
  return result;
}
