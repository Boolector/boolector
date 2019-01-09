/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Mathias Preiner.
 *  Copyright (C) 2017-2018 Aina Niemetz.
 *  Copyright (C) 2017 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "normalizer/btornormquant.h"
#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

static BtorNode *
create_skolem_ite (Btor *btor, BtorNode *ite, BtorIntHashTable *map)
{
  assert (btor_node_is_regular (ite));
  assert (btor_node_is_bv_cond (ite));

  char buf[128];
  uint32_t i;
  BtorNodePtrStack params, visit;
  BtorSortIdStack tsorts;
  BtorNode *param, *uf, *result, *cur;
  BtorSortId domain, funsort;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm   = btor->mm;
  mark = btor_hashint_table_new (mm);

  BTOR_INIT_STACK (mm, params);
  BTOR_INIT_STACK (mm, tsorts);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, ite);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (mark, cur->id) || !cur->parameterized)
      continue;

    if (btor_node_is_param (cur))
    {
      d = btor_hashint_map_get (map, cur->id);
      assert (d);
      assert (d->as_ptr);
      param = d->as_ptr;
      BTOR_PUSH_STACK (params, param);
      BTOR_PUSH_STACK (tsorts, param->sort_id);
    }
    /* param of 'cur' is bound */
    else if (btor_node_is_quantifier (cur))
      btor_hashint_table_add (mark, cur->e[0]->id);

    btor_hashint_table_add (mark, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  sprintf (buf, "ite_%d", ite->id);
  if (BTOR_EMPTY_STACK (params))
    result = btor_exp_var (btor, ite->sort_id, buf);
  else
  {
    domain  = btor_sort_tuple (btor, tsorts.start, BTOR_COUNT_STACK (tsorts));
    funsort = btor_sort_fun (btor, domain, ite->sort_id);
    uf      = btor_exp_uf (btor, funsort, buf);
    result =
        btor_exp_apply_n (btor, uf, params.start, BTOR_COUNT_STACK (params));
    btor_sort_release (btor, domain);
    btor_sort_release (btor, funsort);
    btor_node_release (btor, uf);
  }

  btor_hashint_table_delete (mark);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (params);
  BTOR_RELEASE_STACK (tsorts);
  BTOR_MSG (btor->msg, 1, "create fresh skolem constant %s", buf);
  return result;
}

static BtorNode *
mk_param_with_symbol (Btor *btor, BtorNode *node)
{
  BtorMemMgr *mm;
  BtorNode *result;
  size_t len  = 0;
  int32_t idx = 0;
  char *sym, *buf = 0;

  mm  = btor->mm;
  sym = btor_node_get_symbol (btor, node);
  if (sym)
  {
    len = strlen (sym);
    while (true)
    {
      len += 2 + btor_util_num_digits (idx);
      BTOR_NEWN (mm, buf, len);
      sprintf (buf, "%s!%d", sym, idx);
      if (btor_hashptr_table_get (btor->symbols, buf))
      {
        BTOR_DELETEN (mm, buf, len);
        idx += 1;
      }
      else
        break;
    }
  }
  result = btor_exp_param (btor, node->sort_id, buf);
  if (buf) BTOR_DELETEN (mm, buf, len);
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
  map = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, conds);

  for (j = 0; j < num_roots; j++) BTOR_PUSH_STACK (visit, roots[j]);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    d        = btor_hashint_map_get (map, real_cur->id);

    if (!d)
    {
      /* mark new scope of 'real_cur' */
      if (btor_node_is_quantifier (real_cur)) BTOR_PUSH_STACK (conds, real_cur);

      btor_hashint_map_add (map, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_node_is_param (real_cur))
          result = mk_param_with_symbol (btor, real_cur);
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      else if (btor_node_is_bv_cond (real_cur)
               && btor_node_real_addr (real_cur->e[0])->quantifier_below)
      {
        result = create_skolem_ite (btor, real_cur, map);

        tmp    = btor_exp_eq (btor, result, e[1]);
        ite_if = btor_exp_implies (btor, e[0], tmp);
        btor_node_release (btor, tmp);

        tmp      = btor_exp_eq (btor, result, e[2]);
        ite_else = btor_exp_implies (btor, btor_node_invert (e[0]), tmp);
        btor_node_release (btor, tmp);

        ite = btor_exp_bv_and (btor, ite_if, ite_else);
        btor_node_release (btor, ite_if);
        btor_node_release (btor, ite_else);

        BTOR_PUSH_STACK (conds, ite);
      }
      else
      {
        if (btor_node_is_quantifier (real_cur))
        {
          assert (!BTOR_EMPTY_STACK (conds));
          /* add ite contraints in scope of 'real_cur' to body of
           * quantifier */
          do
          {
            ite = BTOR_POP_STACK (conds);
            if (ite == real_cur) break;
            tmp = btor_exp_bv_and (btor, ite, e[1]);
            btor_node_release (btor, ite);
            btor_node_release (btor, e[1]);
            e[1] = tmp;
          } while (!BTOR_EMPTY_STACK (conds));
        }
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);
    PUSH_RESULT:
      result = btor_node_cond_invert (cur, result);
      BTOR_PUSH_STACK (args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == num_roots);

  /* add remaining constraints to top level */
  while (!BTOR_EMPTY_STACK (conds))
  {
    tmp = BTOR_POP_STACK (conds);
    assert (!btor_node_is_quantifier (tmp));
    BTOR_PUSH_STACK (args, tmp);
  }

  result = BTOR_POP_STACK (args);
  while (!BTOR_EMPTY_STACK (args))
  {
    cur = BTOR_POP_STACK (args);
    tmp = btor_exp_bv_and (btor, result, cur);
    btor_node_release (btor, result);
    btor_node_release (btor, cur);
    result = tmp;
  }
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (conds);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_node_release (btor, map->data[j].as_ptr);
  }
  btor_hashint_map_delete (map);
  return result;
}

static int32_t
get_polarity (BtorNode *n)
{
  return btor_node_is_inverted (n) ? -1 : 1;
}

static BtorNode *
fix_quantifier_polarities (Btor *btor, BtorNode *root)
{
  int32_t i, id, cur_pol;
  uint32_t j;
  BtorNode *cur, *real_cur, *result, **e;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args, cleanup;
  BtorIntHashTable *map;
  BtorIntStack polarity, reset;
  BtorHashTableData *d, data;
  BtorNodeKind kind;

  mm  = btor->mm;
  map = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, polarity);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, reset);
  BTOR_INIT_STACK (mm, cleanup);

  BTOR_PUSH_STACK (visit, root);
  BTOR_PUSH_STACK (polarity, get_polarity (root));
  while (!BTOR_EMPTY_STACK (visit))
  {
    assert (BTOR_COUNT_STACK (visit) == BTOR_COUNT_STACK (polarity));
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    cur_pol  = BTOR_POP_STACK (polarity);

    /* bv variables have been converted to outermost existential vars in
     * normalize_quantifiers */
    assert (!btor_node_is_bv_var (real_cur));

    /* polarities are only pushed along the boolean skeleton */
    if (!btor_node_is_bv_and (real_cur) && !btor_node_is_quantifier (real_cur)
        && !(btor_node_is_bv_eq (real_cur) && real_cur->quantifier_below
             && btor_node_bv_get_width (btor, real_cur) == 1))
      cur_pol = 1;

    id = real_cur->id * cur_pol;
    d  = btor_hashint_map_get (map, id);

    if (!d)
    {
      btor_hashint_map_add (map, id);

      if (btor_node_is_quantifier (real_cur) && btor_node_is_inverted (cur)
          && cur_pol == -1)
      {
        BTOR_PUSH_STACK (visit, real_cur);
        BTOR_PUSH_STACK (polarity, cur_pol);
        /* push negation down */
        BTOR_PUSH_STACK (visit, btor_node_invert (real_cur->e[1]));
        BTOR_PUSH_STACK (polarity,
                         get_polarity (btor_node_invert (real_cur->e[1])));
        BTOR_PUSH_STACK (visit, real_cur->e[0]);
        BTOR_PUSH_STACK (polarity, 1);
      }
      /* represent boolean equality as with and/not */
      else if (btor_node_is_bv_eq (real_cur) && real_cur->quantifier_below
               && btor_node_bv_get_width (btor, real_cur->e[0]) == 1)
      {
        /* Explicitely disable rewriting here, since we *never* want the
         * created 'iff' to be rewritten to an actual boolean equality.
         * The created node is only used for traversing and getting the
         * polarities right.  With the current set of rewriting rules the
         * generated 'iff' is not rewritten to an equality, however, if
         * additional rules are introduced later we want to make sure that
         * this does not break normalization. */
        unsigned rwl = btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL);
        btor_opt_set (btor, BTOR_OPT_REWRITE_LEVEL, 0);
        BtorNode *i1  = btor_exp_implies (btor, real_cur->e[0], real_cur->e[1]);
        BtorNode *i2  = btor_exp_implies (btor, real_cur->e[1], real_cur->e[0]);
        BtorNode *iff = btor_exp_bv_and (btor, i1, i2);
        btor_node_release (btor, i1);
        btor_node_release (btor, i2);
        iff = btor_node_cond_invert (cur, iff);
        BTOR_PUSH_STACK (visit, iff);
        BTOR_PUSH_STACK (polarity, cur_pol);
        BTOR_PUSH_STACK (cleanup, iff);
        btor_opt_set (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
      }
      else
      {
        BTOR_PUSH_STACK (visit, cur);
        BTOR_PUSH_STACK (polarity, cur_pol);
        for (i = real_cur->arity - 1; i >= 0; i--)
        {
          BTOR_PUSH_STACK (visit, real_cur->e[i]);
          BTOR_PUSH_STACK (polarity, cur_pol * get_polarity (real_cur->e[i]));
        }
      }

      /* push marker for scope of 'real_cur', every parameterized exp
       * under 'real_cur' is in the scope of 'real_cur' */
      if (btor_node_is_quantifier (real_cur)) BTOR_PUSH_STACK (reset, 0);
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_node_is_param (real_cur))
          result = mk_param_with_symbol (btor, real_cur);
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      else
      {
        /* flip quantification */
        if (btor_node_is_quantifier (real_cur) && cur_pol == -1)
        {
          kind = real_cur->kind == BTOR_FORALL_NODE ? BTOR_EXISTS_NODE
                                                    : BTOR_FORALL_NODE;
        }
        else
          kind = real_cur->kind;

        result = btor_exp_create (btor, kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);

      if (real_cur->parameterized && real_cur->arity > 0)
        BTOR_PUSH_STACK (reset, id);

      /* scope of 'real_cur' is closed remove all parameterized nodes from
       * cache that are in the scope of 'real_cur'. */
      if (btor_node_is_quantifier (real_cur))
      {
        while (!BTOR_EMPTY_STACK (reset))
        {
          id = BTOR_POP_STACK (reset);
          /* scope of 'real_cur' closed */
          if (id == 0) break;
          btor_hashint_map_remove (map, id, &data);
          btor_node_release (btor, data.as_ptr);
        }
        /* remove cached param from current quantifier */
        btor_hashint_map_remove (map, real_cur->e[0]->id, &data);
        btor_node_release (btor, data.as_ptr);
      }
    PUSH_RESULT:
      result = btor_node_cond_invert (cur, result);
      BTOR_PUSH_STACK (args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_EMPTY_STACK (polarity));
  assert (BTOR_COUNT_STACK (args) == 1);

  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (polarity);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (reset);

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_node_release (btor, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (cleanup);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_node_release (btor, map->data[j].as_ptr);
  }
  btor_hashint_map_delete (map);
  return result;
}

static BtorNode *
collect_existential_vars (Btor *btor, BtorNode *root)
{
  int32_t i, id;
  uint32_t j;
  BtorNode *cur, *real_cur, *tmp, *result, **e;
  BtorMemMgr *mm;
  BtorNodePtrStack visit, args, vars;
  BtorIntHashTable *map;
  BtorHashTableData *d;

  mm  = btor->mm;
  map = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, vars);

  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    if (btor_node_is_quantifier (real_cur))
      id = btor_node_get_id (cur);
    else
      id = real_cur->id;
    d = btor_hashint_map_get (map, id);

    if (!d)
    {
      btor_hashint_map_add (map, id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_node_is_param (real_cur))
          result = mk_param_with_symbol (btor, real_cur);
        else if (btor_node_is_bv_var (real_cur))
        {
          result = mk_param_with_symbol (btor, real_cur);
          BTOR_PUSH_STACK (vars, result);
        }
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
      {
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      }
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);
    PUSH_RESULT:
      result = btor_node_cond_invert (cur, result);
      BTOR_PUSH_STACK (args, result);
    }
    else
    {
      assert (d->as_ptr);
      result = btor_node_copy (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  /* create outermost existential scope for bv variables */
  while (!BTOR_EMPTY_STACK (vars))
  {
    tmp = btor_exp_exists (btor, BTOR_POP_STACK (vars), result);
    btor_node_release (btor, result);
    result = tmp;
  }
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (vars);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_node_release (btor, map->data[j].as_ptr);
  }
  btor_hashint_map_delete (map);

  return result;
}

#ifndef NDEBUG

static bool
check_quantifiers_in_bool_skeleton (Btor *btor, BtorNode *root)
{
  bool res;
  uint32_t i;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorNode *cur;
  BtorIntHashTable *cache, *all, *found;

  mm    = btor->mm;
  cache = btor_hashint_table_new (mm);
  all   = btor_hashint_table_new (mm);
  found = btor_hashint_table_new (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)) continue;
    btor_hashint_table_add (cache, cur->id);

    if (btor_node_is_quantifier (cur)) btor_hashint_table_add (all, cur->id);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  btor_hashint_table_delete (cache);
  cache = btor_hashint_table_new (mm);

  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cache, cur->id)
        || btor_node_bv_get_width (btor, cur) != 1)
      continue;
    btor_hashint_table_add (cache, cur->id);

    if (btor_node_is_quantifier (cur)) btor_hashint_table_add (found, cur->id);

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  res = found->count == all->count;
  btor_hashint_table_delete (cache);
  btor_hashint_table_delete (found);
  btor_hashint_table_delete (all);
  BTOR_RELEASE_STACK (visit);
  return res;
}

#endif

static BtorNode *
normalize_quantifiers (Btor *btor, BtorNode *roots[], uint32_t num_roots)
{
  assert (btor);
  assert (roots);

  BtorNode *root, *root_fixed, *tmp;

  tmp = elim_quantified_ite (btor, roots, num_roots);
  assert (check_quantifiers_in_bool_skeleton (btor, tmp));

  root = collect_existential_vars (btor, tmp);
  btor_node_release (btor, tmp);

  /* since we don't have a NNF we have to check the polarities of the
   * quantifiers and flip them if necessary */
  root_fixed = fix_quantifier_polarities (btor, root);
  btor_node_release (btor, root);

  return root_fixed;
}

BtorNode *
btor_normalize_quantifiers_node (Btor *btor, BtorNode *root)
{
  assert (btor);
  assert (root);
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
  BtorPtrHashTableIterator it;

  mm = btor->mm;

  if (btor->unsynthesized_constraints->count == 0)
  {
    return btor_exp_true (btor);
  }

  /* we do not want simplification of constraints here as we need the
   * complete formula in nnf */
  opt_simp_const = btor_opt_get (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS);
  btor_opt_set (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, 0);

  BTOR_INIT_STACK (mm, roots);
  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    root = btor_iter_hashptr_next (&it);
    BTOR_PUSH_STACK (roots, root);
  }

  result = normalize_quantifiers (btor, roots.start, BTOR_COUNT_STACK (roots));
  BTOR_RELEASE_STACK (roots);
  btor_opt_set (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, opt_simp_const);
  return result;
}

#if 0
BtorNode *
btor_invert_quantifiers (Btor * btor, BtorNode * root,
			 BtorIntHashTable * node_map)
{
  size_t j;
  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, **e;
  BtorNodePtrStack stack, args;
  BtorIntHashTable *map;
  BtorHashTableData *d;

  mm = btor->mm;
  map = btor_hashint_map_new (mm);
  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, args);
  BTOR_PUSH_STACK (stack, root);
  while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_POP_STACK (stack);
      real_cur = btor_node_real_addr (cur);
      d = btor_hashint_map_get (map, real_cur->id);

      if (!d)
	{
	  btor_hashint_table_add (map, real_cur->id);

	  BTOR_PUSH_STACK (stack, cur);
	  for (i = real_cur->arity - 1; i >= 0; i--)
	    BTOR_PUSH_STACK (stack, real_cur->e[i]);
	}
      else if (!d->as_ptr)
	{
	  /* bit vector variables should be existentially quantified */
	  assert (!btor_node_is_bv_var (real_cur));
	  assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
	  args.top -= real_cur->arity;
	  e = args.top;

	  if (real_cur->arity == 0)
	    {
	      if (btor_node_is_param (real_cur))
		result = mk_param_with_symbol (btor, real_cur);
	      else
		result = btor_node_copy (btor, real_cur);

	    }
	  else if (btor_node_is_bv_slice (real_cur))
	    {
	      result = btor_exp_bv_slice (btor, e[0],
				       btor_node_bv_slice_get_upper (real_cur),
				       btor_node_bv_slice_get_lower (real_cur));
	    }
	  /* invert quantifier nodes */
	  else if (btor_node_is_quantifier (real_cur))
	    {
	      /* quantifiers are never negated (but flipped) */
	      if (!btor_node_is_quantifier (e[1]))
		e[1] = btor_node_invert (e[1]);
	      result =
		btor_exp_create (btor,
				 real_cur->kind == BTOR_EXISTS_NODE
				 ? BTOR_FORALL_NODE
				 : BTOR_EXISTS_NODE,
				 e, real_cur->arity);
	    }
	  else
	    result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

	  d->as_ptr = btor_node_copy (btor, result);

	  for (i = 0; i < real_cur->arity; i++)
	    btor_node_release (btor, e[i]);

	  if (node_map)
	    {
	      if (!btor_contains_int_hash_map (node_map, real_cur->id))
		btor_hashint_map_add (node_map, real_cur->id)->as_int =
		  btor_node_real_addr (result)->id;
	    }
PUSH_RESULT:
	  /* quantifiers are never negated (but flipped) */
	  if (!btor_node_is_quantifier (real_cur))
	    result = btor_node_cond_invert (cur, result);
	  BTOR_PUSH_STACK (args, result);
	}
      else
	{
	  assert (d->as_ptr);
	  result = btor_node_copy (btor, d->as_ptr);
	  goto PUSH_RESULT;
	}

    }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (args);

  for (j = 0; j < map->size; j++)
    {
      if (!map->data[j].as_ptr) continue;
      btor_node_release (btor, map->data[j].as_ptr);
    }
  btor_hashint_map_delete (map);

  /* quantifiers are never negated (but flipped) */
  if (!btor_node_is_quantifier (result))
    result = btor_node_invert (result);

  return result;
}
#endif
