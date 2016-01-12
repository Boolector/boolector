/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorminiscope.h"
#include "utils/btorhashint.h"
#include "utils/btoriter.h"
#include "utils/btorstack.h"

static BtorNode *
get_body (BtorNode *quantifier)
{
  assert (BTOR_IS_QUANTIFIER_NODE (quantifier));
  BtorNodeKind kind;
  BtorNode *cur;

  kind = quantifier->kind;
  cur  = quantifier->e[1];
  while (BTOR_REAL_ADDR_NODE (cur)->kind == kind)
    cur = BTOR_REAL_ADDR_NODE (cur)->e[1];

  /* nested quantifier with different quantification type */
  if (BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (cur))) return 0;
  return cur;
}

#define INV_KIND(k) \
  (k == BTOR_FORALL_NODE ? BTOR_EXISTS_NODE : BTOR_FORALL_NODE)

static BtorNode *
substitute_params (Btor *btor, BtorNode *root, BtorNodeMap *param_substs)
{
  assert (btor);
  assert (root);
  assert (param_substs);

  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *subst, *result, **e;
  BtorNodePtrStack visit, args, cleanup;
  BtorIntHashTable *mark, *cache;
  BtorIntHashTableData *d;

  mm    = btor->mm;
  mark  = btor_new_int_hash_map (mm);
  cache = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (cleanup);
  BTOR_PUSH_STACK (mm, visit, root);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    subst    = btor_mapped_node (param_substs, real_cur);
    // TODO (ma): for now we only support bit vector terms

    if (!real_cur->parameterized)
    {
      result = btor_copy_exp (btor, real_cur);
      goto PUSH_RESULT;
    }

    if (subst)
    {
      result = btor_copy_exp (btor, subst);
      goto PUSH_RESULT;
    }

    assert (!BTOR_IS_BINDER_NODE (real_cur));
    d = btor_get_int_hash_map (mark, real_cur->id);
    if (!d)
    {
      (void) btor_add_int_hash_map (mark, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, visit, real_cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;

      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        result = btor_copy_exp (btor, real_cur);
      }
      else if (real_cur->arity == 1)
      {
        assert (BTOR_IS_SLICE_NODE (real_cur));
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      else
      {
        result = btor_create_exp (btor, real_cur->kind, real_cur->arity, e);
      }
      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);
      assert (!btor_get_int_hash_map (cache, real_cur->id));
      btor_add_int_hash_map (cache, real_cur->id)->as_ptr =
          btor_copy_exp (btor, result);
      BTOR_PUSH_STACK (mm, cleanup, result);
    PUSH_RESULT:
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, result));
    }
    else
    {
      assert (d->as_int == 1);
      d = btor_get_int_hash_map (cache, real_cur->id);
      assert (d);
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_release_exp (btor, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (mm, cleanup);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);
  btor_delete_int_hash_map (cache);
  btor_delete_int_hash_map (mark);
  return result;
}

static BtorNode *
invert_quantifiers (Btor *btor, BtorNode *quantifier)
{
  assert (BTOR_IS_REGULAR_NODE (quantifier));
  assert (BTOR_IS_QUANTIFIER_NODE (quantifier));

  BtorNode *cur, *param, *new_param, *body, *result, *tmp;
  BtorNodeIterator it;
  BtorNodeMap *param_substs;
  BtorNodePtrStack params;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (params);
  param_substs = btor_new_node_map (btor);
  btor_init_binder_iterator (&it, quantifier);
  while (btor_has_next_binder_iterator (&it))
  {
    cur = btor_next_binder_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_QUANTIFIER_NODE (cur));
    param = cur->e[0];
    // TODO (ma): symbol handling?
    new_param = btor_param_exp (btor, btor_get_exp_width (btor, param), 0);
    btor_map_node (param_substs, param, new_param);
    BTOR_PUSH_STACK (mm, params, cur);
    BTOR_PUSH_STACK (mm, params, new_param);
    if (btor_get_ptr_hash_table (btor->inputs, param))
    {
      btor_remove_ptr_hash_table (btor->inputs, param, 0, 0);
      btor_release_exp (btor, param);
    }
  }

  body   = btor_binder_get_body (quantifier);
  result = substitute_params (btor, body, param_substs);
  result = BTOR_INVERT_NODE (result); /* push negation down to body */
  btor_delete_node_map (param_substs);

  /* create inverted quantifier prefix */
  while (!BTOR_EMPTY_STACK (params))
  {
    param = BTOR_POP_STACK (params);
    cur   = BTOR_POP_STACK (params);
    assert (BTOR_IS_REGULAR_NODE (param));
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_PARAM_NODE (param));
    assert (BTOR_IS_QUANTIFIER_NODE (cur));
    if (BTOR_IS_FORALL_NODE (cur))
    {
      tmp = btor_exists_exp (btor, param, result);
      //	  printf ("add input: %s\n", node2string (new_param));
      /* add existential param to inputs in order to correctly print
       * models.  do not use param here as tmp might be a cached
       * existential quantifier */
      btor_add_ptr_hash_table (btor->inputs, btor_copy_exp (btor, tmp->e[0]));
    }
    else
      tmp = btor_forall_exp (btor, param, result);
    btor_release_exp (btor, result);
    btor_release_exp (btor, param);
    result = tmp;
  }
  BTOR_RELEASE_STACK (mm, params);

  assert (BTOR_IS_REGULAR_NODE (result));
  assert (BTOR_IS_QUANTIFIER_NODE (result));
  return result;
}

static BtorNode *
push_down_quantifier (Btor *btor, BtorNode *quantifier)
{
  assert (BTOR_IS_REGULAR_NODE (quantifier));
  assert (BTOR_IS_QUANTIFIER_NODE (quantifier));

  int i;
  BtorNode *param, *body, *real_body, *cur, *real_cur, *and, *e[2], *t;
  BtorNode *result, *p, *tmp;
  BtorNodeMap *subst_map;
  BtorNodePtrStack visit, args;
  BtorIntStack kind, args_kind;
  BtorMemMgr *mm;
  BtorIntHashTable *map, *cache;
  BtorNodeKind cur_kind, t_kind;

  mm        = btor->mm;
  param     = quantifier->e[0];
  body      = get_body (quantifier);
  real_body = BTOR_REAL_ADDR_NODE (body);
  /* cannot push down quantifier */
  if (!body || !BTOR_IS_AND_NODE (real_body)) return 0;

  cache = btor_new_int_hash_table (mm);
  map   = btor_new_int_hash_map (mm);
  //  printf ("quant: %s\n", node2string (quantifier));
  //  printf ("  body: %s\n", node2string (body));

  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (kind);
  BTOR_INIT_STACK (args_kind);
  BTOR_PUSH_STACK (mm, kind, quantifier->kind);
  BTOR_PUSH_STACK (mm, visit, body);
  /* push down quantifier */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    cur_kind = BTOR_POP_STACK (kind);
    //      printf ("visit: %s (%s)\n", node2string (cur), cur_kind ==
    //      BTOR_FORALL_NODE ? "forall" : "exists");
    assert (real_cur->parameterized);

    // TODO (ma): push over quantifiers of same kind?
    if (!BTOR_IS_AND_NODE (real_cur))
    {
      //	  printf ("  no and\n");
      BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, cur));
      BTOR_PUSH_STACK (mm, args_kind, cur_kind);
      continue;
    }
    assert (cur_kind == BTOR_FORALL_NODE || cur_kind == BTOR_EXISTS_NODE);

    if (!btor_contains_int_hash_table (cache, real_cur->id))
    {
      btor_add_int_hash_table (cache, real_cur->id);
      BTOR_PUSH_STACK (mm, visit, cur);
      BTOR_PUSH_STACK (mm, kind, cur_kind);

      if (btor_param_is_free (btor, param, real_cur->e[0]))
      {
        //	      printf ("  free: %s\n", node2string (real_cur->e[0]));
        assert (!btor_param_is_free (btor, param, real_cur->e[1]));
        BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, real_cur->e[0]));
        BTOR_PUSH_STACK (mm, args_kind, 0);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        if (BTOR_IS_INVERTED_NODE (cur)) cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      else if (btor_param_is_free (btor, param, real_cur->e[1]))
      {
        //	      printf ("  free: %s\n", node2string (real_cur->e[1]));
        assert (!btor_param_is_free (btor, param, real_cur->e[0]));
        BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, real_cur->e[1]));
        BTOR_PUSH_STACK (mm, args_kind, 0);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
        if (BTOR_IS_INVERTED_NODE (cur)) cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      /* match: \forall x . (e0[x] /\ e1[x])
       * result: (\forall x' . e0[x']) /\ (\forall x'' . e1[x''])
       */
      else if (BTOR_IS_FORALL_NODE_KIND (cur_kind)
               && !BTOR_IS_INVERTED_NODE (cur))
      {
        //	      printf ("  push forall\n");
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      else if (BTOR_IS_EXISTS_NODE_KIND (cur_kind)
               && BTOR_IS_INVERTED_NODE (cur))
      {
        //	      printf ("  push exists\n");
        //	      cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[0]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
        BTOR_PUSH_STACK (mm, visit, real_cur->e[1]);
        BTOR_PUSH_STACK (mm, kind, cur_kind);
      }
      else
      {
        //	      printf ("  no push\n");
        BTOR_PUSH_STACK (mm, args, btor_copy_exp (btor, cur));
        BTOR_PUSH_STACK (mm, args_kind, cur_kind);
      }
    }
    else
    {
      assert (BTOR_COUNT_STACK (args) >= 2);
      for (i = 0; i < 2; i++)
      {
        t      = BTOR_POP_STACK (args);
        t_kind = BTOR_POP_STACK (args_kind);

        if (t_kind == 0)
          e[i] = btor_copy_exp (btor, t);
        else
        {
          assert (t_kind == BTOR_FORALL_NODE || t_kind == BTOR_EXISTS_NODE);
          p = btor_param_exp (btor, btor_get_exp_width (btor, param), 0);
          subst_map = btor_new_node_map (btor);
          btor_map_node (subst_map, param, p);
          tmp = btor_substitute_terms (btor, t, subst_map);
          btor_delete_node_map (subst_map);
          if (t_kind == BTOR_FORALL_NODE)
            e[i] = btor_forall_exp (btor, p, tmp);
          else
            e[i] = btor_exists_exp (btor, p, tmp);
          btor_release_exp (btor, p);
          btor_release_exp (btor, tmp);

          // TODO (ma):
          //    1) create new param p
          //    2) substitute 'param' with p in t1 and obtain t1'
          //    3) create new quantifier with p and t1'
        }
        //	      printf ("  %d: %s (%s)\n", i, node2string (e[i]),
        // node2string (t));
        btor_release_exp (btor, t);
      }

      and = btor_and_exp (btor, e[0], e[1]);
      btor_release_exp (btor, e[0]);
      btor_release_exp (btor, e[1]);

      //	  printf ("  result: %s\n", node2string (BTOR_COND_INVERT_NODE
      //(cur, and)));
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, and));
      BTOR_PUSH_STACK (mm, args_kind, 0);
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  btor_delete_int_hash_map (map);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);
  BTOR_RELEASE_STACK (mm, args_kind);
  BTOR_RELEASE_STACK (mm, kind);
  return result;
}

static void
elimininate_negated_quantifiers (Btor *btor)
{
  assert (btor->embedded_constraints->count == 0);
  assert (btor->varsubst_constraints->count == 0);
  assert (btor->synthesized_constraints->count == 0);
  assert (btor->quantifiers->count > 0);

  int32_t i;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, **e, *cnstr, *child;
  BtorNodePtrStack visit, args, cleanup;
  BtorIntHashTable *mark, *cache;
  BtorIntHashTableData *d;
  BtorHashTableIterator it;
  BtorPtrHashTable *usc;

  mm    = btor->mm;
  mark  = btor_new_int_hash_map (mm);
  cache = btor_new_int_hash_map (mm);
  BTOR_INIT_STACK (visit);
  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (cleanup);

  usc = btor->unsynthesized_constraints;
  btor->unsynthesized_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor_init_node_hash_table_iterator (&it, usc);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cnstr = btor_next_node_hash_table_iterator (&it);
    BTOR_REAL_ADDR_NODE (cnstr)->constraint = 0;

    if (BTOR_IS_INVERTED_NODE (cnstr) && BTOR_IS_QUANTIFIER_NODE (cnstr))
    {
      result = invert_quantifiers (btor, BTOR_REAL_ADDR_NODE (cnstr));
      BTOR_PUSH_STACK (mm, visit, result);
      BTOR_PUSH_STACK (mm, cleanup, result);
    }
    else
      BTOR_PUSH_STACK (mm, visit, cnstr);

    while (!BTOR_EMPTY_STACK (visit))
    {
      cur      = BTOR_POP_STACK (visit);
      real_cur = BTOR_REAL_ADDR_NODE (cur);
      //	  printf ("visit: %s\n", node2string (cur));
      assert (!BTOR_IS_QUANTIFIER_NODE (real_cur)
              || !BTOR_IS_INVERTED_NODE (cur));

      d = btor_get_int_hash_map (mark, real_cur->id);
      if (!d)
      {
        (void) btor_add_int_hash_map (mark, real_cur->id);
        BTOR_PUSH_STACK (mm, visit, cur);
        for (i = real_cur->arity - 1; i >= 0; i--)
        {
          child = real_cur->e[i];
          if (BTOR_IS_INVERTED_NODE (child) && BTOR_IS_QUANTIFIER_NODE (child))
          {
            child = invert_quantifiers (btor, BTOR_REAL_ADDR_NODE (child));
            BTOR_PUSH_STACK (mm, cleanup, child);
          }
          //		  printf ("  child: %s\n", node2string (child));
          BTOR_PUSH_STACK (mm, visit, child);
        }
      }
      else if (d->as_int == 0)
      {
        d->as_int = 1;

        args.top -= real_cur->arity;
        e = args.top;

        if (real_cur->arity == 0)
        {
          result = btor_copy_exp (btor, real_cur);
        }
        else if (real_cur->arity == 1)
        {
          assert (BTOR_IS_SLICE_NODE (real_cur));
          result = btor_slice_exp (btor,
                                   e[0],
                                   btor_slice_get_upper (real_cur),
                                   btor_slice_get_lower (real_cur));
        }
        else
        {
          result = btor_create_exp (btor, real_cur->kind, real_cur->arity, e);
        }
        for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);
        assert (!btor_get_int_hash_map (cache, real_cur->id));
        btor_add_int_hash_map (cache, real_cur->id)->as_ptr =
            btor_copy_exp (btor, result);
        BTOR_PUSH_STACK (mm, cleanup, result);
      PUSH_RESULT:
        //	      printf ("  result: %s\n", node2string
        //(BTOR_COND_INVERT_NODE (cur, result)));
        BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, result));
      }
      else
      {
        assert (d->as_int == 1);
        d = btor_get_int_hash_map (cache, real_cur->id);
        assert (d);
        result = btor_copy_exp (btor, d->as_ptr);
        goto PUSH_RESULT;
      }
    }

    assert (BTOR_COUNT_STACK (args) == 1);
    result = BTOR_POP_STACK (args);

    if (BTOR_IS_INVERTED_NODE (result) && BTOR_IS_QUANTIFIER_NODE (result))
    {
      child = invert_quantifiers (btor, BTOR_REAL_ADDR_NODE (result));
      btor_release_exp (btor, result);
      result = child;
    }

    btor_assert_exp (btor, result);
    btor_release_exp (btor, result);
    btor_release_exp (btor, cnstr);
  }

  btor_delete_ptr_hash_table (usc);

  while (!BTOR_EMPTY_STACK (cleanup))
    btor_release_exp (btor, BTOR_POP_STACK (cleanup));
  BTOR_RELEASE_STACK (mm, cleanup);
  BTOR_RELEASE_STACK (mm, visit);
  BTOR_RELEASE_STACK (mm, args);
  btor_delete_int_hash_map (cache);
  btor_delete_int_hash_map (mark);
}

void
btor_miniscope (Btor *btor)
{
  uint32_t i;
  BtorHashTableIterator it;
  BtorNode *cur, *subst;
  BtorNodePtrStack quants;
  BtorMemMgr *mm;

  if (btor->quantifiers->count == 0) return;

  elimininate_negated_quantifiers (btor);
  return;

  mm = btor->mm;
  BTOR_INIT_STACK (quants);
  btor_init_node_hash_table_iterator (&it, btor->quantifiers);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    BTOR_PUSH_STACK (mm, quants, cur);
  }

  btor_init_substitutions (btor);
  for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
  {
    cur   = BTOR_PEEK_STACK (quants, i);
    subst = push_down_quantifier (btor, cur);
    if (!subst) continue;
    btor_insert_substitution (btor, cur, subst, 0);
    btor_release_exp (btor, subst);
  }
  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  BTOR_RELEASE_STACK (mm, quants);
}
