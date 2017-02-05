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
#include "utils/btorexpiter.h"
#include "utils/btorhashint.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#define INV_KIND(k) \
  (k == BTOR_FORALL_NODE ? BTOR_EXISTS_NODE : BTOR_FORALL_NODE)

static BtorNode *
push_down_quantifier (Btor *btor, BtorNode *quantifier)
{
  assert (BTOR_IS_REGULAR_NODE (quantifier));
  assert (btor_is_quantifier_node (quantifier));

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
  body      = btor_binder_get_body (quantifier);
  real_body = BTOR_REAL_ADDR_NODE (body);
  /* cannot push down quantifier */
  if (!body || !btor_is_and_node (real_body)) return 0;

  cache = btor_new_int_hash_table (mm);
  map   = btor_new_int_hash_map (mm);
  //  printf ("quant: %s\n", node2string (quantifier));
  //  printf ("  body: %s\n", node2string (body));

  BTOR_INIT_STACK (mm, visit);
  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, kind);
  BTOR_INIT_STACK (mm, args_kind);
  BTOR_PUSH_STACK (kind, quantifier->kind);
  BTOR_PUSH_STACK (visit, body);
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
    if (!btor_is_and_node (real_cur))
    {
      //	  printf ("  no and\n");
      BTOR_PUSH_STACK (args, btor_copy_exp (btor, cur));
      BTOR_PUSH_STACK (args_kind, cur_kind);
      continue;
    }
    assert (cur_kind == BTOR_FORALL_NODE || cur_kind == BTOR_EXISTS_NODE);

    if (!btor_contains_int_hash_table (cache, real_cur->id))
    {
      btor_add_int_hash_table (cache, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      BTOR_PUSH_STACK (kind, cur_kind);

      // FIXME: is_free not available anymore
#if 0
	  if (btor_param_is_free (btor, param, real_cur->e[0]))
	    {
//	      printf ("  free: %s\n", node2string (real_cur->e[0]));
	      assert (!btor_param_is_free (btor, param, real_cur->e[1]));
	      BTOR_PUSH_STACK (args, btor_copy_exp (btor, real_cur->e[0]));
	      BTOR_PUSH_STACK (args_kind, 0);
	      BTOR_PUSH_STACK (visit, real_cur->e[1]);
	      if (BTOR_IS_INVERTED_NODE (cur))
		cur_kind = INV_KIND (cur_kind);
	      BTOR_PUSH_STACK (kind, cur_kind);
	    }
	  else if (btor_param_is_free (btor, param, real_cur->e[1]))
	    {
//	      printf ("  free: %s\n", node2string (real_cur->e[1]));
	      assert (!btor_param_is_free (btor, param, real_cur->e[0]));
	      BTOR_PUSH_STACK (args, btor_copy_exp (btor, real_cur->e[1]));
	      BTOR_PUSH_STACK (args_kind, 0);
	      BTOR_PUSH_STACK (visit, real_cur->e[0]);
	      if (BTOR_IS_INVERTED_NODE (cur))
		cur_kind = INV_KIND (cur_kind);
	      BTOR_PUSH_STACK (kind, cur_kind);
	    }
	  /* match: \forall x . (e0[x] /\ e1[x])
	   * result: (\forall x' . e0[x']) /\ (\forall x'' . e1[x''])
	   */
	  else
#endif
      if (cur_kind == BTOR_FORALL_NODE && !BTOR_IS_INVERTED_NODE (cur))
      {
        //	      printf ("  push forall\n");
        BTOR_PUSH_STACK (visit, real_cur->e[0]);
        BTOR_PUSH_STACK (kind, cur_kind);
        BTOR_PUSH_STACK (visit, real_cur->e[1]);
        BTOR_PUSH_STACK (kind, cur_kind);
      }
      else if (cur_kind == BTOR_EXISTS_NODE && BTOR_IS_INVERTED_NODE (cur))
      {
        //	      printf ("  push exists\n");
        //	      cur_kind = INV_KIND (cur_kind);
        BTOR_PUSH_STACK (visit, real_cur->e[0]);
        BTOR_PUSH_STACK (kind, cur_kind);
        BTOR_PUSH_STACK (visit, real_cur->e[1]);
        BTOR_PUSH_STACK (kind, cur_kind);
      }
      else
      {
        //	      printf ("  no push\n");
        BTOR_PUSH_STACK (args, btor_copy_exp (btor, cur));
        BTOR_PUSH_STACK (args_kind, cur_kind);
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
      BTOR_PUSH_STACK (args, BTOR_COND_INVERT_NODE (cur, and));
      BTOR_PUSH_STACK (args_kind, 0);
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  btor_delete_int_hash_map (map);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);
  BTOR_RELEASE_STACK (args_kind);
  BTOR_RELEASE_STACK (kind);
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
  sym = btor_get_symbol_exp (btor, node);
  if (sym)
  {
    len = strlen (sym);
    while (true)
    {
      len += 2 + btor_num_digits_util (idx);
      BTOR_NEWN (mm, buf, len);
      sprintf (buf, "%s!%d", sym, idx);
      if (btor_get_ptr_hash_table (btor->symbols, buf))
      {
        BTOR_DELETEN (mm, buf, len);
        idx += 1;
      }
      else
        break;
    }
  }
  result = btor_param_exp (btor, node->sort_id, buf);
  if (buf) BTOR_DELETEN (mm, buf, len);
  return result;
}

void
btor_miniscope (Btor *btor)
{
  uint32_t i;
  BtorPtrHashTableIterator it;
  BtorNode *cur, *subst;
  BtorNodePtrStack quants;
  BtorMemMgr *mm;

  if (btor->quantifiers->count == 0) return;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, quants);
  btor_init_ptr_hash_table_iterator (&it, btor->quantifiers);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    BTOR_PUSH_STACK (quants, cur);
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
  BTOR_RELEASE_STACK (quants);
}

static BtorNode *
miniscope (Btor *btor,
           BtorNode *quant,
           BtorIntHashTable *pushed_to,
           BtorIntHashTable *rev_pushed_to)
{
  BtorIntHashTable *cone, *cache;
  BtorNodeIterator it;
  BtorNodePtrStack visit, *pushed;
  BtorNode *cur, *real_cur, *e0, *e1;
  int32_t cur_pol;
  bool e0_cone, e1_cone;
  BtorHashTableData *d;

  cone  = btor_new_int_hash_table (btor->mm);
  cache = btor_new_int_hash_table (btor->mm);
  BTOR_INIT_STACK (btor->mm, visit);

  /* mark cone of var in order to determine parts of the formula that are
   * not dependent on var */
  BTOR_PUSH_STACK (visit, quant->e[0]);
  btor_add_int_hash_table (cone, quant->id);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (btor_contains_int_hash_table (cone, cur->id)) continue;

    btor_add_int_hash_table (cone, cur->id);
    btor_init_parent_iterator (&it, cur);
    while (btor_has_next_parent_iterator (&it))
      BTOR_PUSH_STACK (visit, btor_next_parent_iterator (&it));
  }

  // printf ("miniscope(%s)\n", node2string (quant));
  cur_pol = 1;
  BTOR_PUSH_STACK (visit, quant->e[1]);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_table (cache, real_cur->id)
        || !btor_is_bool_sort (btor, real_cur->sort_id))
      continue;

    btor_add_int_hash_table (cache, real_cur->id);

#if 0
      if ((d = btor_get_int_hash_map (rev_pushed_to, real_cur->id)))
	{
	  quants = d->as_ptr;
	  if (tmp->kind != real_cur->kind)
	    break;
	}
#endif
    if (btor_is_and_node (cur))
    {
      e0      = BTOR_REAL_ADDR_NODE (real_cur->e[0]);
      e1      = BTOR_REAL_ADDR_NODE (real_cur->e[1]);
      e0_cone = btor_contains_int_hash_table (cone, e0->id);
      e1_cone = btor_contains_int_hash_table (cone, e1->id);
      if (e0_cone && !e1_cone)
      {
        if (BTOR_IS_INVERTED_NODE (cur)) cur_pol *= -1;
        BTOR_PUSH_STACK (visit, real_cur->e[0]);
        //	      printf ("push down: %s\n", node2string (real_cur->e[0]));
      }
      else if (!e0_cone && e1_cone)
      {
        if (BTOR_IS_INVERTED_NODE (cur)) cur_pol *= -1;
        BTOR_PUSH_STACK (visit, real_cur->e[1]);
        //	      printf ("push down: %s\n", node2string (real_cur->e[1]));
      }
      else
        break;
    }
    else if ((btor_is_quantifier_node (real_cur)
              && btor_get_int_hash_map (pushed_to, real_cur->id))
             || real_cur->kind == quant->kind)
    {
      BTOR_PUSH_STACK (visit, real_cur->e[1]);
    }
  }
  if (cur != btor_binder_get_body (quant))
  {
    btor_add_int_hash_map (pushed_to, quant->id)->as_ptr = real_cur;
    if ((d = btor_get_int_hash_map (rev_pushed_to, real_cur->id)))
      pushed = d->as_ptr;
    else
    {
      d = btor_add_int_hash_map (rev_pushed_to, real_cur->id);
      BTOR_CNEW (btor->mm, pushed);
      BTOR_INIT_STACK (btor->mm, *pushed);
      d->as_ptr = pushed;
    }
    quant = BTOR_COND_INVERT_NODE (cur_pol == -1, quant);
    BTOR_PUSH_STACK (*pushed, quant);
    //      printf ("%s new scope %s\n", node2string (quant), node2string
    //      (cur));
  }

  btor_delete_int_hash_table (cone);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (visit);
  return 0;
}

static BtorNode *
rebuild (Btor *btor, BtorNode *root, BtorIntHashTable *pushed)
{
  int32_t i;
  uint32_t j;
  BtorNode *cur, *real_cur, *result, **e, *tmp, *q, *top_q;
  BtorNodePtrStack visit, args, *quants;
  BtorMemMgr *mm;
  BtorHashTableData *d, *d_p;
  BtorIntHashTable *map, *pushed_quants;

  if (pushed->count == 0) return btor_copy_exp (btor, root);

  mm = btor->mm;

  map           = btor_new_int_hash_map (mm);
  pushed_quants = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    d = btor_get_int_hash_map (map, real_cur->id);
    if (!d)
    {
      btor_add_int_hash_map (map, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (d->as_ptr == 0)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (btor_is_param_node (real_cur))
          result = mk_param_with_symbol (btor, real_cur);
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
      else if (btor_is_quantifier_node (real_cur)
               && btor_contains_int_hash_table (pushed_quants, real_cur->id))
        result = btor_copy_exp (btor, e[1]);
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

      // CHECK: can we really guarantee that 'cur' is referenced only once
      //        in the formula?
      if ((d_p = btor_get_int_hash_map (pushed, real_cur->id)))
      {
        quants = d_p->as_ptr;
        assert (!BTOR_EMPTY_STACK (*quants));
        top_q = BTOR_PEEK_STACK (*quants, 0);
        /* pol=-1, Qx .t[x] -> -(Qx . -t[x]) */
        if (BTOR_IS_INVERTED_NODE (top_q) && !BTOR_IS_INVERTED_NODE (cur))
          result = BTOR_INVERT_NODE (result);
#ifndef NDEBUG
        for (j = 1; j < BTOR_COUNT_STACK (*quants); j++)
          assert (BTOR_IS_INVERTED_NODE (top_q)
                  == BTOR_IS_INVERTED_NODE (BTOR_PEEK_STACK (*quants, j)));
#endif

        for (j = 0; j < BTOR_COUNT_STACK (*quants); j++)
        {
          q = BTOR_REAL_ADDR_NODE (BTOR_PEEK_STACK (*quants, j));
          //		  printf ("rebuild: %s (%s)\n", node2string (q),
          //node2string (result));
          assert (btor_is_quantifier_node (q));
          d_p = btor_get_int_hash_map (map, q->e[0]->id);
          assert (d_p);
          if (btor_is_forall_node (q))
            tmp = btor_forall_exp (btor, d_p->as_ptr, result);
          else
            tmp = btor_exists_exp (btor, d_p->as_ptr, result);
          btor_release_exp (btor, result);
          result = tmp;
          btor_add_int_hash_table (pushed_quants, q->id);
        }
        /* pol=-1, Qx .t[x] -> -(Qx . -t[x]) */
        if (BTOR_IS_INVERTED_NODE (top_q) && !BTOR_IS_INVERTED_NODE (cur))
          result = BTOR_INVERT_NODE (result);
        BTOR_RELEASE_STACK (*quants);
        BTOR_DELETE (mm, quants);
      }

      d->as_ptr = btor_copy_exp (btor, result);
    PUSH_RESULT:
      BTOR_PUSH_STACK (args, BTOR_COND_INVERT_NODE (cur, result));
    }
    else
    {
      result = btor_copy_exp (btor, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert (BTOR_COUNT_STACK (args) == 1);
  result = BTOR_POP_STACK (args);

  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (args);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    btor_release_exp (btor, map->data[j].as_ptr);
  }
  btor_delete_int_hash_map (map);
  btor_delete_int_hash_table (pushed_quants);

  return result;
}

BtorNode *
btor_miniscope_node (Btor *btor, BtorNode *root)
{
  uint32_t i;
  BtorNode *cur, *result;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *cache, *pushed_to, *rev_pushed_to;
  BtorHashTableData *d;

  if (btor->quantifiers->count == 0) return 0;

  mm            = btor->mm;
  cache         = btor_new_int_hash_map (mm);
  pushed_to     = btor_new_int_hash_map (mm);
  rev_pushed_to = btor_new_int_hash_map (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    d = btor_get_int_hash_map (cache, cur->id);
    if (!d)
    {
      btor_add_int_hash_map (cache, cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (btor_is_quantifier_node (cur) && btor_is_exists_node (cur))
        miniscope (btor, cur, pushed_to, rev_pushed_to);
    }
  }

  result = rebuild (btor, root, rev_pushed_to);

  //  btor_substitute_and_rebuild (btor, btor->substitutions);
  //  btor_delete_substitutions (btor);
  btor_delete_int_hash_map (cache);
  btor_delete_int_hash_map (pushed_to);
  btor_delete_int_hash_map (rev_pushed_to);
  BTOR_RELEASE_STACK (visit);
  return result;
}
