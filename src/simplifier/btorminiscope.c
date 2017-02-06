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
#include "utils/btormisc.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

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

static void
miniscope (Btor *btor,
           BtorNode *quant,
           BtorIntHashTable *pushed_to,
           BtorPtrHashTable *rev_pushed_to)
{
  BtorIntHashTable *cone, *cache;
  BtorNodeIterator it;
  BtorNodePtrStack visit, *pushed;
  BtorNode *cur, *real_cur, *e0, *e1, *cur_parent, *scope, *scope_parent;
  int32_t cur_pol;
  bool e0_cone, e1_cone;
  BtorPtrHashBucket *b;

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

  //  printf ("miniscope(%s)\n", node2string (quant));
  cur_pol      = 1;
  cur          = quant->e[1];
  cur_parent   = 0;
  scope_parent = 0;
  scope        = 0;
  while (true)
  {
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_table (cache, real_cur->id)
        || !btor_is_bool_sort (btor, real_cur->sort_id))
      continue;

    btor_add_int_hash_table (cache, real_cur->id);

    if (btor_is_and_node (cur))
    {
      e0      = BTOR_REAL_ADDR_NODE (real_cur->e[0]);
      e1      = BTOR_REAL_ADDR_NODE (real_cur->e[1]);
      e0_cone = btor_contains_int_hash_table (cone, e0->id);
      e1_cone = btor_contains_int_hash_table (cone, e1->id);
      if (e0_cone && !e1_cone)
      {
        if (BTOR_IS_INVERTED_NODE (cur)) cur_pol *= -1;
        cur          = real_cur->e[0];
        cur_parent   = BTOR_TAG_NODE (real_cur, 0);
        scope        = cur;
        scope_parent = cur_parent;
        //	      printf ("push down: %s (%s)\n", node2string (cur),
        // node2string (cur_parent));
        continue;
      }
      else if (!e0_cone && e1_cone)
      {
        if (BTOR_IS_INVERTED_NODE (cur)) cur_pol *= -1;
        cur          = real_cur->e[1];
        cur_parent   = BTOR_TAG_NODE (real_cur, 1);
        scope        = cur;
        scope_parent = cur_parent;
        //	      printf ("push down: %s (%s)\n", node2string (cur),
        // node2string (cur_parent));
        continue;
      }
    }
    else if ((btor_is_quantifier_node (real_cur)
              && btor_get_int_hash_map (pushed_to, real_cur->id))
             || real_cur->kind == quant->kind)
    {
      cur        = real_cur->e[1];
      cur_parent = BTOR_TAG_NODE (real_cur, 1);
      continue;
    }
    break;
  }

  if (scope)
  {
    assert (scope != btor_binder_get_body (quant));
    assert (cur != btor_binder_get_body (quant));
    /* 'cur_parent' is tagged with the child number, where the new scope
     * of 'quant' begins */
    assert (btor_is_and_node (scope_parent));

    btor_add_int_hash_map (pushed_to, quant->id)->as_ptr = scope;
    b = btor_get_ptr_hash_table (rev_pushed_to, scope_parent);
    if (b)
      pushed = b->data.as_ptr;
    else
    {
      b = btor_add_ptr_hash_table (rev_pushed_to, scope_parent);
      BTOR_CNEW (btor->mm, pushed);
      BTOR_INIT_STACK (btor->mm, *pushed);
      b->data.as_ptr = pushed;
    }
    quant = BTOR_COND_INVERT_NODE (cur_pol == -1, quant);
    BTOR_PUSH_STACK (*pushed, quant);
    //      printf ("%s new scope %s\n", node2string (quant), node2string
    //      (cur));
  }

  btor_delete_int_hash_table (cone);
  btor_delete_int_hash_table (cache);
  BTOR_RELEASE_STACK (visit);
}

/* create quantifiers with new scopes */
static BtorNode *
rebuild_mk_quantifiers (Btor *btor,
                        BtorNodePtrStack *quants,
                        BtorNode *body,
                        BtorIntHashTable *map,
                        BtorIntHashTable *pushed_quants)
{
  uint32_t i;
  BtorNode *top_q, *q, *result, *tmp;
  BtorHashTableData *d;

  top_q  = BTOR_PEEK_STACK (*quants, 0);
  result = btor_copy_exp (btor, body);

  /* we do not have NNF, polarities of quantifiers must not be changed
   * pol=-1, Qx . t[x] -> -(Qx . -t[x])
   * pol=-1, Qx .-t[x] -> -(Qx . t[x])
   */
  if (BTOR_IS_INVERTED_NODE (top_q)) result = BTOR_INVERT_NODE (result);

  for (i = 0; i < BTOR_COUNT_STACK (*quants); i++)
  {
    q = BTOR_PEEK_STACK (*quants, i);
    assert (btor_is_quantifier_node (q));

    //      printf ("rebuild: %s (%s)\n", node2string (q), node2string
    //      (result));
    /* all quantifiers must have the same polarity */
    assert (BTOR_IS_INVERTED_NODE (top_q) == BTOR_IS_INVERTED_NODE (q));
    d = btor_get_int_hash_map (map, BTOR_REAL_ADDR_NODE (q)->e[0]->id);
    assert (d);
    assert (d->as_ptr);
    if (btor_is_forall_node (q))
      tmp = btor_forall_exp (btor, d->as_ptr, result);
    else
      tmp = btor_exists_exp (btor, d->as_ptr, result);
    btor_release_exp (btor, result);
    result = tmp;
    btor_add_int_hash_table (pushed_quants, BTOR_REAL_ADDR_NODE (q)->id);
  }

  /* we do not have NNF, polarities of quantifiers must not be changed
   * pol=-1, Qx . t[x] -> -(Qx . -t[x])
   * pol=-1, Qx .-t[x] -> -(Qx . t[x])
   */
  if (BTOR_IS_INVERTED_NODE (top_q)) result = BTOR_INVERT_NODE (result);

  return result;
}

static BtorNode *
rebuild (Btor *btor, BtorNode *root, BtorPtrHashTable *pushed)
{
  int32_t i;
  uint32_t j;
  BtorNode *cur, *real_cur, *result, **e, *tmp;
  BtorNodePtrStack visit, args, *quants;
  BtorMemMgr *mm;
  BtorHashTableData *d;
  BtorIntHashTable *map, *pushed_quants;
  BtorPtrHashBucket *b;

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

      if ((b = btor_get_ptr_hash_table (pushed, real_cur)))
      {
        assert (btor_is_and_node (real_cur));
        quants = b->data.as_ptr;
        assert (!BTOR_EMPTY_STACK (*quants));
        tmp = rebuild_mk_quantifiers (btor, quants, e[0], map, pushed_quants);
        assert (btor_is_quantifier_node (tmp));
        //	      printf ("tmp: %s\n", node2string (tmp));
        btor_release_exp (btor, e[0]);
        e[0] = tmp;
        BTOR_RELEASE_STACK (*quants);
        BTOR_DELETE (mm, quants);
      }
      if ((b = btor_get_ptr_hash_table (pushed, BTOR_TAG_NODE (real_cur, 1))))
      {
        assert (btor_is_and_node (real_cur));
        quants = b->data.as_ptr;
        assert (!BTOR_EMPTY_STACK (*quants));
        tmp = rebuild_mk_quantifiers (btor, quants, e[1], map, pushed_quants);
        assert (btor_is_quantifier_node (tmp));
        //	      printf ("tmp: %s\n", node2string (tmp));
        btor_release_exp (btor, e[1]);
        e[1] = tmp;
        BTOR_RELEASE_STACK (*quants);
        BTOR_DELETE (mm, quants);
      }

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
      /* scope of quantifier changed */
      else if (btor_is_quantifier_node (real_cur)
               && btor_contains_int_hash_table (pushed_quants, real_cur->id))
        result = btor_copy_exp (btor, e[1]);
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_release_exp (btor, e[i]);

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
  BtorIntHashTable *cache, *pushed_to;
  BtorPtrHashTable *rev_pushed_to;
  BtorHashTableData *d;

  if (btor->quantifiers->count == 0) return 0;

  mm            = btor->mm;
  cache         = btor_new_int_hash_map (mm);
  pushed_to     = btor_new_int_hash_map (mm);
  rev_pushed_to = btor_new_ptr_hash_table (mm, 0, 0);

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

  btor_delete_int_hash_map (cache);
  btor_delete_int_hash_map (pushed_to);
  btor_delete_ptr_hash_table (rev_pushed_to);
  BTOR_RELEASE_STACK (visit);
  assert (!BTOR_REAL_ADDR_NODE (result)->parameterized);
  return result;
}
