/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorminiscope.h"
#include "btorexp.h"
#include "btornode.h"
#include "utils/btorhashint.h"
#include "utils/btornodeiter.h"
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

  cone  = btor_hashint_table_new (btor->mm);
  cache = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, visit);

  /* mark cone of var in order to determine parts of the formula that are
   * not dependent on var */
  BTOR_PUSH_STACK (visit, quant->e[0]);
  btor_hashint_table_add (cone, quant->id);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (cone, cur->id)) continue;

    btor_hashint_table_add (cone, cur->id);
    btor_iter_parent_init (&it, cur);
    while (btor_iter_parent_has_next (&it))
      BTOR_PUSH_STACK (visit, btor_iter_parent_next (&it));
  }

  //  printf ("miniscope(%s)\n", node2string (quant));
  cur_pol      = 1;
  cur          = quant->e[1];
  cur_parent   = 0;
  scope_parent = 0;
  scope        = 0;
  while (true)
  {
    real_cur = btor_node_real_addr (cur);

    if (btor_hashint_table_contains (cache, real_cur->id)
        || !btor_sort_is_bool (btor, real_cur->sort_id))
      continue;

    btor_hashint_table_add (cache, real_cur->id);

    if (btor_node_is_bv_and (cur))
    {
      e0      = btor_node_real_addr (real_cur->e[0]);
      e1      = btor_node_real_addr (real_cur->e[1]);
      e0_cone = btor_hashint_table_contains (cone, e0->id);
      e1_cone = btor_hashint_table_contains (cone, e1->id);
      if (e0_cone && !e1_cone)
      {
        if (btor_node_is_inverted (cur)) cur_pol *= -1;
        cur          = real_cur->e[0];
        cur_parent   = btor_node_set_tag (real_cur, 0);
        scope        = cur;
        scope_parent = cur_parent;
        //	      printf ("push down: %s (%s)\n", node2string (cur),
        // node2string (cur_parent));
        continue;
      }
      else if (!e0_cone && e1_cone)
      {
        if (btor_node_is_inverted (cur)) cur_pol *= -1;
        cur          = real_cur->e[1];
        cur_parent   = btor_node_set_tag (real_cur, 1);
        scope        = cur;
        scope_parent = cur_parent;
        //	      printf ("push down: %s (%s)\n", node2string (cur),
        // node2string (cur_parent));
        continue;
      }
    }
    else if ((btor_node_is_quantifier (real_cur)
              && btor_hashint_map_get (pushed_to, real_cur->id))
             || real_cur->kind == quant->kind)
    {
      cur        = real_cur->e[1];
      cur_parent = btor_node_set_tag (real_cur, 1);
      continue;
    }
    break;
  }

  if (scope)
  {
    assert (scope != btor_node_binder_get_body (quant));
    assert (cur != btor_node_binder_get_body (quant));
    /* 'cur_parent' is tagged with the child number, where the new scope
     * of 'quant' begins */
    assert (btor_node_is_bv_and (scope_parent));

    btor_hashint_map_add (pushed_to, quant->id)->as_ptr = scope;
    b = btor_hashptr_table_get (rev_pushed_to, scope_parent);
    if (b)
      pushed = b->data.as_ptr;
    else
    {
      b = btor_hashptr_table_add (rev_pushed_to, scope_parent);
      BTOR_CNEW (btor->mm, pushed);
      BTOR_INIT_STACK (btor->mm, *pushed);
      b->data.as_ptr = pushed;
    }
    quant = (cur_pol == -1) ? btor_node_invert (quant) : quant;
    BTOR_PUSH_STACK (*pushed, quant);
    //      printf ("%s new scope %s\n", node2string (quant), node2string
    //      (cur));
  }

  btor_hashint_table_delete (cone);
  btor_hashint_table_delete (cache);
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
  result = btor_node_copy (btor, body);

  /* we do not have NNF, polarities of quantifiers must not be changed
   * pol=-1, Qx . t[x] -> -(Qx . -t[x])
   * pol=-1, Qx .-t[x] -> -(Qx . t[x])
   */
  if (btor_node_is_inverted (top_q)) result = btor_node_invert (result);

  for (i = 0; i < BTOR_COUNT_STACK (*quants); i++)
  {
    q = BTOR_PEEK_STACK (*quants, i);
    assert (btor_node_is_quantifier (q));

    //      printf ("rebuild: %s (%s)\n", node2string (q), node2string
    //      (result));
    /* all quantifiers must have the same polarity */
    assert (btor_node_is_inverted (top_q) == btor_node_is_inverted (q));
    d = btor_hashint_map_get (map, btor_node_real_addr (q)->e[0]->id);
    assert (d);
    assert (d->as_ptr);
    if (btor_node_is_forall (q))
      tmp = btor_exp_forall (btor, d->as_ptr, result);
    else
      tmp = btor_exp_exists (btor, d->as_ptr, result);
    btor_node_release (btor, result);
    result = tmp;
    btor_hashint_table_add (pushed_quants, btor_node_real_addr (q)->id);
  }

  /* we do not have NNF, polarities of quantifiers must not be changed
   * pol=-1, Qx . t[x] -> -(Qx . -t[x])
   * pol=-1, Qx .-t[x] -> -(Qx . t[x])
   */
  if (btor_node_is_inverted (top_q)) result = btor_node_invert (result);

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

  if (pushed->count == 0) return btor_node_copy (btor, root);

  mm = btor->mm;

  map           = btor_hashint_map_new (mm);
  pushed_quants = btor_hashint_table_new (mm);

  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    d = btor_hashint_map_get (map, real_cur->id);
    if (!d)
    {
      btor_hashint_map_add (map, real_cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if (d->as_ptr == 0)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if ((b = btor_hashptr_table_get (pushed, real_cur)))
      {
        assert (btor_node_is_bv_and (real_cur));
        quants = b->data.as_ptr;
        assert (!BTOR_EMPTY_STACK (*quants));
        tmp = rebuild_mk_quantifiers (btor, quants, e[0], map, pushed_quants);
        btor_node_release (btor, e[0]);
        e[0] = tmp;
        BTOR_RELEASE_STACK (*quants);
        BTOR_DELETE (mm, quants);
      }
      if ((b = btor_hashptr_table_get (pushed,
                                       btor_node_set_tag (real_cur, 1))))
      {
        assert (btor_node_is_bv_and (real_cur));
        quants = b->data.as_ptr;
        assert (!BTOR_EMPTY_STACK (*quants));
        tmp = rebuild_mk_quantifiers (btor, quants, e[1], map, pushed_quants);
        btor_node_release (btor, e[1]);
        e[1] = tmp;
        BTOR_RELEASE_STACK (*quants);
        BTOR_DELETE (mm, quants);
      }

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
      /* scope of quantifier changed */
      else if (btor_node_is_quantifier (real_cur)
               && btor_hashint_table_contains (pushed_quants, real_cur->id))
        result = btor_node_copy (btor, e[1]);
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) btor_node_release (btor, e[i]);

      d->as_ptr = btor_node_copy (btor, result);
    PUSH_RESULT:
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
    }
    else
    {
      result = btor_node_copy (btor, d->as_ptr);
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
    btor_node_release (btor, map->data[j].as_ptr);
  }
  btor_hashint_map_delete (map);
  btor_hashint_table_delete (pushed_quants);
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
  cache         = btor_hashint_map_new (mm);
  pushed_to     = btor_hashint_map_new (mm);
  rev_pushed_to = btor_hashptr_table_new (mm, 0, 0);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    d = btor_hashint_map_get (cache, cur->id);
    if (!d)
    {
      btor_hashint_map_add (cache, cur->id);
      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (btor_node_is_quantifier (cur))
        miniscope (btor, cur, pushed_to, rev_pushed_to);
    }
  }

  result = rebuild (btor, root, rev_pushed_to);

  btor_hashint_map_delete (cache);
  btor_hashint_map_delete (pushed_to);
  btor_hashptr_table_delete (rev_pushed_to);
  BTOR_RELEASE_STACK (visit);
  assert (!btor_node_real_addr (result)->parameterized);
  return result;
}
