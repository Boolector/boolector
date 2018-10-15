/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorder.h"
#include "btorcore.h"
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

static bool
occurs (Btor *btor, BtorNode *param, BtorNode *term, BtorIntHashTable *deps)
{
  assert (btor_node_is_regular (param));
  assert (btor_node_is_param (param));

  bool res = false;
  uint32_t i;
  BtorNodePtrStack visit;
  BtorIntHashTable *mark, *var_deps;
  BtorNode *cur;
  BtorMemMgr *mm;

  mm   = btor->mm;
  mark = btor_hashint_table_new (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, term);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (!cur->parameterized || btor_hashint_table_contains (mark, cur->id))
      continue;

    if (cur == param)
    {
      res = true;
      break;
    }

    /* be dependency aware when substituting variables */
    if (btor_node_is_param (cur)
        && ((btor_node_param_is_forall_var (param)
             && btor_node_param_is_exists_var (cur))
            || (btor_node_param_is_exists_var (param)
                && btor_node_param_is_forall_var (cur))))
    {
      assert (btor_hashint_map_contains (deps, cur->id));
      var_deps = btor_hashint_map_get (deps, cur->id)->as_ptr;
      if (btor_hashint_table_contains (var_deps, param->id))
      {
        res = true;
        break;
      }
    }

    btor_hashint_table_add (mark, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  btor_hashint_table_delete (mark);
  BTOR_RELEASE_STACK (visit);
  return res;
}

static BtorNode *
find_subst (BtorIntHashTable *map, BtorNode *node)
{
  bool inv = false;
  BtorHashTableData *d;

  goto FIND_SUBST;

  while ((d = btor_hashint_map_get (map, node->id)))
  {
    node = d->as_ptr;
  FIND_SUBST:
    if (btor_node_is_inverted (node))
    {
      inv  = !inv;
      node = btor_node_invert (node);
    }
  }
  return inv ? btor_node_invert (node) : node;
}

static void
map_subst_node (BtorIntHashTable *map, BtorNode *left, BtorNode *right)
{
  right = find_subst (map, right);
  if (btor_node_is_inverted (left))
  {
    left  = btor_node_invert (left);
    right = btor_node_invert (right);
  }

  assert (btor_node_is_regular (left));

  // TODO (ma): overwrite subst if substitution is "better"?
  if (btor_hashint_map_contains (map, left->id))
  {
    //      printf ("skip add subst: %s -> %s\n", node2string (left),
    //      node2string (right));
    return;
  }

  //  printf ("subst: %s -> %s\n", node2string (left), node2string (right));
  btor_hashint_map_add (map, left->id)->as_ptr = right;
}

static void
find_substitutions (Btor *btor,
                    BtorNode *root,
                    BtorIntHashTable *vars,
                    BtorIntHashTable *subst_map,
                    BtorIntHashTable *deps,
                    bool elim_evars)
{
  assert (btor);
  assert (root);
  assert (!btor_node_is_quantifier (root));
  assert (subst_map);

  BtorNode *cur, *real_cur, *top_and = 0;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  if (!btor_node_is_bv_and (root)) return;

  if (elim_evars && !btor_node_is_inverted (root))
    top_and = root;
  else if (!elim_evars && btor_node_is_inverted (root))
    top_and = btor_node_real_addr (root);

  if (!top_and) return;

  mm    = btor->mm;
  cache = btor_hashint_table_new (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, top_and);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    if (btor_hashint_table_contains (cache, real_cur->id)) continue;

    btor_hashint_table_add (cache, real_cur->id);

    if (!btor_node_is_inverted (cur) && btor_node_is_bv_and (cur))
    {
      BTOR_PUSH_STACK (visit, cur->e[0]);
      BTOR_PUSH_STACK (visit, cur->e[1]);
    }
#if 0
      else if (!btor_node_is_inverted (cur) && btor_node_is_quantifier (cur))
	{
	  BTOR_PUSH_STACK (visit, cur->e[1]);
	}
#endif
    else if (!btor_node_is_inverted (cur) && btor_node_is_bv_eq (cur))
    {
      if (btor_hashint_table_contains (vars, btor_node_get_id (cur->e[0]))
          && !occurs (btor, cur->e[0], cur->e[1], deps))
        map_subst_node (subst_map, cur->e[0], cur->e[1]);
      else if (btor_hashint_table_contains (vars, btor_node_get_id (cur->e[1]))
               && !occurs (btor, cur->e[1], cur->e[0], deps))
        map_subst_node (subst_map, cur->e[1], cur->e[0]);
    }
  }
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);
}

static BtorIntHashTable *
collect_quantifier_block_vars (Btor *btor,
                               BtorNode *block,
                               BtorIntHashTable *qcache,
                               bool elim_evars)
{
  assert (btor_node_is_quantifier (block));

  BtorNode *cur;
  BtorNodeIterator it;
  BtorIntHashTable *vars;
  BtorNodeKind kind;

  kind = elim_evars ? BTOR_EXISTS_NODE : BTOR_FORALL_NODE;
  vars = btor_hashint_table_new (btor->mm);

  /* collect all variables in quantifier block 'block' of given kind,
   * DER: kind == BTOR_FORALL_NODE
   * CER: kind == BTOR_EXISTS_NODE
   */
  btor_iter_binder_init (&it, block);
  while (btor_iter_binder_has_next (&it))
  {
    cur = btor_iter_binder_next (&it);
    assert (btor_node_is_regular (cur));
    assert (btor_node_is_quantifier (cur));
    if (cur->kind == kind) btor_hashint_table_add (vars, cur->e[0]->id);
    btor_hashint_table_add (qcache, cur->id);
  }
  assert (it.cur == btor_node_binder_get_body (block));
  return vars;
}

static BtorIntHashTable *
compute_deps (Btor *btor, BtorNode *root)
{
  uint32_t i;
  BtorNode *cur, *q;
  BtorNodePtrStack visit, quants;
  BtorMemMgr *mm;
  BtorIntHashTable *mark, *deps, *tmp;
  BtorHashTableData *d;

  mm   = btor->mm;
  mark = btor_hashint_map_new (mm);
  deps = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, quants);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));
    d   = btor_hashint_map_get (mark, cur->id);

    if (!d)
    {
      btor_hashint_map_add (mark, cur->id);

      if (btor_node_is_quantifier (cur)) BTOR_PUSH_STACK (quants, cur);

      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
    }
    else if (!d->as_int)
    {
      if (btor_node_is_quantifier (cur))
      {
        tmp = btor_hashint_table_new (mm);
        for (i = 0; i < BTOR_COUNT_STACK (quants); i++)
        {
          q = BTOR_PEEK_STACK (quants, i);
          if (q->kind != cur->kind) btor_hashint_table_add (tmp, q->e[0]->id);
        }
        btor_hashint_map_add (deps, cur->e[0]->id)->as_ptr = tmp;
        q = BTOR_POP_STACK (quants);
        assert (q == cur);
      }
      d->as_int = 1;
    }
  }
  btor_hashint_map_delete (mark);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (quants);
  return deps;
}

static BtorNode *
elim_vars (Btor *btor, BtorNode *root, bool elim_evars)
{
  uint32_t i, num_quant_vars = 0, num_elim_vars = 0, opt_simp_const;
  BtorNode *cur, *real_cur, *e[3], *result;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *mark, *map, *vars, *qcache, *deps;
  BtorHashTableData *cur_d, *d;

  opt_simp_const = btor_opt_get (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS);
  btor_opt_set (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, 0);

  mm     = btor->mm;
  mark   = btor_hashint_map_new (mm);
  map    = btor_hashint_map_new (mm);
  qcache = btor_hashint_table_new (mm);
  deps   = compute_deps (btor, root);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    cur_d    = btor_hashint_map_get (mark, real_cur->id);

    if (!cur_d)
    {
      btor_hashint_map_add (mark, real_cur->id);

      /* search for var substitutions in current quantifier block */
      if (btor_node_is_quantifier (real_cur)
          && !btor_hashint_table_contains (qcache, real_cur->id))
      {
        vars =
            collect_quantifier_block_vars (btor, real_cur, qcache, elim_evars);
        if (vars->count > 0)
          find_substitutions (btor,
                              btor_node_binder_get_body (real_cur),
                              vars,
                              map,
                              deps,
                              elim_evars);
        btor_hashint_table_delete (vars);
      }

      if ((elim_evars && btor_node_is_exists (real_cur))
          || (!elim_evars && btor_node_is_forall (real_cur)))
        num_quant_vars++;

      BTOR_PUSH_STACK (visit, real_cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);

      /* we need to rebuild the substitution first */
      if ((d = btor_hashint_map_get (map, real_cur->id)))
        BTOR_PUSH_STACK (visit, d->as_ptr);
    }
    else if (!cur_d->as_ptr)
    {
      for (i = 0; i < real_cur->arity; i++)
      {
        e[i] = find_subst (map, real_cur->e[i]);
        d    = btor_hashint_map_get (mark, btor_node_real_addr (e[i])->id);
        assert (d);
        e[i] = btor_node_cond_invert (e[i], d->as_ptr);
      }
      if (real_cur->arity == 0)
      {
        /* variables in 'map' get substitued */
        if (btor_hashint_map_contains (map, real_cur->id))
        {
          assert (btor_node_is_param (real_cur));
          continue;
        }
        if (btor_node_is_param (real_cur))
          result = mk_param_with_symbol (btor, real_cur);
        else
          result = btor_node_copy (btor, real_cur);
      }
      else if (btor_node_is_bv_slice (real_cur))
        result = btor_exp_bv_slice (btor,
                                    e[0],
                                    btor_node_bv_slice_get_upper (real_cur),
                                    btor_node_bv_slice_get_lower (real_cur));
      /* param of quantifier got substituted */
      else if (btor_node_is_quantifier (real_cur)
               && btor_hashint_map_contains (map, real_cur->e[0]->id))
      {
        result = btor_node_copy (btor, e[1]);
        num_elim_vars++;
      }
      else
        result = btor_exp_create (btor, real_cur->kind, e, real_cur->arity);

      cur_d->as_ptr = result;
    }
  }
  d = btor_hashint_map_get (mark, btor_node_real_addr (root)->id);
  assert (d);
  assert (d->as_ptr);
  result = btor_node_copy (btor, btor_node_cond_invert (root, d->as_ptr));
  assert (btor_node_real_addr (result)->parameterized
          == btor_node_real_addr (root)->parameterized);

  //  printf ("substituted %u out of %u %s variables\n",
  //	  num_elim_vars, num_quant_vars, elim_evars ? "existential" :
  //"universal");

  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    btor_node_release (btor, mark->data[i].as_ptr);
  }
  for (i = 0; i < deps->size; i++)
  {
    if (!deps->data[i].as_ptr) continue;
    btor_hashint_table_delete (deps->data[i].as_ptr);
  }
  btor_hashint_map_delete (mark);
  btor_hashint_map_delete (map);
  btor_hashint_map_delete (deps);
  btor_hashint_table_delete (qcache);
  BTOR_RELEASE_STACK (visit);
  btor_opt_set (btor, BTOR_OPT_SIMPLIFY_CONSTRAINTS, opt_simp_const);
  return result;
}

BtorNode *
btor_der_node (Btor *btor, BtorNode *root)
{
  return elim_vars (btor, root, false);
}

BtorNode *
btor_cer_node (Btor *btor, BtorNode *root)
{
  return elim_vars (btor, root, true);
}
