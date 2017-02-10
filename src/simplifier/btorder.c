/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorder.h"
#include "btorcore.h"
#include "utils/btorexpiter.h"
#include "utils/btorhashint.h"
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

static bool
occurs (Btor *btor, BtorNode *param, BtorNode *term)
{
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (btor_is_param_node (param));

  bool res = false;
  uint32_t i;
  BtorNodePtrStack visit;
  BtorIntHashTable *mark;
  BtorNode *cur;
  BtorMemMgr *mm;

  mm   = btor->mm;
  mark = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, term);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (visit));

    if (!cur->parameterized || btor_contains_int_hash_table (mark, cur->id))
      continue;

    if (cur == param)
    {
      res = true;
      break;
    }

    btor_add_int_hash_table (mark, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }
  btor_delete_int_hash_table (mark);
  BTOR_RELEASE_STACK (visit);
  return res;
}

static BtorNode *
find_subst (BtorIntHashTable *map, BtorNode *node)
{
  bool inv = false;
  BtorHashTableData *d;

  goto FIND_SUBST;

  while ((d = btor_get_int_hash_map (map, node->id)))
  {
    node = d->as_ptr;
  FIND_SUBST:
    if (BTOR_IS_INVERTED_NODE (node))
    {
      inv  = !inv;
      node = BTOR_INVERT_NODE (node);
    }
  }
  return BTOR_COND_INVERT_NODE (inv, node);
}

static void
map_subst_node (BtorIntHashTable *map, BtorNode *left, BtorNode *right)
{
  right = find_subst (map, right);
  if (BTOR_IS_INVERTED_NODE (left))
  {
    left  = BTOR_INVERT_NODE (left);
    right = BTOR_INVERT_NODE (right);
  }

  assert (BTOR_IS_REGULAR_NODE (left));

  // TODO (ma): overwrite subst if substitution is "better"?
  if (btor_contains_int_hash_map (map, left->id))
  {
    //      printf ("skip add subst: %s -> %s\n", node2string (left),
    //      node2string (right));
    return;
  }

  //  printf ("subst: %s -> %s\n", node2string (left), node2string (right));
  btor_add_int_hash_map (map, left->id)->as_ptr = right;
}

static void
find_substitutions (Btor *btor,
                    BtorNode *root,
                    BtorIntHashTable *vars,
                    BtorIntHashTable *subst_map,
                    bool elim_evars)
{
  assert (btor);
  assert (root);
  assert (!btor_is_quantifier_node (root));
  assert (subst_map);

  BtorNode *cur, *real_cur, *top_and = 0;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorMemMgr *mm;

  if (!btor_is_and_node (root)) return;

  if (elim_evars && !BTOR_IS_INVERTED_NODE (root))
    top_and = root;
  else if (!elim_evars && BTOR_IS_INVERTED_NODE (root))
    top_and = BTOR_REAL_ADDR_NODE (root);

  if (!top_and) return;

  mm    = btor->mm;
  cache = btor_new_int_hash_table (mm);
  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, top_and);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_table (cache, real_cur->id)) continue;

    btor_add_int_hash_table (cache, real_cur->id);

    if (!BTOR_IS_INVERTED_NODE (cur) && btor_is_and_node (cur))
    {
      BTOR_PUSH_STACK (visit, cur->e[0]);
      BTOR_PUSH_STACK (visit, cur->e[1]);
    }
    else if (!BTOR_IS_INVERTED_NODE (cur) && btor_is_bv_eq_node (cur))
    {
      if (btor_contains_int_hash_table (vars, btor_exp_get_id (cur->e[0]))
          && !occurs (btor, cur->e[0], cur->e[1]))
        map_subst_node (subst_map, cur->e[0], cur->e[1]);
      else if (btor_contains_int_hash_table (vars, btor_exp_get_id (cur->e[1]))
               && !occurs (btor, cur->e[1], cur->e[0]))
        map_subst_node (subst_map, cur->e[1], cur->e[0]);
    }
  }
  BTOR_RELEASE_STACK (visit);
  btor_delete_int_hash_table (cache);
}

static BtorIntHashTable *
collect_quantifier_block_vars (Btor *btor,
                               BtorNode *quant,
                               BtorIntHashTable *qcache)
{
  assert (btor_is_quantifier_node (quant));

  BtorNode *cur;
  BtorNodeIterator it;
  BtorIntHashTable *vars;

  vars = btor_new_int_hash_table (btor->mm);

  /* collect variables in quantifier block 'quant' */
  btor_init_binder_iterator (&it, quant);
  while (btor_has_next_binder_iterator (&it))
  {
    cur = btor_next_binder_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (btor_is_quantifier_node (cur));
    if (cur->kind == quant->kind) btor_add_int_hash_table (vars, cur->e[0]->id);
    btor_add_int_hash_table (qcache, cur->id);
  }
  assert (it.cur == btor_binder_get_body (quant));
  assert (vars->count > 0);
  return vars;
}

static BtorNode *
elim_vars (Btor *btor, BtorNode *root, bool elim_evars)
{
  uint32_t i, num_quant_vars = 0, num_elim_vars = 0;
  BtorNode *cur, *real_cur, *e[3], *result;
  BtorNodePtrStack visit;
  BtorMemMgr *mm;
  BtorIntHashTable *mark, *map, *vars, *qcache;
  BtorHashTableData *cur_d, *d;

  mm     = btor->mm;
  mark   = btor_new_int_hash_map (mm);
  map    = btor_new_int_hash_map (mm);
  qcache = btor_new_int_hash_table (mm);

  BTOR_INIT_STACK (mm, visit);
  BTOR_PUSH_STACK (visit, root);
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    cur_d    = btor_get_int_hash_map (mark, real_cur->id);

    if (!cur_d)
    {
      btor_add_int_hash_map (mark, real_cur->id);

      /* search for var substitutions in current quantifier block */
      if (btor_is_quantifier_node (real_cur)
          && !btor_contains_int_hash_table (qcache, real_cur->id))
      {
        vars = collect_quantifier_block_vars (btor, real_cur, qcache);
        find_substitutions (
            btor, btor_binder_get_body (real_cur), vars, map, elim_evars);
        btor_delete_int_hash_table (vars);
      }

      if ((elim_evars && btor_is_exists_node (real_cur))
          || (!elim_evars && btor_is_forall_node (real_cur)))
        num_quant_vars++;

      BTOR_PUSH_STACK (visit, real_cur);
      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);

      /* we need to rebuild the substitution first */
      if ((d = btor_get_int_hash_map (map, real_cur->id)))
        BTOR_PUSH_STACK (visit, d->as_ptr);
    }
    else if (!cur_d->as_ptr)
    {
      for (i = 0; i < real_cur->arity; i++)
      {
        e[i] = find_subst (map, real_cur->e[i]);
        d    = btor_get_int_hash_map (mark, BTOR_REAL_ADDR_NODE (e[i])->id);
        assert (d);
        e[i] = BTOR_COND_INVERT_NODE (e[i], d->as_ptr);
      }
      if (real_cur->arity == 0)
      {
        /* variables in 'map' get substitued */
        if (btor_contains_int_hash_map (map, real_cur->id))
        {
          assert (btor_is_param_node (real_cur));
          continue;
        }
        if (btor_is_param_node (real_cur))
          result = mk_param_with_symbol (btor, real_cur);
        else
          result = btor_copy_exp (btor, real_cur);
      }
      else if (btor_is_slice_node (real_cur))
        result = btor_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      /* param of quantifier got substituted */
      else if (btor_is_quantifier_node (real_cur)
               && btor_contains_int_hash_map (map, real_cur->e[0]->id))
      {
        result = btor_copy_exp (btor, e[1]);
        num_elim_vars++;
      }
      else
        result = btor_create_exp (btor, real_cur->kind, e, real_cur->arity);

      cur_d->as_ptr = result;
    }
  }
  d = btor_get_int_hash_map (mark, BTOR_REAL_ADDR_NODE (root)->id);
  assert (d);
  assert (d->as_ptr);
  result = btor_copy_exp (btor, BTOR_COND_INVERT_NODE (root, d->as_ptr));
  assert (BTOR_REAL_ADDR_NODE (result)->parameterized
          == BTOR_REAL_ADDR_NODE (root)->parameterized);

  printf ("substituted %u out of %u %s variables\n",
          num_elim_vars,
          num_quant_vars,
          elim_evars ? "existential" : "universal");

  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    btor_release_exp (btor, mark->data[i].as_ptr);
  }
  btor_delete_int_hash_map (mark);
  btor_delete_int_hash_map (map);
  btor_delete_int_hash_table (qcache);
  BTOR_RELEASE_STACK (visit);
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
