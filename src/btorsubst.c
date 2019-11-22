/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2012-2019 Mathias Preiner.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsubst.h"

#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btorlog.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static void
update_assumptions (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *ass;
  BtorNode *cur, *simp;
  BtorPtrHashTableIterator it;

  ass = btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
  btor_iter_hashptr_init (&it, btor->orig_assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    simp = btor_simplify_exp (btor, cur);
    if (!btor_hashptr_table_get (ass, simp))
    {
      BTORLOG (2,
               "update assumption: %s -> %s",
               btor_util_node2string (cur),
               btor_util_node2string (simp));
      btor_hashptr_table_add (ass, btor_node_copy (btor, simp));
    }
  }
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
    btor_node_release (btor, btor_iter_hashptr_next (&it));
  btor_hashptr_table_delete (btor->assumptions);
  btor->assumptions = ass;
}

/* update hash tables of nodes in order to get rid of proxy nodes
 */
static void
update_node_hash_tables (Btor *btor)
{
  BtorNode *cur, *data, *key, *simp_key, *simp_data;
  BtorPtrHashTableIterator it, iit;
  BtorPtrHashTable *static_rho, *new_static_rho;

  /* update static_rhos */
  btor_iter_hashptr_init (&it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur        = btor_iter_hashptr_next (&it);
    static_rho = btor_node_lambda_get_static_rho (cur);

    if (!static_rho) continue;

    new_static_rho =
        btor_hashptr_table_new (btor->mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    /* update static rho to get rid of proxy nodes */
    btor_iter_hashptr_init (&iit, static_rho);
    while (btor_iter_hashptr_has_next (&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = btor_iter_hashptr_next (&iit);
      assert (btor_node_is_regular (key));
      simp_key  = btor_simplify_exp (btor, key);
      simp_data = btor_simplify_exp (btor, data);

      if (!btor_hashptr_table_get (new_static_rho, simp_key))
      {
        btor_hashptr_table_add (new_static_rho, btor_node_copy (btor, simp_key))
            ->data.as_ptr = btor_node_copy (btor, simp_data);
      }
      btor_node_release (btor, key);
      btor_node_release (btor, data);
    }
    btor_hashptr_table_delete (static_rho);
    btor_node_lambda_set_static_rho (cur, new_static_rho);
  }
}

static BtorNode *
rebuild_binder_exp (Btor *btor, BtorNode *exp)
{
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_binder (exp));
  assert (!btor_node_param_get_assigned_exp (exp->e[0]));

  BtorNode *result;

  /* we need to reset the binding lambda here as otherwise it is not possible
   * to create a new lambda term with the same param that substitutes 'exp' */
  btor_node_param_set_binder (exp->e[0], 0);
  if (btor_node_is_forall (exp))
    result = btor_exp_forall (btor, exp->e[0], exp->e[1]);
  else if (btor_node_is_exists (exp))
    result = btor_exp_exists (btor, exp->e[0], exp->e[1]);
  else
  {
    assert (btor_node_is_lambda (exp));
    result = btor_exp_lambda (btor, exp->e[0], exp->e[1]);
  }

  /* binder not rebuilt, set binder again */
  if (result == exp) btor_node_param_set_binder (exp->e[0], exp);

  return result;
}

static BtorNode *
rebuild_lambda_exp (Btor *btor, BtorNode *exp)
{
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_lambda (exp));
  assert (!btor_node_param_get_assigned_exp (exp->e[0]));

  BtorNode *result;

  result = rebuild_binder_exp (btor, exp);

  /* copy static_rho for new lambda */
  if (btor_node_lambda_get_static_rho (exp)
      && !btor_node_lambda_get_static_rho (result))
    btor_node_lambda_set_static_rho (
        result, btor_node_lambda_copy_static_rho (btor, exp));
  if (exp->is_array) result->is_array = 1;
  return result;
}

static BtorNode *
rebuild_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));

  switch (exp->kind)
  {
    case BTOR_PROXY_NODE:
    case BTOR_BV_CONST_NODE:
    case BTOR_VAR_NODE:
    case BTOR_PARAM_NODE:
    case BTOR_UF_NODE:
      return btor_node_copy (btor, btor_simplify_exp (btor, exp));
    case BTOR_BV_SLICE_NODE:
      return btor_exp_bv_slice (btor,
                                exp->e[0],
                                btor_node_bv_slice_get_upper (exp),
                                btor_node_bv_slice_get_lower (exp));
    case BTOR_LAMBDA_NODE: return rebuild_lambda_exp (btor, exp);
    case BTOR_EXISTS_NODE:
    case BTOR_FORALL_NODE: return rebuild_binder_exp (btor, exp);
    default: return btor_exp_create (btor, exp->kind, exp->e, exp->arity);
  }
}

static BtorNode *
rebuild_noproxy (Btor *btor, BtorNode *node, BtorIntHashTable *cache)
{
  assert (btor);
  assert (node);
  assert (btor_node_is_regular (node));
  assert (!btor_node_is_simplified (node));

  size_t i;
  BtorNode *e[3]   = {0, 0, 0}, *child, *real_child, *simp;
  BtorNode *result = 0;
  BtorHashTableData *d;

  /* Note: the simplified pointer is not set for parameterized nodes. Hence, we
   * have to lookup cache. */
  for (i = 0; i < node->arity; i++)
  {
    child      = node->e[i];
    real_child = btor_node_real_addr (child);
    if (real_child->parameterized
        && (d = btor_hashint_map_get (cache, real_child->id)))
      e[i] = btor_node_cond_invert (child, d->as_ptr);
    else
      e[i] = child;
  }

  switch (node->kind)
  {
    case BTOR_PROXY_NODE:
    case BTOR_BV_CONST_NODE:
    case BTOR_VAR_NODE:
    case BTOR_UF_NODE:
    case BTOR_PARAM_NODE:
      d = btor_hashint_map_get (cache, node->id);
      if (d && d->as_ptr)
      {
        assert (d->as_ptr);
        result = btor_node_copy (btor, d->as_ptr);
      }
      else if (node->kind == BTOR_PARAM_NODE)
      {
        char *sym = btor_node_get_symbol (btor, node);
        if (0 && sym)
        {
          // TODO: make unique symbol
          size_t len = strlen (sym) + 1 + strlen ("::subst");
          char buf[len];
          snprintf (buf, len, "%s::subst", sym);
          result = btor_exp_param (btor, node->sort_id, buf);
        }
        else
        {
          result = btor_exp_param (btor, node->sort_id, 0);
        }
      }
      else
      {
        result = btor_node_copy (btor, node);
      }
      break;

    case BTOR_BV_SLICE_NODE:
      result = btor_exp_bv_slice (btor,
                                  e[0],
                                  btor_node_bv_slice_get_upper (node),
                                  btor_node_bv_slice_get_lower (node));
      break;

    default: result = btor_exp_create (btor, node->kind, e, node->arity);
  }

  simp = btor_node_copy (btor, btor_node_get_simplified (btor, result));
  btor_node_release (btor, result);
  result = simp;

  if (btor_node_is_lambda (node))
  {
    /* copy static_rho for new lambda */
    if (btor_node_lambda_get_static_rho (node)
        && !btor_node_lambda_get_static_rho (result))
    {
      btor_node_lambda_set_static_rho (
          result, btor_node_lambda_copy_static_rho (btor, node));
    }
    result->is_array = node->is_array;
  }

  assert (result);
  return result;
}

static void
substitute (Btor *btor,
            BtorNode *roots[],
            size_t nroots,
            BtorPtrHashTable *substitutions)
{
  assert (btor);
  assert (roots);
  assert (nroots);
  assert (substitutions);

  int32_t id;
  size_t i, cur_num_nodes;
  BtorNodePtrStack visit, release_stack;
  BtorHashTableData *d, *dsub;
  BtorNode *cur, *cur_subst, *real_cur_subst, *rebuilt, *simplified;
  BtorIntHashTable *substs, *cache;
#ifndef NDEBUG
  BtorIntHashTable *cnt;
#endif
  BtorPtrHashTableIterator it;
  bool opt_nondestr_subst = btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST) == 1;

  if (nroots == 0) return;

  BTORLOG (1, "start substitute");

  BTOR_INIT_STACK (btor->mm, visit);
  BTOR_INIT_STACK (btor->mm, release_stack);
  cache = btor_hashint_map_new (btor->mm);
#ifndef NDEBUG
  cnt = btor_hashint_map_new (btor->mm);
#endif

  /* normalize substitutions: -t1 -> t2 ---> t1 -> -t2 */
  substs = btor_hashint_map_new (btor->mm);
  btor_iter_hashptr_init (&it, substitutions);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur_subst = it.bucket->data.as_ptr;
    cur       = btor_iter_hashptr_next (&it);
    assert (!btor_node_is_simplified (cur));
    assert (!cur_subst || !btor_node_is_simplified (cur_subst));

    if (btor_node_is_inverted (cur))
    {
      cur = btor_node_invert (cur);
      if (cur_subst)
      {
        cur_subst = btor_node_invert (cur_subst);
      }
    }
    assert (btor_node_is_regular (cur));

    d = btor_hashint_map_add (substs, cur->id);

    /* Sometimes substitute is called with just a hash table without mapped
     * nodes (process_embedded_constraints, rebuild_formula).
     * In this case, we will just rebuild with the same node. */
    if (cur_subst)
    {
      d->as_ptr = cur_subst;
      assert (!btor_node_is_simplified (cur_subst));
    }

    BTORLOG (1,
             "substitution: %s -> %s",
             btor_util_node2string (cur),
             btor_util_node2string (cur_subst));
  }

  for (i = 0; i < nroots; i++)
  {
    BTOR_PUSH_STACK (visit, roots[i]);
    BTORLOG (1, "root: %s", btor_util_node2string (roots[i]));
  }

RESTART:
  cur_num_nodes = BTOR_COUNT_STACK (btor->nodes_id_table);

  do
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));
    assert (cur);
    id = btor_node_get_id (cur);

    /* do not traverse nodes that were not previously marked or are already
     * processed */

    if (!cur->rebuild) continue;

    d = btor_hashint_map_get (cache, id);
    BTORLOG (2,
             "visit (%s, synth: %u, param: %u): %s",
             d == 0 ? "pre" : "post",
             btor_node_is_synth (cur),
             cur->parameterized,
             btor_util_node2string (cur));
    assert (opt_nondestr_subst || !btor_node_is_simplified (cur));
    assert (!btor_node_is_proxy (cur));

    if (!d)
    {
      d         = btor_hashint_map_add (cache, id);
      d->as_ptr = 0;
      BTOR_PUSH_STACK (visit, cur);

      if ((dsub = btor_hashint_map_get (substs, id)) && dsub->as_ptr)
      {
        cur_subst = dsub->as_ptr;
        BTOR_PUSH_STACK (visit, cur_subst);
      }

      if (btor_node_is_simplified (cur))
      {
        BTOR_PUSH_STACK (visit, btor_node_get_simplified (btor, cur));
      }

      for (i = 0; i < cur->arity; i++)
      {
        BTOR_PUSH_STACK (visit, cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      if ((dsub = btor_hashint_map_get (substs, id)) && dsub->as_ptr)
      {
        cur_subst = dsub->as_ptr;
      }
      else
      {
        cur_subst = cur;
      }

      cur_subst      = btor_node_get_simplified (btor, cur_subst);
      real_cur_subst = btor_node_real_addr (cur_subst);

      if (opt_nondestr_subst)
      {
        rebuilt = rebuild_noproxy (btor, real_cur_subst, cache);
      }
      else
      {
        rebuilt = rebuild_exp (btor, real_cur_subst);
      }
      rebuilt = btor_node_cond_invert (cur_subst, rebuilt);

      assert (rebuilt);
      assert (!btor_node_is_simplified (rebuilt));

      if (cur != rebuilt && btor_node_real_addr (rebuilt)->rebuild)
      {
        BTORLOG (1,
                 "needs rebuild: %s != %s",
                 btor_util_node2string (cur),
                 btor_util_node2string (rebuilt));
        BTOR_PUSH_STACK (release_stack, rebuilt);
        BTOR_PUSH_STACK (visit, cur);
        BTOR_PUSH_STACK (visit, rebuilt);
#ifndef NDEBUG
        BtorHashTableData *d;
        if (!(d = btor_hashint_map_get (cnt, btor_node_real_addr (cur)->id)))
          d = btor_hashint_map_add (cnt, btor_node_real_addr (cur)->id);
        d->as_int++;
        assert (d->as_int < 100);
#endif
        continue;
      }

      if (dsub || cur != rebuilt)
      {
        BTORLOG (1,
                 dsub ? "substitute: %s -> %s" : "rebuild: %s -> %s",
                 btor_util_node2string (cur),
                 btor_util_node2string (rebuilt));
      }
      assert (!btor_node_real_addr (rebuilt)->parameterized
              || cur->parameterized);

      btor_hashint_map_add (cache, id)->as_ptr = btor_node_copy (btor, rebuilt);

      if (cur != rebuilt)
      {
        /* Do not rewrite synthesized and parameterized nodes if
         * non-destructive substitution is enabled.
         */
        if (!opt_nondestr_subst
            || (!btor_node_is_synth (cur) && !cur->parameterized))
        {
          simplified = btor_simplify_exp (btor, rebuilt);
          btor_set_simplified_exp (btor, cur, simplified);
        }
      }
      btor_node_release (btor, rebuilt);

      /* mark as done */
      cur->rebuild = 0;
      BTORLOG (1, "reset needs rebuild: %s", btor_util_node2string (cur));
#ifndef NDEBUG
      for (i = 0; i < cur->arity; i++)
        assert (!btor_node_real_addr (cur->e[i])->rebuild);
#endif
    }
  } while (!BTOR_EMPTY_STACK (visit));

  /* We check the rebuild flag of all new nodes that were created while
   * executing above loop. If a node's rebuild flag is true, we need to process
   * the node and thus push it onto the 'visit' stack.  We have to do this in
   * order to ensure that after a substitution pass all nodes are rebuilt and
   * consistent.
   *
   * Note: We have to do this after the pass since it can happen that new nodes
   * get created while calling btor_set_simplified_exp on a constraint that
   * have to rebuild flag enabled. For these nodes we have to do the below
   * check.
   */
  for (; cur_num_nodes < BTOR_COUNT_STACK (btor->nodes_id_table);
       cur_num_nodes++)
  {
    cur = BTOR_PEEK_STACK (btor->nodes_id_table, cur_num_nodes);
    if (!cur) continue;
    if (cur->rebuild && !cur->parents)
    {
      BTORLOG (
          1, "needs rebuild (post-subst): %s", btor_util_node2string (cur));
      BTOR_PUSH_STACK (visit, cur);
    }
  }

  if (!BTOR_EMPTY_STACK (visit))
  {
    goto RESTART;
  }

  for (i = 0; i < cache->size; i++)
  {
    if (!cache->data[i].as_ptr) continue;
    btor_node_release (btor, cache->data[i].as_ptr);
  }
  btor_hashint_map_delete (cache);
  btor_hashint_map_delete (substs);
#ifndef NDEBUG
  btor_hashint_map_delete (cnt);
#endif
  BTOR_RELEASE_STACK (visit);

  update_node_hash_tables (btor);
  update_assumptions (btor);

  while (!BTOR_EMPTY_STACK (release_stack))
  {
    btor_node_release (btor, BTOR_POP_STACK (release_stack));
  }
  BTOR_RELEASE_STACK (release_stack);

  BTORLOG (1, "end substitute");
  assert (btor_dbg_check_unique_table_rebuild (btor));
  assert (btor_dbg_check_constraints_simp_free (btor));
}

/* we perform all variable substitutions in one pass and rebuild the formula
 * cyclic substitutions must have been deleted before! */
void
btor_substitute_and_rebuild (Btor *btor, BtorPtrHashTable *substs)
{
  assert (btor);
  assert (substs);

  BtorNodePtrStack stack, root_stack;
  BtorNode *cur, *cur_parent;
  BtorMemMgr *mm;
  BtorPtrHashTableIterator it;
  BtorNodeIterator nit;
  bool ispushed;
  uint32_t i;
  bool opt_nondestr_subst;

  if (substs->count == 0u) return;

  mm                 = btor->mm;
  opt_nondestr_subst = btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST) == 1;

  BTOR_INIT_STACK (mm, stack);
  BTOR_INIT_STACK (mm, root_stack);

  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  btor_iter_hashptr_init (&it, substs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (!btor_node_is_simplified (cur));
    BTOR_PUSH_STACK (stack, cur);
  }

  do
  {
    assert (!BTOR_EMPTY_STACK (stack));
    cur = btor_node_real_addr (BTOR_POP_STACK (stack));
    assert (opt_nondestr_subst || !btor_node_is_simplified (cur));
    if (!cur->rebuild)
    {
      BTORLOG (2, "  cone: %s", btor_util_node2string (cur));

      /* All nodes in the cone of the substitutions need to be rebuilt. This
       * flag gets propagated to the parent nodes when a node gets created.
       * After a completed substitution pass, the flag for every node must be
       * zero. */
      cur->rebuild = 1;

      btor_iter_parent_init (&nit, cur);
      /* are we at a root ? */
      ispushed = false;
      while (btor_iter_parent_has_next (&nit))
      {
        cur_parent = btor_iter_parent_next (&nit);
        assert (btor_node_is_regular (cur_parent));
        ispushed = true;
        BTOR_PUSH_STACK (stack, cur_parent);
      }
      /* Alwas rebuild param nodes of binders if non-destructive substitution
       * is enabled. */
      if (opt_nondestr_subst && btor_node_is_binder (cur))
      {
        BTOR_PUSH_STACK (stack, cur->e[0]);
      }
      if (!ispushed)
      {
        BTOR_PUSH_STACK (root_stack, btor_node_copy (btor, cur));
      }
    }
  } while (!BTOR_EMPTY_STACK (stack));

  BTOR_RELEASE_STACK (stack);

  substitute (btor,
              root_stack.start,
              BTOR_COUNT_STACK (root_stack),
              substs);

  for (i = 0; i < BTOR_COUNT_STACK (root_stack); i++)
  {
    btor_node_release (btor, BTOR_PEEK_STACK (root_stack, i));
  }
  BTOR_RELEASE_STACK (root_stack);

  assert (btor_dbg_check_lambdas_static_rho_proxy_free (btor));
}
