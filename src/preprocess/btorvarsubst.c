/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2012-2019 Mathias Preiner.
 *  Copyright (C) 2012-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "preprocess/btorvarsubst.h"

#include "btorcore.h"
#include "btordbg.h"
#include "btorlog.h"
#include "btorsubst.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

static void
substitute_remove_cycles (Btor *btor, BtorPtrHashTable *substs)
{
  BtorPtrHashTable *order;
  BtorNode *cur, *left, *right, *child;
  BtorPtrHashBucket *b, *b_temp;
  BtorPtrHashTableIterator it;
  int32_t order_num, val, max;
  uint32_t i;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;
  BtorHashTableData *d;

  mm        = btor->mm;
  order_num = 1;
  order     = btor_hashptr_table_new (mm,
                                  (BtorHashPtr) btor_node_hash_by_id,
                                  (BtorCmpPtr) btor_node_compare_by_id);
  mark      = btor_hashint_table_new (mm);

  BTOR_INIT_STACK (mm, stack);

  /* we search for cyclic substitution dependencies
   * and map the substitutions to an ordering number */
  btor_iter_hashptr_init (&it, substs);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (cur));
    assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
    BTOR_PUSH_STACK (stack, cur);

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = btor_node_real_addr (BTOR_POP_STACK (stack));

      if (!cur)
      {
        cur = BTOR_POP_STACK (stack); /* left */
        assert (btor_node_is_regular (cur));
        assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
        assert (!btor_hashptr_table_get (order, cur));
        btor_hashptr_table_add (order, cur)->data.as_int = order_num++;
        continue;
      }
      /* visited (DFS) */
      if (btor_hashint_table_contains (mark, cur->id)) continue;

      btor_hashint_table_add (mark, cur->id);

      if (btor_node_is_bv_const (cur) || btor_node_is_bv_var (cur)
          || btor_node_is_param (cur) || btor_node_is_uf (cur))
      {
        b_temp = btor_hashptr_table_get (substs, cur);
        if (b_temp)
        {
          BTOR_PUSH_STACK (stack, cur); /* left  */
          BTOR_PUSH_STACK (stack, 0);
          BTOR_PUSH_STACK (stack, /* right */
                           (BtorNode *) b_temp->data.as_ptr);
        }
        else
        {
          assert (!btor_hashptr_table_get (order, cur));
          btor_hashptr_table_add (order, cur)->data.as_int = 0;
        }
      }
      else
      {
        assert (cur->arity >= 1);
        assert (cur->arity <= 3);
        for (i = 1; i <= cur->arity; i++)
          BTOR_PUSH_STACK (stack, cur->e[cur->arity - i]);
      }
    }
  }

  btor_hashint_table_delete (mark);
  mark = btor_hashint_map_new (mm);

  /* we look for cycles */
  btor_iter_hashptr_init (&it, substs);
  while (btor_iter_hashptr_has_next (&it))
  {
    b   = it.bucket;
    cur = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (cur));
    assert (btor_node_is_bv_var (cur) || btor_node_is_uf (cur));
    BTOR_PUSH_STACK (stack, (BtorNode *) b->data.as_ptr);

    /* we assume that there are no direct cycles as a result of occurrence
     * check */
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = btor_node_real_addr (BTOR_POP_STACK (stack));
      d   = btor_hashint_map_get (mark, cur->id);

      if (d && d->as_int == 1) /* cur has max order of its children */
        continue;

      if (btor_node_is_bv_const (cur) || btor_node_is_bv_var (cur)
          || btor_node_is_param (cur) || btor_node_is_uf (cur))
      {
        assert (btor_hashptr_table_get (order, cur));
        continue;
      }

      assert (cur->arity >= 1);
      assert (cur->arity <= 3);

      if (!d)
      {
        btor_hashint_map_add (mark, cur->id);
        BTOR_PUSH_STACK (stack, cur);
        for (i = 1; i <= cur->arity; i++)
          BTOR_PUSH_STACK (stack, cur->e[cur->arity - i]);
      }
      else /* cur is visited, its children are visited */
      {
        /* compute maximum of children */
        assert (d->as_int == 0);
        d->as_int = 1;
        max       = 0;
        for (i = 1; i <= cur->arity; i++)
        {
          child  = btor_node_real_addr (cur->e[cur->arity - i]);
          b_temp = btor_hashptr_table_get (order, child);
          assert (b_temp);
          val = b_temp->data.as_int;
          assert (val >= 0);
          max = BTOR_MAX_UTIL (max, val);
        }
        btor_hashptr_table_add (order, cur)->data.as_int = max;
      }
    }
  }
  btor_hashint_map_delete (mark);

  assert (BTOR_EMPTY_STACK (stack));
  /* we eliminate cyclic substitutions, and reset mark flags */
  btor_iter_hashptr_init (&it, substs);
  while (btor_iter_hashptr_has_next (&it))
  {
    right = (BtorNode *) it.bucket->data.as_ptr;
    assert (right);
    left = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (left));
    assert (btor_node_is_bv_var (left) || btor_node_is_uf (left));
    b_temp = btor_hashptr_table_get (order, left);
    assert (b_temp);
    order_num = b_temp->data.as_int;
    b_temp    = btor_hashptr_table_get (order, btor_node_real_addr (right));
    assert (b_temp);
    max = b_temp->data.as_int;
    assert (order_num != max);
    /* found cycle */
    if (max > order_num) BTOR_PUSH_STACK (stack, left);
  }

  /* we delete cyclic substitutions */
  while (!BTOR_EMPTY_STACK (stack))
  {
    left = BTOR_POP_STACK (stack);
    assert (btor_node_is_regular (left));
    assert (btor_node_is_bv_var (left) || btor_node_is_uf (left));
    right = (BtorNode *) btor_hashptr_table_get (substs, left)->data.as_ptr;
    assert (right);
    btor_hashptr_table_remove (substs, left, 0, 0);
    BTORLOG (1,
             "remove (cyclic) variable substitution: %s -> %s",
             btor_util_node2string (left),
             btor_util_node2string (right));
    btor_node_release (btor, left);
    btor_node_release (btor, right);
  }

  btor_hashptr_table_delete (order);
  BTOR_RELEASE_STACK (stack);
}

void
btor_substitute_var_exps (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *varsubst_constraints, *substs;
  BtorNode *cur, *simp, *left, *right, *simp_right;
  BtorPtrHashBucket *b;
  BtorPtrHashTableIterator it;
  double start, delta;
  uint32_t count;
  BtorMemMgr *mm;

  mm                   = btor->mm;
  varsubst_constraints = btor->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  start = btor_util_time_stamp ();

  /* new equality constraints may be added during rebuild */
  count = 0;
  while (varsubst_constraints->count > 0u)
  {
    substs = btor_hashptr_table_new (mm,
                                     (BtorHashPtr) btor_node_hash_by_id,
                                     (BtorCmpPtr) btor_node_compare_by_id);

    /* we copy the current substitution constraints into a local hash table,
     * and empty the global substitution table */
    while (varsubst_constraints->count > 0u)
    {
      b   = varsubst_constraints->first;
      cur = (BtorNode *) b->key;
      right = (BtorNode *) b->data.as_ptr;
      simp  = btor_node_get_simplified (btor, cur);
      btor_hashptr_table_remove (varsubst_constraints, cur, 0, 0);

      if (btor_node_is_regular (simp)
          && (btor_node_is_bv_var (simp) || btor_node_is_uf (simp)))
      {
        assert (btor_node_is_regular (simp));
        assert (btor_node_is_bv_var (simp) || btor_node_is_uf (simp));
        simp_right = btor_node_get_simplified (btor, right);
        assert (!btor_node_is_simplified (simp_right));
        btor_hashptr_table_add (substs, btor_node_copy (btor, simp))
            ->data.as_ptr = btor_node_copy (btor, simp_right);
      }
      btor_node_release (btor, cur);
      btor_node_release (btor, right);
    }
    assert (varsubst_constraints->count == 0u);

    BTORLOG (1, "start variable substitution");

    /* remove cycles from substitution table 'substs' */
    substitute_remove_cycles (btor, substs);

    /* we rebuild and substiute variables in one pass */
    btor_substitute_and_rebuild (btor, substs);

    BTORLOG (1, "end variable substitution");

    /* cleanup, we delete all substitution constraints */
    btor_iter_hashptr_init (&it, substs);
    while (btor_iter_hashptr_has_next (&it))
    {
      right = (BtorNode *) it.bucket->data.as_ptr;
      assert (right);
      left = btor_iter_hashptr_next (&it);
      assert (btor_node_is_regular (left));
      assert (btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST)
              || btor_node_is_proxy (left));
      assert (btor_node_is_simplified (left)
              || (!btor_opt_get (btor, BTOR_OPT_NONDESTR_SUBST)
                  || btor_node_is_synth (left)));

      /* Count number of performed substitutions. */
      if (btor_node_is_simplified (left))
      {
        count++;
      }
      btor_node_release (btor, left);
      btor_node_release (btor, right);
    }

    btor_hashptr_table_delete (substs);
  }

  delta = btor_util_time_stamp () - start;
  btor->time.subst += delta;
  BTOR_MSG (
      btor->msg, 1, "%d variables substituted in %.1f seconds", count, delta);
  assert (btor_dbg_check_all_hash_tables_proxy_free (btor));
  assert (btor_dbg_check_all_hash_tables_simp_free (btor));
  assert (btor_dbg_check_unique_table_children_proxy_free (btor));
}
