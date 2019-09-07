/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

// WIP: compact adder chains (an)
// WIP: shift negated terms on equalities over adders
//      - remove terms on both sides...
// TODO: factorize equal parts of assoc. operators (make rewrite rule global
// pass)
// TODO: normalizations of adders
//         x + 1 = -(~x)
//         x - 1 = ~(-x)
//         -(x + 1) = ~x

#include "preprocess/btornormadd.h"

#include <stdbool.h>

#include "btorcore.h"
#include "btorexp.h"
#include "btorsubst.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

static void
add_leaf_coeff (Btor *btor,
                BtorPtrHashTable *leafs,
                BtorNode *n,
                BtorNode *coeff)
{
  assert (leafs);
  assert (n);
  assert (coeff);
  assert (btor_node_is_bv_const (coeff));

#ifndef NDEBUG
  /* All constants are added into one constant at the beginning of leafs */
  BtorNode *one = btor_exp_bv_one (btor, btor_node_get_sort_id (n));
  assert (!btor_node_is_bv_const (n) || n == one);
  btor_node_release (btor, one);
#endif

  BtorPtrHashBucket *b;

  if (!(b = btor_hashptr_table_get (leafs, n)))
  {
    b              = btor_hashptr_table_add (leafs, btor_node_copy (btor, n));
    b->data.as_ptr = btor_node_copy (btor, coeff);
  }
  else
  {
    BtorNode *old_coeff = b->data.as_ptr;
    b->data.as_ptr      = btor_exp_bv_add (btor, old_coeff, coeff);
    btor_node_release (btor, old_coeff);
  }
}

static void
inc_leaf_coeff (Btor *btor, BtorPtrHashTable *leafs, BtorNode *n)
{
  BtorNode *one = btor_exp_bv_int (btor, 1, btor_node_get_sort_id (n));
  /* Constants are added as coeff of one */
  if (btor_node_is_bv_const (n))
  {
    add_leaf_coeff (btor, leafs, one, n);
  }
  else
  {
    add_leaf_coeff (btor, leafs, n, one);
  }
  btor_node_release (btor, one);
}

static BtorNode *
mul_get_coeff (BtorNode *n, BtorNode **res)
{
  if (btor_node_is_inverted (n)) return 0;
  if (!btor_node_is_bv_mul (n)) return 0;
  if (btor_node_is_bv_const (n->e[0]))
  {
    assert (!btor_node_is_bv_const (n->e[1]));
    *res = n->e[1];
    return n->e[0];
  }
  if (btor_node_is_bv_const (n->e[1]))
  {
    assert (!btor_node_is_bv_const (n->e[0]));
    *res = n->e[0];
    return n->e[1];
  }
  return 0;
}

static void
collect_add_leafs (Btor *btor, BtorNode *n, BtorPtrHashTable *leafs)
{
  assert (n);
  assert (leafs);

  uint32_t i;
  int32_t id;
  BtorIntHashTable *cache;
  BtorNodePtrStack visit;
  BtorNode *cur, *coeff, *real_cur, *res;

  // printf("*** collect\n");
  cache = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, visit);
  BTOR_PUSH_STACK (visit, n);
  do
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);
    id       = btor_node_get_id (cur);
    res      = 0;

    if (btor_node_is_bv_add (real_cur)
        && !btor_hashint_table_contains (cache, id) && real_cur->parents == 1)
    {
      btor_hashint_table_add (cache, id);

      /* ~(x + y) = ~x + ~y + 1 */
      if (btor_node_is_inverted (cur))
      {
        BTOR_PUSH_STACK (visit, btor_node_invert (real_cur->e[0]));
        BTOR_PUSH_STACK (visit, btor_node_invert (real_cur->e[1]));

        BtorNode *one = btor_exp_bv_one (btor, btor_node_get_sort_id (cur));
        inc_leaf_coeff (btor, leafs, one);
        // printf ("leaf (i): %s\n", btor_util_node2string (one));
        btor_node_release (btor, one);
        continue;
      }

      /* only traverse along adders with one parent */
      if (real_cur->parents > 1)
      {
        // printf ("leaf (p): %s\n", btor_util_node2string (cur));
        inc_leaf_coeff (btor, leafs, cur);
        continue;
      }

      for (i = 0; i < real_cur->arity; i++)
        BTOR_PUSH_STACK (visit, real_cur->e[i]);
    }
    else if ((coeff = mul_get_coeff (cur, &res)))
    {
      assert (res);
      // printf ("mul coeff: %s\n", btor_util_node2string(cur));
      // printf ("coeff: %s\n", btor_util_node2string(coeff));
      // printf ("leaf: %s\n", btor_util_node2string (res));
      add_leaf_coeff (btor, leafs, res, coeff);
    }
    else
    {
      // printf ("leaf: %s\n", btor_util_node2string (cur));
      inc_leaf_coeff (btor, leafs, cur);
    }
  } while (!BTOR_EMPTY_STACK (visit));
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);
}

static void
prep_leafs (Btor *btor, BtorPtrHashTable *t, BtorNodePtrStack *leafs)
{
  assert (t->count > 0);

  BtorPtrHashBucket *b;
  BtorPtrHashTableIterator it;
  BtorNode *cur, *coeff, *leaf;
  BtorSortId sort_id;

  sort_id        = btor_node_get_sort_id (t->first->key);
  BtorNode *zero = btor_exp_bv_zero (btor, sort_id);

  // printf("*** prep\n");
  btor_iter_hashptr_init (&it, t);
  while (btor_iter_hashptr_has_next (&it))
  {
    assert (!btor_node_is_bv_const (it.cur) || t->first->key == it.cur);
    b     = it.bucket;
    coeff = b->data.as_ptr;
    cur   = btor_iter_hashptr_next (&it);
    assert (coeff);

    // printf ("leaf: %s (%s)\n", btor_util_node2string (cur),
    // btor_util_node2string(coeff));

    /* skip all nodes with coefficient zero */
    if (coeff == zero)
    {
      goto CLEANUP;
    }

#ifndef NDEBUG
    /* all leafs have been normalized to a positive coefficient */
    if (cur != t->first->key)
    {
      BtorNode *gtz = btor_exp_bv_sgt (btor, coeff, zero);
      assert (gtz == btor->true_exp);
      btor_node_release (btor, gtz);
    }
#endif

    /* multiply with coefficient */
    leaf = btor_exp_bv_mul (btor, cur, coeff);
    BTOR_PUSH_STACK (*leafs, leaf);
    // printf ("push %s\n", btor_util_node2string(leaf));

  CLEANUP:
    btor_node_release (btor, coeff);
    b->data.as_ptr = 0;
    btor_hashptr_table_remove (t, cur, 0, 0);
    btor_node_release (btor, cur);
  }

  BTOR_PUSH_STACK_IF (
      BTOR_EMPTY_STACK (*leafs), *leafs, btor_node_copy (btor, zero));
  btor_node_release (btor, zero);
}

static void
normalize_coeffs (Btor *btor,
                  BtorSortId sort_id,
                  BtorPtrHashTable *lhs,
                  BtorPtrHashTable *rhs)
{
  BtorPtrHashBucket *blhs, *brhs;
  BtorPtrHashTableIterator it;
  BtorNode *cur, *real_cur, *lt, *c1, *c2, *neg_coeff;

  BtorNode *zero = btor_exp_bv_zero (btor, sort_id);

  assert (btor_node_is_bv_const (lhs->first->key));

  // printf ("*** normalize coeffs\n");
  btor_iter_hashptr_init (&it, lhs);
  // printf ("const leaf: %s (%s)\n", btor_util_node2string(it.cur),
  // btor_util_node2string(it.bucket->data.as_ptr));
  while (btor_iter_hashptr_has_next (&it))
  {
    blhs     = it.bucket;
    cur      = btor_iter_hashptr_next (&it);
    real_cur = btor_node_real_addr (cur);

    if (btor_node_is_bv_const (cur) || blhs->data.as_ptr == zero) continue;

      // printf ("leaf: %s (%s)\n", btor_util_node2string(cur),
      // btor_util_node2string(blhs->data.as_ptr));

#if 1
    /* c1 * ~x + c2 * x  -->  (c2 - c1) * x - c1 */
    if (btor_node_is_inverted (cur)
        && (brhs = btor_hashptr_table_get (lhs, real_cur)))
    {
      c1 = blhs->data.as_ptr;
      c2 = brhs->data.as_ptr;

      /* Apply only if there is an x */
      if (c2 != zero)
      {
        // printf ("c1: %s\n", btor_util_node2string(c1));
        // printf ("c2: %s\n", btor_util_node2string(c2));
        neg_coeff = btor_exp_bv_neg (btor, c1);
        add_leaf_coeff (btor, lhs, real_cur, neg_coeff);
        // printf ("diff: %s\n",
        // btor_util_node2string(btor_hashptr_table_get(lhs,
        // real_cur)->data.as_ptr));
        inc_leaf_coeff (btor, lhs, neg_coeff);
        btor_node_release (btor, neg_coeff);

        btor_node_release (btor, blhs->data.as_ptr);
        blhs->data.as_ptr = btor_node_copy (btor, zero);
        // printf ("n1\n");
        continue;
      }
    }
#endif

#if 1
    /* c1 * x = c2 * x  -->  0 = (c2 - c1) * x  if c1 <= c2 */
    if ((brhs = btor_hashptr_table_get (rhs, cur)))
    {
      c1 = blhs->data.as_ptr;
      c2 = brhs->data.as_ptr;

      lt = btor_exp_bv_slte (btor, c1, c2);
      if (lt == btor->true_exp)
      {
        neg_coeff = btor_exp_bv_neg (btor, c1);
        add_leaf_coeff (btor, rhs, cur, neg_coeff);
        btor_node_release (btor, neg_coeff);

        btor_node_release (btor, blhs->data.as_ptr);
        blhs->data.as_ptr = btor_node_copy (btor, zero);
        // printf ("n2\n");
      }
      btor_node_release (btor, lt);
      continue;
    }
#endif

#if 0
    /* t1 + -c * x = t2  --> t1 = t2 + c * x  */
    lt = btor_exp_bv_slt (btor, blhs->data.as_ptr, zero);
    bool is_lt = lt == btor->true_exp;
    btor_node_release (btor, lt);
    if (is_lt)
    {
      neg_coeff = btor_exp_bv_neg (btor, blhs->data.as_ptr);
      add_leaf_coeff (btor, rhs, cur, neg_coeff);
      btor_node_release (btor, neg_coeff);

      btor_node_release (btor, blhs->data.as_ptr);
      blhs->data.as_ptr = btor_node_copy (btor, zero);
      //printf ("n3\n");
      continue;
    }
#endif

#if 1
    /* t1  + c * ~a + c = t2  --> t1 = t2 + c * a */
    if (btor_node_is_inverted (cur))
    {
      c1 = blhs->data.as_ptr;
      c2 = lhs->first->data.as_ptr;

      lt         = btor_exp_bv_sgte (btor, c2, c1);
      bool is_lt = lt == btor->true_exp;
      btor_node_release (btor, lt);
      if (is_lt)
      {
        neg_coeff = btor_exp_bv_neg (btor, c1);
        inc_leaf_coeff (btor, lhs, neg_coeff);
        btor_node_release (btor, neg_coeff);

        add_leaf_coeff (btor, rhs, real_cur, c1);

        btor_node_release (btor, blhs->data.as_ptr);
        blhs->data.as_ptr = btor_node_copy (btor, zero);
        // printf ("n3\n");
        continue;
      }
    }
#endif

#if 1
    /* Normalize c * ~x  -->  -c * x - c and try to substract from rhs. */
    if (btor_node_is_inverted (cur)
        && (brhs = btor_hashptr_table_get (rhs, real_cur)))
    {
      c1 = blhs->data.as_ptr;
      c2 = brhs->data.as_ptr;

      neg_coeff = btor_exp_bv_neg (btor, c1);

      /* Move cur rhs other side, add negative coefficient rhs 'lhs' */
      lt = btor_exp_bv_slte (btor, neg_coeff, c2);
      if (lt == btor->true_exp)
      {
        add_leaf_coeff (btor, rhs, real_cur, c1);
        inc_leaf_coeff (btor, lhs, neg_coeff);

        btor_node_release (btor, blhs->data.as_ptr);
        blhs->data.as_ptr = btor_node_copy (btor, zero);
        // printf ("n4\n");
      }
      btor_node_release (btor, lt);
      btor_node_release (btor, neg_coeff);
    }
#endif
  }
  btor_node_release (btor, zero);
}

static BtorNode *
normalize_eq_adds (Btor *btor, BtorNode *eq)
{
  assert (btor_node_is_regular (eq));
  assert (btor_node_is_bv_eq (eq));

  BtorPtrHashTable *lhs_leafs, *rhs_leafs;
  BtorNodePtrStack lhs, rhs;
  BtorSortId sort_id;

  sort_id = btor_node_get_sort_id (eq->e[0]);

  BTOR_INIT_STACK (btor->mm, lhs);
  BTOR_INIT_STACK (btor->mm, rhs);

  lhs_leafs      = btor_hashptr_table_new (btor->mm,
                                      (BtorHashPtr) btor_node_hash_by_id,
                                      (BtorCmpPtr) btor_node_compare_by_id);
  rhs_leafs      = btor_hashptr_table_new (btor->mm,
                                      (BtorHashPtr) btor_node_hash_by_id,
                                      (BtorCmpPtr) btor_node_compare_by_id);
  BtorNode *one  = btor_exp_bv_one (btor, sort_id);
  BtorNode *zero = btor_exp_bv_zero (btor, sort_id);

  /* constants are stored at the first position of the hash tables */
  add_leaf_coeff (btor, lhs_leafs, one, zero);
  add_leaf_coeff (btor, rhs_leafs, one, zero);
  btor_node_release (btor, one);
  btor_node_release (btor, zero);

  collect_add_leafs (btor, eq->e[0], lhs_leafs);
  collect_add_leafs (btor, eq->e[1], rhs_leafs);

  normalize_coeffs (btor, sort_id, lhs_leafs, rhs_leafs);
  normalize_coeffs (btor, sort_id, rhs_leafs, lhs_leafs);

  prep_leafs (btor, lhs_leafs, &lhs);
  prep_leafs (btor, rhs_leafs, &rhs);

#if 0
  BtorNode *lhs_c, *rhs_c;
  lhs_c = BTOR_TOP_STACK(lhs);
  rhs_c = BTOR_TOP_STACK(rhs);

  // TODO: subtract lhs_c from rhs_c
  if (lhs_c != zero && rhs_c != zero
      && btor_node_is_bv_const(lhs_c) && btor_node_is_bv_const(rhs_c))
  {
    BtorNode *c = btor_exp_bv_sub(btor, lhs_c, rhs_c);
    BTOR_POP_STACK(lhs);
    BTOR_POP_STACK(rhs);

    btor_node_release(btor, lhs_c);
    btor_node_release(btor, rhs_c);
    BTOR_PUSH_STACK(lhs, c);
  }
#endif

  BtorNode *add_lhs =
      btor_exp_bv_add_n (btor, lhs.start, BTOR_COUNT_STACK (lhs));
  BtorNode *add_rhs =
      btor_exp_bv_add_n (btor, rhs.start, BTOR_COUNT_STACK (rhs));
  BtorNode *result = btor_exp_eq (btor, add_lhs, add_rhs);
  btor_node_release (btor, add_rhs);
  btor_node_release (btor, add_lhs);

  while (!BTOR_EMPTY_STACK (lhs))
    btor_node_release (btor, BTOR_POP_STACK (lhs));
  BTOR_RELEASE_STACK (lhs);
  while (!BTOR_EMPTY_STACK (rhs))
    btor_node_release (btor, BTOR_POP_STACK (rhs));
  BTOR_RELEASE_STACK (rhs);
  btor_hashptr_table_delete (lhs_leafs);
  btor_hashptr_table_delete (rhs_leafs);
  return result;
}

void
btor_normalize_adds (Btor *btor)
{
  uint32_t i;
  int32_t id;
  BtorPtrHashTableIterator it;
  BtorIntHashTable *cache;
  BtorNodePtrStack visit;
  BtorNode *cur, *subst;

  double start = btor_util_time_stamp ();
  btor_init_substitutions (btor);

  cache = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, visit);
  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    BTOR_PUSH_STACK (visit, cur);
  }

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));
    id  = btor_node_get_id (cur);

    if (btor_hashint_table_contains (cache, id)) continue;
    btor_hashint_table_add (cache, id);

    if (btor_node_is_bv_eq (cur)
        && (btor_node_is_bv_add (cur->e[0]) || btor_node_is_bv_add (cur->e[1])))
    {
      subst = normalize_eq_adds (btor, cur);
      btor_insert_substitution (btor, cur, subst, false);
      btor_node_release (btor, subst);
    }

    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);
  }

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);

  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (cache);

  double delta = btor_util_time_stamp () - start;
  BTOR_MSG (btor->msg, 1, "normalized adds in %.3f seconds", delta);
}
