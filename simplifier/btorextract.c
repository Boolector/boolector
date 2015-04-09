/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorextract.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btoriter.h"
#include "btorutil.h"

static int
cmp_bits (const void *a, const void *b)
{
  const char *b0, *b1;
  BtorNode *x, *y;

  x = *((BtorNode **) a);
  y = *((BtorNode **) b);

  b0 = BTOR_IS_INVERTED_NODE (x) ? btor_get_invbits_const (x)
                                 : btor_get_bits_const (x);
  b1 = BTOR_IS_INVERTED_NODE (y) ? btor_get_invbits_const (y)
                                 : btor_get_bits_const (y);

  assert (b0);
  assert (b1);
  return strcmp (b0, b1);
}

/*
 *
 * diff: d
 * l,....,u
 * l <= i && i <= u && (u - i) % d == 0
 *
 * optimization if d is power of two
 *   l <= i && i <= u && (u - i) & (d - 1) = 0
 *
 *   l <= i && i <= u && (u - i)[bits(d) - 1 - 1: 0] = 0
 *
 *   d: 1
 *   l <= i && i <= u
 *
 *   d: 2
 *   l <= i && i <= u && (u - i)[0:0] = 0
 *
 *   d: 4
 *   l <= i && i <= u && (u - i)[1:0] = 0
 *
 *   d: 8
 *   l <= i && i <= u && (u - i)[2:0] = 0
 */
static inline BtorNode *
create_memset (Btor *btor,
               BtorNode *lower,
               BtorNode *upper,
               BtorNode *value,
               BtorNode *array,
               char *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lower)));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (upper)));
  assert (BTOR_REAL_ADDR_NODE (lower)->sort_id
          == BTOR_REAL_ADDR_NODE (upper)->sort_id);
  assert (offset);

  int pos;
  BtorNode *res, *param, *le0, *le1, *and, *ite, *read, *off, *sub, *rem, *eq;
  BtorNode *zero, *and2, *slice;

  param = btor_param_exp (btor, btor_get_exp_width (btor, lower), 0);
  read  = btor_read_exp (btor, array, param);
  le0   = btor_ulte_exp (btor, lower, param);
  le1   = btor_ulte_exp (btor, param, upper);
  and   = btor_and_exp (btor, le0, le1);

  if (btor_is_one_const (offset))
  {
    //      printf ("MEMSET1\n");
    ite = btor_cond_exp (btor, and, value, read);
  }
  /* const representing two */
  else if ((pos = btor_is_power_of_two_const (offset)) > -1)
  {
    assert (pos > 0);
    //      printf ("MEMSET%d\n", pos);
    sub   = btor_sub_exp (btor, upper, param);
    slice = btor_slice_exp (btor, sub, pos - 1, 0);
    zero  = btor_zero_exp (btor, btor_get_exp_width (btor, slice));
    eq    = btor_eq_exp (btor, slice, zero);
    and2  = btor_and_exp (btor, and, eq);
    ite   = btor_cond_exp (btor, and2, value, read);

    btor_release_exp (btor, zero);
    btor_release_exp (btor, slice);
    btor_release_exp (btor, sub);
    btor_release_exp (btor, eq);
    btor_release_exp (btor, and2);
  }
  else
  {
    //      printf ("MEMSETx: %s\n", offset);
    zero = btor_zero_exp (btor, btor_get_exp_width (btor, lower));
    off  = btor_const_exp (btor, offset);
    assert (BTOR_REAL_ADDR_NODE (off)->sort_id
            == BTOR_REAL_ADDR_NODE (lower)->sort_id);
    sub  = btor_sub_exp (btor, upper, param);
    rem  = btor_urem_exp (btor, sub, off);
    eq   = btor_eq_exp (btor, rem, zero);
    and2 = btor_and_exp (btor, and, eq);
    ite  = btor_cond_exp (btor, and2, value, read);

    btor_release_exp (btor, zero);
    btor_release_exp (btor, off);
    btor_release_exp (btor, sub);
    btor_release_exp (btor, rem);
    btor_release_exp (btor, eq);
    btor_release_exp (btor, and2);
  }

  res = btor_lambda_exp (btor, param, ite);

  btor_release_exp (btor, param);
  btor_release_exp (btor, le0);
  btor_release_exp (btor, le1);
  btor_release_exp (btor, and);
  btor_release_exp (btor, read);
  btor_release_exp (btor, ite);

  return res;
}

static int
is_write_exp (BtorNode *exp,
              BtorNode **array,
              BtorNode **index,
              BtorNode **value)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *param, *body, *eq, *app;

  if (!BTOR_IS_LAMBDA_NODE (exp) || btor_get_fun_arity (exp->btor, exp) > 1)
    return 0;

  param = (BtorNode *) BTOR_LAMBDA_GET_PARAM (exp);
  body  = BTOR_LAMBDA_GET_BODY (exp);

  if (BTOR_IS_INVERTED_NODE (body) || !BTOR_IS_BV_COND_NODE (body)) return 0;

  /* check condition */
  eq = body->e[0];
  if (BTOR_IS_INVERTED_NODE (eq) || !BTOR_IS_BV_EQ_NODE (eq)
      || !eq->parameterized || (eq->e[0] != param && eq->e[1] != param))
    return 0;

  /* check value */
  if (BTOR_REAL_ADDR_NODE (body->e[1])->parameterized) return 0;

  /* check apply on unmodified array */
  app = body->e[2];
  if (BTOR_IS_INVERTED_NODE (app) || !BTOR_IS_APPLY_NODE (app)
      || btor_get_fun_arity (app->btor, app->e[0]) > 1
      || app->e[1]->e[0] != param)
    return 0;

  if (array) *array = app->e[0];
  if (index) *index = eq->e[1] == param ? eq->e[0] : eq->e[1];
  if (value) *value = body->e[1];
  return 1;
}

static int
is_array_ite_exp (BtorNode *exp, BtorNode **array_if, BtorNode **array_else)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *param, *body, *app_if, *app_else;

  if (!BTOR_IS_LAMBDA_NODE (exp) || btor_get_fun_arity (exp->btor, exp) > 1)
    return 0;

  param = (BtorNode *) BTOR_LAMBDA_GET_PARAM (exp);
  body  = BTOR_LAMBDA_GET_BODY (exp);

  if (BTOR_IS_INVERTED_NODE (body) || !BTOR_IS_BV_COND_NODE (body)) return 0;

  /* check value */
  if (!BTOR_REAL_ADDR_NODE (body->e[1])->parameterized
      || !BTOR_REAL_ADDR_NODE (body->e[2])->parameterized)
    return 0;

  /* check applies in if and else branch */
  app_if = body->e[1];
  if (BTOR_IS_INVERTED_NODE (app_if) || !BTOR_IS_APPLY_NODE (app_if)
      || btor_get_fun_arity (app_if->btor, app_if->e[0]) > 1
      || app_if->e[1]->e[0] != param)
    return 0;

  app_else = body->e[1];
  if (BTOR_IS_INVERTED_NODE (app_else) || !BTOR_IS_APPLY_NODE (app_else)
      || btor_get_fun_arity (app_else->btor, app_else->e[0]) > 1
      || app_else->e[1]->e[0] != param)
    return 0;

  if (array_if) *array_if = app_if->e[0];
  if (array_else) *array_else = app_else->e[0];
  return 1;
}

static void
add_to_index_map (Btor *btor,
                  BtorPtrHashTable *map_value_index,
                  BtorNode *lambda,
                  BtorNode *index,
                  BtorNode *value)
{
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *t;
  BtorNodePtrStack *stack;

  mm = btor->mm;

  if (!(b = btor_find_in_ptr_hash_table (map_value_index, lambda)))
  {
    b             = btor_insert_in_ptr_hash_table (map_value_index, lambda);
    t             = btor_new_ptr_hash_table (mm, 0, 0);
    b->data.asPtr = t;
  }
  else
    t = b->data.asPtr;
  assert (t);

  if (!(b = btor_find_in_ptr_hash_table (t, value)))
  {
    b = btor_insert_in_ptr_hash_table (t, value);
    BTOR_NEW (mm, stack);
    BTOR_INIT_STACK (*stack);
    b->data.asPtr = stack;
  }
  else
    stack = (BtorNodePtrStack *) b->data.asPtr;
  assert (stack);
  BTOR_PUSH_STACK (mm, *stack, index);

  if (BTOR_IS_INVERTED_NODE (index) && !btor_get_invbits_const (index))
    btor_set_invbits_const (index,
                            btor_not_const (mm, btor_get_bits_const (index)));
}

static void
collect_indices_writes (Btor *btor,
                        BtorPtrHashTable *map_value_index,
                        BtorPtrHashTable *map_lambda_base)
{
  int is_top;
  BtorNode *lambda, *cur, *array, *index, *value, *tmp, *array_if, *array_else;
  BtorHashTableIterator it;
  BtorNodeIterator pit;
  BtorNodePtrStack lambdas;
  BtorPtrHashTable *index_cache, *visit_cache;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (lambdas);
  visit_cache = btor_new_ptr_hash_table (mm, 0, 0);

  /* collect lambdas that are at the top of lambda chains */
  init_node_hash_table_iterator (&it, btor->lambdas);
  while (has_next_node_hash_table_iterator (&it))
  {
    lambda = next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    /* already visited */
    if (btor_find_in_ptr_hash_table (map_value_index, lambda)) continue;

    /* we only consider writes */
    if (btor_get_fun_arity (btor, lambda) > 1) continue;

    is_top = 0;
    init_apply_parent_iterator (&pit, lambda);
    while (has_next_parent_apply_parent_iterator (&pit))
    {
      tmp = next_parent_apply_parent_iterator (&pit);

      if (!tmp->parameterized)
      {
        is_top = 1;
        break;
      }
    }

    if (!is_top) continue;

    BTOR_PUSH_STACK (mm, lambdas, lambda);
    while (!BTOR_EMPTY_STACK (lambdas))
    {
      lambda = BTOR_POP_STACK (lambdas);

      /* already visited */
      if (btor_find_in_ptr_hash_table (visit_cache, lambda)) continue;

      btor_insert_in_ptr_hash_table (visit_cache, lambda);

      //	  printf ("top: %s\n", node2string (lambda));
      cur         = lambda;
      index_cache = btor_new_ptr_hash_table (mm, 0, 0);
      while (is_write_exp (cur, &array, &index, &value))
      {
        //	      printf ("(%d) is_write: %s\n", cur->parents, node2string
        //(cur));
        assert (BTOR_IS_REGULAR_NODE (array));
        assert (BTOR_IS_FUN_NODE (array));

        /* if 'cur' has more than one parent we have to treat as a top
         * lambda */
        // TODO (ma): check if it has an effect if this is disabled
        //	  -> it seems better if disabled
#if 0
	      if (0 && cur != lambda && cur->parents > 1)
		{
		  BTOR_PUSH_STACK (mm, lambdas, cur);
		  break;
		}
#endif

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (btor_find_in_ptr_hash_table (index_cache, index))
        {
          //		  printf ("  skip: %s\n", node2string (index));
          cur = array;
          continue;
        }

        if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index)))
        {
          //		  printf ("  index: %s\n", node2string (index));
          btor_insert_in_ptr_hash_table (index_cache, index);
          add_to_index_map (btor, map_value_index, lambda, index, value);
        }
        else
        {
          //		  printf ("  no index: %s\n", node2string (index));
          BTOR_PUSH_STACK (mm, lambdas, array);
          break;
        }

        cur = array;
      }
      if (btor_find_in_ptr_hash_table (map_value_index, lambda))
      {
        assert (!btor_find_in_ptr_hash_table (map_lambda_base, lambda));
        btor_insert_in_ptr_hash_table (map_lambda_base, lambda)->data.asPtr =
            cur;
        //	    printf ("### base: %s (%d)\n", node2string (cur),
        // index_cache->count);
      }
      btor_delete_ptr_hash_table (index_cache);

      if (is_array_ite_exp (cur, &array_if, &array_else))
      {
        BTOR_PUSH_STACK (mm, lambdas, array_if);
        BTOR_PUSH_STACK (mm, lambdas, array_else);
      }
    }
  }
  btor_delete_ptr_hash_table (visit_cache);
  BTOR_RELEASE_STACK (mm, lambdas);
}

static void
collect_indices_top_eqs (Btor *btor, BtorPtrHashTable *map_value_index)
{
  BtorHashTableIterator it;
  BtorNode *cur, *lhs, *rhs, *read, *array, *index, *value;

  /* top level equality pre-initialization */
  init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
  queue_node_hash_table_iterator (&it, btor->embedded_constraints);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur = next_node_hash_table_iterator (&it);
    if (BTOR_IS_INVERTED_NODE (cur) || !BTOR_IS_BV_EQ_NODE (cur)) continue;

    lhs = cur->e[0];
    rhs = cur->e[1];

    index = value = 0;
    if (!BTOR_IS_INVERTED_NODE (lhs) && BTOR_IS_APPLY_NODE (lhs)
        && BTOR_IS_UF_ARRAY_NODE (lhs->e[0])
        && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lhs->e[1]->e[0]))
        && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (rhs)))
    {
      read  = lhs;
      array = lhs->e[0];
      index = lhs->e[1]->e[0];
      value = rhs;
    }
    else if (!BTOR_IS_INVERTED_NODE (rhs) && BTOR_IS_APPLY_NODE (rhs)
             && BTOR_IS_UF_ARRAY_NODE (rhs->e[0])
             && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (rhs->e[1]->e[0]))
             && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lhs)))
    {
      read  = rhs;
      array = rhs->e[0];
      index = rhs->e[1]->e[0];
      value = lhs;
    }

    if (!index) continue;

    add_to_index_map (btor, map_value_index, array, index, value);

    /* substitute 'read' with 'value', in order to prevent down propgation
     * rewriting for 'read' during substitute_and_rebuild(...), which
     * simplifies 'read' to 'value' anyways.
     * NOTE: if 'read' is already in 'substitutions', we let the rewriting
     * engine handle inconsistencies (i,e., if 'value' is not the same
     * as in 'substitutions'. */
    if (!btor_find_in_ptr_hash_table (btor->substitutions, read))
      btor_insert_substitution (btor, read, value, 0);
  }
}

void
find_ranges (Btor *btor,
             BtorNodePtrStack *stack,
             BtorNodePtrStack *ranges,
             BtorCharPtrStack *offsets,
             BtorNodePtrStack *indices)
{
  assert (stack);
  assert (ranges);
  assert (offsets);
  assert (indices);

#ifndef NDEBUG
  unsigned num_indices = 0;
#endif
  bool in_range;
  char *b0, *b1, *diff, *last_diff;
  unsigned cnt, lower, upper;
  BtorNode *n0, *n1;
  BtorMemMgr *mm;
  BtorNodePtrStack index_stack;

  mm          = btor->mm;
  index_stack = *stack;
  cnt         = BTOR_COUNT_STACK (index_stack);
  assert (BTOR_EMPTY_STACK (*ranges));
  assert (BTOR_EMPTY_STACK (*indices));
  if (cnt == 1)
    BTOR_PUSH_STACK (mm, *indices, BTOR_PEEK_STACK (index_stack, 0));
  else
  {
    assert (cnt > 1);
    qsort (index_stack.start, cnt, sizeof (BtorNode *), cmp_bits);
    diff = last_diff = 0;
    lower = upper = 0;
    while (upper < cnt)
    {
      in_range = false;
      diff     = 0;
      if (upper + 1 < cnt)
      {
        n0 = BTOR_PEEK_STACK (index_stack, upper);
        n1 = BTOR_PEEK_STACK (index_stack, upper + 1);
        b0 = BTOR_IS_INVERTED_NODE (n0) ? btor_get_invbits_const (n0)
                                        : btor_get_bits_const (n0);
        b1 = BTOR_IS_INVERTED_NODE (n1) ? btor_get_invbits_const (n1)
                                        : btor_get_bits_const (n1);
        assert (b0);
        assert (b1);
        diff = btor_sub_const (mm, b1, b0);

        if (!last_diff) last_diff = btor_copy_const (mm, diff);

        /* increment upper bound of range */
        in_range = strcmp (diff, last_diff) == 0;
        if (in_range) upper += 1;
      }

      if (!in_range)
      {
        /* push index */
        if (upper == lower)
        {
          BTOR_PUSH_STACK (mm, *indices, BTOR_PEEK_STACK (index_stack, lower));
#ifndef NDEBUG
          num_indices++;
#endif
          goto NEW_RANGE;
        }
        /* range is too small, push separate indices */
        else if (upper - lower <= 1
                 /* range with an offset greater than 1 */
                 && btor_is_power_of_two_const (last_diff) != 0)
        {
          /* last iteration step: if range contains all indices
           * up to the last one, we can push all indices */
          if (upper == cnt - 1) upper += 1;

          /* push all indices from lower until upper - 1 */
          for (; lower < upper; lower++)
          {
            BTOR_PUSH_STACK (
                mm, *indices, BTOR_PEEK_STACK (index_stack, lower));
#ifndef NDEBUG
            num_indices++;
#endif
          }
          /* lower is now that last index in the range, from
           * which we try to find a new range */
          upper += 1;
        }
        /* found range */
        else
        {
          assert (upper - lower > 0);
          BTOR_PUSH_STACK (mm, *offsets, last_diff);
          BTOR_PUSH_STACK (mm, *ranges, BTOR_PEEK_STACK (index_stack, lower));
          BTOR_PUSH_STACK (mm, *ranges, BTOR_PEEK_STACK (index_stack, upper));
#ifndef NDEBUG
          num_indices += upper - lower + 1;
#endif
          //			  printf ("range %d:%d\n", lower, upper);
          /* 'last_diff' will be released later */
          last_diff = 0;
        NEW_RANGE:
          /* reset range */
          upper += 1;
          lower = upper;
          if (diff) btor_delete_const (mm, diff);
          diff = 0;
        }
      }
      if (last_diff) btor_delete_const (mm, last_diff);
      last_diff = diff;
    }
    if (diff) btor_delete_const (mm, diff);
    assert (num_indices == cnt);
  }
}

void
btor_extract_lambdas (Btor *btor)
{
  assert (btor);

  unsigned num_memsets = 0, num_writes = 0, num_indices = 0;
  double start, delta;
  char *offset;
  BtorNode *subst, *base, *tmp, *array, *value, *lower, *upper;
  BtorHashTableIterator it, iit;
  BtorPtrHashTable *t, *map_value_index, *map_lambda_base;
  BtorPtrHashBucket *b;
  BtorNodePtrStack *stack, ranges, indices;
  BtorCharPtrStack offsets;
  BtorMemMgr *mm;

  start = btor_time_stamp ();

  mm = btor->mm;
  /* maps for each array values to stacks of indices */
  map_value_index = btor_new_ptr_hash_table (mm, 0, 0);
  /* contains the base array for each write chain */
  map_lambda_base = btor_new_ptr_hash_table (mm, 0, 0);
  btor_init_substitutions (btor);

  /* collect lambdas that are at the top of lambda chains */
  collect_indices_writes (btor, map_value_index, map_lambda_base);

  /* top level equality pre-initialization */
  collect_indices_top_eqs (btor, map_value_index);

  BTOR_INIT_STACK (ranges);
  BTOR_INIT_STACK (indices);
  BTOR_INIT_STACK (offsets);
  init_node_hash_table_iterator (&it, map_value_index);
  while (has_next_node_hash_table_iterator (&it))
  {
    t     = it.bucket->data.asPtr;
    array = next_node_hash_table_iterator (&it);
    assert (t);

    /* choose base array for memsets/writes:
     *  1) write chains: base array of the write chains
     *  2) top eqs: a new UF symbol */
    if ((b = btor_find_in_ptr_hash_table (map_lambda_base, array)))
    {
      assert (BTOR_IS_LAMBDA_NODE (array));
      subst = btor_copy_exp (btor, b->data.asPtr);
    }
    else
    {
      assert (BTOR_IS_UF_ARRAY_NODE (array));
      subst = btor_uf_exp (btor, array->sort_id, 0);
    }

    base = subst;
    init_node_hash_table_iterator (&iit, t);
    while (has_next_node_hash_table_iterator (&iit))
    {
      stack = iit.bucket->data.asPtr;
      value = next_node_hash_table_iterator (&iit);
      assert (stack);

      num_indices += BTOR_COUNT_STACK (*stack);
      find_ranges (btor, stack, &ranges, &offsets, &indices);
      BTOR_RELEASE_STACK (mm, *stack);
      BTOR_DELETE (mm, stack);
      assert (!BTOR_EMPTY_STACK (ranges) || !BTOR_EMPTY_STACK (indices));
      assert (BTOR_COUNT_STACK (ranges) % 2 == 0);
      assert (BTOR_COUNT_STACK (ranges) / 2 == BTOR_COUNT_STACK (offsets));

      /* create memset regions */
      while (!BTOR_EMPTY_STACK (ranges))
      {
        assert (!BTOR_EMPTY_STACK (offsets));
        offset = BTOR_POP_STACK (offsets);
        upper  = BTOR_POP_STACK (ranges);
        lower  = BTOR_POP_STACK (ranges);
        tmp    = create_memset (btor, lower, upper, value, subst, offset);
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_delete_const (mm, offset);
        num_memsets++;
      }

      /* create writes */
      while (!BTOR_EMPTY_STACK (indices))
      {
        lower = BTOR_POP_STACK (indices);
        tmp   = btor_write_exp (btor, subst, lower, value);
        btor_release_exp (btor, subst);
        subst = tmp;
        num_writes++;
      }
    }
    btor_delete_ptr_hash_table (t);

    if (base != subst) btor_insert_substitution (btor, array, subst, 0);
    btor_release_exp (btor, subst);
  }
  btor_delete_ptr_hash_table (map_value_index);
  btor_delete_ptr_hash_table (map_lambda_base);
  BTOR_RELEASE_STACK (mm, ranges);
  BTOR_RELEASE_STACK (mm, indices);
  BTOR_RELEASE_STACK (mm, offsets);

  btor_substitute_and_rebuild (btor, btor->substitutions, 0);
  btor_delete_substitutions (btor);
  delta = btor_time_stamp () - start;
  BTOR_MSG (btor->msg,
            1,
            "found %d memsets (%d indices), %d writes in %.3f seconds",
            num_memsets,
            num_indices - num_writes,
            num_writes,
            delta);
}
