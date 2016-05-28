/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorextract.h"
#include "btorbitvec.h"
#include "btorcore.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

#define BTOR_CONST_GET_BITS(c)                           \
  BTOR_IS_INVERTED_NODE (c) ? btor_const_get_invbits (c) \
                            : btor_const_get_bits (c)

inline static void
extract_base_addr_offset (BtorNode *bvadd, BtorNode **base, BtorNode **offset)
{
  assert (BTOR_IS_REGULAR_NODE (bvadd));
  assert (btor_is_add_node (bvadd));

  if (btor_is_bv_const_node (bvadd->e[0]))
  {
    if (offset) *offset = bvadd->e[0];
    if (base) *base = bvadd->e[1];
  }
  else
  {
    assert (btor_is_bv_const_node (bvadd->e[1]));
    if (offset) *offset = bvadd->e[1];
    if (base) *base = bvadd->e[0];
  }
}

static int
cmp_abs_rel_indices (const void *a, const void *b)
{
  bool is_abs;
  BtorBitVector *bx, *by;
  BtorNode *x, *y, *x_base_addr, *y_base_addr, *x_offset, *y_offset;

  x = *((BtorNode **) a);
  y = *((BtorNode **) b);

  is_abs = btor_is_bv_const_node (x) && btor_is_bv_const_node (y);

  if (is_abs) /* absolute address */
  {
    bx = BTOR_CONST_GET_BITS (x);
    by = BTOR_CONST_GET_BITS (y);
  }
  else /* relative address */
  {
    assert (!BTOR_IS_INVERTED_NODE (x));
    assert (!BTOR_IS_INVERTED_NODE (y));
    assert (btor_is_add_node (x));
    assert (btor_is_add_node (y));
    extract_base_addr_offset (x, &x_base_addr, &x_offset);
    extract_base_addr_offset (y, &y_base_addr, &y_offset);
    assert (x_base_addr == y_base_addr);
    assert (btor_is_bv_const_node (x_offset));
    assert (btor_is_bv_const_node (y_offset));
    bx = BTOR_CONST_GET_BITS (x_offset);
    by = BTOR_CONST_GET_BITS (y_offset);
  }
  assert (bx);
  assert (by);
  return btor_compare_bv (bx, by);
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
create_range (Btor *btor,
              BtorNode *lower,
              BtorNode *upper,
              BtorNode *param,
              BtorBitVector *offset)
{
  assert (lower);
  assert (upper);
  assert (param);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (btor_is_param_node (param));
  assert (btor_is_bv_const_node (lower) || btor_is_add_node (lower));
  assert (btor_is_bv_const_node (upper) || btor_is_add_node (upper));
  assert (BTOR_REAL_ADDR_NODE (lower)->sort_id
          == BTOR_REAL_ADDR_NODE (upper)->sort_id);
  assert (offset);

  int pos;
  BtorNode *res, *le0, *le1, *and, *off, *sub, *rem, *eq, *zero, *slice;

  le0 = btor_ulte_exp (btor, lower, param);
  le1 = btor_ulte_exp (btor, param, upper);
  and = btor_and_exp (btor, le0, le1);

  /* increment by one */
  if (btor_is_one_bv (offset)) res = btor_copy_exp (btor, and);
  /* increment by power of two */
  else if ((pos = btor_power_of_two_bv (offset)) > -1)
  {
    assert (pos > 0);
    sub   = btor_sub_exp (btor, upper, param);
    slice = btor_slice_exp (btor, sub, pos - 1, 0);
    zero  = btor_zero_exp (btor, btor_get_exp_width (btor, slice));
    eq    = btor_eq_exp (btor, slice, zero);
    res   = btor_and_exp (btor, and, eq);

    btor_release_exp (btor, zero);
    btor_release_exp (btor, slice);
    btor_release_exp (btor, sub);
    btor_release_exp (btor, eq);
  }
  /* increment by some arbitrary value */
  else
  {
    zero = btor_zero_exp (btor, btor_get_exp_width (btor, lower));
    off  = btor_const_exp (btor, offset);
    assert (BTOR_REAL_ADDR_NODE (off)->sort_id
            == BTOR_REAL_ADDR_NODE (lower)->sort_id);
    sub = btor_sub_exp (btor, upper, param);
    rem = btor_urem_exp (btor, sub, off);
    eq  = btor_eq_exp (btor, rem, zero);
    res = btor_and_exp (btor, and, eq);

    btor_release_exp (btor, zero);
    btor_release_exp (btor, off);
    btor_release_exp (btor, sub);
    btor_release_exp (btor, rem);
    btor_release_exp (btor, eq);
  }
  btor_release_exp (btor, le0);
  btor_release_exp (btor, le1);
  btor_release_exp (btor, and);
  return res;
}

/* pattern: lower <= j <= upper && range_cond ? value : a[j] */
static inline BtorNode *
create_pattern_memset (Btor *btor,
                       BtorNode *lower,
                       BtorNode *upper,
                       BtorNode *value,
                       BtorNode *array,
                       BtorBitVector *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_REAL_ADDR_NODE (lower)->kind
          == BTOR_REAL_ADDR_NODE (upper)->kind);
  assert (btor_is_bv_const_node (lower) || btor_is_add_node (lower));
  assert (BTOR_REAL_ADDR_NODE (lower)->sort_id
          == BTOR_REAL_ADDR_NODE (upper)->sort_id);
  assert (offset);

  BtorNode *res, *param, *ite, *read, *cond;

  param = btor_param_exp (btor, btor_get_exp_width (btor, lower), 0);
  read  = btor_read_exp (btor, array, param);
  cond  = create_range (btor, lower, upper, param, offset);
  ;
  ite = btor_cond_exp (btor, cond, value, read);
  res = btor_lambda_exp (btor, param, ite);

  btor_release_exp (btor, param);
  btor_release_exp (btor, read);
  btor_release_exp (btor, cond);
  btor_release_exp (btor, ite);

  return res;
}

/* pattern: lower <= j <= upper && range_cond ? j : a[j] */
static inline BtorNode *
create_pattern_itoi (Btor *btor,
                     BtorNode *lower,
                     BtorNode *upper,
                     BtorNode *array,
                     BtorBitVector *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_REAL_ADDR_NODE (lower)->kind
          == BTOR_REAL_ADDR_NODE (upper)->kind);
  assert (btor_is_bv_const_node (lower) || btor_is_add_node (lower));
  assert (BTOR_REAL_ADDR_NODE (lower)->sort_id
          == BTOR_REAL_ADDR_NODE (upper)->sort_id);
  assert (btor_get_codomain_fun_sort (&btor->sorts_unique_table, array->sort_id)
          == BTOR_REAL_ADDR_NODE (lower)->sort_id);
  assert (offset);

  BtorNode *res, *param, *ite, *read, *cond;

  param = btor_param_exp (btor, btor_get_exp_width (btor, lower), 0);
  read  = btor_read_exp (btor, array, param);
  cond  = create_range (btor, lower, upper, param, offset);
  ;
  ite = btor_cond_exp (btor, cond, param, read);
  res = btor_lambda_exp (btor, param, ite);

  btor_release_exp (btor, param);
  btor_release_exp (btor, read);
  btor_release_exp (btor, cond);
  btor_release_exp (btor, ite);

  return res;
}

/* pattern: lower <= j <= upper && range_cond ? j + 1 : a[j] */
static inline BtorNode *
create_pattern_itoip1 (Btor *btor,
                       BtorNode *lower,
                       BtorNode *upper,
                       BtorNode *array,
                       BtorBitVector *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_REAL_ADDR_NODE (lower)->kind
          == BTOR_REAL_ADDR_NODE (upper)->kind);
  assert (btor_is_bv_const_node (lower) || btor_is_add_node (lower));
  assert (BTOR_REAL_ADDR_NODE (lower)->sort_id
          == BTOR_REAL_ADDR_NODE (upper)->sort_id);
  assert (btor_get_codomain_fun_sort (&btor->sorts_unique_table, array->sort_id)
          == BTOR_REAL_ADDR_NODE (lower)->sort_id);
  assert (offset);

  BtorNode *res, *param, *ite, *read, *cond, *inc;

  param = btor_param_exp (btor, btor_get_exp_width (btor, lower), 0);
  read  = btor_read_exp (btor, array, param);
  cond  = create_range (btor, lower, upper, param, offset);
  ;
  inc = btor_inc_exp (btor, param);
  ite = btor_cond_exp (btor, cond, inc, read);
  res = btor_lambda_exp (btor, param, ite);

  btor_release_exp (btor, param);
  btor_release_exp (btor, read);
  btor_release_exp (btor, cond);
  btor_release_exp (btor, inc);
  btor_release_exp (btor, ite);

  return res;
}

static inline BtorNode *
create_pattern_cpy (Btor *btor,
                    BtorNode *lower,
                    BtorNode *upper,
                    BtorNode *src_array,
                    BtorNode *dst_array,
                    BtorNode *src_addr,
                    BtorNode *dst_addr,
                    BtorBitVector *offset)
{
  assert (!BTOR_IS_INVERTED_NODE (lower));
  assert (!BTOR_IS_INVERTED_NODE (upper));
  assert (btor_is_add_node (lower));
  assert (btor_is_add_node (upper));

  BtorNode *res, *param, *ite, *read, *cond, *read_src, *add, *sub;

  param = btor_param_exp (btor, btor_get_exp_width (btor, lower), 0);
  read  = btor_read_exp (btor, dst_array, param);
  cond  = create_range (btor, lower, upper, param, offset);

  sub      = btor_sub_exp (btor, param, dst_addr);
  add      = btor_add_exp (btor, src_addr, sub);
  read_src = btor_read_exp (btor, src_array, add);
  ite      = btor_cond_exp (btor, cond, read_src, read);
  res      = btor_lambda_exp (btor, param, ite);

  btor_release_exp (btor, param);
  btor_release_exp (btor, read);
  btor_release_exp (btor, cond);
  btor_release_exp (btor, sub);
  btor_release_exp (btor, add);
  btor_release_exp (btor, read_src);
  btor_release_exp (btor, ite);
  return res;
}

static bool
is_write_exp (BtorNode *exp,
              BtorNode **array,
              BtorNode **index,
              BtorNode **value)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *param, *body, *eq, *app;

  if (!btor_is_lambda_node (exp) || btor_get_fun_arity (exp->btor, exp) > 1)
    return false;

  param = exp->e[0];
  body  = btor_lambda_get_body (exp);

  if (BTOR_IS_INVERTED_NODE (body) || !btor_is_bv_cond_node (body))
    return false;

  /* check condition */
  eq = body->e[0];
  if (BTOR_IS_INVERTED_NODE (eq) || !btor_is_bv_eq_node (eq)
      || !eq->parameterized || (eq->e[0] != param && eq->e[1] != param))
    return false;

  /* check value */
  if (BTOR_REAL_ADDR_NODE (body->e[1])->parameterized) return false;

  /* check apply on unmodified array */
  app = body->e[2];
  if (BTOR_IS_INVERTED_NODE (app) || !btor_is_apply_node (app)
      || btor_get_fun_arity (app->btor, app->e[0]) > 1
      || app->e[1]->e[0] != param)
    return false;

  if (array) *array = app->e[0];
  if (index) *index = eq->e[1] == param ? eq->e[0] : eq->e[1];
  if (value) *value = body->e[1];
  return true;
}

static bool
is_array_ite_exp (BtorNode *exp, BtorNode **array_if, BtorNode **array_else)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *param, *body, *app_if, *app_else;

  if (!btor_is_lambda_node (exp) || btor_get_fun_arity (exp->btor, exp) > 1)
    return false;

  param = exp->e[0];
  body  = btor_lambda_get_body (exp);

  if (BTOR_IS_INVERTED_NODE (body) || !btor_is_bv_cond_node (body))
    return false;

  /* check value */
  if (!BTOR_REAL_ADDR_NODE (body->e[1])->parameterized
      || !BTOR_REAL_ADDR_NODE (body->e[2])->parameterized)
    return false;

  /* check applies in if and else branch */
  app_if = body->e[1];
  if (BTOR_IS_INVERTED_NODE (app_if) || !btor_is_apply_node (app_if)
      || btor_get_fun_arity (app_if->btor, app_if->e[0]) > 1
      || app_if->e[1]->e[0] != param)
    return false;

  app_else = body->e[1];
  if (BTOR_IS_INVERTED_NODE (app_else) || !btor_is_apply_node (app_else)
      || btor_get_fun_arity (app_else->btor, app_else->e[0]) > 1
      || app_else->e[1]->e[0] != param)
    return false;

  if (array_if) *array_if = app_if->e[0];
  if (array_else) *array_else = app_else->e[0];
  return true;
}

inline static bool
is_itoi_pattern (BtorNode *index, BtorNode *value)
{
  return index == value;
}

inline static bool
is_itoip1_pattern (BtorNode *index, BtorNode *value)
{
  bool res;
  BtorNode *inc;

  inc = btor_inc_exp (BTOR_REAL_ADDR_NODE (index)->btor, index);
  res = inc == value;
  btor_release_exp (BTOR_REAL_ADDR_NODE (index)->btor, inc);
  return res;
}

inline static bool
is_cpy_pattern (BtorNode *index, BtorNode *value)
{
  BtorNode *bvadd, *dst_addr, *off;

  if (BTOR_IS_INVERTED_NODE (index) || !btor_is_add_node (index)
      || BTOR_IS_INVERTED_NODE (value) || !btor_is_apply_node (value)
      || BTOR_IS_INVERTED_NODE (value->e[1]->e[0])
      || !btor_is_add_node (value->e[1]->e[0]))
    return false;

  if (btor_is_bv_const_node (index->e[0]))
    off = index->e[0];
  else if (btor_is_bv_const_node (index->e[1]))
    off = index->e[1];
  else
    return false;

  bvadd    = value->e[1]->e[0];
  dst_addr = 0;
  if (bvadd->e[0] == off)
    dst_addr = bvadd->e[1];
  else if (bvadd->e[1] == off)
    dst_addr = bvadd->e[0];

  return dst_addr != 0;
}

/* extracts source array, source address, destination address and offset of
 * a memcopy pattern. */
static void
extract_cpy_src_dst_info (BtorNode *index,
                          BtorNode *value,
                          BtorNode **src_array,
                          BtorNode **src_addr,
                          BtorNode **dst_addr,
                          BtorNode **off)
{
  assert (is_cpy_pattern (index, value));

  BtorNode *bvadd, *offset;

  extract_base_addr_offset (index, dst_addr, &offset);
  bvadd = value->e[1]->e[0];
  if (off) *off = offset;
  if (src_addr) *src_addr = bvadd->e[0] == offset ? bvadd->e[1] : bvadd->e[0];
  if (src_array) *src_array = value->e[0];
}

inline static bool
is_abs_set_pattern (BtorNode *index, BtorNode *prev_index)
{
  return btor_is_bv_const_node (index)
         && (!prev_index || btor_is_bv_const_node (prev_index));
}

inline static bool
is_rel_set_pattern (BtorNode *index, BtorNode *prev_index)
{
  BtorNode *base_addr, *offset, *prev_base_addr, *prev_offset;

  if (BTOR_IS_INVERTED_NODE (index) || !btor_is_add_node (index)) return false;

  if (!btor_is_bv_const_node (index->e[0])
      && !btor_is_bv_const_node (index->e[1]))
    return false;

  if (!prev_index) return true;

  if (BTOR_IS_INVERTED_NODE (prev_index) || !btor_is_add_node (prev_index))
    return false;

  if (!btor_is_bv_const_node (prev_index->e[0])
      && !btor_is_bv_const_node (prev_index->e[1]))
    return false;

  extract_base_addr_offset (index, &base_addr, &offset);
  extract_base_addr_offset (prev_index, &prev_base_addr, &prev_offset);
  assert (btor_is_bv_const_node (offset));
  assert (btor_is_bv_const_node (prev_offset));

  return base_addr == prev_base_addr;
}

/* Pattern 1)
 *
 *   dst0 := write(dst, dst_addr + c, read(src, src_addr + c))
 *   dst1 := write(dst0, dst_addr + c + 1, read(src, src_addr + c + 1))
 *   dst2 := write(dst1, dst_addr + c + 2, read(src, src_addr + c + 2))
 *
 * Pattern 2) overlapping memory regions
 *
 *   dst0 := write(dst, dst_addr + c, read(dst, src_addr + c))
 *   dst1 := write(dst0, dst_addr + c + 1, read(dst0, src_addr + c + 1))
 *   dst2 := write(dst1, dst_addr + c + 2, read(dst1, src_addr + c + 2))
 */
inline static bool
is_copy_pattern (BtorNode *index,
                 BtorNode *value,
                 BtorNode *prev_index,
                 BtorNode *prev_value,
                 BtorNode *array)
{
  BtorNode *src_addr, *dst_addr;
  BtorNode *prev_src_addr, *prev_dst_addr;

  if (!is_cpy_pattern (index, value)) return false;

  /* 'index' is the first index collected for the current memcopy pattern */
  if (!prev_index) return true;

  /* 'index' belongs to a new memcopy pattern (create new pattern) */
  if (!is_cpy_pattern (prev_index, prev_value)) return false;

  extract_cpy_src_dst_info (index, value, 0, &src_addr, &dst_addr, 0);
  extract_cpy_src_dst_info (
      prev_index, prev_value, 0, &prev_src_addr, &prev_dst_addr, 0);

  return src_addr == prev_src_addr
         && dst_addr == prev_dst_addr
         /* destination array check: either every copy step uses the same
          * destination array or they use the intermediate results of the write
          * operations */
         && (value->e[0] == prev_value->e[0] || value->e[0] == array);
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
  BtorNodePtrStack *indices;
  BtorNode *offset;

  mm = btor->mm;

  if (!(b = btor_get_ptr_hash_table (map_value_index, lambda)))
  {
    b              = btor_add_ptr_hash_table (map_value_index, lambda);
    t              = btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    b->data.as_ptr = t;
  }
  else
    t = b->data.as_ptr;
  assert (t);

  if (!(b = btor_get_ptr_hash_table (t, value)))
  {
    b = btor_add_ptr_hash_table (t, value);
    BTOR_NEW (mm, indices);
    BTOR_INIT_STACK (*indices);
    b->data.as_ptr = indices;
  }
  else
    indices = (BtorNodePtrStack *) b->data.as_ptr;
  assert (indices);
  if (btor_is_bv_const_node (index))
    offset = index;
  else
  {
    assert (BTOR_IS_REGULAR_NODE (index));
    assert (btor_is_add_node (index));
    extract_base_addr_offset (index, 0, &offset);
    assert (btor_is_bv_const_node (offset));
  }

  BTOR_PUSH_STACK (mm, *indices, index);
}

static void
collect_indices_writes (Btor *btor,
                        BtorPtrHashTable *map_value_index,
                        BtorPtrHashTable *map_lambda_base)
{
  int is_top;
  BtorNode *lambda, *cur, *array, *index, *value, *tmp, *array_if, *array_else;
  BtorNode *prev_index, *prev_value;
  BtorHashTableIterator it;
  BtorNodeIterator pit;
  BtorNodePtrStack lambdas;
  BtorPtrHashTable *index_cache, *visit_cache;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (lambdas);
  visit_cache = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect lambdas that are at the top of lambda chains */
  btor_init_reversed_hash_table_iterator (&it, btor->lambdas);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    lambda = btor_next_node_hash_table_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (lambda));

    /* already visited */
    if (btor_get_ptr_hash_table (map_value_index, lambda)) continue;

    /* we only consider writes */
    if (btor_get_fun_arity (btor, lambda) > 1) continue;

    is_top = 0;
    btor_init_apply_parent_iterator (&pit, lambda);
    while (btor_has_next_apply_parent_iterator (&pit))
    {
      tmp = btor_next_apply_parent_iterator (&pit);

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
      if (btor_get_ptr_hash_table (visit_cache, lambda)) continue;

      btor_add_ptr_hash_table (visit_cache, lambda);

      cur = lambda;
      index_cache =
          btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);
      prev_index = prev_value = 0;
      while (is_write_exp (cur, &array, &index, &value))
      {
        assert (BTOR_IS_REGULAR_NODE (array));
        assert (btor_is_fun_node (array));

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (btor_get_ptr_hash_table (index_cache, index))
        {
          cur = array;
          continue;
        }

        /* collect index/value pairs for absolute set patterns */
        if (is_abs_set_pattern (index, prev_index))
        {
          btor_add_ptr_hash_table (index_cache, index);
          add_to_index_map (btor, map_value_index, lambda, index, value);
        }
        // TODO (ma): is there a way to recognize base_addr + 0 as
        //            relative?
        //            -> only if its the last index
        //	       - prev_index->base_addr == index
        else if (is_rel_set_pattern (index, prev_index))
        {
          /* collect index/value pairs for memcopy pattern if 'index'
           * and 'value' still belong to current memcopy pattern */
          if (is_copy_pattern (index, value, prev_index, prev_value, array))
          {
            /* optimization for memcopy: do not visit lambdas that
             * are only accessed via this lambda (reduces number of
             * redundant memcopy patterns) */
            if (value->e[0] == array && array->parents == 2)
              btor_add_ptr_hash_table (visit_cache, array);
            btor_add_ptr_hash_table (index_cache, index);
            add_to_index_map (btor, map_value_index, lambda, index, value);
          }
          /* collect index/value pairs for relative set patterns */
          else
          {
            btor_add_ptr_hash_table (index_cache, index);
            add_to_index_map (btor, map_value_index, lambda, index, value);
          }
        }
        /* use array as new start point */
        else
        {
          BTOR_PUSH_STACK (mm, lambdas, array);
          break;
        }

        cur        = array;
        prev_index = index;
        prev_value = value;
      }
      if (btor_get_ptr_hash_table (map_value_index, lambda))
      {
        assert (!btor_get_ptr_hash_table (map_lambda_base, lambda));
        btor_add_ptr_hash_table (map_lambda_base, lambda)->data.as_ptr = cur;
      }
      btor_delete_ptr_hash_table (index_cache);

      // TODO (ma): can only be ite now
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
  btor_init_node_hash_table_iterator (&it, btor->unsynthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->synthesized_constraints);
  btor_queue_node_hash_table_iterator (&it, btor->embedded_constraints);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    cur = btor_next_node_hash_table_iterator (&it);
    if (BTOR_IS_INVERTED_NODE (cur) || !btor_is_bv_eq_node (cur)) continue;

    lhs = cur->e[0];
    rhs = cur->e[1];

    index = value = 0;
    if (!BTOR_IS_INVERTED_NODE (lhs) && btor_is_apply_node (lhs)
        && btor_is_uf_array_node (lhs->e[0])
        && btor_is_bv_const_node (lhs->e[1]->e[0])
        && btor_is_bv_const_node (rhs))
    {
      read  = lhs;
      array = lhs->e[0];
      index = lhs->e[1]->e[0];
      value = rhs;
    }
    else if (!BTOR_IS_INVERTED_NODE (rhs) && btor_is_apply_node (rhs)
             && btor_is_uf_array_node (rhs->e[0])
             && btor_is_bv_const_node (rhs->e[1]->e[0])
             && btor_is_bv_const_node (lhs))
    {
      read  = rhs;
      array = rhs->e[0];
      index = rhs->e[1]->e[0];
      value = lhs;
    }

    if (!index) continue;

    if (btor_get_ptr_hash_table (btor->substitutions, read)) continue;

    /* only add each index once */
    add_to_index_map (btor, map_value_index, array, index, value);

    /* substitute 'read' with 'value', in order to prevent down propgation
     * rewriting for 'read' during substitute_and_rebuild(...), which
     * simplifies 'read' to 'value' anyways.
     * NOTE: if 'read' is already in 'substitutions', we let the rewriting
     * engine handle inconsistencies (i,e., if 'value' is not the same
     * as in 'substitutions'. */
    btor_insert_substitution (btor, read, value, 0);
  }
}

void
find_ranges (Btor *btor,
             BtorNodePtrStack *stack,
             BtorNodePtrStack *ranges,
             BtorBitVectorPtrStack *increments,
             BtorNodePtrStack *indices,
             unsigned *num_pat,
             unsigned *num_pat_inc,
             unsigned *size_pat,
             unsigned *size_pat_inc)
{
  assert (stack);
  assert (ranges);
  assert (increments);
  assert (indices);
  assert (num_pat);
  assert (size_pat);

#ifndef NDEBUG
  unsigned num_indices = 0;
  int i;
#endif
  bool in_range;
  BtorBitVector *b0, *b1, *inc, *prev_inc;
  unsigned cnt, lower, upper;
  unsigned num_pattern = 0, num_pattern_inc = 0, size_pattern = 0;
  unsigned size_pattern_inc = 0;
  BtorNode *n0, *n1, *n0_base_addr, *n1_base_addr, *n0_offset, *n1_offset;
  BtorMemMgr *mm;
  BtorNodePtrStack index_stack;

  mm          = btor->mm;
  index_stack = *stack;
  cnt         = BTOR_COUNT_STACK (index_stack);
  if (cnt == 0) return;

  if (cnt == 1)
    BTOR_PUSH_STACK (mm, *indices, BTOR_PEEK_STACK (index_stack, 0));
  else
  {
    assert (cnt > 1);
#ifndef NDEBUG
    /* sanity check: 'index_stack' contains either absolute or relative
     * addresses */
    for (i = 1; i < BTOR_COUNT_STACK (index_stack); i++)
    {
      n0 = BTOR_REAL_ADDR_NODE (BTOR_PEEK_STACK (index_stack, i - 1));
      n1 = BTOR_REAL_ADDR_NODE (BTOR_PEEK_STACK (index_stack, i));
      assert (n0->kind == n1->kind);
      assert (btor_is_add_node (n0) || btor_is_bv_const_node (n0));
      if (btor_is_add_node (n0))
      {
        extract_base_addr_offset (n0, &n0_base_addr, &n0_offset);
        extract_base_addr_offset (n1, &n1_base_addr, &n1_offset);
        assert (n0_base_addr == n1_base_addr);
        assert (btor_is_bv_const_node (n0_offset));
        assert (btor_is_bv_const_node (n1_offset));
      }
    }
#endif
    qsort (index_stack.start, cnt, sizeof (BtorNode *), cmp_abs_rel_indices);
    inc = prev_inc = 0;
    lower = upper = 0;
    while (upper < cnt)
    {
      in_range = false;
      inc      = 0;
      if (upper + 1 < cnt)
      {
        n0 = BTOR_PEEK_STACK (index_stack, upper);
        n1 = BTOR_PEEK_STACK (index_stack, upper + 1);

        if (btor_is_bv_const_node (n0))
        {
          assert (btor_is_bv_const_node (n1));
          b0 = BTOR_CONST_GET_BITS (n0);
          b1 = BTOR_CONST_GET_BITS (n1);
        }
        else
        {
          assert (!BTOR_IS_INVERTED_NODE (n0));
          assert (!BTOR_IS_INVERTED_NODE (n1));
          assert (btor_is_add_node (n0));
          assert (btor_is_add_node (n1));
          extract_base_addr_offset (n0, &n0_base_addr, &n0_offset);
          extract_base_addr_offset (n1, &n1_base_addr, &n1_offset);
          assert (n0_base_addr == n1_base_addr);
          b0 = BTOR_CONST_GET_BITS (n0_offset);
          b1 = BTOR_CONST_GET_BITS (n1_offset);
        }
        assert (b0);
        assert (b1);
        inc = btor_sub_bv (mm, b1, b0);

        if (!prev_inc) prev_inc = btor_copy_bv (mm, inc);

        /* increment upper bound of range */
        in_range = btor_compare_bv (inc, prev_inc) == 0;
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
                 && btor_power_of_two_bv (prev_inc) != 0)
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
          BTOR_PUSH_STACK (mm, *increments, prev_inc);
          BTOR_PUSH_STACK (mm, *ranges, BTOR_PEEK_STACK (index_stack, lower));
          BTOR_PUSH_STACK (mm, *ranges, BTOR_PEEK_STACK (index_stack, upper));
#ifndef NDEBUG
          num_indices += upper - lower + 1;
#endif
          if (btor_is_one_bv (prev_inc))
          {
            size_pattern += upper - lower + 1;
            num_pattern++;
          }
          else
          {
            size_pattern_inc += upper - lower + 1;
            num_pattern_inc++;
          }
          /* 'prev_inc' will be released later */
          prev_inc = 0;
        NEW_RANGE:
          /* reset range */
          upper += 1;
          lower = upper;
          if (inc) btor_free_bv (mm, inc);
          inc = 0;
        }
      }
      if (prev_inc) btor_free_bv (mm, prev_inc);
      prev_inc = inc;
    }
    if (inc) btor_free_bv (mm, inc);
    assert (num_indices == cnt);
  }

  /* return statistics */
  if (num_pat)
  {
    *num_pat += num_pattern;
    /* if no separate statistic variable is given for the 'inc' pattern,
     * we just add the number to the normal one */
    if (!num_pat_inc) *num_pat += num_pattern_inc;
  }
  if (num_pat_inc) *num_pat_inc += num_pattern_inc;
  if (size_pat)
  {
    *size_pat += size_pattern;
    /* if no separate statistic variable is given for the 'inc' pattern,
     * we just add the size to the normal one */
    if (!size_pat_inc) *size_pat += size_pattern_inc;
  }
  if (size_pat_inc) *size_pat_inc += size_pattern_inc;
}

static unsigned
extract_lambdas (Btor *btor,
                 BtorPtrHashTable *map_value_index,
                 BtorPtrHashTable *map_lambda_base)
{
  assert (btor);
  assert (map_value_index);
  assert (map_lambda_base);

  bool is_top_eq;
  BtorBitVector *inc;
  unsigned i_range, i_index, i_value, i_inc;
  BtorNode *subst, *base, *tmp, *array, *value, *lower, *upper;
  BtorNode *src_array, *src_addr, *dst_addr;
  BtorHashTableIterator it, iit;
  BtorPtrHashTable *t, *index_value_map;
  BtorPtrHashBucket *b;
  BtorNodePtrStack ranges, indices, values, indices_itoi, indices_itoip1;
  BtorNodePtrStack indices_cpy, indices_rem, *stack;
  BtorBitVectorPtrStack increments;
  BtorMemMgr *mm;

  /* statistics */
  unsigned num_total = 0, num_writes = 0;
  unsigned num_set = 0, num_set_inc = 0, num_set_itoi = 0, num_set_itoip1 = 0;
  unsigned num_cpy = 0, size_set = 0, size_set_inc = 0, size_set_itoi = 0;
  unsigned size_set_itoip1 = 0, size_cpy = 0;

  mm = btor->mm;
  BTOR_INIT_STACK (ranges);
  BTOR_INIT_STACK (indices);
  BTOR_INIT_STACK (increments);
  BTOR_INIT_STACK (values);
  BTOR_INIT_STACK (indices_itoi);
  BTOR_INIT_STACK (indices_itoip1);
  BTOR_INIT_STACK (indices_cpy);
  BTOR_INIT_STACK (indices_rem);
  btor_init_node_hash_table_iterator (&it, map_value_index);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    t     = it.bucket->data.as_ptr;
    array = btor_next_node_hash_table_iterator (&it);
    assert (t);

    /* find memset patterns, the remaining unused indices are pushed onto
     * stack 'indices' */
    btor_init_node_hash_table_iterator (&iit, t);
    while (btor_has_next_node_hash_table_iterator (&iit))
    {
      stack = iit.bucket->data.as_ptr;
      value = btor_next_node_hash_table_iterator (&iit);
      assert (stack);
      find_ranges (btor,
                   stack,
                   &ranges,
                   &increments,
                   &indices,
                   &num_set,
                   &num_set_inc,
                   &size_set,
                   &size_set_inc);
      BTOR_RELEASE_STACK (mm, *stack);
      BTOR_DELETE (mm, stack);
      BTOR_PUSH_STACK (mm, ranges, 0);
      BTOR_PUSH_STACK (mm, indices, 0);
      BTOR_PUSH_STACK (mm, values, value);
      assert (BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values) > 0
              || BTOR_COUNT_STACK (indices) - BTOR_COUNT_STACK (values) > 0);
      assert ((BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values)) % 2 == 0);
      assert ((BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values)) / 2
              == BTOR_COUNT_STACK (increments));
    }

    /* choose base array for patterns/writes:
     *  1) write chains: base array of the write chains
     *  2) top eqs: a new UF symbol */
    if ((b = btor_get_ptr_hash_table (map_lambda_base, array)))
    {
      assert (btor_is_lambda_node (array));
      b = btor_get_ptr_hash_table (map_lambda_base, array);
      assert (b);
      subst     = btor_copy_exp (btor, b->data.as_ptr);
      is_top_eq = false;
    }
    else
    {
      assert (btor_is_uf_array_node (array));
      subst = btor_array_exp (btor,
                              btor_get_fun_exp_width (btor, array),
                              btor_get_index_exp_width (btor, array),
                              0);

      is_top_eq = true;
    }

    index_value_map =
        btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    base    = subst;
    i_range = i_index = i_inc = 0;
    for (i_value = 0; i_value < BTOR_COUNT_STACK (values); i_value++)
    {
      value = BTOR_PEEK_STACK (values, i_value);

      /* create memset regions */
      for (; i_range < BTOR_COUNT_STACK (ranges) - 1; i_range += 2)
      {
        lower = BTOR_PEEK_STACK (ranges, i_range);
        /* next value */
        if (!lower)
        {
          i_range++;
          break;
        }
        upper = BTOR_PEEK_STACK (ranges, i_range + 1);
        assert (i_inc < BTOR_COUNT_STACK (increments));
        inc = BTOR_PEEK_STACK (increments, i_inc);
        tmp = create_pattern_memset (btor, lower, upper, value, subst, inc);
        tmp->is_array = 1;
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_free_bv (mm, inc);
        i_inc++;
      }

      /* find patterns that are dependent on the current index */
      for (; i_index < BTOR_COUNT_STACK (indices); i_index++)
      {
        lower = BTOR_PEEK_STACK (indices, i_index);
        /* next value */
        if (!lower)
        {
          i_index++;
          break;
        }
        assert (!btor_get_ptr_hash_table (index_value_map, lower));
        /* save index value pairs for later */
        btor_add_ptr_hash_table (index_value_map, lower)->data.as_ptr = value;

        /* pattern 1: index -> index */
        if (is_itoi_pattern (lower, value))
          BTOR_PUSH_STACK (mm, indices_itoi, lower);
        /* pattern 2: index -> index + 1 */
        else if (is_itoip1_pattern (lower, value))
          BTOR_PUSH_STACK (mm, indices_itoip1, lower);
        /* pattern 3: memcopy pattern */
        else if (is_cpy_pattern (lower, value))
          BTOR_PUSH_STACK (mm, indices_cpy, lower);
        else /* no pattern found */
          BTOR_PUSH_STACK (mm, indices_rem, lower);
      }
    }

    /* pattern: index -> index */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (increments);
    find_ranges (btor,
                 &indices_itoi,
                 &ranges,
                 &increments,
                 &indices_rem,
                 &num_set_itoi,
                 0,
                 &size_set_itoi,
                 0);
    if (!BTOR_EMPTY_STACK (ranges))
    {
      assert (BTOR_COUNT_STACK (ranges) % 2 == 0);
      for (i_range = 0, i_inc = 0; i_range < BTOR_COUNT_STACK (ranges) - 1;
           i_range += 2, i_inc++)
      {
        lower = BTOR_PEEK_STACK (ranges, i_range);
        upper = BTOR_PEEK_STACK (ranges, i_range + 1);
        assert (i_inc < BTOR_COUNT_STACK (increments));
        inc           = BTOR_PEEK_STACK (increments, i_inc);
        tmp           = create_pattern_itoi (btor, lower, upper, subst, inc);
        tmp->is_array = 1;
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_free_bv (mm, inc);
      }
    }

    /* pattern: index -> index + 1 */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (increments);
    find_ranges (btor,
                 &indices_itoip1,
                 &ranges,
                 &increments,
                 &indices_rem,
                 &num_set_itoip1,
                 0,
                 &size_set_itoip1,
                 0);
    if (!BTOR_EMPTY_STACK (ranges))
    {
      assert (BTOR_COUNT_STACK (ranges) % 2 == 0);
      for (i_range = 0, i_inc = 0; i_range < BTOR_COUNT_STACK (ranges) - 1;
           i_range += 2, i_inc++)
      {
        lower = BTOR_PEEK_STACK (ranges, i_range);
        upper = BTOR_PEEK_STACK (ranges, i_range + 1);
        assert (i_inc < BTOR_COUNT_STACK (increments));
        inc           = BTOR_PEEK_STACK (increments, i_inc);
        tmp           = create_pattern_itoip1 (btor, lower, upper, subst, inc);
        tmp->is_array = 1;
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_free_bv (mm, inc);
      }
    }

    /* pattern: memcopy */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (increments);
    find_ranges (btor,
                 &indices_cpy,
                 &ranges,
                 &increments,
                 &indices_rem,
                 &num_cpy,
                 0,
                 &size_cpy,
                 0);
    if (!BTOR_EMPTY_STACK (ranges))
    {
      assert (base == subst);
      assert (BTOR_COUNT_STACK (ranges) % 2 == 0);
      for (i_range = 0, i_inc = 0; i_range < BTOR_COUNT_STACK (ranges) - 1;
           i_range += 2, i_inc++)
      {
        lower = BTOR_PEEK_STACK (ranges, i_range);
        upper = BTOR_PEEK_STACK (ranges, i_range + 1);
        assert (i_inc < BTOR_COUNT_STACK (increments));
        inc   = BTOR_PEEK_STACK (increments, i_inc);
        b     = btor_get_ptr_hash_table (index_value_map, lower);
        value = b->data.as_ptr;
        extract_cpy_src_dst_info (
            lower, value, &src_array, &src_addr, &dst_addr, 0);
        /* 'subst' == destination array */
        tmp = create_pattern_cpy (
            btor, lower, upper, src_array, subst, src_addr, dst_addr, inc);
        tmp->is_array = 1;
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_free_bv (mm, inc);
      }
    }

    num_total = num_set + num_set_inc + num_set_itoi + num_set_itoip1 + num_cpy;

    /* we can skip creating writes if we did not find any pattern in a write
     * chain, and thus can leave the write chain as-is.
     * for the top equality case we always have to create writes since we
     * convert top level equalities to writes. */
    if (is_top_eq || num_total > 0)
    {
      /* no pattern found for indices in 'indices_rem'. create writes */
      for (i_index = 0; i_index < BTOR_COUNT_STACK (indices_rem); i_index++)
      {
        lower = BTOR_PEEK_STACK (indices_rem, i_index);
        b     = btor_get_ptr_hash_table (index_value_map, lower);
        assert (b);
        value = b->data.as_ptr;
        tmp   = btor_write_exp (btor, subst, lower, value);
        btor_release_exp (btor, subst);
        subst = tmp;
        num_writes++;
      }
    }

    assert ((is_top_eq || num_total > 0) || base == subst);
    if (base != subst) btor_insert_substitution (btor, array, subst, 0);
    btor_release_exp (btor, subst);

    btor_delete_ptr_hash_table (index_value_map);
    btor_delete_ptr_hash_table (t);
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (indices);
    BTOR_RESET_STACK (values);
    BTOR_RESET_STACK (increments);
    BTOR_RESET_STACK (indices_itoi);
    BTOR_RESET_STACK (indices_itoip1);
    BTOR_RESET_STACK (indices_cpy);
    BTOR_RESET_STACK (indices_rem);
  }
  BTOR_RELEASE_STACK (mm, ranges);
  BTOR_RELEASE_STACK (mm, indices);
  BTOR_RELEASE_STACK (mm, values);
  BTOR_RELEASE_STACK (mm, increments);
  BTOR_RELEASE_STACK (mm, indices_itoi);
  BTOR_RELEASE_STACK (mm, indices_itoip1);
  BTOR_RELEASE_STACK (mm, indices_cpy);
  BTOR_RELEASE_STACK (mm, indices_rem);

  BTOR_MSG (btor->msg,
            1,
            "set: %u (%u), "
            "set_inc: %u (%u), "
            "set_itoi: %u (%u), "
            "set_itoip1: %u (%u), "
            "cpy: %u (%u)",
            num_set,
            size_set,
            num_set_inc,
            size_set_inc,
            num_set_itoi,
            size_set_itoi,
            num_set_itoip1,
            size_set_itoip1,
            num_cpy,
            size_cpy);
  return num_total;
}

void
btor_extract_lambdas (Btor *btor)
{
  assert (btor);

  unsigned num_lambdas;
  double start, delta;
  BtorPtrHashTable *map_value_index, *map_lambda_base;
  BtorMemMgr *mm;

  if (btor->lambdas->count == 0 && btor->ufs->count == 0) return;

  start = btor_time_stamp ();

  mm = btor->mm;
  /* maps for each array values to stacks of indices */
  map_value_index =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  /* contains the base array for each write chain */
  map_lambda_base =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor_init_substitutions (btor);

  /* collect lambdas that are at the top of lambda chains */
  collect_indices_writes (btor, map_value_index, map_lambda_base);
  /* top level equality pre-initialization */
  collect_indices_top_eqs (btor, map_value_index);
  num_lambdas = extract_lambdas (btor, map_value_index, map_lambda_base);
  btor_delete_ptr_hash_table (map_lambda_base);
  btor_delete_ptr_hash_table (map_value_index);

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  delta = btor_time_stamp () - start;
  BTOR_MSG (
      btor->msg, 1, "extracted %u lambdas in %.3f seconds", num_lambdas, delta);
}
