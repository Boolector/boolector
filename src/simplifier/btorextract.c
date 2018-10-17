/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Mathias Preiner.
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorextract.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btorexp.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

#define BTOR_CONST_GET_BITS(c)                                   \
  btor_node_is_inverted (c) ? btor_node_bv_const_get_invbits (c) \
                            : btor_node_bv_const_get_bits (c)

inline static void
extract_base_addr_offset (BtorNode *bvadd, BtorNode **base, BtorNode **offset)
{
  assert (btor_node_is_regular (bvadd));
  assert (btor_node_is_bv_add (bvadd));

  if (btor_node_is_bv_const (bvadd->e[0]))
  {
    if (offset) *offset = bvadd->e[0];
    if (base) *base = bvadd->e[1];
  }
  else
  {
    assert (btor_node_is_bv_const (bvadd->e[1]));
    if (offset) *offset = bvadd->e[1];
    if (base) *base = bvadd->e[0];
  }
}

static int32_t
cmp_abs_rel_indices (const void *a, const void *b)
{
  bool is_abs;
  BtorBitVector *bx, *by;
  BtorNode *x, *y, *x_base_addr, *y_base_addr, *x_offset, *y_offset;

  x = *((BtorNode **) a);
  y = *((BtorNode **) b);

  is_abs = btor_node_is_bv_const (x) && btor_node_is_bv_const (y);

  if (is_abs) /* absolute address */
  {
    bx = BTOR_CONST_GET_BITS (x);
    by = BTOR_CONST_GET_BITS (y);
  }
  else /* relative address */
  {
    assert (!btor_node_is_inverted (x));
    assert (!btor_node_is_inverted (y));
    assert (btor_node_is_bv_add (x));
    assert (btor_node_is_bv_add (y));
    extract_base_addr_offset (x, &x_base_addr, &x_offset);
    extract_base_addr_offset (y, &y_base_addr, &y_offset);
    assert (x_base_addr == y_base_addr);
    assert (btor_node_is_bv_const (x_offset));
    assert (btor_node_is_bv_const (y_offset));
    bx = BTOR_CONST_GET_BITS (x_offset);
    by = BTOR_CONST_GET_BITS (y_offset);
  }
  assert (bx);
  assert (by);
  return btor_bv_compare (bx, by);
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
  assert (btor_node_is_regular (param));
  assert (btor_node_is_param (param));
  assert (btor_node_is_bv_const (lower) || btor_node_is_bv_add (lower));
  assert (btor_node_is_bv_const (upper) || btor_node_is_bv_add (upper));
  assert (btor_node_get_sort_id (lower) == btor_node_get_sort_id (upper));
  assert (offset);

  int64_t pos;
  BtorNode *res, *le0, *le1, *and, *off, *sub, *rem, *eq, *zero, *slice;

  le0 = btor_exp_bv_ulte (btor, lower, param);
  le1 = btor_exp_bv_ulte (btor, param, upper);
  and = btor_exp_bv_and (btor, le0, le1);

  /* increment by one */
  if (btor_bv_is_one (offset)) res = btor_node_copy (btor, and);
  /* increment by power of two */
  else if ((pos = btor_bv_power_of_two (offset)) > -1)
  {
    assert (pos > 0);
    sub   = btor_exp_bv_sub (btor, upper, param);
    slice = btor_exp_bv_slice (btor, sub, pos - 1, 0);
    zero  = btor_exp_bv_zero (btor, btor_node_get_sort_id (slice));
    eq    = btor_exp_eq (btor, slice, zero);
    res   = btor_exp_bv_and (btor, and, eq);

    btor_node_release (btor, zero);
    btor_node_release (btor, slice);
    btor_node_release (btor, sub);
    btor_node_release (btor, eq);
  }
  /* increment by some arbitrary value */
  else
  {
    zero = btor_exp_bv_zero (btor, btor_node_get_sort_id (lower));
    off  = btor_exp_bv_const (btor, offset);
    assert (btor_node_get_sort_id (off) == btor_node_get_sort_id (lower));
    sub = btor_exp_bv_sub (btor, upper, param);
    rem = btor_exp_bv_urem (btor, sub, off);
    eq  = btor_exp_eq (btor, rem, zero);
    res = btor_exp_bv_and (btor, and, eq);

    btor_node_release (btor, zero);
    btor_node_release (btor, off);
    btor_node_release (btor, sub);
    btor_node_release (btor, rem);
    btor_node_release (btor, eq);
  }
  btor_node_release (btor, le0);
  btor_node_release (btor, le1);
  btor_node_release (btor, and);
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
  assert (btor_node_real_addr (lower)->kind
          == btor_node_real_addr (upper)->kind);
  assert (btor_node_is_bv_const (lower) || btor_node_is_bv_add (lower));
  assert (btor_node_get_sort_id (lower) == btor_node_get_sort_id (upper));
  assert (offset);

  BtorNode *res, *param, *ite, *read, *cond;

  param = btor_exp_param (btor, btor_node_get_sort_id (lower), 0);
  read  = btor_exp_read (btor, array, param);
  cond  = create_range (btor, lower, upper, param, offset);
  ;
  ite = btor_exp_cond (btor, cond, value, read);
  res = btor_exp_lambda (btor, param, ite);

  btor_node_release (btor, param);
  btor_node_release (btor, read);
  btor_node_release (btor, cond);
  btor_node_release (btor, ite);

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
  assert (btor_node_real_addr (lower)->kind
          == btor_node_real_addr (upper)->kind);
  assert (btor_node_is_bv_const (lower) || btor_node_is_bv_add (lower));
  assert (btor_node_get_sort_id (lower) == btor_node_get_sort_id (upper));
  assert (btor_sort_fun_get_codomain (btor, btor_node_get_sort_id (array))
          == btor_node_get_sort_id (lower));
  assert (offset);

  BtorNode *res, *param, *ite, *read, *cond;

  param = btor_exp_param (btor, btor_node_get_sort_id (lower), 0);
  read  = btor_exp_read (btor, array, param);
  cond  = create_range (btor, lower, upper, param, offset);
  ;
  ite = btor_exp_cond (btor, cond, param, read);
  res = btor_exp_lambda (btor, param, ite);

  btor_node_release (btor, param);
  btor_node_release (btor, read);
  btor_node_release (btor, cond);
  btor_node_release (btor, ite);

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
  assert (btor_node_real_addr (lower)->kind
          == btor_node_real_addr (upper)->kind);
  assert (btor_node_is_bv_const (lower) || btor_node_is_bv_add (lower));
  assert (btor_node_get_sort_id (lower) == btor_node_get_sort_id (upper));
  assert (btor_sort_fun_get_codomain (btor, btor_node_get_sort_id (array))
          == btor_node_get_sort_id (lower));
  assert (offset);

  BtorNode *res, *param, *ite, *read, *cond, *inc;

  param = btor_exp_param (btor, btor_node_get_sort_id (lower), 0);
  read  = btor_exp_read (btor, array, param);
  cond  = create_range (btor, lower, upper, param, offset);
  ;
  inc = btor_exp_bv_inc (btor, param);
  ite = btor_exp_cond (btor, cond, inc, read);
  res = btor_exp_lambda (btor, param, ite);

  btor_node_release (btor, param);
  btor_node_release (btor, read);
  btor_node_release (btor, cond);
  btor_node_release (btor, inc);
  btor_node_release (btor, ite);

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
  assert (!btor_node_is_inverted (lower));
  assert (!btor_node_is_inverted (upper));
  assert (btor_node_is_bv_add (lower));
  assert (btor_node_is_bv_add (upper));

  BtorNode *res, *param, *ite, *read, *cond, *read_src, *add, *sub;

  param = btor_exp_param (btor, btor_node_get_sort_id (lower), 0);
  read  = btor_exp_read (btor, dst_array, param);
  cond  = create_range (btor, lower, upper, param, offset);

  sub      = btor_exp_bv_sub (btor, param, dst_addr);
  add      = btor_exp_bv_add (btor, src_addr, sub);
  read_src = btor_exp_read (btor, src_array, add);
  ite      = btor_exp_cond (btor, cond, read_src, read);
  res      = btor_exp_lambda (btor, param, ite);

  btor_node_release (btor, param);
  btor_node_release (btor, read);
  btor_node_release (btor, cond);
  btor_node_release (btor, sub);
  btor_node_release (btor, add);
  btor_node_release (btor, read_src);
  btor_node_release (btor, ite);
  return res;
}

static bool
is_write_exp (BtorNode *exp,
              BtorNode **array,
              BtorNode **index,
              BtorNode **value)
{
  assert (exp);
  assert (btor_node_is_regular (exp));

  BtorNode *param, *body, *eq, *app;

  if (!btor_node_is_lambda (exp)
      || btor_node_fun_get_arity (exp->btor, exp) > 1)
    return false;

  param = exp->e[0];
  body  = btor_node_binder_get_body (exp);

  if (btor_node_is_inverted (body) || !btor_node_is_bv_cond (body))
    return false;

  /* check condition */
  eq = body->e[0];
  if (btor_node_is_inverted (eq) || !btor_node_is_bv_eq (eq)
      || !eq->parameterized || (eq->e[0] != param && eq->e[1] != param))
    return false;

  /* check value */
  if (btor_node_real_addr (body->e[1])->parameterized) return false;

  /* check apply on unmodified array */
  app = body->e[2];
  if (btor_node_is_inverted (app) || !btor_node_is_apply (app)
      || btor_node_fun_get_arity (app->btor, app->e[0]) > 1
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
  assert (btor_node_is_regular (exp));

  BtorNode *param, *body, *app_if, *app_else;

  if (!btor_node_is_lambda (exp)
      || btor_node_fun_get_arity (exp->btor, exp) > 1)
    return false;

  param = exp->e[0];
  body  = btor_node_binder_get_body (exp);

  if (btor_node_is_inverted (body) || !btor_node_is_bv_cond (body))
    return false;

  /* check value */
  if (!btor_node_real_addr (body->e[1])->parameterized
      || !btor_node_real_addr (body->e[2])->parameterized)
    return false;

  /* check applies in if and else branch */
  app_if = body->e[1];
  if (btor_node_is_inverted (app_if) || !btor_node_is_apply (app_if)
      || btor_node_fun_get_arity (app_if->btor, app_if->e[0]) > 1
      || app_if->e[1]->e[0] != param)
    return false;

  app_else = body->e[1];
  if (btor_node_is_inverted (app_else) || !btor_node_is_apply (app_else)
      || btor_node_fun_get_arity (app_else->btor, app_else->e[0]) > 1
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

  inc = btor_exp_bv_inc (btor_node_real_addr (index)->btor, index);
  res = inc == value;
  btor_node_release (btor_node_real_addr (index)->btor, inc);
  return res;
}

inline static bool
is_cpy_pattern (BtorNode *index, BtorNode *value)
{
  BtorNode *bvadd, *dst_addr, *off;

  if (btor_node_is_inverted (index) || !btor_node_is_bv_add (index)
      || btor_node_is_inverted (value) || !btor_node_is_apply (value)
      || btor_node_is_inverted (value->e[1]->e[0])
      || !btor_node_is_bv_add (value->e[1]->e[0]))
    return false;

  if (btor_node_is_bv_const (index->e[0]))
    off = index->e[0];
  else if (btor_node_is_bv_const (index->e[1]))
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
  return btor_node_is_bv_const (index)
         && (!prev_index || btor_node_is_bv_const (prev_index));
}

inline static bool
is_rel_set_pattern (BtorNode *index, BtorNode *prev_index)
{
  BtorNode *base_addr, *offset, *prev_base_addr, *prev_offset;

  if (btor_node_is_inverted (index) || !btor_node_is_bv_add (index))
    return false;

  if (!btor_node_is_bv_const (index->e[0])
      && !btor_node_is_bv_const (index->e[1]))
    return false;

  if (!prev_index) return true;

  if (btor_node_is_inverted (prev_index) || !btor_node_is_bv_add (prev_index))
    return false;

  if (!btor_node_is_bv_const (prev_index->e[0])
      && !btor_node_is_bv_const (prev_index->e[1]))
    return false;

  extract_base_addr_offset (index, &base_addr, &offset);
  extract_base_addr_offset (prev_index, &prev_base_addr, &prev_offset);
  assert (btor_node_is_bv_const (offset));
  assert (btor_node_is_bv_const (prev_offset));

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

  if (!(b = btor_hashptr_table_get (map_value_index, lambda)))
  {
    b              = btor_hashptr_table_add (map_value_index, lambda);
    t              = btor_hashptr_table_new (mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    b->data.as_ptr = t;
  }
  else
    t = b->data.as_ptr;
  assert (t);

  if (!(b = btor_hashptr_table_get (t, value)))
  {
    b = btor_hashptr_table_add (t, value);
    BTOR_NEW (mm, indices);
    BTOR_INIT_STACK (mm, *indices);
    b->data.as_ptr = indices;
  }
  else
    indices = (BtorNodePtrStack *) b->data.as_ptr;
  assert (indices);
  if (btor_node_is_bv_const (index))
    offset = index;
  else
  {
    assert (btor_node_is_regular (index));
    assert (btor_node_is_bv_add (index));
    extract_base_addr_offset (index, 0, &offset);
    assert (btor_node_is_bv_const (offset));
  }

  BTOR_PUSH_STACK (*indices, index);
}

// TODO (ma): is there a way to recognize base_addr + 0 as
//            relative?
//            -> only if its the last index
//	       - prev_index->base_addr == index
static bool
check_and_add_index (Btor *btor,
                     BtorPtrHashTable *map_value_index,
                     BtorNode *fun,
                     BtorNode *index,
                     BtorNode *prev_index,
                     BtorNode *value,
                     BtorNode *prev_value,
                     BtorNode *next_fun,
                     BtorIntHashTable *visit_cache,
                     BtorIntHashTable *index_cache)
{
  if (!is_abs_set_pattern (index, prev_index)
      && !is_rel_set_pattern (index, prev_index))
    return false;

  /* optimization for memcopy: do not visit lambdas that are only accessed via
   * this lambda (reduces number of redundant memcopy patterns)
   */
  if (is_rel_set_pattern (index, prev_index)
      && is_copy_pattern (index, value, prev_index, prev_value, next_fun)
      && value->e[0] == next_fun && next_fun->parents == 2)
  {
    btor_hashint_table_add (visit_cache, btor_node_get_id (next_fun));
  }

  btor_hashint_table_add (index_cache, btor_node_get_id (index));
  add_to_index_map (btor, map_value_index, fun, index, value);
  return true;
}

static void
collect_indices_updates (Btor *btor,
                         BtorPtrHashTable *map_value_index,
                         BtorPtrHashTable *map_lambda_base)
{
  uint32_t i;
  BtorNode *cur, *cur_upd, *top_upd, *index, *prev_index, *value;
  BtorNode *prev_value;
  BtorPtrHashTableIterator it;
  BtorNodePtrStack visit, upd_nodes;
  BtorIntHashTable *visit_cache, *index_cache;

  BTOR_INIT_STACK (btor->mm, visit);
  BTOR_INIT_STACK (btor->mm, upd_nodes);
  visit_cache = btor_hashint_table_new (btor->mm);

  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    BTOR_PUSH_STACK (visit, cur);
  }

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (btor_hashint_table_contains (visit_cache, cur->id)) continue;

    btor_hashint_table_add (visit_cache, cur->id);
    for (i = 0; i < cur->arity; i++) BTOR_PUSH_STACK (visit, cur->e[i]);

    /* follow update chains */
    // TODO: add fun equalities?
    if (btor_node_is_apply (cur))
      BTOR_PUSH_STACK (upd_nodes, cur->e[0]);
    else if (btor_node_is_fun_cond (cur))
    {
      BTOR_PUSH_STACK (upd_nodes, cur->e[1]);
      BTOR_PUSH_STACK (upd_nodes, cur->e[2]);
    }

    while (!BTOR_EMPTY_STACK (upd_nodes))
    {
      cur_upd = top_upd = BTOR_POP_STACK (upd_nodes);
      prev_index = prev_value = 0;

      if (btor_hashint_table_contains (visit_cache, btor_node_get_id (top_upd)))
        continue;

      index_cache = btor_hashint_table_new (btor->mm);
      while (btor_node_is_update (cur_upd))
      {
        assert (btor_node_is_regular (cur_upd));
        assert (cur_upd->is_array);
        index = cur_upd->e[1]->e[0];
        value = cur_upd->e[2];

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (btor_hashint_table_contains (index_cache, btor_node_get_id (index)))
        {
          cur_upd = cur_upd->e[0];
          continue;
        }

        /* use array as new start point */
        if (!check_and_add_index (btor,
                                  map_value_index,
                                  top_upd,
                                  index,
                                  prev_index,
                                  value,
                                  prev_value,
                                  cur_upd->e[0],
                                  visit_cache,
                                  index_cache))
        {
          break;
        }

        cur_upd    = cur_upd->e[0];
        prev_index = index;
        prev_value = value;
      }
      if (btor_node_is_update (top_upd))
      {
        if (btor_hashptr_table_get (map_value_index, top_upd))
        {
          assert (!btor_hashptr_table_get (map_lambda_base, top_upd));
          btor_hashptr_table_add (map_lambda_base, top_upd)->data.as_ptr =
              cur_upd;
        }
      }
      btor_hashint_table_delete (index_cache);
      btor_hashint_table_add (visit_cache, btor_node_get_id (top_upd));
    }
  }
  btor_hashint_table_delete (visit_cache);
  BTOR_RELEASE_STACK (visit);
  BTOR_RELEASE_STACK (upd_nodes);
}

static void
collect_indices_lambdas (Btor *btor,
                         BtorPtrHashTable *map_value_index,
                         BtorPtrHashTable *map_lambda_base)
{
  bool is_top;
  BtorNode *lambda, *cur, *array, *index, *value, *tmp, *array_if, *array_else;
  BtorNode *prev_index, *prev_value;
  BtorPtrHashTableIterator it;
  BtorNodeIterator pit;
  BtorNodePtrStack lambdas;
  BtorIntHashTable *index_cache, *visit_cache;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, lambdas);
  visit_cache = btor_hashint_table_new (mm);

  /* collect lambdas that are at the top of lambda chains */
  btor_iter_hashptr_init_reversed (&it, btor->lambdas);
  while (btor_iter_hashptr_has_next (&it))
  {
    lambda = btor_iter_hashptr_next (&it);
    assert (btor_node_is_regular (lambda));

    /* already visited */
    if (btor_hashptr_table_get (map_value_index, lambda)) continue;

    /* we only consider writes */
    if (!lambda->is_array || !btor_node_lambda_get_static_rho (lambda))
      continue;

    is_top = false;
    btor_iter_apply_parent_init (&pit, lambda);
    while (btor_iter_apply_parent_has_next (&pit))
    {
      tmp = btor_iter_apply_parent_next (&pit);

      if (!tmp->parameterized)
      {
        is_top = true;
        break;
      }
    }

    if (!is_top) continue;

    BTOR_PUSH_STACK (lambdas, lambda);
    while (!BTOR_EMPTY_STACK (lambdas))
    {
      lambda = BTOR_POP_STACK (lambdas);

      /* already visited */
      if (btor_hashint_table_contains (visit_cache, btor_node_get_id (lambda)))
        continue;

      btor_hashint_table_add (visit_cache, btor_node_get_id (lambda));

      cur         = lambda;
      index_cache = btor_hashint_table_new (mm);
      prev_index = prev_value = 0;
      while (is_write_exp (cur, &array, &index, &value))
      {
        assert (btor_node_is_regular (array));
        assert (btor_node_is_fun (array));

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (btor_hashint_table_contains (index_cache, btor_node_get_id (index)))
        {
          cur = array;
          continue;
        }

        /* use array as new start point */
        if (!check_and_add_index (btor,
                                  map_value_index,
                                  lambda,
                                  index,
                                  prev_index,
                                  value,
                                  prev_value,
                                  array,
                                  visit_cache,
                                  index_cache))
        {
          BTOR_PUSH_STACK (lambdas, array);
          break;
        }

        cur        = array;
        prev_index = index;
        prev_value = value;
      }
      if (btor_hashptr_table_get (map_value_index, lambda))
      {
        assert (!btor_hashptr_table_get (map_lambda_base, lambda));
        btor_hashptr_table_add (map_lambda_base, lambda)->data.as_ptr = cur;
      }
      btor_hashint_table_delete (index_cache);

      // TODO (ma): can only be ite now change to is_fun_cond_node check
      if (is_array_ite_exp (cur, &array_if, &array_else))
      {
        BTOR_PUSH_STACK (lambdas, array_if);
        BTOR_PUSH_STACK (lambdas, array_else);
      }
    }
  }
  btor_hashint_table_delete (visit_cache);
  BTOR_RELEASE_STACK (lambdas);
}

static void
collect_indices_top_eqs (Btor *btor, BtorPtrHashTable *map_value_index)
{
  BtorPtrHashTableIterator it;
  BtorNode *cur, *lhs, *rhs, *read, *array, *index, *value;

  /* top level equality pre-initialization */
  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->synthesized_constraints);
  btor_iter_hashptr_queue (&it, btor->embedded_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);
    if (btor_node_is_inverted (cur) || !btor_node_is_bv_eq (cur)) continue;

    lhs = cur->e[0];
    rhs = cur->e[1];

    index = value = 0;
    if (!btor_node_is_inverted (lhs) && btor_node_is_apply (lhs)
        && btor_node_is_uf_array (lhs->e[0])
        && btor_node_is_bv_const (lhs->e[1]->e[0])
        && btor_node_is_bv_const (rhs))
    {
      read  = lhs;
      array = lhs->e[0];
      index = lhs->e[1]->e[0];
      value = rhs;
    }
    else if (!btor_node_is_inverted (rhs) && btor_node_is_apply (rhs)
             && btor_node_is_uf_array (rhs->e[0])
             && btor_node_is_bv_const (rhs->e[1]->e[0])
             && btor_node_is_bv_const (lhs))
    {
      read  = rhs;
      array = rhs->e[0];
      index = rhs->e[1]->e[0];
      value = lhs;
    }

    if (!index) continue;

    if (btor_hashptr_table_get (btor->substitutions, read)) continue;

    /* only add each index once */
    add_to_index_map (btor, map_value_index, array, index, value);

    /* substitute 'read' with 'value', in order to prevent down propgation
     * rewriting for 'read' during substitute_and_rebuild(...), which
     * simplifies 'read' to 'value' anyways.
     * NOTE: if 'read' is already in 'substitutions', we let the rewriting
     * engine handle inconsistencies (i,e., if 'value' is not the same
     * as in 'substitutions'. */
    btor_insert_substitution (btor, read, value, false);
  }
}

void
find_ranges (Btor *btor,
             BtorNodePtrStack *stack,
             BtorNodePtrStack *ranges,
             BtorBitVectorPtrStack *increments,
             BtorNodePtrStack *indices,
             BtorNodePtrStack *indices_ranges,
             uint32_t *num_pat,
             uint32_t *num_pat_inc,
             uint32_t *size_pat,
             uint32_t *size_pat_inc)
{
  assert (stack);
  assert (ranges);
  assert (increments);
  assert (indices);
  assert (num_pat);
  assert (size_pat);

#ifndef NDEBUG
  uint32_t num_indices = 0;
#endif
  bool in_range;
  BtorBitVector *b0, *b1, *inc, *prev_inc;
  uint32_t i, cnt, lower, upper;
  uint32_t num_pattern = 0, num_pattern_inc = 0, size_pattern = 0;
  uint32_t size_pattern_inc = 0;
  BtorNode *n0, *n1, *n0_base_addr, *n1_base_addr, *n0_offset, *n1_offset;
  BtorMemMgr *mm;
  BtorNodePtrStack index_stack;

  mm          = btor->mm;
  index_stack = *stack;
  cnt         = BTOR_COUNT_STACK (index_stack);
  if (cnt == 0) return;

  if (cnt == 1)
    BTOR_PUSH_STACK (*indices, BTOR_PEEK_STACK (index_stack, 0));
  else
  {
    assert (cnt > 1);
#ifndef NDEBUG
    /* sanity check: 'index_stack' contains either absolute or relative
     * addresses */
    for (i = 1; i < BTOR_COUNT_STACK (index_stack); i++)
    {
      n0 = btor_node_real_addr (BTOR_PEEK_STACK (index_stack, i - 1));
      n1 = btor_node_real_addr (BTOR_PEEK_STACK (index_stack, i));
      assert (n0->kind == n1->kind);
      assert (btor_node_is_bv_add (n0) || btor_node_is_bv_const (n0));
      if (btor_node_is_bv_add (n0))
      {
        extract_base_addr_offset (n0, &n0_base_addr, &n0_offset);
        extract_base_addr_offset (n1, &n1_base_addr, &n1_offset);
        assert (n0_base_addr == n1_base_addr);
        assert (btor_node_is_bv_const (n0_offset));
        assert (btor_node_is_bv_const (n1_offset));
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

        if (btor_node_is_bv_const (n0))
        {
          assert (btor_node_is_bv_const (n1));
          b0 = BTOR_CONST_GET_BITS (n0);
          b1 = BTOR_CONST_GET_BITS (n1);
        }
        else
        {
          assert (!btor_node_is_inverted (n0));
          assert (!btor_node_is_inverted (n1));
          assert (btor_node_is_bv_add (n0));
          assert (btor_node_is_bv_add (n1));
          extract_base_addr_offset (n0, &n0_base_addr, &n0_offset);
          extract_base_addr_offset (n1, &n1_base_addr, &n1_offset);
          assert (n0_base_addr == n1_base_addr);
          b0 = BTOR_CONST_GET_BITS (n0_offset);
          b1 = BTOR_CONST_GET_BITS (n1_offset);
        }
        assert (b0);
        assert (b1);
        inc = btor_bv_sub (mm, b1, b0);

        if (!prev_inc) prev_inc = btor_bv_copy (mm, inc);

        /* increment upper bound of range */
        in_range = btor_bv_compare (inc, prev_inc) == 0;
        if (in_range) upper += 1;
      }

      if (!in_range)
      {
        /* push index */
        if (upper == lower)
        {
          BTOR_PUSH_STACK (*indices, BTOR_PEEK_STACK (index_stack, lower));
#ifndef NDEBUG
          num_indices++;
#endif
          goto NEW_RANGE;
        }
        /* range is too small, push separate indices */
        else if (upper - lower <= 1
                 /* range with an offset greater than 1 */
                 && btor_bv_power_of_two (prev_inc) != 0)
        {
          /* last iteration step: if range contains all indices
           * up to the last one, we can push all indices */
          if (upper == cnt - 1) upper += 1;

          /* push all indices from lower until upper - 1 */
          for (; lower < upper; lower++)
          {
            BTOR_PUSH_STACK (*indices, BTOR_PEEK_STACK (index_stack, lower));
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
          BTOR_PUSH_STACK (*increments, prev_inc);
          BTOR_PUSH_STACK (*ranges, BTOR_PEEK_STACK (index_stack, lower));
          BTOR_PUSH_STACK (*ranges, BTOR_PEEK_STACK (index_stack, upper));
          /* push all indices in range lower <= i <= upper onto
           * 'indices_ranges' stack */
          for (i = lower; i <= upper; i++)
            BTOR_PUSH_STACK (*indices_ranges, BTOR_PEEK_STACK (index_stack, i));
          BTOR_PUSH_STACK (*indices_ranges, 0);
#ifndef NDEBUG
          num_indices += upper - lower + 1;
#endif
          if (btor_bv_is_one (prev_inc))
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
          if (inc) btor_bv_free (mm, inc);
          inc = 0;
        }
      }
      if (prev_inc) btor_bv_free (mm, prev_inc);
      prev_inc = inc;
    }
    if (inc) btor_bv_free (mm, inc);
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

static BtorPtrHashTable *
create_static_rho (Btor *btor,
                   BtorNode *indices[],
                   BtorNode *value,
                   BtorPtrHashTable *index_value_map)
{
  uint32_t i;
  BtorNode *idx, *args;
  BtorPtrHashTable *static_rho;
  BtorPtrHashBucket *b;

  static_rho = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);
  if (value)
  {
    for (i = 0; indices[i]; i++)
    {
      idx            = indices[i];
      args           = btor_exp_args (btor, &idx, 1);
      b              = btor_hashptr_table_add (static_rho, args);
      b->data.as_ptr = btor_node_copy (btor, value);
    }
  }
  else
  {
    assert (index_value_map);
    for (i = 0; indices[i]; i++)
    {
      idx = indices[i];
      b   = btor_hashptr_table_get (index_value_map, idx);
      assert (b);
      value          = b->data.as_ptr;
      args           = btor_exp_args (btor, &idx, 1);
      b              = btor_hashptr_table_add (static_rho, args);
      b->data.as_ptr = btor_node_copy (btor, value);
    }
  }
  return static_rho;
}

static uint32_t
extract_lambdas (Btor *btor,
                 BtorPtrHashTable *map_value_index,
                 BtorPtrHashTable *map_lambda_base)
{
  assert (btor);
  assert (map_value_index);
  assert (map_lambda_base);

  bool is_top_eq;
  BtorBitVector *inc;
  uint32_t i_range, i_index, i_value, i_inc, i_index_r;
  BtorNode *subst, *base, *tmp, *array, *value, *lower, *upper;
  BtorNode *src_array, *src_addr, *dst_addr;
  BtorPtrHashTableIterator it, iit;
  BtorPtrHashTable *t, *index_value_map, *static_rho;
  BtorPtrHashBucket *b;
  BtorNodePtrStack ranges, indices, values, indices_itoi, indices_itoip1;
  BtorNodePtrStack indices_cpy, indices_rem, indices_ranges, *stack;
  BtorBitVectorPtrStack increments;
  BtorMemMgr *mm;

  /* statistics */
  uint32_t num_total = 0, num_writes = 0;
  uint32_t num_set = 0, num_set_inc = 0, num_set_itoi = 0, num_set_itoip1 = 0;
  uint32_t num_cpy = 0, size_set = 0, size_set_inc = 0, size_set_itoi = 0;
  uint32_t size_set_itoip1 = 0, size_cpy = 0;

  mm = btor->mm;
  BTOR_INIT_STACK (mm, ranges);
  BTOR_INIT_STACK (mm, indices);
  BTOR_INIT_STACK (mm, indices_ranges);
  BTOR_INIT_STACK (mm, increments);
  BTOR_INIT_STACK (mm, values);
  BTOR_INIT_STACK (mm, indices_itoi);
  BTOR_INIT_STACK (mm, indices_itoip1);
  BTOR_INIT_STACK (mm, indices_cpy);
  BTOR_INIT_STACK (mm, indices_rem);
  btor_iter_hashptr_init (&it, map_value_index);
  while (btor_iter_hashptr_has_next (&it))
  {
    t     = it.bucket->data.as_ptr;
    array = btor_iter_hashptr_next (&it);
    assert (t);
    assert (array->is_array);

    /* find memset patterns, the remaining unused indices are pushed onto
     * stack 'indices' */
    btor_iter_hashptr_init (&iit, t);
    while (btor_iter_hashptr_has_next (&iit))
    {
      stack = iit.bucket->data.as_ptr;
      value = btor_iter_hashptr_next (&iit);
      assert (stack);
      find_ranges (btor,
                   stack,
                   &ranges,
                   &increments,
                   &indices,
                   &indices_ranges,
                   &num_set,
                   &num_set_inc,
                   &size_set,
                   &size_set_inc);
      BTOR_PUSH_STACK (ranges, 0);
      BTOR_PUSH_STACK (indices, 0);
      BTOR_PUSH_STACK (values, value);
      assert (BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values) > 0
              || BTOR_COUNT_STACK (indices) - BTOR_COUNT_STACK (values) > 0);
      assert ((BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values)) % 2 == 0);
      assert ((BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values)) / 2
              == BTOR_COUNT_STACK (increments));
    }

    /* choose base array for patterns/writes:
     *  1) write chains: base array of the write chains
     *  2) top eqs: a new UF symbol */
    if ((b = btor_hashptr_table_get (map_lambda_base, array)))
    {
      assert (btor_node_is_lambda (array) || btor_node_is_update (array));
      b = btor_hashptr_table_get (map_lambda_base, array);
      assert (b);
      subst     = btor_node_copy (btor, b->data.as_ptr);
      is_top_eq = false;
    }
    else
    {
      assert (btor_node_is_uf_array (array));
      subst     = btor_exp_array (btor, btor_node_get_sort_id (array), 0);
      is_top_eq = true;
    }

    index_value_map =
        btor_hashptr_table_new (mm,
                                (BtorHashPtr) btor_node_hash_by_id,
                                (BtorCmpPtr) btor_node_compare_by_id);
    base    = subst;
    i_range = i_index = i_inc = 0;
    i_index_r                 = 0;
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
        btor_node_release (btor, subst);
        subst = tmp;
        btor_bv_free (mm, inc);
        i_inc++;

        assert (i_index_r < BTOR_COUNT_STACK (indices_ranges));
        static_rho = create_static_rho (
            btor, indices_ranges.start + i_index_r, value, 0);
        i_index_r += static_rho->count + 1;
        if (btor_node_lambda_get_static_rho (subst))
          btor_node_lambda_delete_static_rho (btor, subst);
        btor_node_lambda_set_static_rho (subst, static_rho);
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
        assert (!btor_hashptr_table_get (index_value_map, lower));
        /* save index value pairs for later */
        btor_hashptr_table_add (index_value_map, lower)->data.as_ptr = value;

        /* pattern 1: index -> index */
        if (is_itoi_pattern (lower, value))
          BTOR_PUSH_STACK (indices_itoi, lower);
        /* pattern 2: index -> index + 1 */
        else if (is_itoip1_pattern (lower, value))
          BTOR_PUSH_STACK (indices_itoip1, lower);
        /* pattern 3: memcopy pattern */
        else if (is_cpy_pattern (lower, value))
          BTOR_PUSH_STACK (indices_cpy, lower);
        else /* no pattern found */
          BTOR_PUSH_STACK (indices_rem, lower);
      }
    }

    /* pattern: index -> index */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (indices_ranges);
    BTOR_RESET_STACK (increments);
    find_ranges (btor,
                 &indices_itoi,
                 &ranges,
                 &increments,
                 &indices_rem,
                 &indices_ranges,
                 &num_set_itoi,
                 0,
                 &size_set_itoi,
                 0);
    i_index_r = 0;
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
        btor_node_release (btor, subst);
        subst = tmp;
        btor_bv_free (mm, inc);

        assert (i_index_r < BTOR_COUNT_STACK (indices_ranges));
        static_rho = create_static_rho (
            btor, indices_ranges.start + i_index_r, 0, index_value_map);
        i_index_r += static_rho->count + 1;
        if (btor_node_lambda_get_static_rho (subst))
          btor_node_lambda_delete_static_rho (btor, subst);
        btor_node_lambda_set_static_rho (subst, static_rho);
      }
    }

    /* pattern: index -> index + 1 */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (indices_ranges);
    BTOR_RESET_STACK (increments);
    find_ranges (btor,
                 &indices_itoip1,
                 &ranges,
                 &increments,
                 &indices_rem,
                 &indices_ranges,
                 &num_set_itoip1,
                 0,
                 &size_set_itoip1,
                 0);
    i_index_r = 0;
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
        btor_node_release (btor, subst);
        subst = tmp;
        btor_bv_free (mm, inc);

        assert (i_index_r < BTOR_COUNT_STACK (indices_ranges));
        static_rho = create_static_rho (
            btor, indices_ranges.start + i_index_r, 0, index_value_map);
        i_index_r += static_rho->count + 1;
        if (btor_node_lambda_get_static_rho (subst))
          btor_node_lambda_delete_static_rho (btor, subst);
        btor_node_lambda_set_static_rho (subst, static_rho);
      }
    }

    /* pattern: memcopy */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (indices_ranges);
    BTOR_RESET_STACK (increments);
    find_ranges (btor,
                 &indices_cpy,
                 &ranges,
                 &increments,
                 &indices_rem,
                 &indices_ranges,
                 &num_cpy,
                 0,
                 &size_cpy,
                 0);
    i_index_r = 0;
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
        b     = btor_hashptr_table_get (index_value_map, lower);
        value = b->data.as_ptr;
        extract_cpy_src_dst_info (
            lower, value, &src_array, &src_addr, &dst_addr, 0);
        /* 'subst' == destination array */
        tmp = create_pattern_cpy (
            btor, lower, upper, src_array, subst, src_addr, dst_addr, inc);
        tmp->is_array = 1;
        btor_node_release (btor, subst);
        subst = tmp;
        btor_bv_free (mm, inc);

        assert (i_index_r < BTOR_COUNT_STACK (indices_ranges));
        static_rho = create_static_rho (
            btor, indices_ranges.start + i_index_r, 0, index_value_map);
        i_index_r += static_rho->count + 1;
        if (btor_node_lambda_get_static_rho (subst))
          btor_node_lambda_delete_static_rho (btor, subst);
        btor_node_lambda_set_static_rho (subst, static_rho);
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
        b     = btor_hashptr_table_get (index_value_map, lower);
        assert (b);
        value = b->data.as_ptr;
        tmp   = btor_exp_write (btor, subst, lower, value);
        btor_node_release (btor, subst);
        subst = tmp;
        num_writes++;
      }
    }

    assert ((is_top_eq || num_total > 0) || base == subst);
    if (base != subst) btor_insert_substitution (btor, array, subst, false);

    btor_iter_hashptr_init (&iit, t);
    while (btor_iter_hashptr_has_next (&iit))
    {
      stack = iit.bucket->data.as_ptr;
      (void) btor_iter_hashptr_next (&iit);
      BTOR_RELEASE_STACK (*stack);
      BTOR_DELETE (mm, stack);
    }
    btor_node_release (btor, subst);

    btor_hashptr_table_delete (index_value_map);
    btor_hashptr_table_delete (t);
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (indices);
    BTOR_RESET_STACK (indices_ranges);
    BTOR_RESET_STACK (values);
    BTOR_RESET_STACK (increments);
    BTOR_RESET_STACK (indices_itoi);
    BTOR_RESET_STACK (indices_itoip1);
    BTOR_RESET_STACK (indices_cpy);
    BTOR_RESET_STACK (indices_rem);
  }
  BTOR_RELEASE_STACK (ranges);
  BTOR_RELEASE_STACK (indices);
  BTOR_RELEASE_STACK (indices_ranges);
  BTOR_RELEASE_STACK (values);
  BTOR_RELEASE_STACK (increments);
  BTOR_RELEASE_STACK (indices_itoi);
  BTOR_RELEASE_STACK (indices_itoip1);
  BTOR_RELEASE_STACK (indices_cpy);
  BTOR_RELEASE_STACK (indices_rem);

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

/* NOTE: Macro extraction may introduce extensional lambdas, which can not be
 * handled right now. If that happens Boolector aborts with an error message
 * about extensional lambdas. However, this is not a problem since we would
 * abort anyways since we only support pure quantified BV right now. */
void
extract_macros (Btor *btor)
{
  double start;
  BtorPtrHashTableIterator it;
  BtorNode *cur, *eq, *app, *var, *lambda, *param;
  BtorNode *body, *fun_body, *lambda_body;
  uint32_t num_extracted = 0;

  if (btor->forall_vars->count == 0) return;

  start = btor_util_time_stamp ();
  btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
  while (btor_iter_hashptr_has_next (&it))
  {
    cur = btor_iter_hashptr_next (&it);

    if (btor_node_is_inverted (cur) || !btor_node_is_forall (cur)) continue;

    body = cur->e[1];
    if (!btor_node_is_bv_eq (body)) continue;

    if (btor_node_is_apply (body->e[0]))
    {
      app      = body->e[0];
      fun_body = body->e[1];
    }
    else if (btor_node_is_apply (body->e[1]))
    {
      app      = body->e[1];
      fun_body = body->e[0];
    }
    else
      continue;

    if (btor_node_is_inverted (app))
    {
      app      = btor_node_invert (app);
      fun_body = btor_node_invert (fun_body);
    }

    if (btor_node_is_lambda (app->e[0])) continue;
    assert (btor_node_is_uf (app->e[0]));

    if (btor_sort_fun_get_arity (btor, app->e[0]->sort_id) != 1) continue;

    var = app->e[1]->e[0];

    if (!btor_node_param_is_forall_var (var) || var != cur->e[0]) continue;

    num_extracted++;
    param       = btor_exp_param (btor, var->sort_id, 0);
    lambda_body = btor_substitute_node (btor, fun_body, var, param);
    lambda      = btor_exp_lambda (btor, param, lambda_body);
    assert (!lambda->parameterized);
    lambda->is_array = app->e[0]->is_array;
    eq               = btor_exp_eq (btor, app->e[0], lambda);
    btor_assert_exp (btor, eq);
    btor_node_release (btor, eq);
    btor_node_release (btor, param);
    btor_node_release (btor, lambda_body);
    btor_node_release (btor, lambda);
    btor_hashptr_table_remove (btor->unsynthesized_constraints, cur, 0, 0);
    btor_node_release (btor, cur);
  }
  BTOR_MSG (btor->msg,
            1,
            "extracted %u macros in %.3f seconds",
            num_extracted,
            btor_util_time_stamp () - start);
}

void
btor_extract_lambdas (Btor *btor)
{
  assert (btor);

  uint32_t num_lambdas;
  double start, delta;
  BtorPtrHashTable *map_value_index, *map_lambda_base;
  BtorMemMgr *mm;

  if (btor->lambdas->count == 0 && btor->ufs->count == 0) return;

  start = btor_util_time_stamp ();

  mm = btor->mm;
  /* maps for each array values to stacks of indices */
  map_value_index =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  /* contains the base array for each write chain */
  map_lambda_base =
      btor_hashptr_table_new (mm,
                              (BtorHashPtr) btor_node_hash_by_id,
                              (BtorCmpPtr) btor_node_compare_by_id);
  btor_init_substitutions (btor);

  /* collect lambdas that are at the top of lambda chains */
  collect_indices_lambdas (btor, map_value_index, map_lambda_base);
  collect_indices_updates (btor, map_value_index, map_lambda_base);
  /* top level equality pre-initialization */
  collect_indices_top_eqs (btor, map_value_index);
  num_lambdas = extract_lambdas (btor, map_value_index, map_lambda_base);
  btor_hashptr_table_delete (map_lambda_base);
  btor_hashptr_table_delete (map_value_index);

  btor_substitute_and_rebuild (btor, btor->substitutions);
  btor_delete_substitutions (btor);
  delta = btor_util_time_stamp () - start;
  BTOR_MSG (
      btor->msg, 1, "extracted %u lambdas in %.3f seconds", num_lambdas, delta);
  btor->time.extract += delta;

  extract_macros (btor);
}
