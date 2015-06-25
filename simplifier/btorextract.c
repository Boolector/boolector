/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "simplifier/btorextract.h"
#include "btorconst.h"
#include "btorcore.h"
#include "utils/btoriter.h"
#include "utils/btorutil.h"

#include "dumper/btordumpsmt.h"

inline static bool is_idxidx_pattern (BtorNode *, BtorNode *);
inline static bool is_idxinc_pattern (BtorNode *, BtorNode *);
inline static bool is_memcopy_pattern (BtorNode *, BtorNode *);
static void memcopy_pattern_get_arguments (BtorNode *index,
                                           BtorNode *value,
                                           BtorNode **src_array,
                                           BtorNode **src,
                                           BtorNode **dst,
                                           BtorNode **off);

struct MemcopyOp
{
  BtorNode *src_array;
  BtorNode *src_addr;
  BtorNode *dst_addr;
  BtorNode *index;
  BtorNode *orig_index;
};

typedef struct MemcopyOp MemcopyOp;

BTOR_DECLARE_STACK (MemcopyOpPtr, MemcopyOp *);

static MemcopyOp *
new_memcopy_op (BtorMemMgr *mm, BtorNode *index, BtorNode *value)
{
  assert (is_memcopy_pattern (index, value));
  MemcopyOp *res;

  BTOR_NEW (mm, res);
  memcopy_pattern_get_arguments (index,
                                 value,
                                 &res->src_array,
                                 &res->src_addr,
                                 &res->dst_addr,
                                 &res->index);
  res->orig_index = index;

  if (BTOR_IS_INVERTED_NODE (res->index)
      && !btor_const_get_invbits (res->index))
    btor_const_set_invbits (
        res->index, btor_not_const (mm, btor_const_get_bits (res->index)));

  return res;
}

static void
free_memcopy_op (BtorMemMgr *mm, MemcopyOp *mcpyop)
{
  BTOR_DELETE (mm, mcpyop);
}

#define BTOR_CONST_GET_BITS(c)                           \
  BTOR_IS_INVERTED_NODE (c) ? btor_const_get_invbits (c) \
                            : btor_const_get_bits (c)

static int
cmp_bvconst_bits (const void *a, const void *b)
{
  const char *b0, *b1;
  BtorNode *x, *y;

  x = *((BtorNode **) a);
  y = *((BtorNode **) b);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (x)));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (y)));

  b0 = BTOR_CONST_GET_BITS (x);
  b1 = BTOR_CONST_GET_BITS (y);

  assert (b0);
  assert (b1);
  return strcmp (b0, b1);
}

inline static void
bvadd_get_base_and_offset (BtorNode *bvadd, BtorNode **base, BtorNode **offset)
{
  assert (BTOR_IS_REGULAR_NODE (bvadd));
  assert (BTOR_IS_ADD_NODE (bvadd));

  if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (bvadd->e[0])))
  {
    *offset = bvadd->e[0];
    *base   = bvadd->e[1];
  }
  else
  {
    assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (bvadd->e[1])));
    *offset = bvadd->e[1];
    *base   = bvadd->e[0];
  }
}

static int
cmp_memcopy_op (const void *a, const void *b)
{
  const char *b0, *b1;
  MemcopyOp *op_a, *op_b;

  op_a = *((MemcopyOp **) a);
  op_b = *((MemcopyOp **) b);

  if (op_a->src_array != op_b->src_array)
    return BTOR_REAL_ADDR_NODE (op_a->src_array)->id
           - BTOR_REAL_ADDR_NODE (op_b->src_array)->id;

  b0 = BTOR_CONST_GET_BITS (op_a->index);
  b1 = BTOR_CONST_GET_BITS (op_b->index);
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
create_range (
    Btor *btor, BtorNode *lower, BtorNode *upper, BtorNode *param, char *offset)
{
  assert (lower);
  assert (upper);
  assert (param);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lower))
          || BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (lower)));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (upper))
          || BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (upper)));
  assert (BTOR_REAL_ADDR_NODE (lower)->sort_id
          == BTOR_REAL_ADDR_NODE (upper)->sort_id);
  assert (offset);

  int pos;
  BtorNode *res, *le0, *le1, *and, *off, *sub, *rem, *eq, *zero, *slice;

  le0 = btor_ulte_exp (btor, lower, param);
  le1 = btor_ulte_exp (btor, param, upper);
  and = btor_and_exp (btor, le0, le1);

  /* increment by one */
  if (btor_is_one_const (offset)) res = btor_copy_exp (btor, and);
  /* increment by power of two */
  else if ((pos = btor_is_power_of_two_const (offset)) > -1)
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
                       char *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lower))
          || BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (lower)));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (upper))
          || BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (upper)));
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
create_pattern_idxidx (
    Btor *btor, BtorNode *lower, BtorNode *upper, BtorNode *array, char *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lower)));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (upper)));
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
create_pattern_idxinc (
    Btor *btor, BtorNode *lower, BtorNode *upper, BtorNode *array, char *offset)
{
  assert (lower);
  assert (upper);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (lower)));
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (upper)));
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
create_pattern_memcopy (Btor *btor,
                        MemcopyOp *lower,
                        MemcopyOp *upper,
                        BtorNode *dst_array,
                        char *offset)
{
  assert (lower->dst_addr == upper->dst_addr);
  assert (lower->src_addr == upper->src_addr);

  BtorNode *res, *param, *ite, *read, *cond, *read_src, *add, *sub;

  param =
      btor_param_exp (btor, btor_get_exp_width (btor, lower->orig_index), 0);
  read = btor_read_exp (btor, dst_array, param);
  cond =
      create_range (btor, lower->orig_index, upper->orig_index, param, offset);
  sub      = btor_sub_exp (btor, param, lower->dst_addr);
  add      = btor_add_exp (btor, lower->src_addr, sub);
  read_src = btor_read_exp (btor, lower->src_array, add);
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

  param = exp->e[0];
  body  = btor_lambda_get_body (exp);

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

  param = exp->e[0];
  body  = btor_lambda_get_body (exp);

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

inline static bool
is_idxidx_pattern (BtorNode *index, BtorNode *value)
{
  return index == value;
}

inline static bool
is_idxinc_pattern (BtorNode *index, BtorNode *value)
{
  bool res;
  BtorNode *inc;

  inc = btor_inc_exp (BTOR_REAL_ADDR_NODE (index)->btor, index);
  res = inc == value;
  btor_release_exp (BTOR_REAL_ADDR_NODE (index)->btor, inc);
  return res;
}

inline static bool
is_memcopy_pattern (BtorNode *index, BtorNode *value)
{
  BtorNode *bvadd, *dst, *offset;

  if (BTOR_IS_INVERTED_NODE (index) || !BTOR_IS_ADD_NODE (index)
      || BTOR_IS_INVERTED_NODE (value) || !BTOR_IS_APPLY_NODE (value)
      || BTOR_IS_INVERTED_NODE (value->e[1]->e[0])
      || !BTOR_IS_ADD_NODE (value->e[1]->e[0]))
    return false;

  if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index->e[0])))
    offset = index->e[0];
  else if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index->e[1])))
    offset = index->e[1];
  else
    return false;

  bvadd = value->e[1]->e[0];
  dst   = 0;
  if (bvadd->e[0] == offset)
    dst = bvadd->e[1];
  else if (bvadd->e[1] == offset)
    dst = bvadd->e[0];

  return dst != 0;
}

static void
memcopy_pattern_get_arguments (BtorNode *index,
                               BtorNode *value,
                               BtorNode **src_array,
                               BtorNode **src,
                               BtorNode **dst,
                               BtorNode **off)
{
  assert (is_memcopy_pattern (index, value));

  BtorNode *bvadd;

  bvadd_get_base_and_offset (index, dst, off);
  bvadd      = value->e[1]->e[0];
  *src       = bvadd->e[0] == *off ? bvadd->e[1] : bvadd->e[0];
  *src_array = value->e[0];
}

inline static bool
is_equal_memcopy_pattern (BtorNode *index0,
                          BtorNode *value0,
                          BtorNode *index1,
                          BtorNode *value1)
{
  assert (is_memcopy_pattern (index0, value0));
  assert (is_memcopy_pattern (index1, value1));

  BtorNode *src_array0, *src0, *dst0, *off0, *src_array1, *src1, *dst1, *off1;

  memcopy_pattern_get_arguments (
      index0, value0, &src_array0, &src0, &dst0, &off0);
  memcopy_pattern_get_arguments (
      index1, value1, &src_array1, &src1, &dst1, &off1);
  return src0 == src1 && dst0 == dst1;
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
    BTOR_NEW (mm, indices);
    BTOR_INIT_STACK (*indices);
    b->data.asPtr = indices;
  }
  else
    indices = (BtorNodePtrStack *) b->data.asPtr;
  assert (indices);
  if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index)))
  {
    if (BTOR_IS_INVERTED_NODE (index) && !btor_const_get_invbits (index))
      btor_const_set_invbits (index,
                              btor_not_const (mm, btor_const_get_bits (index)));
  }
  else
  {
    assert (BTOR_IS_REGULAR_NODE (index));
    assert (BTOR_IS_ADD_NODE (index));
    assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index->e[0]))
            || BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index->e[1])));
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index->e[0])))
      offset = BTOR_REAL_ADDR_NODE (index->e[0]);
    else
      offset = BTOR_REAL_ADDR_NODE (index->e[1]);

    if (BTOR_IS_INVERTED_NODE (offset) && !btor_const_get_invbits (offset))
      btor_const_set_invbits (
          offset, btor_not_const (mm, btor_const_get_bits (offset)));
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
  visit_cache = btor_new_ptr_hash_table (mm, 0, 0);

  /* collect lambdas that are at the top of lambda chains */
  init_reversed_hash_table_iterator (&it, btor->lambdas);
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

      cur         = lambda;
      index_cache = btor_new_ptr_hash_table (mm, 0, 0);
      prev_index = prev_value = 0;
      while (is_write_exp (cur, &array, &index, &value))
      {
        assert (BTOR_IS_REGULAR_NODE (array));
        assert (BTOR_IS_FUN_NODE (array));

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (btor_find_in_ptr_hash_table (index_cache, index))
        {
          cur = array;
          continue;
        }

        if ((!prev_index
             || BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (prev_index)))
            && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (index)))
        {
          btor_insert_in_ptr_hash_table (index_cache, index);
          add_to_index_map (btor, map_value_index, lambda, index, value);
        }
        else if (is_memcopy_pattern (index, value)
                 && (!prev_index
                     || (is_memcopy_pattern (prev_index, prev_value)
                         && is_equal_memcopy_pattern (
                                index, value, prev_index, prev_value)
                         && (value->e[0] == prev_value->e[0]
                             || value->e[0] == array))))
        {
          /* optimization for memcopy: do not visit lambdas that are
           * only accessed via this lambda (reduces number of redundant
           * memcopy patterns) */
          if (value->e[0] == array && array->parents == 2)
            btor_insert_in_ptr_hash_table (visit_cache, array);
          btor_insert_in_ptr_hash_table (index_cache, index);
          add_to_index_map (btor, map_value_index, lambda, index, value);
        }
        else
        {
          BTOR_PUSH_STACK (mm, lambdas, array);
          break;
        }

        cur        = array;
        prev_index = index;
        prev_value = value;
      }
      if (btor_find_in_ptr_hash_table (map_value_index, lambda))
      {
        assert (!btor_find_in_ptr_hash_table (map_lambda_base, lambda));
        btor_insert_in_ptr_hash_table (map_lambda_base, lambda)->data.asPtr =
            cur;
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

    if (btor_find_in_ptr_hash_table (btor->substitutions, read)) continue;

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
             BtorCharPtrStack *offsets,
             BtorNodePtrStack *indices,
             unsigned *res_num_memset,
             unsigned *res_num_memset_inc,
             unsigned *res_range_size,
             unsigned *res_range_size_inc)
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
  unsigned cnt, lower, upper, range_size = 0, range_size_inc = 0;
  unsigned num_memset = 0, num_memset_inc = 0;
  BtorNode *n0, *n1;
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
    qsort (index_stack.start, cnt, sizeof (BtorNode *), cmp_bvconst_bits);
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
        assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (n0)));
        assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (n1)));
        b0 = BTOR_CONST_GET_BITS (n0);
        b1 = BTOR_CONST_GET_BITS (n1);
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
          if (btor_is_one_const (last_diff))
          {
            range_size += upper - lower + 1;
            num_memset++;
          }
          else
          {
            range_size_inc += upper - lower + 1;
            num_memset_inc++;
          }
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
  if (res_num_memset) *res_num_memset += num_memset;
  if (res_num_memset_inc) *res_num_memset_inc += num_memset_inc;
  if (res_range_size) *res_range_size += range_size;
  if (res_range_size_inc) *res_range_size_inc += range_size_inc;
}

unsigned
find_memcopy_ranges (Btor *btor,
                     MemcopyOpPtrStack *stack,
                     MemcopyOpPtrStack *ranges,
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
  unsigned cnt, lower, upper, range_size = 0;
  BtorMemMgr *mm;
  MemcopyOpPtrStack memcopy_stack;
  MemcopyOp *op0, *op1;

  mm            = btor->mm;
  memcopy_stack = *stack;
  cnt           = BTOR_COUNT_STACK (memcopy_stack);
  if (cnt == 0) return 0;
  if (cnt == 1)
  {
    op0 = BTOR_PEEK_STACK (memcopy_stack, 0);
    BTOR_PUSH_STACK (mm, *indices, op0->orig_index);
  }
  else
  {
    assert (cnt > 1);
    qsort (memcopy_stack.start, cnt, sizeof (MemcopyOp *), cmp_memcopy_op);
    diff = last_diff = 0;
    lower = upper = 0;
    while (upper < cnt)
    {
      in_range = false;
      diff     = 0;
      if (upper + 1 < cnt)
      {
        op0 = BTOR_PEEK_STACK (memcopy_stack, upper);
        op1 = BTOR_PEEK_STACK (memcopy_stack, upper + 1);
        b0  = BTOR_CONST_GET_BITS (op0->index);
        b1  = BTOR_CONST_GET_BITS (op1->index);
        assert (b0);
        assert (b1);
        diff = btor_sub_const (mm, b1, b0);

        if (!last_diff) last_diff = btor_copy_const (mm, diff);

        /* increment upper bound of range */
        in_range = op0->src_addr == op1->src_addr
                   && op0->dst_addr == op1->dst_addr
                   && strcmp (diff, last_diff) == 0;
        if (in_range) upper += 1;
      }

      if (!in_range)
      {
        /* push index */
        if (upper == lower)
        {
          op0 = BTOR_PEEK_STACK (memcopy_stack, lower);
          BTOR_PUSH_STACK (mm, *indices, op0->orig_index);
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
            op0 = BTOR_PEEK_STACK (memcopy_stack, lower);
            BTOR_PUSH_STACK (mm, *indices, op0->orig_index);
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
          BTOR_PUSH_STACK (mm, *ranges, BTOR_PEEK_STACK (memcopy_stack, lower));
          BTOR_PUSH_STACK (mm, *ranges, BTOR_PEEK_STACK (memcopy_stack, upper));
#ifndef NDEBUG
          num_indices += upper - lower + 1;
#endif
          range_size += upper - lower + 1;
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
  return range_size;
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
  unsigned i_range, i_rel_range, i_index, i_value, i_offset, i_rel_offset;
  unsigned num_patterns = 0, num_writes = 0;
  unsigned num_pat_memset = 0, num_pat_idxidx = 0, num_pat_idxinc = 0;
  unsigned num_pat_memcopy = 0, num_indices_memset = 0, num_indices_memcopy = 0;
  unsigned num_pat_memset_inc = 0, num_indices_memset_inc = 0;
  unsigned num_indices_idxidx = 0, num_indices_idxinc = 0;
  char *offset;
  BtorNode *subst, *base, *tmp, *array, *value, *lower, *upper;
  BtorHashTableIterator it, iit;
  BtorPtrHashTable *t, *index_value_map;
  BtorPtrHashBucket *b;
  BtorNodePtrStack ranges, indices, values, idxidx, idxinc, remidx;
  BtorNodePtrStack *stack;
  BtorCharPtrStack offsets;
  BtorMemMgr *mm;
  MemcopyOpPtrStack p_memcopy, memcopy_ranges;
  MemcopyOp *op_lower, *op_upper;

  mm = btor->mm;
  BTOR_INIT_STACK (ranges);
  BTOR_INIT_STACK (indices);
  BTOR_INIT_STACK (offsets);
  BTOR_INIT_STACK (values);
  BTOR_INIT_STACK (idxidx);
  BTOR_INIT_STACK (idxinc);
  BTOR_INIT_STACK (remidx);
  BTOR_INIT_STACK (p_memcopy);
  BTOR_INIT_STACK (memcopy_ranges);
  init_node_hash_table_iterator (&it, map_value_index);
  while (has_next_node_hash_table_iterator (&it))
  {
    t     = it.bucket->data.asPtr;
    array = next_node_hash_table_iterator (&it);
    assert (t);

    /* find memset patterns, the remaining unused indices are pushed onto
     * stack 'indices' */
    init_node_hash_table_iterator (&iit, t);
    while (has_next_node_hash_table_iterator (&iit))
    {
      stack = iit.bucket->data.asPtr;
      value = next_node_hash_table_iterator (&iit);
      assert (stack);
      find_ranges (btor,
                   stack,
                   &ranges,
                   &offsets,
                   &indices,
                   &num_pat_memset,
                   &num_pat_memset_inc,
                   &num_indices_memset,
                   &num_indices_memset_inc);
      BTOR_RELEASE_STACK (mm, *stack);
      BTOR_DELETE (mm, stack);
      BTOR_PUSH_STACK (mm, ranges, 0);
      BTOR_PUSH_STACK (mm, indices, 0);
      BTOR_PUSH_STACK (mm, values, value);
      assert (BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values) > 0
              || BTOR_COUNT_STACK (indices) - BTOR_COUNT_STACK (values) > 0);
      assert ((BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values)) % 2 == 0);
      assert ((BTOR_COUNT_STACK (ranges) - BTOR_COUNT_STACK (values)) / 2
              == BTOR_COUNT_STACK (offsets));
    }

    /* choose base array for patterns/writes:
     *  1) write chains: base array of the write chains
     *  2) top eqs: a new UF symbol */
    if ((b = btor_find_in_ptr_hash_table (map_lambda_base, array)))
    {
      assert (BTOR_IS_LAMBDA_NODE (array));
      b = btor_find_in_ptr_hash_table (map_lambda_base, array);
      assert (b);
      subst     = btor_copy_exp (btor, b->data.asPtr);
      is_top_eq = false;
    }
    else
    {
      assert (BTOR_IS_UF_ARRAY_NODE (array));
      subst     = btor_uf_exp (btor, array->sort_id, 0);
      is_top_eq = true;
    }

    index_value_map = btor_new_ptr_hash_table (mm, 0, 0);
    base            = subst;
    i_range = i_rel_range = i_index = i_offset = i_rel_offset = 0;
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
        assert (i_offset < BTOR_COUNT_STACK (offsets));
        offset = BTOR_PEEK_STACK (offsets, i_offset);
        tmp = create_pattern_memset (btor, lower, upper, value, subst, offset);
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_delete_const (mm, offset);
        i_offset++;
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
        assert (!btor_find_in_ptr_hash_table (index_value_map, lower));
        /* save index value pairs for later */
        btor_insert_in_ptr_hash_table (index_value_map, lower)->data.asPtr =
            value;

        /* pattern 1: index -> index */
        if (is_idxidx_pattern (lower, value))
          BTOR_PUSH_STACK (mm, idxidx, lower);
        /* pattern 2: index -> index + 1 */
        else if (is_idxinc_pattern (lower, value))
          BTOR_PUSH_STACK (mm, idxinc, lower);
        /* pattern 3: memcopy pattern */
        else if (is_memcopy_pattern (lower, value))
          BTOR_PUSH_STACK (mm, p_memcopy, new_memcopy_op (mm, lower, value));
        else /* no pattern found */
          BTOR_PUSH_STACK (mm, remidx, lower);
      }
    }

    /* pattern: index = index */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (offsets);
    find_ranges (btor,
                 &idxidx,
                 &ranges,
                 &offsets,
                 &remidx,
                 &num_pat_idxidx,
                 &num_pat_idxidx,
                 &num_indices_idxidx,
                 &num_indices_idxinc);
    if (!BTOR_EMPTY_STACK (ranges))
    {
      assert (BTOR_COUNT_STACK (ranges) % 2 == 0);
      for (i_range = 0, i_offset = 0; i_range < BTOR_COUNT_STACK (ranges) - 1;
           i_range += 2, i_offset++)
      {
        lower = BTOR_PEEK_STACK (ranges, i_range);
        upper = BTOR_PEEK_STACK (ranges, i_range + 1);
        assert (i_offset < BTOR_COUNT_STACK (offsets));
        offset = BTOR_PEEK_STACK (offsets, i_offset);
        tmp    = create_pattern_idxidx (btor, lower, upper, subst, offset);
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_delete_const (mm, offset);
        i_offset++;
      }
    }

    /* pattern: index = index + 1 */
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (offsets);
    find_ranges (btor,
                 &idxinc,
                 &ranges,
                 &offsets,
                 &remidx,
                 &num_pat_idxinc,
                 &num_pat_idxinc,
                 &num_indices_idxinc,
                 &num_indices_idxinc);
    if (!BTOR_EMPTY_STACK (ranges))
    {
      assert (BTOR_COUNT_STACK (ranges) % 2 == 0);
      for (i_range = 0, i_offset = 0; i_range < BTOR_COUNT_STACK (ranges) - 1;
           i_range += 2, i_offset++)
      {
        lower = BTOR_PEEK_STACK (ranges, i_range);
        upper = BTOR_PEEK_STACK (ranges, i_range + 1);
        assert (i_offset < BTOR_COUNT_STACK (offsets));
        offset = BTOR_PEEK_STACK (offsets, i_offset);
        tmp    = create_pattern_idxinc (btor, lower, upper, subst, offset);
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_delete_const (mm, offset);
        i_offset++;
      }
    }

    /* pattern: memcopy */
    BTOR_RESET_STACK (offsets);
    num_indices_memcopy += find_memcopy_ranges (
        btor, &p_memcopy, &memcopy_ranges, &offsets, &remidx);
    if (!BTOR_EMPTY_STACK (memcopy_ranges))
    {
      assert (base == subst);
      assert (BTOR_COUNT_STACK (memcopy_ranges) % 2 == 0);
      for (i_range = 0, i_offset = 0;
           i_range < BTOR_COUNT_STACK (memcopy_ranges) - 1;
           i_range += 2, i_offset++)
      {
        op_lower = BTOR_PEEK_STACK (memcopy_ranges, i_range);
        op_upper = BTOR_PEEK_STACK (memcopy_ranges, i_range + 1);
        assert (i_offset < BTOR_COUNT_STACK (offsets));
        offset = BTOR_PEEK_STACK (offsets, i_offset);
        tmp = create_pattern_memcopy (btor, op_lower, op_upper, subst, offset);
        btor_release_exp (btor, subst);
        subst = tmp;
        btor_delete_const (mm, offset);
        i_offset++;
        num_pat_memcopy++;
      }
    }
    while (!BTOR_EMPTY_STACK (p_memcopy))
      free_memcopy_op (mm, BTOR_POP_STACK (p_memcopy));

    num_patterns =
        num_pat_memset + num_pat_idxidx + num_pat_idxinc + num_pat_memcopy;

    /* we can skip creating writes if we did not find any pattern in a write
     * chain, and thus can leave the write chain as-is.
     * for the top equality case we always have to create writes since we
     * convert top level equalities to writes. */
    if (is_top_eq || num_patterns > 0)
    {
      /* no pattern found for indices in 'remidx'. create writes */
      for (i_index = 0; i_index < BTOR_COUNT_STACK (remidx); i_index++)
      {
        lower = BTOR_PEEK_STACK (remidx, i_index);
        b     = btor_find_in_ptr_hash_table (index_value_map, lower);
        assert (b);
        value = b->data.asPtr;
        tmp   = btor_write_exp (btor, subst, lower, value);
        btor_release_exp (btor, subst);
        subst = tmp;
        num_writes++;
      }
    }

    assert ((is_top_eq || num_patterns > 0) || base == subst);
    if (base != subst) btor_insert_substitution (btor, array, subst, 0);
    btor_release_exp (btor, subst);

    btor_delete_ptr_hash_table (index_value_map);
    btor_delete_ptr_hash_table (t);
    BTOR_RESET_STACK (ranges);
    BTOR_RESET_STACK (indices);
    BTOR_RESET_STACK (values);
    BTOR_RESET_STACK (offsets);
    BTOR_RESET_STACK (idxidx);
    BTOR_RESET_STACK (idxinc);
    BTOR_RESET_STACK (remidx);
    BTOR_RESET_STACK (memcopy_ranges);
    BTOR_RESET_STACK (p_memcopy);
  }
  BTOR_RELEASE_STACK (mm, idxidx);
  BTOR_RELEASE_STACK (mm, idxinc);
  BTOR_RELEASE_STACK (mm, remidx);
  BTOR_RELEASE_STACK (mm, ranges);
  BTOR_RELEASE_STACK (mm, indices);
  BTOR_RELEASE_STACK (mm, offsets);
  BTOR_RELEASE_STACK (mm, values);
  BTOR_RELEASE_STACK (mm, memcopy_ranges);
  BTOR_RELEASE_STACK (mm, p_memcopy);

  BTOR_MSG (btor->msg,
            1,
            "extracted %u memsets (%u), "
            "%u memset_inc (%u), "
            "%u idxidx (%u), "
            "%u idxinc (%u), "
            "%u memcopies (%u)",
            num_pat_memset,
            num_indices_memset,
            num_pat_memset_inc,
            num_indices_memset_inc,
            num_pat_idxidx,
            num_indices_idxidx,
            num_pat_idxinc,
            num_indices_idxinc,
            num_pat_memcopy,
            num_indices_memcopy);
  return num_pat_memset + num_pat_idxidx + num_pat_idxinc + num_pat_memcopy;
}

void
btor_extract_lambdas (Btor *btor)
{
  assert (btor);

  unsigned num_lambdas;
  double start, delta;
  BtorPtrHashTable *map_value_index, *map_lambda_base;
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
  num_lambdas = extract_lambdas (btor, map_value_index, map_lambda_base);
  btor_delete_ptr_hash_table (map_lambda_base);
  btor_delete_ptr_hash_table (map_value_index);

  btor_substitute_and_rebuild (btor, btor->substitutions, 0);
  btor_delete_substitutions (btor);
  delta = btor_time_stamp () - start;
  BTOR_MSG (
      btor->msg, 1, "extracted %u lambdas in %.3f seconds", num_lambdas, delta);
}
