/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorexp.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormisc.h"
#include "btorrewrite.h"
#include "btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTOR_ABORT_NODE(cond, msg)                  \
  do                                                \
  {                                                 \
    if (cond)                                       \
    {                                               \
      printf ("[btorexp] %s: %s\n", __func__, msg); \
      fflush (stdout);                              \
      exit (BTOR_ERR_EXIT);                         \
    }                                               \
  } while (0)

#define BTOR_UNIQUE_TABLE_LIMIT 30

#define BTOR_NODE_UNIQUE_TABLE_PRIME 2000000137u

#define BTOR_FULL_UNIQUE_TABLE(table)   \
  ((table).num_elements >= (table).size \
   && btor_log_2_util ((table).size) < BTOR_UNIQUE_TABLE_LIMIT)

//#define NBTOR_SORT_BIN_COMMUTATIVE

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

int
btor_precond_slice_exp_dbg (const Btor *btor,
                            const BtorNode *exp,
                            int upper,
                            int lower)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_NODE (exp)->len);
  assert (BTOR_REAL_ADDR_NODE (exp)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  return 1;
}

static int
btor_precond_ext_exp_dbg (const Btor *btor, const BtorNode *exp, int len)
{
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));
  assert (len >= 0);
  return 1;
}

int
btor_precond_regular_unary_bv_exp_dbg (const Btor *btor, const BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  return 1;
}

// TODO: add proper sort check
int
btor_precond_eq_exp_dbg (const Btor *btor,
                         const BtorNode *e0,
                         const BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;

  assert (btor);
  assert (e0);
  assert (e1);

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  assert (real_e0);
  assert (real_e1);
  assert (real_e0->btor == btor);
  assert (real_e1->btor == btor);
  assert (!real_e0->simplified);
  assert (!real_e1->simplified);
  assert (btor_is_equal_sort ((Btor *) btor, (BtorNode *) e0, (BtorNode *) e1));
  assert (!BTOR_IS_FUN_NODE (real_e0)
          || (BTOR_IS_REGULAR_NODE (e0) && BTOR_IS_REGULAR_NODE (e1)));
  return 1;
}

int
btor_precond_concat_exp_dbg (const Btor *btor,
                             const BtorNode *e0,
                             const BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (e1)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (e0)->len
          <= INT_MAX - BTOR_REAL_ADDR_NODE (e1)->len);
  assert (BTOR_REAL_ADDR_NODE (e0)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e1)->btor == btor);
  return 1;
}

int
btor_precond_shift_exp_dbg (const Btor *btor,
                            const BtorNode *e0,
                            const BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->len > 1);
  assert (BTOR_REAL_ADDR_NODE (e1)->len > 0);
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_NODE (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_NODE (e0)->len)
          == BTOR_REAL_ADDR_NODE (e1)->len);
  assert (BTOR_REAL_ADDR_NODE (e0)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e1)->btor == btor);
  return 1;
}

int
btor_precond_regular_binary_bv_exp_dbg (const Btor *btor,
                                        const BtorNode *e0,
                                        const BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->len == BTOR_REAL_ADDR_NODE (e1)->len);
  assert (BTOR_REAL_ADDR_NODE (e0)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (e0)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e1)->btor == btor);
  return 1;
}

int
btor_precond_read_exp_dbg (const Btor *btor,
                           const BtorNode *e_array,
                           const BtorNode *e_index)
{
  assert (btor);
  assert (e_array);
  assert (e_index);
  assert (BTOR_IS_REGULAR_NODE (e_array));
  assert (BTOR_IS_FUN_NODE (e_array));
  assert (!e_array->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_index)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_index)));
  assert (BTOR_REAL_ADDR_NODE (e_index)->len > 0);
  assert (e_array->len > 0);
  assert (BTOR_IS_LAMBDA_NODE (e_array)
          || BTOR_ARRAY_INDEX_LEN (e_array)
                 == BTOR_REAL_ADDR_NODE (e_index)->len);
  assert (BTOR_REAL_ADDR_NODE (e_array)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e_index)->btor == btor);
  return 1;
}

int
btor_precond_write_exp_dbg (const Btor *btor,
                            const BtorNode *e_array,
                            const BtorNode *e_index,
                            const BtorNode *e_value)
{
  assert (btor);
  assert (e_array);
  assert (e_index);
  assert (e_value);
  assert (BTOR_IS_REGULAR_NODE (e_array));
  assert (BTOR_IS_FUN_NODE (e_array));
  assert (!e_array->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_index)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_value)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_index)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_value)));
  assert (BTOR_ARRAY_INDEX_LEN (e_array) == BTOR_REAL_ADDR_NODE (e_index)->len);
  assert (BTOR_REAL_ADDR_NODE (e_index)->len > 0);
  assert (e_array->len == BTOR_REAL_ADDR_NODE (e_value)->len);
  assert (BTOR_REAL_ADDR_NODE (e_value)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (e_array)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e_index)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e_value)->btor == btor);
  return 1;
}

int
btor_precond_cond_exp_dbg (const Btor *btor,
                           const BtorNode *e_cond,
                           const BtorNode *e_if,
                           const BtorNode *e_else)
{
  assert (btor);
  assert (e_cond);
  assert (e_if);
  assert (e_else);
  assert (!BTOR_REAL_ADDR_NODE (e_cond)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_cond)));
  assert (BTOR_REAL_ADDR_NODE (e_cond)->len == 1);

  BtorNode *real_e_if, *real_e_else;

  real_e_if   = BTOR_REAL_ADDR_NODE (e_if);
  real_e_else = BTOR_REAL_ADDR_NODE (e_else);

  assert (!real_e_if->simplified);
  assert (!real_e_else->simplified);
  assert (!BTOR_IS_FUN_NODE (real_e_if));
  assert (!BTOR_IS_FUN_NODE (real_e_else));

  assert (real_e_if->len == real_e_else->len);
  assert (real_e_if->len > 0);

  assert (BTOR_REAL_ADDR_NODE (e_cond)->btor == btor);
  assert (real_e_if->btor == btor);
  assert (real_e_else->btor == btor);
  return 1;
}

int
btor_precond_apply_exp_dbg (const Btor *btor,
                            const BtorNode *fun,
                            const BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_REGULAR_NODE (args));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (BTOR_IS_ARGS_NODE (args));

  // TODO: sort check
  assert (!BTOR_IS_UF_NODE (fun)
          || ((BtorArgsNode *) args)->num_args
                 == ((BtorUFNode *) fun)->num_params);
  assert (!BTOR_IS_LAMBDA_NODE (fun)
          || ((BtorArgsNode *) args)->num_args
                 == ((BtorLambdaNode *) fun)->num_params);

  return 1;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

void
btor_set_btor_id (Btor *btor, BtorNode *exp, int id)
{
  assert (btor);
  assert (exp);
  assert (id);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  assert (btor_is_bv_var_exp (btor, exp)
          || btor_is_uf_array_var_exp (btor, exp));

  (void) btor;
  BtorNode *real_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (BTOR_IS_BV_VAR_NODE (real_exp))
    ((BtorBVVarNode *) real_exp)->btor_id = id;
  else if (BTOR_IS_UF_NODE (real_exp))
    ((BtorUFNode *) real_exp)->btor_id = id;
}

/*------------------------------------------------------------------------*/

/* Creates an expression pair which can be compared with
 * other expression pairs via the function
 * 'compare_exp_pair'
 */
BtorNodePair *
new_exp_pair (Btor *btor, BtorNode *exp1, BtorNode *exp2)
{
  assert (btor);
  assert (exp1);
  assert (exp2);
  assert (btor == BTOR_REAL_ADDR_NODE (exp1)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (exp2)->btor);

  int id1, id2;
  BtorNodePair *result;

  BTOR_NEW (btor->mm, result);
  id1 = BTOR_GET_ID_NODE (exp1);
  id2 = BTOR_GET_ID_NODE (exp2);
  if (id2 < id1)
  {
    result->exp1 = btor_copy_exp (btor, exp2);
    result->exp2 = btor_copy_exp (btor, exp1);
  }
  else
  {
    result->exp1 = btor_copy_exp (btor, exp1);
    result->exp2 = btor_copy_exp (btor, exp2);
  }
  return result;
}

void
delete_exp_pair (Btor *btor, BtorNodePair *pair)
{
  assert (btor);
  assert (pair);
  btor_release_exp (btor, pair->exp1);
  btor_release_exp (btor, pair->exp2);
  BTOR_DELETE (btor->mm, pair);
}

unsigned int
hash_exp_pair (BtorNodePair *pair)
{
  unsigned int result;
  assert (pair);
  result = (unsigned int) BTOR_REAL_ADDR_NODE (pair->exp1)->id;
  result += (unsigned int) BTOR_REAL_ADDR_NODE (pair->exp2)->id;
  result *= 7334147u;
  return result;
}

int
compare_exp_pair (BtorNodePair *pair1, BtorNodePair *pair2)
{
  assert (pair1);
  assert (pair2);

  int result;

  result = BTOR_GET_ID_NODE (pair1->exp1);
  result -= BTOR_GET_ID_NODE (pair2->exp1);
  if (result != 0) return result;
  result = BTOR_GET_ID_NODE (pair1->exp2);
  result -= BTOR_GET_ID_NODE (pair2->exp2);
  return result;
}

/*------------------------------------------------------------------------*/

static void
inc_exp_ref_counter (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *real_exp;

  (void) btor;
  real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_ABORT_NODE (real_exp->refs == INT_MAX,
                   "Node reference counter overflow");
  real_exp->refs++;
}

BtorNode *
btor_copy_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  inc_exp_ref_counter (btor, exp);
  return exp;
}

/* Disconnects a child from its parent and updates its parent list */
static void
disconnect_child_exp (Btor *btor, BtorNode *parent, int pos)
{
  assert (btor);
  assert (parent);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (btor == parent->btor);
  assert (!BTOR_IS_BV_CONST_NODE (parent));
  assert (!BTOR_IS_BV_VAR_NODE (parent));
  assert (!BTOR_IS_UF_NODE (parent));
  assert (pos >= 0);
  assert (pos <= 2);

  (void) btor;
  BtorNode *first_parent, *last_parent;
  BtorNode *real_child, *tagged_parent;

  tagged_parent = BTOR_TAG_NODE (parent, pos);
  real_child    = BTOR_REAL_ADDR_NODE (parent->e[pos]);
  real_child->parents--;
  first_parent = real_child->first_parent;
  last_parent  = real_child->last_parent;
  assert (first_parent);
  assert (last_parent);

  /* only one parent? */
  if (first_parent == tagged_parent && first_parent == last_parent)
  {
    assert (!parent->next_parent[pos]);
    assert (!parent->prev_parent[pos]);
    real_child->first_parent = 0;
    real_child->last_parent  = 0;
  }
  /* is parent first parent in the list? */
  else if (first_parent == tagged_parent)
  {
    assert (parent->next_parent[pos]);
    assert (!parent->prev_parent[pos]);
    real_child->first_parent                    = parent->next_parent[pos];
    BTOR_PREV_PARENT (real_child->first_parent) = 0;
  }
  /* is parent last parent in the list? */
  else if (last_parent == tagged_parent)
  {
    assert (!parent->next_parent[pos]);
    assert (parent->prev_parent[pos]);
    real_child->last_parent                    = parent->prev_parent[pos];
    BTOR_NEXT_PARENT (real_child->last_parent) = 0;
  }
  /* detach parent from list */
  else
  {
    assert (parent->next_parent[pos]);
    assert (parent->prev_parent[pos]);
    BTOR_PREV_PARENT (parent->next_parent[pos]) = parent->prev_parent[pos];
    BTOR_NEXT_PARENT (parent->prev_parent[pos]) = parent->next_parent[pos];
  }
  parent->next_parent[pos] = 0;
  parent->prev_parent[pos] = 0;
  parent->e[pos]           = 0;
}

static unsigned int
hash_lambda_exp (Btor *btor, BtorNode *param, BtorNode *body, int *curried)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  int i;
  unsigned int hash = 0;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack visit;
  BtorPtrHashTable *marked;

  if (curried) *curried = 0;

  if (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (body)))
  {
    *curried = 1;
    return BTOR_GET_ID_NODE (param) + BTOR_GET_ID_NODE (body);
  }

  marked = btor_new_ptr_hash_table (btor->mm, 0, 0);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (btor->mm, visit, body);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_find_in_ptr_hash_table (marked, real_cur)) continue;

    // TODO (ma): hashing arbitrarily deep lambdas might be too expensive
    if (marked->count > 10)
    {
      hash = BTOR_GET_ID_NODE (param) + BTOR_GET_ID_NODE (body);
      break;
    }

    if (!real_cur->parameterized)
    {
      hash += BTOR_GET_ID_NODE (cur);
      continue;
    }

    /* no support for curried lambdas yet */
    if (BTOR_IS_PARAM_NODE (real_cur) && real_cur != param)
    {
      hash = BTOR_GET_ID_NODE (param) + BTOR_GET_ID_NODE (body);
      if (curried) *curried = 1;
      break;
    }

    (void) btor_insert_in_ptr_hash_table (marked, real_cur);
    hash += BTOR_IS_INVERTED_NODE (cur) ? -real_cur->kind : real_cur->kind;
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (btor->mm, visit, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (btor->mm, visit);
  btor_delete_ptr_hash_table (marked);
  return hash;
}

static inline unsigned int
hash_exp (int arity, BtorNode **e)
{
  int i;
  unsigned int hash = 0;
  for (i = 0; i < arity; i++) hash += (unsigned) BTOR_REAL_ADDR_NODE (e[i])->id;
  return hash;
}

/* Computes hash value of expresssion by children ids */
static unsigned int
compute_hash_exp (BtorNode *exp, int table_size)
{
  assert (exp);
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!BTOR_IS_BV_VAR_NODE (exp));
  assert (!BTOR_IS_UF_NODE (exp));

  int i;
  unsigned int hash = 0;

  if (BTOR_IS_BV_CONST_NODE (exp)) hash = btor_hash_str ((void *) exp->bits);
  /* hash for lambdas is computed once during creation. afterwards, we always
   * have to use the saved hash value since hashing of lambdas requires all
   * parameterized nodes and their inputs (cf. hash_lambda_exp), which may
   * change at some point. */
  else if (BTOR_IS_LAMBDA_NODE (exp))
    hash = btor_find_in_ptr_hash_table (exp->btor->lambdas, exp)->data.asInt;
  else if (exp)
  {
    hash = hash_exp (exp->arity, exp->e);
    if (exp->kind == BTOR_SLICE_NODE)
      hash += (unsigned int) exp->upper + (unsigned int) exp->lower;
  }
  hash = (hash * BTOR_NODE_UNIQUE_TABLE_PRIME) & (table_size - 1);
  return hash;
}

static void
remove_param_parameterized (Btor *btor, BtorNode *exp, BtorNode *param)
{
  assert (btor);
  assert (exp);
  assert (param);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->parameterized, exp);
  assert (b);
  t = (BtorPtrHashTable *) b->data.asPtr;
  assert (t->count > 0);
  assert (btor_find_in_ptr_hash_table (t, param));
  btor_remove_from_ptr_hash_table (t, param, 0, 0);
  btor_release_exp (btor, param);

  /* remove hash table if it is empty */
  if (t->count == 0)
  {
    btor_remove_from_ptr_hash_table (btor->parameterized, exp, 0, 0);
    btor_delete_ptr_hash_table (t);
  }
}

static void
remove_parameterized (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;

  b = btor_find_in_ptr_hash_table (btor->parameterized, exp);
  if (!b) return;

  t = (BtorPtrHashTable *) b->data.asPtr;

  /* release params */
  init_node_hash_table_iterator (&it, t);
  while (has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (t);

  btor_remove_from_ptr_hash_table (btor->parameterized, exp, 0, 0);
}

static int
is_parameterized (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;

  b = btor_find_in_ptr_hash_table (btor->parameterized, exp);
  if (b)
  {
    t = (BtorPtrHashTable *) b->data.asPtr;
    return t->count > 0;
  }

  return 0;
}

static void
update_parameterized (Btor *btor, BtorNode *parent, BtorNode *child)
{
  assert (btor);
  assert (parent);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (child);
  assert (BTOR_REAL_ADDR_NODE (child)->parameterized);

  BtorNode *param;
  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;
  BtorParameterizedIterator it;

  child = BTOR_REAL_ADDR_NODE (child);

  b = btor_find_in_ptr_hash_table (btor->parameterized, parent);
  if (b)
  {
    assert (b->data.asPtr);
    t = (BtorPtrHashTable *) b->data.asPtr;
  }
  else
  {
    t = btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    btor_insert_in_ptr_hash_table (btor->parameterized, parent)->data.asPtr = t;
  }

  if (BTOR_IS_PARAM_NODE (child))
  {
    if (!btor_find_in_ptr_hash_table (t, child))
      btor_insert_in_ptr_hash_table (t, btor_copy_exp (btor, child));
  }
  else
  {
    init_parameterized_iterator (btor, &it, child);
    while (has_next_parameterized_iterator (&it))
    {
      param = next_parameterized_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (param));
      assert (BTOR_IS_PARAM_NODE (param));
      if (!btor_find_in_ptr_hash_table (t, param))
        btor_insert_in_ptr_hash_table (t, btor_copy_exp (btor, param));
      /* cleanup */
      else if (param->refs == 1)
      {
        btor_remove_from_ptr_hash_table (t, param, 0, 0);
        btor_release_exp (btor, param);
      }
    }
  }
}

static void
remove_from_nodes_unique_table_exp (Btor *btor, BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  unsigned int hash;
  BtorNode *cur, *prev;

  if (!exp->unique) return;

  assert (btor);
  assert (btor->nodes_unique_table.num_elements > 0);

  hash = compute_hash_exp (exp, btor->nodes_unique_table.size);
  prev = 0;
  cur  = btor->nodes_unique_table.chains[hash];

  while (cur != exp)
  {
    assert (cur);
    assert (BTOR_IS_REGULAR_NODE (cur));
    prev = cur;
    cur  = cur->next;
  }
  assert (cur);
  if (!prev)
    btor->nodes_unique_table.chains[hash] = cur->next;
  else
    prev->next = cur->next;

  btor->nodes_unique_table.num_elements--;

  exp->unique = 0; /* NOTE: this is not debugging code ! */
  exp->next   = 0;
}

static void
remove_from_hash_tables (Btor *btor, BtorNode *exp, int keep_symbol)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!BTOR_IS_INVALID_NODE (exp));

  BtorPtrHashData data;

  switch (exp->kind)
  {
    case BTOR_BV_VAR_NODE:
      btor_remove_from_ptr_hash_table (btor->bv_vars, exp, 0, 0);
      break;
    case BTOR_LAMBDA_NODE:
      btor_remove_from_ptr_hash_table (btor->lambdas, exp, 0, 0);
      break;
    case BTOR_UF_NODE:
      btor_remove_from_ptr_hash_table (btor->ufs, exp, 0, 0);
      break;
    default: break;
  }

  if (!keep_symbol && btor_find_in_ptr_hash_table (btor->node2symbol, exp))
  {
    btor_remove_from_ptr_hash_table (btor->node2symbol, exp, 0, &data);
    if (data.asStr[0] != 0)
    {
      btor_remove_from_ptr_hash_table (btor->symbols, data.asStr, 0, 0);
      btor_freestr (btor->mm, data.asStr);
    }
  }
  if (btor->searched_applies
      && btor_find_in_ptr_hash_table (btor->searched_applies, exp))
    btor_remove_from_ptr_hash_table (btor->searched_applies, exp, 0, 0);

  remove_parameterized (btor, exp);
}

/* Disconnect children of expression in parent list and if applicable from
 * unique table.  Do not touch local data, nor any reference counts.  The
 * kind of the expression becomes 'BTOR_DISCONNECTED_NODE' in debugging mode.
 *
 * Actually we have the sequence
 *
 *   UNIQUE -> !UNIQUE -> ERASED -> DISCONNECTED -> INVALID
 *
 * after a unique or non uninque expression is allocated until it is
 * deallocated.  We also have loop back from DISCONNECTED to !UNIQUE
 * if an expression is rewritten and reused as PROXY.
 */
static void
disconnect_children_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!BTOR_IS_INVALID_NODE (exp));
  assert (!exp->unique);
  assert (exp->erased);
  assert (!exp->disconnected);

  int i;

  for (i = 0; i < exp->arity; i++) disconnect_child_exp (btor, exp, i);
  exp->disconnected = 1;
}

/* Delete local data of expression.
 *
 * Virtual reads and simplified expressions have to be handled by the
 * calling function, e.g. 'btor_release_exp', to avoid recursion.
 *
 * We use this function to update operator stats
 */
static void
erase_local_data_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_NODE (exp));

  assert (!exp->unique);
  assert (!exp->erased);
  assert (!exp->disconnected);
  assert (!BTOR_IS_INVALID_NODE (exp));

  BtorMemMgr *mm;
  BtorPtrHashTable *synth_apps;
  BtorHashTableIterator it;

  mm = btor->mm;
  //  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  switch (exp->kind)
  {
    case BTOR_BV_CONST_NODE:
      btor_freestr (mm, exp->bits);
      if (exp->invbits) btor_freestr (mm, exp->invbits);
      exp->bits = exp->invbits = 0;
      break;
    case BTOR_LAMBDA_NODE:
      synth_apps = ((BtorLambdaNode *) exp)->synth_apps;
      if (synth_apps)
      {
        init_node_hash_table_iterator (&it, synth_apps);
        while (has_next_node_hash_table_iterator (&it))
          btor_release_exp (btor, next_node_hash_table_iterator (&it));
        btor_delete_ptr_hash_table (synth_apps);
        ((BtorLambdaNode *) exp)->synth_apps = 0;
      }
      goto ERASE_LOCAL_ARRAY_RHO;
    case BTOR_UF_NODE:
      btor_release_sort (&btor->sorts_unique_table, ((BtorUFNode *) exp)->sort);
      ((BtorUFNode *) exp)->sort = 0;
    ERASE_LOCAL_ARRAY_RHO:
      if (exp->rho)
      {
        btor_delete_ptr_hash_table (exp->rho);
        exp->rho = 0;
      }
      break;
    case BTOR_FEQ_NODE:
      if (exp->vreads)
      {
        BTOR_DELETE (mm, exp->vreads);
        exp->vreads = 0;
      }
      break;
    default: break;
  }

  if (exp->av)
  {
    btor_release_delete_aigvec (btor->avmgr, exp->av);
    exp->av = 0;
  }
  exp->erased = 1;
}

#ifndef NDEBUG
static int
is_valid_kind (BtorNodeKind kind)
{
  return 0 <= (int) kind && kind < BTOR_NUM_OPS_NODE;
}
#endif

static void
set_kind (Btor *btor, BtorNode *exp, BtorNodeKind kind)
{
  assert (is_valid_kind (kind));
  assert (is_valid_kind (exp->kind));

  assert (!BTOR_INVALID_NODE);

  if (exp->kind)
  {
    assert (btor->ops[exp->kind].cur > 0);
    btor->ops[exp->kind].cur--;
  }

  if (kind)
  {
    btor->ops[kind].cur++;
    assert (btor->ops[kind].cur > 0);
    if (btor->ops[kind].cur > btor->ops[kind].max)
      btor->ops[kind].max = btor->ops[kind].cur;
  }

  exp->kind = kind;
}

/* Delete expression from memory.
 */
static void
really_deallocate_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor == exp->btor);
  assert (!exp->unique);
  assert (exp->disconnected);
  assert (exp->erased);
  assert (exp->id);
  assert (BTOR_PEEK_STACK (btor->nodes_id_table, exp->id) == exp);
  BTOR_POKE_STACK (btor->nodes_id_table, exp->id, 0);

  BtorMemMgr *mm;

  mm = btor->mm;

  set_kind (btor, exp, BTOR_INVALID_NODE);

  if (exp->bits) btor_freestr (btor->mm, exp->bits);
  if (exp->invbits) btor_freestr (btor->mm, exp->invbits);

  btor_free (mm, exp, exp->bytes);
}

static void
recursively_release_exp (Btor *btor, BtorNode *root)
{
  assert (btor);
  assert (root);
  assert (BTOR_IS_REGULAR_NODE (root));
  assert (root->refs == 1);

  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorNode *cur;
  int i;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  cur = root;
  goto RECURSIVELY_RELEASE_NODE_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

    if (cur->refs > 1)
      cur->refs--;
    else
    {
    RECURSIVELY_RELEASE_NODE_ENTER_WITHOUT_POP:
      assert (cur->refs == 1);
      assert (!cur->ext_refs || cur->ext_refs == 1);
      assert (cur->parents == 0);

      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);

      if (cur->simplified)
      {
        BTOR_PUSH_STACK (mm, stack, cur->simplified);
        cur->simplified = 0;
      }

      if (BTOR_IS_FEQ_NODE (cur) && cur->vreads)
      {
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp2);
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp1);
      }

      remove_from_nodes_unique_table_exp (btor, cur);
      erase_local_data_exp (btor, cur);

      /* It is safe to access the children here, since they are pushed
       * on the stack and will be released later if necessary.
       */
      remove_from_hash_tables (btor, cur, 0);
      disconnect_children_exp (btor, cur);
      really_deallocate_exp (btor, cur);
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
}

void
btor_release_exp (Btor *btor, BtorNode *root)
{
  assert (btor);
  assert (root);
  assert (btor == BTOR_REAL_ADDR_NODE (root)->btor);

  root = BTOR_REAL_ADDR_NODE (root);

  assert (root->refs > 0);

  if (root->refs > 1)
    root->refs--;
  else
    recursively_release_exp (btor, root);
}

void
btor_set_to_proxy_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor == exp->btor);
  assert (exp->simplified);

  int i;
  BtorNode *e[3];

  if (exp->kind == BTOR_FEQ_NODE && exp->vreads)
  {
    btor_release_exp (btor, exp->vreads->exp2);
    btor_release_exp (btor, exp->vreads->exp1);
    BTOR_DELETE (btor->mm, exp->vreads);
    exp->vreads = 0;
  }

  remove_from_nodes_unique_table_exp (btor, exp);
  /* also updates op stats */
  erase_local_data_exp (btor, exp);
  assert (exp->arity <= 3);
  BTOR_CLR (e);
  for (i = 0; i < exp->arity; i++) e[i] = exp->e[i];
  remove_from_hash_tables (btor, exp, 1);
  disconnect_children_exp (btor, exp);

  for (i = 0; i < exp->arity; i++) btor_release_exp (btor, e[i]);

  set_kind (btor, exp, BTOR_PROXY_NODE);

  exp->disconnected  = 0;
  exp->erased        = 0;
  exp->arity         = 0;
  exp->parameterized = 0;
}

/* Connects child to its parent and updates list of parent pointers.
 * Expressions are inserted at the beginning of the regular parent list
 */
static void
connect_child_exp (Btor *btor, BtorNode *parent, BtorNode *child, int pos)
{
  assert (btor);
  assert (parent);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (btor == parent->btor);
  assert (child);
  assert (btor == BTOR_REAL_ADDR_NODE (child)->btor);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (btor_simplify_exp (btor, child) == child);
  assert (!BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (child))
          || BTOR_IS_ARGS_NODE (parent) || BTOR_IS_APPLY_NODE (parent));

  (void) btor;
  int tag, insert_beginning = 1;
  BtorNode *real_child, *first_parent, *last_parent, *tagged_parent;

  /* set parent parameterized if child is parameterized */
  if (!BTOR_IS_LAMBDA_NODE (parent)
      && BTOR_REAL_ADDR_NODE (child)->parameterized)
    parent->parameterized = 1;

  if (BTOR_REAL_ADDR_NODE (child)->lambda_below) parent->lambda_below = 1;

  if (BTOR_REAL_ADDR_NODE (child)->apply_below) parent->apply_below = 1;

  if (BTOR_REAL_ADDR_NODE (child)->parameterized)
    update_parameterized (btor, parent, child);

  BTOR_REAL_ADDR_NODE (child)->parents++;
  inc_exp_ref_counter (btor, child);

  if (BTOR_IS_APPLY_NODE (parent)) insert_beginning = 0;

  real_child     = BTOR_REAL_ADDR_NODE (child);
  parent->e[pos] = child;
  tagged_parent  = BTOR_TAG_NODE (parent, pos);

  assert (!parent->prev_parent[pos]);
  assert (!parent->next_parent[pos]);

  /* no parent so far? */
  if (!real_child->first_parent)
  {
    assert (!real_child->last_parent);
    real_child->first_parent = tagged_parent;
    real_child->last_parent  = tagged_parent;
  }
  /* add parent at the beginning of the list */
  else if (insert_beginning)
  {
    first_parent = real_child->first_parent;
    assert (first_parent);
    parent->next_parent[pos] = first_parent;
    tag                      = BTOR_GET_TAG_NODE (first_parent);
    BTOR_REAL_ADDR_NODE (first_parent)->prev_parent[tag] = tagged_parent;
    real_child->first_parent                             = tagged_parent;
  }
  /* add parent at the end of the list */
  else
  {
    last_parent = real_child->last_parent;
    assert (last_parent);
    parent->prev_parent[pos] = last_parent;
    tag                      = BTOR_GET_TAG_NODE (last_parent);
    BTOR_REAL_ADDR_NODE (last_parent)->next_parent[tag] = tagged_parent;
    real_child->last_parent                             = tagged_parent;
  }
}

static void
setup_node_and_add_to_id_table (Btor *btor, void *ptr)
{
  assert (btor);
  assert (ptr);

  BtorNode *exp;
  int id;

  exp = (BtorNode *) ptr;
  assert (!BTOR_IS_INVERTED_NODE (exp));
  assert (!exp->id);

  exp->refs = 1;
  exp->btor = btor;
  btor->stats.expressions++;
  id = BTOR_COUNT_STACK (btor->nodes_id_table);
  BTOR_ABORT_NODE (id == INT_MAX, "expression id overflow");
  exp->id = id;
  BTOR_PUSH_STACK (btor->mm, btor->nodes_id_table, exp);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == exp->id + 1);
  assert (BTOR_PEEK_STACK (btor->nodes_id_table, exp->id) == exp);
  btor->stats.node_bytes_alloc += exp->bytes;

  if (BTOR_IS_APPLY_NODE (exp)) exp->apply_below = 1;
}

static BtorNode *
new_const_exp_node (Btor *btor, const char *bits, int len)
{
  assert (btor);
  assert (bits);
  assert (len > 0);
  assert ((int) strlen (bits) == len);
  assert (btor_is_const_2vl (btor->mm, bits));

  BtorBVConstNode *exp;
  int i;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_BV_CONST_NODE);
  exp->bytes = sizeof *exp;
  BTOR_NEWN (btor->mm, exp->bits, len + 1);
  for (i = 0; i < len; i++) exp->bits[i] = bits[i];
  exp->bits[len] = '\0';
  exp->len       = len;
  setup_node_and_add_to_id_table (btor, exp);
  return (BtorNode *) exp;
}

static BtorNode *
new_slice_exp_node (Btor *btor, BtorNode *e0, int upper, int lower)
{
  assert (btor);
  assert (e0);
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (upper < BTOR_REAL_ADDR_NODE (e0)->len);
  assert (upper >= lower);
  assert (lower >= 0);

  BtorBVNode *exp = 0;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_SLICE_NODE);
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  exp->upper = upper;
  exp->lower = lower;
  exp->len   = upper - lower + 1;
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, (BtorNode *) exp, e0, 0);
  return (BtorNode *) exp;
}

static BtorNode *
new_aeq_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  /* we need aeq and acond next and prev fields -> type is BtorNode */
  BtorNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, exp, BTOR_FEQ_NODE);
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = 1;
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, exp, e0, 0);
  connect_child_exp (btor, exp, e1, 1);
  return exp;
}

static BtorNode *
new_lambda_exp_node (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (e_param);
  assert (BTOR_IS_REGULAR_NODE (e_param));
  assert (BTOR_IS_PARAM_NODE (e_param));
  assert (!BTOR_IS_BOUND_PARAM_NODE (e_param));
  assert (e_exp);
  assert (btor == e_param->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_exp)->btor);

  BtorNodeIterator it;
  BtorNode *exp;
  BtorLambdaNode *lambda_exp;

  BTOR_CNEW (btor->mm, lambda_exp);
  set_kind (btor, (BtorNode *) lambda_exp, BTOR_LAMBDA_NODE);
  lambda_exp->bytes        = sizeof *lambda_exp;
  lambda_exp->arity        = 2;
  lambda_exp->len          = BTOR_REAL_ADDR_NODE (e_exp)->len;
  lambda_exp->lambda_below = 1;
  lambda_exp->num_params   = 1;
  setup_node_and_add_to_id_table (btor, (BtorNode *) lambda_exp);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_param, 0);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_exp, 1);

  /* curried lambdas (functions) */
  if (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (e_exp)))
  {
    lambda_exp->num_params += ((BtorLambdaNode *) e_exp)->num_params;
    lambda_exp->body = btor_simplify_exp (btor, BTOR_LAMBDA_GET_BODY (e_exp));
  }
  else
    lambda_exp->body = e_exp;

  /* check if 'lambda' is parameterized, i.e. if it contains params that are not
   * bound by 'lambda' */
  remove_param_parameterized (btor, (BtorNode *) lambda_exp, e_param);
  if (is_parameterized (btor, (BtorNode *) lambda_exp))
    lambda_exp->parameterized = 1;

  assert (!BTOR_REAL_ADDR_NODE (lambda_exp->body)->simplified);
  assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (lambda_exp->body)));
  assert (!btor_find_in_ptr_hash_table (btor->lambdas, lambda_exp));
  (void) btor_insert_in_ptr_hash_table (btor->lambdas, lambda_exp);
  /* set lambda expression of parameter */
  BTOR_PARAM_SET_LAMBDA_NODE (e_param, lambda_exp);
  return (BtorNode *) lambda_exp;
}

static BtorNode *
new_args_exp_node (Btor *btor, int arity, BtorNode **e, int len)
{
  assert (btor);
  assert (arity > 0);
  assert (e);
  assert (len > 0);

  int i;
  BtorArgsNode *exp;
#ifndef NDEBUG
  for (i = 0; i < arity; i++) assert (e[i]);
#endif

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_ARGS_NODE);
  exp->bytes = sizeof (*exp);
  exp->arity = arity;
  exp->len   = len;
  setup_node_and_add_to_id_table (btor, exp);

  for (i = 0; i < arity; i++)
    connect_child_exp (btor, (BtorNode *) exp, e[i], i);

  /* set args node specific fields */
  if (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (exp->e[arity - 1])))
  {
    exp->num_args = ((BtorArgsNode *) exp->e[arity - 1])->num_args + arity - 1;
  }
  else
    exp->num_args = arity;

  return (BtorNode *) exp;
}

static BtorNode *
new_exp_node (Btor *btor, BtorNodeKind kind, int arity, BtorNode **e, int len)
{
  assert (btor);
  assert (arity > 0);
  assert (arity <= 3);
  assert (BTOR_IS_BINARY_NODE_KIND (kind) || BTOR_IS_TERNARY_NODE_KIND (kind));
  assert (e);
  assert (len > 0);

  int i;
  BtorBVNode *exp;
#ifdef NDEBUG
  for (i = 0; i < arity; i++)
  {
    assert (e[i]);
    assert (btor == BTOR_REAL_ADDR_NODE (e[i])->btor);
  }
#endif

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, kind);
  exp->bytes = sizeof (*exp);
  exp->arity = arity;
  exp->len   = len;
  setup_node_and_add_to_id_table (btor, exp);

  for (i = 0; i < arity; i++)
    connect_child_exp (btor, (BtorNode *) exp, e[i], i);

  return (BtorNode *) exp;
}

/* Computes hash value of expression by id */
unsigned int
btor_hash_exp_by_id (BtorNode *exp)
{
  assert (exp);
  return (unsigned int) BTOR_GET_ID_NODE (exp) * 7334147u;
}

/* Compares expressions by id */
int
btor_compare_exp_by_id (BtorNode *exp0, BtorNode *exp1)
{
  assert (exp0);
  assert (exp1);

  int id0, id1;

  id0 = BTOR_GET_ID_NODE (exp0);
  id1 = BTOR_GET_ID_NODE (exp1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

int
btor_cmp_exp_by_id_qsort_desc (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return b->id - a->id;
}

int
btor_cmp_exp_by_id_qsort_asc (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return a->id - b->id;
}

/* Search for constant expression in hash table. Returns 0 if not found. */
static BtorNode **
find_const_exp (Btor *btor, const char *bits, int len)
{
  assert (btor);
  assert (bits);
  assert (len > 0);
  assert ((int) strlen (bits) == len);

  BtorNode *cur, **result;
  unsigned int hash;

  hash = btor_hash_str ((void *) bits);
  hash = (hash * BTOR_NODE_UNIQUE_TABLE_PRIME)
         & (btor->nodes_unique_table.size - 1);
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (BTOR_IS_BV_CONST_NODE (cur) && cur->len == len
        && strcmp (cur->bits, bits) == 0)
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

/* Search for slice expression in hash table. Returns 0 if not found. */
static BtorNode **
find_slice_exp (Btor *btor, BtorNode *e0, int upper, int lower)
{
  assert (btor);
  assert (e0);
  assert (lower >= 0);
  assert (upper >= lower);

  BtorNode *cur, **result;
  unsigned int hash;

  hash = (((unsigned int) BTOR_REAL_ADDR_NODE (e0)->id + (unsigned int) upper
           + (unsigned int) lower)
          * BTOR_NODE_UNIQUE_TABLE_PRIME)
         & (btor->nodes_unique_table.size - 1);
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->kind == BTOR_SLICE_NODE && cur->e[0] == e0 && cur->upper == upper
        && cur->lower == lower)
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

// TODO: possible shortcut: check parents and its children of params
static int
compare_lambda_exp (Btor *btor,
                    BtorNode *param,
                    BtorNode *body,
                    BtorNode *lambda)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (!lambda->parameterized);

  int i, equal = 1;
  BtorNode *cur0, *cur1, *real_cur0, *real_cur1;
  BtorNodePtrStack visit;
  BtorPtrHashTable *marked;

  marked = btor_new_ptr_hash_table (btor->mm, 0, 0);

  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (btor->mm, visit, param);
  BTOR_PUSH_STACK (btor->mm, visit, lambda->e[0]);
  BTOR_PUSH_STACK (btor->mm, visit, body);
  BTOR_PUSH_STACK (btor->mm, visit, lambda->e[1]);

  /* for parameterized nodes it is enough to check their kind and if thy are
   * inverted
   * for non-parameterized nodes the ids have to be equal */
  while (!BTOR_EMPTY_STACK (visit))
  {
    cur1      = BTOR_POP_STACK (visit);
    cur0      = BTOR_POP_STACK (visit);
    real_cur1 = BTOR_REAL_ADDR_NODE (cur1);
    real_cur0 = BTOR_REAL_ADDR_NODE (cur0);

    if (btor_find_in_ptr_hash_table (marked, real_cur0)) continue;

    if (BTOR_IS_INVERTED_NODE (cur0) != BTOR_IS_INVERTED_NODE (cur1)
        || real_cur0->kind != real_cur1->kind
        || real_cur0->parameterized != real_cur1->parameterized
        || real_cur0->len != real_cur1->len
        /* arity might be differnt in case of BTOR_ARGS_NODE */
        || real_cur0->arity != real_cur1->arity)
    {
      equal = 0;
      break;
    }

    if (!real_cur0->parameterized)
    {
      assert (!real_cur1->parameterized);
      if (real_cur0->id != real_cur1->id)
      {
        equal = 0;
        break;
      }
      continue;
    }

    (void) btor_insert_in_ptr_hash_table (marked, real_cur0);

    if (real_cur0->id == real_cur1->id) continue;

    for (i = 0; i < real_cur0->arity; i++)
    {
      BTOR_PUSH_STACK (btor->mm, visit, real_cur0->e[i]);
      BTOR_PUSH_STACK (btor->mm, visit, real_cur1->e[i]);
    }
  }
  BTOR_RELEASE_STACK (btor->mm, visit);
  btor_delete_ptr_hash_table (marked);
  return equal;
}

static BtorNode **
find_lambda_exp (Btor *btor,
                 BtorNode *param,
                 BtorNode *body,
                 unsigned int *lambda_hash)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  BtorNode *cur, **result;
  int curried;
  unsigned int hash;

  hash = hash_lambda_exp (btor, param, body, &curried);
  if (lambda_hash) *lambda_hash = hash;
  hash *= BTOR_NODE_UNIQUE_TABLE_PRIME;
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->kind == BTOR_LAMBDA_NODE
        && ((!curried
             /* no support for curried lambdas yet */
             && !cur->parameterized
             && compare_lambda_exp (btor, param, body, cur))
            || (param == cur->e[0] && body == cur->e[1])))
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  assert (!*result || BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (*result)));
  return result;
}

static BtorNode **
find_exp (Btor *btor,
          BtorNodeKind kind,
          int arity,
          BtorNode **e,
          unsigned int *lambda_hash)
{
  assert (btor);
  assert (arity > 0);
  assert (e);

  BtorNode *cur, **result;
  int i, equal;
  unsigned int hash;

  if (kind == BTOR_LAMBDA_NODE)
    return find_lambda_exp (btor, e[0], e[1], lambda_hash);
  else if (lambda_hash)
    *lambda_hash = 0;

#ifndef NDEBUG
  for (i = 0; i < arity; i++) assert (e[i]);
#endif

  hash = hash_exp (arity, e);
  hash *= BTOR_NODE_UNIQUE_TABLE_PRIME;
  hash &= btor->nodes_unique_table.size - 1;

  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->kind == kind && cur->arity == arity)
    {
      equal = 1;
#ifdef NBTOR_SORT_BIN_COMMUTATIVE
      if (BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind))
      {
        if ((cur->e[0] == e[0] && cur->e[1] == e[1])
            || (cur->e[0] == e[1] && cur->e[1] == e[0]))
          break;
      }
#endif
      for (i = 0; i < arity && equal; i++)
        if (cur->e[i] != e[i]) equal = 0;

      if (equal) break;
    }
    result = &(cur->next);
    cur    = *result;
  }
  return result;
}

BtorNode **
btor_find_unique_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  exp = BTOR_REAL_ADDR_NODE (exp);
  if (BTOR_IS_BV_CONST_NODE (exp))
    return find_const_exp (btor, exp->bits, exp->len);
  if (BTOR_IS_SLICE_NODE (exp))
    return find_slice_exp (btor, exp->e[0], exp->upper, exp->lower);
  if (BTOR_IS_LAMBDA_NODE (exp))
    return find_lambda_exp (btor, exp->e[0], exp->e[1], 0);
  return find_exp (btor, exp->kind, exp->arity, exp->e, 0);
}

/* Enlarges unique table and rehashes expressions. */
static void
enlarge_nodes_unique_table (Btor *btor)
{
  assert (btor);

  BtorMemMgr *mm;
  int size, new_size, i;
  unsigned int hash;
  BtorNode *cur, *temp, **new_chains;

  mm       = btor->mm;
  size     = btor->nodes_unique_table.size;
  new_size = size ? 2 * size : 1;
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = btor->nodes_unique_table.chains[i];
    while (cur)
    {
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (!BTOR_IS_BV_VAR_NODE (cur));
      assert (!BTOR_IS_UF_NODE (cur));
      temp             = cur->next;
      hash             = compute_hash_exp (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BTOR_DELETEN (mm, btor->nodes_unique_table.chains, size);
  btor->nodes_unique_table.size   = new_size;
  btor->nodes_unique_table.chains = new_chains;
}

BtorNode *
btor_const_exp (Btor *btor, const char *bits)
{
  assert (btor);
  assert (bits);
  assert (*bits != '\0');

  BtorNode **lookup;
  int inv, len;
  char *lookupbits;

  len = (int) strlen (bits);
  assert (len > 0);
  inv        = 0;
  lookupbits = (char *) bits;
  /* normalize constants, constants are always even */
  if (bits[len - 1] == '1')
  {
    lookupbits = btor_not_const (btor->mm, bits);
    inv        = 1;
  }
  lookup = find_const_exp (btor, lookupbits, len);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_const_exp (btor, lookupbits, len);
    }
    *lookup = new_const_exp_node (btor, lookupbits, len);
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_NODE (*lookup));
  if (inv)
  {
    btor_delete_const (btor->mm, lookupbits);
    return BTOR_INVERT_NODE (*lookup);
  }
  return *lookup;
}

static BtorNode *
int_min_exp (Btor *btor, int len)
{
  assert (btor);
  assert (len > 0);

  char *string;
  BtorNode *result;

  string    = btor_zero_const (btor->mm, len);
  string[0] = '1';
  result    = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_zero_exp (Btor *btor, int len)
{
  assert (btor);
  assert (len > 0);

  char *string;
  BtorNode *result;

  string = btor_zero_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_false_exp (Btor *btor)
{
  assert (btor);
  return btor_zero_exp (btor, 1);
}

BtorNode *
btor_ones_exp (Btor *btor, int len)
{
  assert (btor);
  assert (len > 0);

  char *string;
  BtorNode *result;

  string = btor_ones_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_one_exp (Btor *btor, int len)
{
  assert (btor);
  assert (len > 0);

  char *string;
  BtorNode *result;

  string = btor_one_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_int_exp (Btor *btor, int i, int len)
{
  assert (btor);
  assert (len > 0);

  char *string;
  BtorNode *result;

  string = btor_int_to_const (btor->mm, i, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_unsigned_exp (Btor *btor, unsigned int u, int len)
{
  assert (btor);
  assert (len > 0);

  char *string;
  BtorNode *result;

  string = btor_unsigned_to_const (btor->mm, u, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_true_exp (Btor *btor)
{
  assert (btor);
  return btor_one_exp (btor, 1);
}

BtorNode *
btor_var_exp (Btor *btor, int len, const char *symbol)
{
  assert (btor);
  assert (len > 0);
  assert (!symbol
          || !btor_find_in_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorBVVarNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_BV_VAR_NODE);
  exp->bytes = sizeof *exp;
  exp->len   = len;
  setup_node_and_add_to_id_table (btor, exp);
  exp->bits = btor_x_const_3vl (btor->mm, len);
  (void) btor_insert_in_ptr_hash_table (btor->bv_vars, exp);
  if (symbol) btor_set_symbol_exp (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

BtorNode *
btor_param_exp (Btor *btor, int len, const char *symbol)
{
  assert (btor);
  assert (len > 0);
  assert (!symbol
          || !btor_find_in_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorParamNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_PARAM_NODE);
  exp->bytes         = sizeof *exp;
  exp->len           = len;
  exp->parameterized = 1;
  setup_node_and_add_to_id_table (btor, exp);
  if (symbol) btor_set_symbol_exp (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

BtorNode *
btor_array_exp (Btor *btor, int elem_len, int index_len, const char *symbol)
{
  assert (btor);
  assert (elem_len > 0);
  assert (index_len > 0);

  BtorNode *exp;
  BtorSort *index_sort, *elem_sort, *sort;

  index_sort = btor_bitvec_sort (&btor->sorts_unique_table, index_len);
  elem_sort  = btor_bitvec_sort (&btor->sorts_unique_table, elem_len);
  sort = btor_fun_sort (&btor->sorts_unique_table, &index_sort, 1, elem_sort);

  exp                            = btor_uf_exp (btor, sort, symbol);
  ((BtorUFNode *) exp)->is_array = 1;
  btor_release_sort (&btor->sorts_unique_table, index_sort);
  btor_release_sort (&btor->sorts_unique_table, elem_sort);
  btor_release_sort (&btor->sorts_unique_table, sort);

  return (BtorNode *) exp;
}

BtorNode *
btor_uf_exp (Btor *btor, BtorSort *sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (sort->table == &btor->sorts_unique_table);
  assert (sort->kind == BTOR_FUN_SORT);
  assert (BTOR_IS_BITVEC_SORT (sort->fun.codomain)
          || BTOR_IS_BOOL_SORT (sort->fun.codomain));
  assert (!symbol
          || !btor_find_in_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorUFNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_UF_NODE);
  exp->bytes = sizeof (*exp);
  exp->sort  = btor_copy_sort (sort);
  if (sort->fun.domain->kind == BTOR_TUPLE_SORT)
    exp->num_params = sort->fun.domain->tuple.num_elements;
  else
    exp->num_params = 1;
  if (BTOR_IS_BITVEC_SORT (sort->fun.codomain))
    exp->len = sort->fun.codomain->bitvec.len;
  else
    exp->len = 1;
  setup_node_and_add_to_id_table (btor, exp);
  (void) btor_insert_in_ptr_hash_table (btor->ufs, exp);
  if (symbol) btor_set_symbol_exp (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

static BtorNode *
unary_exp_slice_exp (Btor *btor, BtorNode *exp, int upper, int lower)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  int inv;
  BtorNode **lookup;

  exp = btor_simplify_exp (btor, exp);

  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_NODE (exp)->len);

  if (btor->options.rewrite_level.val > 0 && BTOR_IS_INVERTED_NODE (exp))
  {
    inv = 1;
    exp = BTOR_INVERT_NODE (exp);
  }
  else
    inv = 0;

  lookup = find_slice_exp (btor, exp, upper, lower);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_slice_exp (btor, exp, upper, lower);
    }
    *lookup = new_slice_exp_node (btor, exp, upper, lower);
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_NODE (*lookup));
  if (inv) return BTOR_INVERT_NODE (*lookup);
  return *lookup;
}

BtorNode *
btor_slice_exp_node (Btor *btor, BtorNode *exp, int upper, int lower)
{
  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));
  return unary_exp_slice_exp (btor, exp, upper, lower);
}

static BtorNode *
create_exp (Btor *btor, BtorNodeKind kind, int arity, BtorNode **e, int len)
{
  assert (btor);
  assert (kind);
  assert (arity > 0);
  assert (e);
#ifndef NBTOR_SORT_BIN_COMMUTATIVE
  assert (btor->options.rewrite_level.val == 0
          || !BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind)
          || BTOR_REAL_ADDR_NODE (e[0])->id <= BTOR_REAL_ADDR_NODE (e[1])->id);
#endif

  unsigned int lambda_hash;
  BtorNode **lookup;

  lookup = find_exp (btor, kind, arity, e, &lambda_hash);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_exp (btor, kind, arity, e, &lambda_hash);
    }

    switch (kind)
    {
      case BTOR_FEQ_NODE:
        assert (arity == 2);
        *lookup = new_aeq_exp_node (btor, e[0], e[1]);
        break;
      case BTOR_LAMBDA_NODE:
        assert (arity == 2);
        *lookup = new_lambda_exp_node (btor, e[0], e[1]);
        btor_find_in_ptr_hash_table (btor->lambdas, *lookup)->data.asInt =
            lambda_hash;
        break;
      case BTOR_ARGS_NODE:
        *lookup = new_args_exp_node (btor, arity, e, len);
        break;
      default: *lookup = new_exp_node (btor, kind, arity, e, len);
    }
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_NODE (*lookup));
  return *lookup;
}

static BtorNode *
binary_exp (Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, int len)
{
  assert (btor);
  assert (BTOR_IS_BINARY_NODE_KIND (kind));
  assert (e0);
  assert (e1);
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);
  assert (len > 0);

  BtorNode *e[2], *t;

  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);

#ifndef NBTOR_SORT_BIN_COMMUTATIVE
  if (btor->options.rewrite_level.val > 0
      && BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind)
      && BTOR_REAL_ADDR_NODE (e[1])->id < BTOR_REAL_ADDR_NODE (e[0])->id)
  {
    t    = e[0];
    e[0] = e[1];
    e[1] = t;
  }
#endif

  return create_exp (btor, kind, 2, e, len);
}

static BtorNode *
ternary_exp (Btor *btor,
             BtorNodeKind kind,
             BtorNode *e0,
             BtorNode *e1,
             BtorNode *e2,
             int len)
{
  assert (btor);
  assert (BTOR_IS_TERNARY_NODE_KIND (kind));
  assert (e0);
  assert (e1);
  assert (e2);
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e2)->btor);

  BtorNode *e[3];

  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  e[2] = btor_simplify_exp (btor, e2);

  return create_exp (btor, kind, 3, e, len);
}

BtorNode *
btor_and_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_AND_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_eq_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNodeKind kind;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)))
    kind = BTOR_FEQ_NODE;
  else
  {
    kind = BTOR_BEQ_NODE;
    if (btor->options.rewrite_level.val > 1)
    {
      if (BTOR_IS_INVERTED_NODE (e0)
          && BTOR_REAL_ADDR_NODE (e0)->kind == BTOR_BV_VAR_NODE)
      {
        e0 = BTOR_INVERT_NODE (e0);
        e1 = BTOR_INVERT_NODE (e1);
      }
      else if (BTOR_IS_INVERTED_NODE (e1)
               && BTOR_REAL_ADDR_NODE (e1)->kind == BTOR_BV_VAR_NODE
               && (BTOR_IS_INVERTED_NODE (e0)
                   || BTOR_REAL_ADDR_NODE (e1)->kind != BTOR_BV_VAR_NODE))
      {
        BtorNode *tmp = BTOR_INVERT_NODE (e0);
        e0            = BTOR_INVERT_NODE (e1);
        e1            = tmp;
      }
    }
  }

  return binary_exp (btor, kind, e0, e1, 1);
}

BtorNode *
btor_add_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_ADD_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_mul_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_MUL_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_ult_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_ULT_NODE, e0, e1, 1);
}

BtorNode *
btor_sll_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_SLL_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_srl_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_SRL_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_udiv_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_UDIV_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_urem_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor, BTOR_UREM_NODE, e0, e1, BTOR_REAL_ADDR_NODE (e0)->len);
}

BtorNode *
btor_concat_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor,
      BTOR_CONCAT_NODE,
      e0,
      e1,
      BTOR_REAL_ADDR_NODE (e0)->len + BTOR_REAL_ADDR_NODE (e1)->len);
}

BtorNode *
btor_lambda_exp_node (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  BtorNode *result;
  int elem_len;

  elem_len = BTOR_REAL_ADDR_NODE (e_exp)->len;
  result   = binary_exp (btor, BTOR_LAMBDA_NODE, e_param, e_exp, elem_len);
  return result;
}

BtorNode *
btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (e_param));
  assert (btor == e_param->btor);
  assert (BTOR_IS_PARAM_NODE (e_param));
  assert (BTOR_REAL_ADDR_NODE (e_param)->len > 0);
  assert (!BTOR_REAL_ADDR_NODE (e_param)->simplified);
  assert (e_exp);
  assert (btor == BTOR_REAL_ADDR_NODE (e_exp)->btor);
  assert (BTOR_REAL_ADDR_NODE (e_exp)->len > 0);

  BtorNode *result;
  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_lambda_exp (btor, e_param, e_exp);
  else
    result = btor_lambda_exp_node (btor, e_param, e_exp);
  assert (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (result)));
  return result;
}

BtorNode *
btor_fun_exp (Btor *btor, int paramc, BtorNode **params, BtorNode *exp)
{
  assert (btor);
  assert (paramc > 0);
  assert (params);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  int i;
  BtorNode *fun      = btor_simplify_exp (btor, exp);
  BtorNode *prev_fun = 0;

  for (i = paramc - 1; i >= 0; i--)
  {
    assert (params[i]);
    assert (btor == BTOR_REAL_ADDR_NODE (params[i])->btor);
    assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (params[i])));
    fun = btor_lambda_exp (btor, params[i], fun);
    if (prev_fun) btor_release_exp (btor, prev_fun);
    prev_fun = fun;
  }

  return fun;
}

// TODO: global define?
#define MAX_NUM_CHILDREN 3

BtorNode *
btor_args_exp (Btor *btor, int argc, BtorNode **args)
{
  assert (btor);
  assert (argc > 0);
  assert (args);

  int i, cur_argc, len, cnt_args, rem_free, num_args;
  BtorNode *e[MAX_NUM_CHILDREN];
  BtorNode *result = 0, *last = 0;

  /* arguments fit in one args node */
  if (argc <= MAX_NUM_CHILDREN)
  {
    num_args = 1;
    rem_free = MAX_NUM_CHILDREN - argc;
    cur_argc = argc;
  }
  /* arguments have to be split into several args nodes.
   * compute number of required args nodes */
  else
  {
    rem_free = argc % (MAX_NUM_CHILDREN - 1);
    num_args = argc / (MAX_NUM_CHILDREN - 1);
    /* we can store at most 1 more element into 'num_args' nodes
     * without needing an additional args node */
    if (rem_free > 1) num_args += 1;

    assert (num_args > 1);
    /* compute number of arguments in last args node */
    cur_argc = argc - (num_args - 1) * (MAX_NUM_CHILDREN - 1);
  }
  cnt_args = cur_argc - 1;

  len = 0;
  /* split up args in 'num_args' of args nodes */
  for (i = argc - 1; i >= 0; i--)
  {
    assert (cnt_args >= 0);
    assert (cnt_args <= MAX_NUM_CHILDREN);
    assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (args[i])));
    assert (btor == BTOR_REAL_ADDR_NODE (args[i])->btor);
    e[cnt_args] = btor_simplify_exp (btor, args[i]);
    len += BTOR_REAL_ADDR_NODE (e[cnt_args])->len;
    cnt_args -= 1;

    assert (i > 0 || cnt_args < 0);
    if (cnt_args < 0)
    {
      result = create_exp (btor, BTOR_ARGS_NODE, cur_argc, e, len);

      /* init for next iteration */
      len         = result->len;
      cur_argc    = MAX_NUM_CHILDREN;
      cnt_args    = cur_argc - 1;
      e[cnt_args] = result;
      cnt_args -= 1;

      if (last) btor_release_exp (btor, last);

      last = result;
    }
  }

  assert (result);
  return result;
}

BtorNode *
btor_apply_exp_node (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor == BTOR_REAL_ADDR_NODE (fun)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (args)->btor);
  assert (btor_precond_apply_exp_dbg (btor, fun, args));

  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, fun);
  e[1] = btor_simplify_exp (btor, args);

  assert (BTOR_IS_REGULAR_NODE (e[0]));
  assert (BTOR_IS_REGULAR_NODE (e[1]));
  assert (BTOR_IS_FUN_NODE (e[0]));
  assert (BTOR_IS_ARGS_NODE (e[1]));
  assert (!BTOR_IS_LAMBDA_NODE (fun)
          || ((BtorLambdaNode *) e[0])->num_params
                 == ((BtorArgsNode *) e[1])->num_args);

  return create_exp (btor, BTOR_APPLY_NODE, 2, e, fun->len);
}

BtorNode *
btor_apply_exp (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor == BTOR_REAL_ADDR_NODE (fun)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (args)->btor);

  fun  = btor_simplify_exp (btor, fun);
  args = btor_simplify_exp (btor, args);

  /* if fun was simplified to a constant value, we return a copy of it */
  if (!BTOR_IS_FUN_NODE (fun))
  {
    assert (!BTOR_REAL_ADDR_NODE (fun)->parameterized);
    return btor_copy_exp (btor, fun);
  }

  if (btor->options.rewrite_level.val > 0)
    return btor_rewrite_apply_exp (btor, fun, args);

  return btor_apply_exp_node (btor, fun, args);
}

BtorNode *
btor_apply_exps (Btor *btor, int argc, BtorNode **args, BtorNode *fun)
{
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_FUN_NODE (fun));

  BtorNode *exp, *_args;

  _args = btor_args_exp (btor, argc, args);
  fun   = btor_simplify_exp (btor, fun);
  _args = btor_simplify_exp (btor, _args);

  exp = btor_apply_exp (btor, fun, _args);
  btor_release_exp (btor, _args);

  return exp;
}

BtorNode *
btor_cond_exp_node (Btor *btor,
                    BtorNode *e_cond,
                    BtorNode *e_if,
                    BtorNode *e_else)
{
  e_cond = btor_simplify_exp (btor, e_cond);
  e_if   = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));
  return ternary_exp (btor,
                      BTOR_BCOND_NODE,
                      e_cond,
                      e_if,
                      e_else,
                      BTOR_REAL_ADDR_NODE (e_if)->len);
}

BtorNode *
btor_bv_cond_exp_node (Btor *btor,
                       BtorNode *e_cond,
                       BtorNode *e_if,
                       BtorNode *e_else)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_cond)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_if)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_else)->btor);

  if (btor->options.rewrite_level.val > 0)
    return btor_rewrite_cond_exp (btor, e_cond, e_if, e_else);

  return btor_cond_exp_node (btor, e_cond, e_if, e_else);
}

// TODO: arbitrary conditionals on functions
BtorNode *
btor_array_cond_exp_node (Btor *btor,
                          BtorNode *e_cond,
                          BtorNode *e_if,
                          BtorNode *e_else)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_cond)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_if)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_else)->btor);

  BtorNode *cond, *param, *lambda, *app_if, *app_else;

  e_cond = btor_simplify_exp (btor, e_cond);
  e_if   = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);

  assert (BTOR_IS_REGULAR_NODE (e_if));
  assert (BTOR_IS_FUN_NODE (e_if));
  assert (BTOR_IS_REGULAR_NODE (e_else));
  assert (BTOR_IS_FUN_NODE (e_else));

  param    = btor_param_exp (btor, BTOR_ARRAY_INDEX_LEN (e_if), 0);
  app_if   = btor_apply_exps (btor, 1, &param, e_if);
  app_else = btor_apply_exps (btor, 1, &param, e_else);
  cond     = btor_bv_cond_exp_node (btor, e_cond, app_if, app_else);
  lambda   = btor_lambda_exp (btor, param, cond);

  btor_release_exp (btor, param);
  btor_release_exp (btor, app_if);
  btor_release_exp (btor, app_else);
  btor_release_exp (btor, cond);

  return lambda;
}

BtorNode *
btor_not_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  (void) btor;
  inc_exp_ref_counter (btor, exp);
  return BTOR_INVERT_NODE (exp);
}

BtorNode *
btor_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_add_exp (btor, e0, e1);
  else
    result = btor_add_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_neg_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *one;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_NODE (exp)->len);
  result = btor_add_exp (btor, BTOR_INVERT_NODE (exp), one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_slice_exp (Btor *btor, BtorNode *exp, int upper, int lower)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_slice_exp (btor, exp, upper, lower);
  else
    result = btor_slice_exp_node (btor, exp, upper, lower);

  assert (result);
  return result;
}

BtorNode *
btor_or_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (
      btor_and_exp (btor, BTOR_INVERT_NODE (e0), BTOR_INVERT_NODE (e1)));
}

BtorNode *
btor_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_eq_exp (btor, e0, e1);
  else
    result = btor_eq_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_and_exp (btor, e0, e1);
  else
    result = btor_and_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_xor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, * or, *and;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  or     = btor_or_exp (btor, e0, e1);
  and    = btor_and_exp (btor, e0, e1);
  result = btor_and_exp (btor, or, BTOR_INVERT_NODE (and));
  btor_release_exp (btor, or);
  btor_release_exp (btor, and);
  return result;
}

BtorNode *
btor_xnor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_xor_exp (btor, e0, e1));
}

BtorNode *
btor_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_concat_exp (btor, e0, e1);
  else
    result = btor_concat_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_cond_exp (Btor *btor, BtorNode *e_cond, BtorNode *e_if, BtorNode *e_else)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_cond)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_if)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_else)->btor);

  if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_if)))
    return btor_array_cond_exp_node (btor, e_cond, e_if, e_else);

  return btor_bv_cond_exp_node (btor, e_cond, e_if, e_else);
}

BtorNode *
btor_redor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  zero   = btor_zero_exp (btor, BTOR_REAL_ADDR_NODE (exp)->len);
  result = BTOR_INVERT_NODE (btor_eq_exp (btor, exp, zero));
  btor_release_exp (btor, zero);
  return result;
}

BtorNode *
btor_redxor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *slice, *xor;
  int i, len;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  len = BTOR_REAL_ADDR_NODE (exp)->len;

  result = btor_slice_exp (btor, exp, 0, 0);
  for (i = 1; i < len; i++)
  {
    slice = btor_slice_exp (btor, exp, i, i);
    xor   = btor_xor_exp (btor, result, slice);
    btor_release_exp (btor, slice);
    btor_release_exp (btor, result);
    result = xor;
  }
  return result;
}

BtorNode *
btor_redand_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *ones;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  ones   = btor_ones_exp (btor, BTOR_REAL_ADDR_NODE (exp)->len);
  result = btor_eq_exp (btor, exp, ones);
  btor_release_exp (btor, ones);
  return result;
}

BtorNode *
btor_uext_exp (Btor *btor, BtorNode *exp, int len)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp, len));

  if (len == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (len > 0);
    zero   = btor_zero_exp (btor, len);
    result = btor_concat_exp (btor, zero, exp);
    btor_release_exp (btor, zero);
  }
  return result;
}

BtorNode *
btor_sext_exp (Btor *btor, BtorNode *exp, int len)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero, *ones, *neg, *cond;
  int exp_len;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp, len));

  if (len == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (len > 0);
    zero    = btor_zero_exp (btor, len);
    ones    = btor_ones_exp (btor, len);
    exp_len = BTOR_REAL_ADDR_NODE (exp)->len;
    neg     = btor_slice_exp (btor, exp, exp_len - 1, exp_len - 1);
    cond    = btor_cond_exp (btor, neg, ones, zero);
    result  = btor_concat_exp (btor, cond, exp);
    btor_release_exp (btor, zero);
    btor_release_exp (btor, ones);
    btor_release_exp (btor, neg);
    btor_release_exp (btor, cond);
  }
  return result;
}

BtorNode *
btor_nand_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_and_exp (btor, e0, e1));
}

BtorNode *
btor_nor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_or_exp (btor, e0, e1));
}

BtorNode *
btor_implies_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (BTOR_REAL_ADDR_NODE (e0)->len == 1);
  return BTOR_INVERT_NODE (btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1)));
}

BtorNode *
btor_iff_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (BTOR_REAL_ADDR_NODE (e0)->len == 1);
  return btor_eq_exp (btor, e0, e1);
}

BtorNode *
btor_ne_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_eq_exp (btor, e0, e1));
}

BtorNode *
btor_uaddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *add;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_NODE (e0)->len;
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, e1, 1);
  add     = btor_add_exp (btor, uext_e1, uext_e2);
  result  = btor_slice_exp (btor, add, len, len);
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, add);
  return result;
}

BtorNode *
btor_saddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *sign_result;
  BtorNode *add, *and1, *and2, *or1, *or2;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len         = BTOR_REAL_ADDR_NODE (e0)->len;
  sign_e1     = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (btor, e1, len - 1, len - 1);
  add         = btor_add_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, add, len - 1, len - 1);
  and1        = btor_and_exp (btor, sign_e1, sign_e2);
  or1         = btor_and_exp (btor, and1, BTOR_INVERT_NODE (sign_result));
  and2        = btor_and_exp (
      btor, BTOR_INVERT_NODE (sign_e1), BTOR_INVERT_NODE (sign_e2));
  or2    = btor_and_exp (btor, and2, sign_result);
  result = btor_or_exp (btor, or1, or2);
  btor_release_exp (btor, and1);
  btor_release_exp (btor, and2);
  btor_release_exp (btor, or1);
  btor_release_exp (btor, or2);
  btor_release_exp (btor, add);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, sign_result);
  return result;
}

BtorNode *
btor_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_mul_exp (btor, e0, e1);
  else
    result = btor_mul_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_umulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *mul, *slice, *and, * or, **temps_e2;
  int i, len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_NODE (e0)->len;
  if (len == 1) return btor_zero_exp (btor, 1);
  BTOR_NEWN (btor->mm, temps_e2, len - 1);
  temps_e2[0] = btor_slice_exp (btor, e1, len - 1, len - 1);
  for (i = 1; i < len - 1; i++)
  {
    slice       = btor_slice_exp (btor, e1, len - 1 - i, len - 1 - i);
    temps_e2[i] = btor_or_exp (btor, temps_e2[i - 1], slice);
    btor_release_exp (btor, slice);
  }
  slice  = btor_slice_exp (btor, e0, 1, 1);
  result = btor_and_exp (btor, slice, temps_e2[0]);
  btor_release_exp (btor, slice);
  for (i = 1; i < len - 1; i++)
  {
    slice = btor_slice_exp (btor, e0, i + 1, i + 1);
    and   = btor_and_exp (btor, slice, temps_e2[i]);
    or    = btor_or_exp (btor, result, and);
    btor_release_exp (btor, slice);
    btor_release_exp (btor, and);
    btor_release_exp (btor, result);
    result = or ;
  }
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, e1, 1);
  mul     = btor_mul_exp (btor, uext_e1, uext_e2);
  slice   = btor_slice_exp (btor, mul, len, len);
  or      = btor_or_exp (btor, result, slice);
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, mul);
  btor_release_exp (btor, slice);
  btor_release_exp (btor, result);
  result = or ;
  for (i = 0; i < len - 1; i++) btor_release_exp (btor, temps_e2[i]);
  BTOR_DELETEN (btor->mm, temps_e2, len - 1);
  return result;
}

BtorNode *
btor_smulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sext_e1, *sext_e2, *sign_e1, *sign_e2, *sext_sign_e1;
  BtorNode *sext_sign_e2, *xor_sign_e1, *xor_sign_e2, *mul, *slice, *slice_n;
  BtorNode *slice_n_minus_1, *xor, *and, * or, **temps_e2;
  int i, len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_NODE (e0)->len;
  if (len == 1) return btor_and_exp (btor, e0, e1);
  if (len == 2)
  {
    sext_e1         = btor_sext_exp (btor, e0, 1);
    sext_e2         = btor_sext_exp (btor, e1, 1);
    mul             = btor_mul_exp (btor, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (btor, mul, len, len);
    slice_n_minus_1 = btor_slice_exp (btor, mul, len - 1, len - 1);
    result          = btor_xor_exp (btor, slice_n, slice_n_minus_1);
    btor_release_exp (btor, sext_e1);
    btor_release_exp (btor, sext_e2);
    btor_release_exp (btor, mul);
    btor_release_exp (btor, slice_n);
    btor_release_exp (btor, slice_n_minus_1);
  }
  else
  {
    sign_e1      = btor_slice_exp (btor, e0, len - 1, len - 1);
    sign_e2      = btor_slice_exp (btor, e1, len - 1, len - 1);
    sext_sign_e1 = btor_sext_exp (btor, sign_e1, len - 1);
    sext_sign_e2 = btor_sext_exp (btor, sign_e2, len - 1);
    xor_sign_e1  = btor_xor_exp (btor, e0, sext_sign_e1);
    xor_sign_e2  = btor_xor_exp (btor, e1, sext_sign_e2);
    BTOR_NEWN (btor->mm, temps_e2, len - 2);
    temps_e2[0] = btor_slice_exp (btor, xor_sign_e2, len - 2, len - 2);
    for (i = 1; i < len - 2; i++)
    {
      slice = btor_slice_exp (btor, xor_sign_e2, len - 2 - i, len - 2 - i);
      temps_e2[i] = btor_or_exp (btor, temps_e2[i - 1], slice);
      btor_release_exp (btor, slice);
    }
    slice  = btor_slice_exp (btor, xor_sign_e1, 1, 1);
    result = btor_and_exp (btor, slice, temps_e2[0]);
    btor_release_exp (btor, slice);
    for (i = 1; i < len - 2; i++)
    {
      slice = btor_slice_exp (btor, xor_sign_e1, i + 1, i + 1);
      and   = btor_and_exp (btor, slice, temps_e2[i]);
      or    = btor_or_exp (btor, result, and);
      btor_release_exp (btor, slice);
      btor_release_exp (btor, and);
      btor_release_exp (btor, result);
      result = or ;
    }
    sext_e1         = btor_sext_exp (btor, e0, 1);
    sext_e2         = btor_sext_exp (btor, e1, 1);
    mul             = btor_mul_exp (btor, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (btor, mul, len, len);
    slice_n_minus_1 = btor_slice_exp (btor, mul, len - 1, len - 1);
    xor             = btor_xor_exp (btor, slice_n, slice_n_minus_1);
    or              = btor_or_exp (btor, result, xor);
    btor_release_exp (btor, sext_e1);
    btor_release_exp (btor, sext_e2);
    btor_release_exp (btor, sign_e1);
    btor_release_exp (btor, sign_e2);
    btor_release_exp (btor, sext_sign_e1);
    btor_release_exp (btor, sext_sign_e2);
    btor_release_exp (btor, xor_sign_e1);
    btor_release_exp (btor, xor_sign_e2);
    btor_release_exp (btor, mul);
    btor_release_exp (btor, slice_n);
    btor_release_exp (btor, slice_n_minus_1);
    btor_release_exp (btor, xor);
    btor_release_exp (btor, result);
    result = or ;
    for (i = 0; i < len - 2; i++) btor_release_exp (btor, temps_e2[i]);
    BTOR_DELETEN (btor->mm, temps_e2, len - 2);
  }
  return result;
}

BtorNode *
btor_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_ult_exp (btor, e0, e1);
  else
    result = btor_ult_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_slt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *determined_by_sign, *eq_sign, *ult, *eq_sign_and_ult;
  BtorNode *res, *s0, *s1, *r0, *r1, *l, *r;

  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_NODE (e0)->len;
  if (len == 1) return btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1));
  s0                 = btor_slice_exp (btor, e0, len - 1, len - 1);
  s1                 = btor_slice_exp (btor, e1, len - 1, len - 1);
  r0                 = btor_slice_exp (btor, e0, len - 2, 0);
  r1                 = btor_slice_exp (btor, e1, len - 2, 0);
  ult                = btor_ult_exp (btor, r0, r1);
  determined_by_sign = btor_and_exp (btor, s0, BTOR_INVERT_NODE (s1));
  l                  = btor_copy_exp (btor, determined_by_sign);
  r                  = btor_and_exp (btor, BTOR_INVERT_NODE (s0), s1);
  eq_sign = btor_and_exp (btor, BTOR_INVERT_NODE (l), BTOR_INVERT_NODE (r));
  eq_sign_and_ult = btor_and_exp (btor, eq_sign, ult);
  res             = btor_or_exp (btor, determined_by_sign, eq_sign_and_ult);
  btor_release_exp (btor, s0);
  btor_release_exp (btor, s1);
  btor_release_exp (btor, r0);
  btor_release_exp (btor, r1);
  btor_release_exp (btor, ult);
  btor_release_exp (btor, determined_by_sign);
  btor_release_exp (btor, l);
  btor_release_exp (btor, r);
  btor_release_exp (btor, eq_sign);
  btor_release_exp (btor, eq_sign_and_ult);
  return res;
}

BtorNode *
btor_ulte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *ult;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  ult    = btor_ult_exp (btor, e1, e0);
  result = btor_not_exp (btor, ult);
  btor_release_exp (btor, ult);
  return result;
}

BtorNode *
btor_slte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *slt;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  slt    = btor_slt_exp (btor, e1, e0);
  result = btor_not_exp (btor, slt);
  btor_release_exp (btor, slt);
  return result;
}

BtorNode *
btor_ugt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_ult_exp (btor, e1, e0);
}

BtorNode *
btor_sgt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_slt_exp (btor, e1, e0);
}

BtorNode *
btor_ugte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *ult;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  ult    = btor_ult_exp (btor, e0, e1);
  result = btor_not_exp (btor, ult);
  btor_release_exp (btor, ult);
  return result;
}

BtorNode *
btor_sgte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *slt;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  slt    = btor_slt_exp (btor, e0, e1);
  result = btor_not_exp (btor, slt);
  btor_release_exp (btor, slt);
  return result;
}

BtorNode *
btor_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_sll_exp (btor, e0, e1);
  else
    result = btor_sll_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_srl_exp (btor, e0, e1);
  else
    result = btor_srl_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_sra_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *srl1, *srl2;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_NODE (e0)->len;
  sign_e1 = btor_slice_exp (btor, e0, len - 1, len - 1);
  srl1    = btor_srl_exp (btor, e0, e1);
  srl2    = btor_srl_exp (btor, BTOR_INVERT_NODE (e0), e1);
  result  = btor_cond_exp (btor, sign_e1, BTOR_INVERT_NODE (srl2), srl1);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, srl1);
  btor_release_exp (btor, srl2);
  return result;
}

BtorNode *
btor_rol_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sll, *neg_e2, *srl;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  sll    = btor_sll_exp (btor, e0, e1);
  neg_e2 = btor_neg_exp (btor, e1);
  srl    = btor_srl_exp (btor, e0, neg_e2);
  result = btor_or_exp (btor, sll, srl);
  btor_release_exp (btor, sll);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, srl);
  return result;
}

BtorNode *
btor_ror_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *srl, *neg_e2, *sll;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  srl    = btor_srl_exp (btor, e0, e1);
  neg_e2 = btor_neg_exp (btor, e1);
  sll    = btor_sll_exp (btor, e0, neg_e2);
  result = btor_or_exp (btor, srl, sll);
  btor_release_exp (btor, srl);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, sll);
  return result;
}

BtorNode *
btor_sub_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *neg_e2;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  neg_e2 = btor_neg_exp (btor, e1);
  result = btor_add_exp (btor, e0, neg_e2);
  btor_release_exp (btor, neg_e2);
  return result;
}

BtorNode *
btor_usubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *uext_e1, *uext_e2, *add1, *add2, *one;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_NODE (e0)->len;
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, BTOR_INVERT_NODE (e1), 1);
  assert (len < INT_MAX);
  one    = btor_one_exp (btor, len + 1);
  add1   = btor_add_exp (btor, uext_e2, one);
  add2   = btor_add_exp (btor, uext_e1, add1);
  result = BTOR_INVERT_NODE (btor_slice_exp (btor, add2, len, len));
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, add1);
  btor_release_exp (btor, add2);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_ssubo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *sign_result;
  BtorNode *sub, *and1, *and2, *or1, *or2;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len         = BTOR_REAL_ADDR_NODE (e0)->len;
  sign_e1     = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (btor, e1, len - 1, len - 1);
  sub         = btor_sub_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, sub, len - 1, len - 1);
  and1        = btor_and_exp (btor, BTOR_INVERT_NODE (sign_e1), sign_e2);
  or1         = btor_and_exp (btor, and1, sign_result);
  and2        = btor_and_exp (btor, sign_e1, BTOR_INVERT_NODE (sign_e2));
  or2         = btor_and_exp (btor, and2, BTOR_INVERT_NODE (sign_result));
  result      = btor_or_exp (btor, or1, or2);
  btor_release_exp (btor, and1);
  btor_release_exp (btor, and2);
  btor_release_exp (btor, or1);
  btor_release_exp (btor, or2);
  btor_release_exp (btor, sub);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, sign_result);
  return result;
}

BtorNode *
btor_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_udiv_exp (btor, e0, e1);
  else
    result = btor_udiv_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_sdiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e1, *sign_e2, *xor, *neg_e1, *neg_e2;
  BtorNode *cond_e1, *cond_e2, *udiv, *neg_udiv;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_NODE (e0)->len;

  if (len == 1)
    return BTOR_INVERT_NODE (btor_and_exp (btor, BTOR_INVERT_NODE (e0), e1));

  sign_e1 = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (btor, e1, len - 1, len - 1);
  /* xor: must result be signed? */
  xor    = btor_xor_exp (btor, sign_e1, sign_e2);
  neg_e1 = btor_neg_exp (btor, e0);
  neg_e2 = btor_neg_exp (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_cond_exp (btor, sign_e1, neg_e1, e0);
  cond_e2  = btor_cond_exp (btor, sign_e2, neg_e2, e1);
  udiv     = btor_udiv_exp (btor, cond_e1, cond_e2);
  neg_udiv = btor_neg_exp (btor, udiv);
  /* sign result if necessary */
  result = btor_cond_exp (btor, xor, neg_udiv, udiv);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, xor);
  btor_release_exp (btor, neg_e1);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, cond_e1);
  btor_release_exp (btor, cond_e2);
  btor_release_exp (btor, udiv);
  btor_release_exp (btor, neg_udiv);
  return result;
}

BtorNode *
btor_sdivo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *int_min, *ones, *eq1, *eq2;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  int_min = int_min_exp (btor, BTOR_REAL_ADDR_NODE (e0)->len);
  ones    = btor_ones_exp (btor, BTOR_REAL_ADDR_NODE (e1)->len);
  eq1     = btor_eq_exp (btor, e0, int_min);
  eq2     = btor_eq_exp (btor, e1, ones);
  result  = btor_and_exp (btor, eq1, eq2);
  btor_release_exp (btor, int_min);
  btor_release_exp (btor, ones);
  btor_release_exp (btor, eq1);
  btor_release_exp (btor, eq2);
  return result;
}

BtorNode *
btor_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->options.rewrite_level.val > 0)
    result = btor_rewrite_urem_exp (btor, e0, e1);
  else
    result = btor_urem_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_srem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1;
  BtorNode *cond_e0, *cond_e1, *urem, *neg_urem;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_NODE (e0)->len;

  if (len == 1) return btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1));

  sign_e0 = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e1 = btor_slice_exp (btor, e1, len - 1, len - 1);
  neg_e0  = btor_neg_exp (btor, e0);
  neg_e1  = btor_neg_exp (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e0  = btor_cond_exp (btor, sign_e0, neg_e0, e0);
  cond_e1  = btor_cond_exp (btor, sign_e1, neg_e1, e1);
  urem     = btor_urem_exp (btor, cond_e0, cond_e1);
  neg_urem = btor_neg_exp (btor, urem);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = btor_cond_exp (btor, sign_e0, neg_urem, urem);
  btor_release_exp (btor, sign_e0);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, neg_e0);
  btor_release_exp (btor, neg_e1);
  btor_release_exp (btor, cond_e0);
  btor_release_exp (btor, cond_e1);
  btor_release_exp (btor, urem);
  btor_release_exp (btor, neg_urem);
  return result;
}

BtorNode *
btor_smod_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e1)->btor);

  BtorNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1, *cond_e0, *cond_e1;
  BtorNode *neg_e0_and_e1, *neg_e0_and_neg_e1, *zero, *e0_zero;
  BtorNode *neg_urem, *add1, *add2, *or1, *or2, *e0_and_e1, *e0_and_neg_e1;
  BtorNode *cond_case1, *cond_case2, *cond_case3, *cond_case4, *urem;
  BtorNode *urem_zero, *gadd1, *gadd2;
  int len;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len       = BTOR_REAL_ADDR_NODE (e0)->len;
  zero      = btor_zero_exp (btor, len);
  e0_zero   = btor_eq_exp (btor, zero, e0);
  sign_e0   = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e1   = btor_slice_exp (btor, e1, len - 1, len - 1);
  neg_e0    = btor_neg_exp (btor, e0);
  neg_e1    = btor_neg_exp (btor, e1);
  e0_and_e1 = btor_and_exp (
      btor, BTOR_INVERT_NODE (sign_e0), BTOR_INVERT_NODE (sign_e1));
  e0_and_neg_e1     = btor_and_exp (btor, BTOR_INVERT_NODE (sign_e0), sign_e1);
  neg_e0_and_e1     = btor_and_exp (btor, sign_e0, BTOR_INVERT_NODE (sign_e1));
  neg_e0_and_neg_e1 = btor_and_exp (btor, sign_e0, sign_e1);
  /* normalize e0 and e1 if necessary */
  cond_e0    = btor_cond_exp (btor, sign_e0, neg_e0, e0);
  cond_e1    = btor_cond_exp (btor, sign_e1, neg_e1, e1);
  urem       = btor_urem_exp (btor, cond_e0, cond_e1);
  urem_zero  = btor_eq_exp (btor, urem, zero);
  neg_urem   = btor_neg_exp (btor, urem);
  add1       = btor_add_exp (btor, neg_urem, e1);
  add2       = btor_add_exp (btor, urem, e1);
  gadd1      = btor_cond_exp (btor, urem_zero, zero, add1);
  gadd2      = btor_cond_exp (btor, urem_zero, zero, add2);
  cond_case1 = btor_cond_exp (btor, e0_and_e1, urem, zero);
  cond_case2 = btor_cond_exp (btor, neg_e0_and_e1, gadd1, zero);
  cond_case3 = btor_cond_exp (btor, e0_and_neg_e1, gadd2, zero);
  cond_case4 = btor_cond_exp (btor, neg_e0_and_neg_e1, neg_urem, zero);
  or1        = btor_or_exp (btor, cond_case1, cond_case2);
  or2        = btor_or_exp (btor, cond_case3, cond_case4);
  result     = btor_or_exp (btor, or1, or2);
  btor_release_exp (btor, zero);
  btor_release_exp (btor, e0_zero);
  btor_release_exp (btor, sign_e0);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, neg_e0);
  btor_release_exp (btor, neg_e1);
  btor_release_exp (btor, cond_e0);
  btor_release_exp (btor, cond_e1);
  btor_release_exp (btor, urem_zero);
  btor_release_exp (btor, cond_case1);
  btor_release_exp (btor, cond_case2);
  btor_release_exp (btor, cond_case3);
  btor_release_exp (btor, cond_case4);
  btor_release_exp (btor, urem);
  btor_release_exp (btor, neg_urem);
  btor_release_exp (btor, add1);
  btor_release_exp (btor, add2);
  btor_release_exp (btor, gadd1);
  btor_release_exp (btor, gadd2);
  btor_release_exp (btor, or1);
  btor_release_exp (btor, or2);
  btor_release_exp (btor, e0_and_e1);
  btor_release_exp (btor, neg_e0_and_e1);
  btor_release_exp (btor, e0_and_neg_e1);
  btor_release_exp (btor, neg_e0_and_neg_e1);
  return result;
}

BtorNode *
btor_read_exp (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_index)->btor);

  BtorNode *result;

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));

  result = btor_apply_exps (btor, 1, &e_index, e_array);

  // TODO (ma): why do reads have bits?
  if (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (result)))
  {
    BTOR_REAL_ADDR_NODE (result)->is_read = 1;
    if (!BTOR_REAL_ADDR_NODE (result)->bits)
      BTOR_REAL_ADDR_NODE (result)->bits =
          btor_x_const_3vl (btor->mm, e_array->len);
  }

  return result;
}

BtorNode *
btor_write_exp (Btor *btor,
                BtorNode *e_array,
                BtorNode *e_index,
                BtorNode *e_value)
{
  assert (btor);
  assert (BTOR_IS_FUN_NODE (e_array));
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_index)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_value)->btor);

  BtorNode *param, *e_cond, *e_if, *e_else, *bvcond;
  BtorLambdaNode *lambda;

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));

  param  = btor_param_exp (btor, BTOR_REAL_ADDR_NODE (e_index)->len, 0);
  e_cond = btor_eq_exp (btor, param, e_index);
  e_if   = btor_copy_exp (btor, e_value);
  e_else = btor_read_exp (btor, e_array, param);
  bvcond = btor_cond_exp (btor, e_cond, e_if, e_else);
  lambda = (BtorLambdaNode *) btor_lambda_exp (btor, param, bvcond);

  btor_release_exp (btor, e_if);
  btor_release_exp (btor, e_else);
  btor_release_exp (btor, e_cond);
  btor_release_exp (btor, bvcond);
  btor_release_exp (btor, param);

  return (BtorNode *) lambda;
}

BtorNode *
btor_inc_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_NODE (exp)->len);
  result = btor_add_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_dec_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_NODE (exp)->len);
  result = btor_sub_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

int
btor_get_exp_len (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_REAL_ADDR_NODE (exp)->len;
}

int
btor_is_array_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  exp = btor_simplify_exp (btor, exp);
  // TODO: check for array sort?
  return (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp))
          && ((BtorLambdaNode *) exp)->num_params == 1)
         || BTOR_IS_UF_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp));
  //         || (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp))
  //	     && ((BtorLambdaNode *) exp)->num_params == 1)
  //	 || (BTOR_IS_UF_NODE (BTOR_REAL_ADDR_NODE (exp))
  //	     && ((BtorUFNode *) exp)->num_params == 1);
}

int
btor_is_uf_array_var_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_UF_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_is_bv_var_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_get_index_exp_len (Btor *btor, BtorNode *e_array)
{
  assert (btor);
  assert (e_array);
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);
  e_array = btor_simplify_exp (btor, e_array);
  assert (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_array)));
  assert (BTOR_IS_REGULAR_NODE (e_array));
  return BTOR_ARRAY_INDEX_LEN (e_array);
}

int
btor_get_id (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  (void) btor;
  return BTOR_REAL_ADDR_NODE (exp)->id;
}

BtorNode *
btor_match_node_by_id (Btor *btor, int id)
{
  assert (btor);
  assert (id > 0);
  if (id >= BTOR_COUNT_STACK (btor->nodes_id_table)) return 0;
  return btor_copy_exp (btor, BTOR_PEEK_STACK (btor->nodes_id_table, id));
}

BtorNode *
btor_match_node (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int id;
  BtorNode *res;

  id = BTOR_REAL_ADDR_NODE (exp)->id;
  assert (id > 0);
  if (id >= BTOR_COUNT_STACK (btor->nodes_id_table)) return 0;
  res = btor_copy_exp (btor, BTOR_PEEK_STACK (btor->nodes_id_table, id));
  return BTOR_IS_INVERTED_NODE (exp) ? BTOR_INVERT_NODE (res) : res;
}

char *
btor_get_symbol_exp (Btor *btor, BtorNode *exp)
{
  /* do not pointer-chase! */
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  BtorPtrHashBucket *b = btor_find_in_ptr_hash_table (
      btor->node2symbol, BTOR_REAL_ADDR_NODE (exp));
  if (b) return b->data.asStr;
  return 0;
}

void
btor_set_symbol_exp (Btor *btor, BtorNode *exp, const char *symbol)
{
  /* do not pointer-chase! */
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  assert (symbol);
  assert (!btor_find_in_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorPtrHashBucket *b;
  char *sym;

  exp = BTOR_REAL_ADDR_NODE (exp);
  sym = btor_strdup (btor->mm, symbol);
  (void) btor_insert_in_ptr_hash_table (btor->symbols, sym);
  b = btor_find_in_ptr_hash_table (btor->node2symbol, exp);

  if (b)
  {
    btor_remove_from_ptr_hash_table (btor->symbols, b->data.asStr, 0, 0);
    btor_freestr (btor->mm, b->data.asStr);
  }
  else
    b = btor_insert_in_ptr_hash_table (btor->node2symbol, exp);

  b->data.asStr = sym;
}

int
btor_is_param_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_is_bound_param_exp (Btor *btor, BtorNode *param)
{
  assert (btor);
  assert (param);
  assert (btor == BTOR_REAL_ADDR_NODE (param)->btor);
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  param = btor_simplify_exp (btor, param);
  return BTOR_IS_BOUND_PARAM_NODE (BTOR_REAL_ADDR_NODE (param));
}

int
btor_is_fun_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp))
         || BTOR_IS_UF_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_get_fun_arity (Btor *btor, BtorNode *exp)
{
  (void) btor;
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  if (BTOR_IS_LAMBDA_NODE (exp)) return ((BtorLambdaNode *) exp)->num_params;
  assert (BTOR_IS_UF_NODE (exp));
  return ((BtorUFNode *) exp)->num_params;
}

int
btor_is_args_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_get_args_arity (Btor *btor, BtorNode *exp)
{
  (void) btor;
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (BTOR_IS_ARGS_NODE (exp));
  return ((BtorArgsNode *) exp)->num_args;
}
