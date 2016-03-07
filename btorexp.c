/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2016 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorexp.h"

#include "btorabort.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbeta.h"
#include "btorlog.h"
#include "btorrewrite.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BTOR_UNIQUE_TABLE_LIMIT 30

#define BTOR_FULL_UNIQUE_TABLE(table)   \
  ((table).num_elements >= (table).size \
   && btor_log_2_util ((table).size) < BTOR_UNIQUE_TABLE_LIMIT)

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

bool
btor_precond_slice_exp_dbg (Btor *btor,
                            BtorNode *exp,
                            uint32_t upper,
                            uint32_t lower)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (upper >= lower);
  assert (upper < btor_get_exp_width (btor, exp));
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  return true;
}

static bool
btor_precond_ext_exp_dbg (Btor *btor, BtorNode *exp)
{
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));
  return true;
}

bool
btor_precond_regular_unary_bv_exp_dbg (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->btor == btor);
  return true;
}

bool
btor_precond_eq_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1)
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
  assert (real_e0->sort_id == real_e1->sort_id);
  assert (real_e0->is_array == real_e1->is_array);
  assert (!BTOR_IS_FUN_NODE (real_e0)
          || (BTOR_IS_REGULAR_NODE (e0) && BTOR_IS_REGULAR_NODE (e1)));
  return true;
}

bool
btor_precond_concat_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (btor_get_exp_width (btor, e0)
          <= INT_MAX - btor_get_exp_width (btor, e1));
  assert (BTOR_REAL_ADDR_NODE (e0)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e1)->btor == btor);
  return true;
}

bool
btor_precond_shift_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (btor_get_exp_width (btor, e0) > 1);
  assert (btor_is_power_of_2_util (btor_get_exp_width (btor, e0)));
  assert (btor_log_2_util (btor_get_exp_width (btor, e0))
          == btor_get_exp_width (btor, e1));
  assert (BTOR_REAL_ADDR_NODE (e0)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e1)->btor == btor);
  return true;
}

bool
btor_precond_regular_binary_bv_exp_dbg (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (btor);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->sort_id
          == BTOR_REAL_ADDR_NODE (e1)->sort_id);
  assert (BTOR_REAL_ADDR_NODE (e0)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e1)->btor == btor);
  return true;
}

bool
btor_precond_read_exp_dbg (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
  assert (btor);
  assert (e_array);
  assert (e_index);
  assert (BTOR_IS_REGULAR_NODE (e_array));
  assert (BTOR_IS_FUN_NODE (e_array));
  assert (!e_array->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_index)->simplified);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_index)));
  assert (
      btor_get_index_array_sort (&btor->sorts_unique_table, e_array->sort_id)
      == BTOR_REAL_ADDR_NODE (e_index)->sort_id);
  assert (BTOR_REAL_ADDR_NODE (e_array)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e_index)->btor == btor);
  assert (e_array->is_array);
  return true;
}

bool
btor_precond_write_exp_dbg (Btor *btor,
                            BtorNode *e_array,
                            BtorNode *e_index,
                            BtorNode *e_value)
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
  assert (
      btor_get_index_array_sort (&btor->sorts_unique_table, e_array->sort_id)
      == BTOR_REAL_ADDR_NODE (e_index)->sort_id);
  assert (
      btor_get_element_array_sort (&btor->sorts_unique_table, e_array->sort_id)
      == BTOR_REAL_ADDR_NODE (e_value)->sort_id);
  assert (BTOR_REAL_ADDR_NODE (e_array)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e_index)->btor == btor);
  assert (BTOR_REAL_ADDR_NODE (e_value)->btor == btor);
  assert (e_array->is_array);
  return true;
}

bool
btor_precond_cond_exp_dbg (Btor *btor,
                           BtorNode *e_cond,
                           BtorNode *e_if,
                           BtorNode *e_else)
{
  assert (btor);
  assert (e_cond);
  assert (e_if);
  assert (e_else);
  assert (!BTOR_REAL_ADDR_NODE (e_cond)->simplified);
  assert (btor_get_exp_width (btor, e_cond) == 1);

  BtorNode *real_e_if, *real_e_else;

  real_e_if   = BTOR_REAL_ADDR_NODE (e_if);
  real_e_else = BTOR_REAL_ADDR_NODE (e_else);

  assert (!real_e_if->simplified);
  assert (!real_e_else->simplified);
  assert (real_e_if->sort_id == real_e_else->sort_id);
  assert (BTOR_REAL_ADDR_NODE (e_cond)->btor == btor);
  assert (real_e_if->btor == btor);
  assert (real_e_else->btor == btor);
  assert (real_e_if->is_array == real_e_else->is_array);
  return true;
}

bool
btor_precond_apply_exp_dbg (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (BTOR_IS_REGULAR_NODE (fun));
  assert (BTOR_IS_REGULAR_NODE (args));
  assert (BTOR_IS_FUN_NODE (fun));
  assert (BTOR_IS_ARGS_NODE (args));
  assert (btor_get_domain_fun_sort (&btor->sorts_unique_table, fun->sort_id)
          == args->sort_id);
  return true;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

const char *const g_btor_op2str[BTOR_NUM_OPS_NODE] = {
    [BTOR_INVALID_NODE] = "invalid", [BTOR_BV_CONST_NODE] = "const",
    [BTOR_BV_VAR_NODE] = "var",      [BTOR_PARAM_NODE] = "param",
    [BTOR_SLICE_NODE] = "slice",     [BTOR_AND_NODE] = "and",
    [BTOR_BEQ_NODE] = "beq",         [BTOR_FEQ_NODE] = "feq",
    [BTOR_ADD_NODE] = "add",         [BTOR_MUL_NODE] = "mul",
    [BTOR_ULT_NODE] = "ult",         [BTOR_SLL_NODE] = "sll",
    [BTOR_SRL_NODE] = "srl",         [BTOR_UDIV_NODE] = "udiv",
    [BTOR_UREM_NODE] = "urem",       [BTOR_CONCAT_NODE] = "concat",
    [BTOR_APPLY_NODE] = "apply",     [BTOR_FORALL_NODE] = "forall",
    [BTOR_EXISTS_NODE] = "exists",   [BTOR_LAMBDA_NODE] = "lambda",
    [BTOR_BCOND_NODE] = "cond",      [BTOR_ARGS_NODE] = "args",
    [BTOR_UF_NODE] = "uf",           [BTOR_PROXY_NODE] = "proxy",
};

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
btor_new_exp_pair (Btor *btor, BtorNode *exp1, BtorNode *exp2)
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
btor_delete_exp_pair (Btor *btor, BtorNodePair *pair)
{
  assert (btor);
  assert (pair);
  btor_release_exp (btor, pair->exp1);
  btor_release_exp (btor, pair->exp2);
  BTOR_DELETE (btor->mm, pair);
}

unsigned int
btor_hash_exp_pair (BtorNodePair *pair)
{
  unsigned int result;
  assert (pair);
  result = (unsigned int) BTOR_REAL_ADDR_NODE (pair->exp1)->id;
  result += (unsigned int) BTOR_REAL_ADDR_NODE (pair->exp2)->id;
  result *= 7334147u;
  return result;
}

int
btor_compare_exp_pair (BtorNodePair *pair1, BtorNodePair *pair2)
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
  BTOR_ABORT (real_exp->refs == INT_MAX, "Node reference counter overflow");
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

  /* if a parameter is disconnected from a lambda we have to reset
   * 'lambda_exp' of the parameter in order to keep a valid state */
  if (BTOR_IS_BINDER_NODE (parent)
      && pos == 0
      /* if parent gets rebuilt via substitute_and_rebuild, it might
       * result in a new binder term, where the param is already reused.
       * if this is the case param is already bound by a different binder
       * and we are not allowed to reset param->binder to 0. */
      && btor_param_get_binder (parent->e[0]) == parent)
    btor_param_set_binder (parent->e[0], 0);

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
hash_binder_exp (Btor *btor, BtorNode *body)
{
  assert (btor);
  assert (body);

  int i;
  unsigned int hash = 0;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *marked;

  marked = btor_new_int_hash_table (btor->mm);
  BTOR_INIT_STACK (visit);
  BTOR_PUSH_STACK (btor->mm, visit, body);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (btor_contains_int_hash_table (marked, real_cur->id)) continue;

    if (!real_cur->parameterized)
    {
      hash += BTOR_GET_ID_NODE (cur);
      continue;
    }

    btor_add_int_hash_table (marked, real_cur->id);
    hash += BTOR_IS_INVERTED_NODE (cur) ? -real_cur->kind : real_cur->kind;
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (btor->mm, visit, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (btor->mm, visit);
  btor_delete_int_hash_table (marked);
  return hash;
}

static bool
is_sorted_bv_exp (Btor *btor, BtorNodeKind kind, BtorNode **e)
{
  if (!btor_get_opt (btor, BTOR_OPT_SORT_EXP)) return 1;
  if (!BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind)) return 1;
  if (e[0] == e[1]) return 1;
  if (BTOR_INVERT_NODE (e[0]) == e[1] && BTOR_IS_INVERTED_NODE (e[1])) return 1;
  return BTOR_REAL_ADDR_NODE (e[0])->id <= BTOR_REAL_ADDR_NODE (e[1])->id;
}

static void
sort_bv_exp (Btor *btor, BtorNodeKind kind, BtorNode **e)
{
  if (!is_sorted_bv_exp (btor, kind, e)) BTOR_SWAP (BtorNode *, e[0], e[1]);
}

static unsigned hash_primes[] = {333444569u, 76891121u, 456790003u};

#define NPRIMES ((int) (sizeof hash_primes / sizeof *hash_primes))

static inline unsigned int
hash_slice_exp (BtorNode *e, uint32_t upper, uint32_t lower)
{
  unsigned int hash;
  assert (upper >= lower);
  hash = hash_primes[0] * (unsigned int) BTOR_REAL_ADDR_NODE (e)->id;
  hash += hash_primes[1] * (unsigned int) upper;
  hash += hash_primes[2] * (unsigned int) lower;
  return hash;
}

static inline unsigned int
hash_bv_exp (Btor *btor, BtorNodeKind kind, int arity, BtorNode **e)
{
  unsigned int hash = 0;
  int i;
#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_SORT_EXP) > 0
      && BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind))
    assert (arity == 2), assert (BTOR_REAL_ADDR_NODE (e[0])->id
                                 <= BTOR_REAL_ADDR_NODE (e[1])->id);
#else
  (void) btor;
  (void) kind;
#endif
  assert (arity <= NPRIMES);
  for (i = 0; i < arity; i++)
    hash += hash_primes[i] * (unsigned int) BTOR_REAL_ADDR_NODE (e[i])->id;
  return hash;
}

/* Computes hash value of expresssion by children ids */
static unsigned int
compute_hash_exp (Btor *btor, BtorNode *exp, int table_size)
{
  assert (exp);
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!BTOR_IS_BV_VAR_NODE (exp));
  assert (!BTOR_IS_UF_NODE (exp));

  unsigned int hash = 0;

  if (BTOR_IS_BV_CONST_NODE (exp))
    hash = btor_hash_bv (btor_const_get_bits (exp));
  /* hash for lambdas is computed once during creation. afterwards, we always
   * have to use the saved hash value since hashing of lambdas requires all
   * parameterized nodes and their inputs (cf. hash_binder_exp), which may
   * change at some point. */
  else if (BTOR_IS_LAMBDA_NODE (exp))
    hash = btor_get_ptr_hash_table (exp->btor->lambdas, exp)->data.as_int;
  else if (BTOR_IS_QUANTIFIER_NODE (exp))
    hash = btor_get_ptr_hash_table (exp->btor->quantifiers, exp)->data.as_int;
  else if (exp->kind == BTOR_SLICE_NODE)
    hash = hash_slice_exp (
        exp->e[0], btor_slice_get_upper (exp), btor_slice_get_lower (exp));
  else
    hash = hash_bv_exp (btor, exp->kind, exp->arity, exp->e);
  hash &= table_size - 1;
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

  b = btor_get_ptr_hash_table (btor->parameterized, exp);
  assert (b);
  t = (BtorPtrHashTable *) b->data.as_ptr;
  assert (t->count > 0);
  assert (btor_get_ptr_hash_table (t, param));
  btor_remove_ptr_hash_table (t, param, 0, 0);
  btor_release_exp (btor, param);

  /* remove hash table if it is empty */
  if (t->count == 0)
  {
    btor_remove_ptr_hash_table (btor->parameterized, exp, 0, 0);
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

  b = btor_get_ptr_hash_table (btor->parameterized, exp);
  if (!b) return;

  t = (BtorPtrHashTable *) b->data.as_ptr;

  /* release params */
  btor_init_node_hash_table_iterator (&it, t);
  while (btor_has_next_node_hash_table_iterator (&it))
    btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
  btor_delete_ptr_hash_table (t);

  btor_remove_ptr_hash_table (btor->parameterized, exp, 0, 0);
}

static bool
is_parameterized (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorPtrHashTable *t;
  BtorPtrHashBucket *b;

  b = btor_get_ptr_hash_table (btor->parameterized, exp);
  if (b)
  {
    t = (BtorPtrHashTable *) b->data.as_ptr;
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

  b = btor_get_ptr_hash_table (btor->parameterized, parent);
  if (b)
  {
    assert (b->data.as_ptr);
    t = (BtorPtrHashTable *) b->data.as_ptr;
  }
  else
  {
    t = btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
    btor_add_ptr_hash_table (btor->parameterized, parent)->data.as_ptr = t;
  }

  if (BTOR_IS_PARAM_NODE (child))
  {
    if (!btor_get_ptr_hash_table (t, child))
      btor_add_ptr_hash_table (t, btor_copy_exp (btor, child));
  }
  else
  {
    btor_init_parameterized_iterator (&it, btor, child);
    while (btor_has_next_parameterized_iterator (&it))
    {
      param = btor_next_parameterized_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (param));
      assert (BTOR_IS_PARAM_NODE (param));
      if (!btor_get_ptr_hash_table (t, param))
        btor_add_ptr_hash_table (t, btor_copy_exp (btor, param));
      /* cleanup */
      else if (param->refs == 1)
      {
        btor_remove_ptr_hash_table (t, param, 0, 0);
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

  hash = compute_hash_exp (btor, exp, btor->nodes_unique_table.size);
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
      btor_remove_ptr_hash_table (btor->bv_vars, exp, 0, 0);
      break;
    case BTOR_LAMBDA_NODE:
      btor_remove_ptr_hash_table (btor->lambdas, exp, 0, 0);
      break;
    case BTOR_FORALL_NODE:
    case BTOR_EXISTS_NODE:
      btor_remove_ptr_hash_table (btor->quantifiers, exp, 0, 0);
      break;
    case BTOR_UF_NODE: btor_remove_ptr_hash_table (btor->ufs, exp, 0, 0); break;
    case BTOR_FEQ_NODE:
      btor_remove_ptr_hash_table (btor->feqs, exp, 0, 0);
      break;
    default: break;
  }

  if (!keep_symbol && btor_get_ptr_hash_table (btor->node2symbol, exp))
  {
    btor_remove_ptr_hash_table (btor->node2symbol, exp, 0, &data);
    if (data.as_str[0] != 0)
    {
      btor_remove_ptr_hash_table (btor->symbols, data.as_str, 0, 0);
      btor_freestr (btor->mm, data.as_str);
    }
  }

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
erase_local_data_exp (Btor *btor, BtorNode *exp, int free_sort)
{
  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_NODE (exp));

  assert (!exp->unique);
  assert (!exp->erased);
  assert (!exp->disconnected);
  assert (!BTOR_IS_INVALID_NODE (exp));

  BtorMemMgr *mm;
  BtorPtrHashTable *static_rho;
  BtorHashTableIterator it;

  mm = btor->mm;
  //  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  switch (exp->kind)
  {
    case BTOR_BV_CONST_NODE:
      btor_free_bv (mm, btor_const_get_bits (exp));
      if (btor_const_get_invbits (exp))
        btor_free_bv (mm, btor_const_get_invbits (exp));
      btor_const_set_bits (exp, 0);
      btor_const_set_invbits (exp, 0);
      break;
    case BTOR_LAMBDA_NODE:
      static_rho = btor_lambda_get_static_rho (exp);
      if (static_rho)
      {
        btor_init_node_hash_table_iterator (&it, static_rho);
        while (btor_has_next_node_hash_table_iterator (&it))
        {
          btor_release_exp (btor, it.bucket->data.as_ptr);
          btor_release_exp (btor, btor_next_node_hash_table_iterator (&it));
        }
        btor_delete_ptr_hash_table (static_rho);
        ((BtorLambdaNode *) exp)->static_rho = 0;
      }
      /* fall through intended */
    case BTOR_UF_NODE:
      if (exp->rho)
      {
        btor_delete_ptr_hash_table (exp->rho);
        exp->rho = 0;
      }
      break;
    case BTOR_BCOND_NODE:
      if (BTOR_IS_FUN_COND_NODE (exp) && exp->rho)
      {
        btor_delete_ptr_hash_table (exp->rho);
        exp->rho = 0;
      }
      break;
    default: break;
  }

  if (free_sort)
  {
    assert (exp->sort_id);
    btor_release_sort (&btor->sorts_unique_table, exp->sort_id);
    exp->sort_id = 0;
  }

  if (exp->av)
  {
    btor_release_delete_aigvec (btor->avmgr, exp->av);
    exp->av = 0;
  }
  exp->erased = 1;
}

#ifndef NDEBUG
static bool
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

  if (BTOR_IS_BV_CONST_NODE (exp))
  {
    btor_free_bv (btor->mm, btor_const_get_bits (exp));
    if (btor_const_get_invbits (exp))
      btor_free_bv (btor->mm, btor_const_get_invbits (exp));
  }
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

      remove_from_nodes_unique_table_exp (btor, cur);
      erase_local_data_exp (btor, cur, 1);

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

  remove_from_nodes_unique_table_exp (btor, exp);
  /* also updates op stats */
  erase_local_data_exp (btor, exp, 0);
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

  /* set specific flags */

  /* set parent parameterized if child is parameterized */
  if (!BTOR_IS_BINDER_NODE (parent)
      && BTOR_REAL_ADDR_NODE (child)->parameterized)
    parent->parameterized = 1;

  // TODO (ma): why don't we bind params here?

  if (BTOR_IS_FUN_COND_NODE (parent) && BTOR_REAL_ADDR_NODE (child)->is_array)
    parent->is_array = 1;

  if (BTOR_REAL_ADDR_NODE (child)->lambda_below) parent->lambda_below = 1;

  if (BTOR_REAL_ADDR_NODE (child)->apply_below) parent->apply_below = 1;

  if (BTOR_REAL_ADDR_NODE (child)->parameterized)
    update_parameterized (btor, parent, child);

  BTOR_REAL_ADDR_NODE (child)->parents++;
  inc_exp_ref_counter (btor, child);

  /* update parent lists */

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
  BTOR_ABORT (id == INT_MAX, "expression id overflow");
  exp->id = id;
  BTOR_PUSH_STACK (btor->mm, btor->nodes_id_table, exp);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == exp->id + 1);
  assert (BTOR_PEEK_STACK (btor->nodes_id_table, exp->id) == exp);
  btor->stats.node_bytes_alloc += exp->bytes;

  if (BTOR_IS_APPLY_NODE (exp)) exp->apply_below = 1;
}

static BtorNode *
new_const_exp_node (Btor *btor, const BtorBitVector *bits)
{
  assert (btor);
  assert (bits);

  BtorBVConstNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_BV_CONST_NODE);
  exp->bytes   = sizeof *exp;
  exp->sort_id = btor_bitvec_sort (&btor->sorts_unique_table, bits->width);
  setup_node_and_add_to_id_table (btor, exp);
  btor_const_set_bits ((BtorNode *) exp, btor_copy_bv (btor->mm, bits));
  return (BtorNode *) exp;
}

static BtorNode *
new_slice_exp_node (Btor *btor, BtorNode *e0, uint32_t upper, uint32_t lower)
{
  assert (btor);
  assert (e0);
  assert (btor == BTOR_REAL_ADDR_NODE (e0)->btor);
  assert (upper < btor_get_exp_width (btor, e0));
  assert (upper >= lower);

  BtorSliceNode *exp = 0;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_SLICE_NODE);
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  exp->upper = upper;
  exp->lower = lower;
  exp->sort_id =
      btor_bitvec_sort (&btor->sorts_unique_table, upper - lower + 1);
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, (BtorNode *) exp, e0, 0);
  return (BtorNode *) exp;
}

static BtorNode *
new_lambda_exp_node (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (e_param);
  assert (BTOR_IS_REGULAR_NODE (e_param));
  assert (BTOR_IS_PARAM_NODE (e_param));
  assert (!btor_param_is_bound (e_param));
  assert (e_exp);
  assert (btor == e_param->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_exp)->btor);

  BtorSortId s, domain, codomain;
  BtorSortIdStack param_sorts;
  BtorSortUniqueTable *sorts;
  BtorLambdaNode *lambda_exp;
  BtorTupleSortIterator it;

  BTOR_INIT_STACK (param_sorts);

  sorts = &btor->sorts_unique_table;
  BTOR_CNEW (btor->mm, lambda_exp);
  set_kind (btor, (BtorNode *) lambda_exp, BTOR_LAMBDA_NODE);
  lambda_exp->bytes        = sizeof *lambda_exp;
  lambda_exp->arity        = 2;
  lambda_exp->lambda_below = 1;
  setup_node_and_add_to_id_table (btor, (BtorNode *) lambda_exp);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_param, 0);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_exp, 1);

  BTOR_PUSH_STACK (btor->mm, param_sorts, e_param->sort_id);
  /* curried lambdas (functions) */
  if (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (e_exp)))
  {
    btor_binder_set_body (
        (BtorNode *) lambda_exp,
        btor_simplify_exp (btor, btor_binder_get_body (e_exp)));
    btor_init_tuple_sort_iterator (
        &it, sorts, btor_get_domain_fun_sort (sorts, e_exp->sort_id));
    while (btor_has_next_tuple_sort_iterator (&it))
    {
      s = btor_next_tuple_sort_iterator (&it);
      BTOR_PUSH_STACK (btor->mm, param_sorts, s);
    }
  }
  else
    btor_binder_set_body ((BtorNode *) lambda_exp, e_exp);

  domain = btor_tuple_sort (
      sorts, param_sorts.start, BTOR_COUNT_STACK (param_sorts));
  codomain            = BTOR_REAL_ADDR_NODE (lambda_exp->body)->sort_id;
  lambda_exp->sort_id = btor_fun_sort (sorts, domain, codomain);

  btor_release_sort (sorts, domain);
  BTOR_RELEASE_STACK (btor->mm, param_sorts);

  /* check if 'lambda' is parameterized, i.e. if it contains params that are not
   * bound by 'lambda' */
  remove_param_parameterized (btor, (BtorNode *) lambda_exp, e_param);
  if (is_parameterized (btor, (BtorNode *) lambda_exp))
    lambda_exp->parameterized = 1;

  assert (!BTOR_REAL_ADDR_NODE (lambda_exp->body)->simplified);
  assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (lambda_exp->body)));
  assert (!btor_get_ptr_hash_table (btor->lambdas, lambda_exp));
  (void) btor_add_ptr_hash_table (btor->lambdas, lambda_exp);
  /* set lambda expression of parameter */
  btor_param_set_binder (e_param, (BtorNode *) lambda_exp);
  return (BtorNode *) lambda_exp;
}

static BtorNode *
new_args_exp_node (Btor *btor, int arity, BtorNode **e)
{
  assert (btor);
  assert (arity > 0);
  assert (arity <= 3);
  assert (e);

  int i;
  BtorArgsNode *exp;
  BtorSortIdStack sorts;
  BtorTupleSortIterator it;
#ifndef NDEBUG
  for (i = 0; i < arity; i++) assert (e[i]);
#endif

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_ARGS_NODE);
  exp->bytes = sizeof (*exp);
  exp->arity = arity;
  setup_node_and_add_to_id_table (btor, exp);

  for (i = 0; i < arity; i++)
    connect_child_exp (btor, (BtorNode *) exp, e[i], i);

  /* create tuple sort for argument node */
  BTOR_INIT_STACK (sorts);
  for (i = 0; i < arity; i++)
  {
    if (BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (e[i])))
    {
      assert (i == 2);
      assert (BTOR_IS_REGULAR_NODE (e[i]));
      btor_init_tuple_sort_iterator (
          &it, &btor->sorts_unique_table, e[i]->sort_id);
      while (btor_has_next_tuple_sort_iterator (&it))
        BTOR_PUSH_STACK (btor->mm, sorts, btor_next_tuple_sort_iterator (&it));
    }
    else
      BTOR_PUSH_STACK (btor->mm, sorts, BTOR_REAL_ADDR_NODE (e[i])->sort_id);
  }
  exp->sort_id = btor_tuple_sort (
      &btor->sorts_unique_table, sorts.start, BTOR_COUNT_STACK (sorts));
  BTOR_RELEASE_STACK (btor->mm, sorts);
  return (BtorNode *) exp;
}

#if 0
static void
mark_cone_quantified (Btor * btor, BtorNode * param)
{
  assert (btor);
  assert (param);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  BtorNode *cur;
  BtorNodeIterator it;
  BtorNodePtrStack stack;

  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (btor->mm, stack, param);

  while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_POP_STACK (stack);
      assert (BTOR_IS_REGULAR_NODE (cur));

      if (cur->quantified)
	continue;

      if (!cur->parameterized)
	{
	  assert (BTOR_IS_FORALL_NODE (cur) || BTOR_IS_EXISTS_NODE (cur));
	  continue;
	}

      assert (cur->parameterized); 
      cur->quantified = 1;

      init_full_parent_iterator (&it, cur);
      while (has_next_parent_full_parent_iterator (&it))
	BTOR_PUSH_STACK (btor->mm, stack,
			 next_parent_full_parent_iterator (&it));
    }
  BTOR_RELEASE_STACK (btor->mm, stack);
}
#endif

BtorNode *
btor_invert_quantifier (Btor *btor, BtorNode *quantifier)
{
  assert (BTOR_IS_REGULAR_NODE (quantifier));
  assert (BTOR_IS_QUANTIFIER_NODE (quantifier));

  size_t len;
  char *sym, *buf;
  BtorNode *cur, *param, *new_param, *body, *result, *tmp;
  BtorNodeIterator it;
  BtorNodeMap *param_substs;
  BtorNodePtrStack params;
  BtorMemMgr *mm;

  mm = btor->mm;
  BTOR_INIT_STACK (params);
  param_substs = btor_new_node_map (btor);
  btor_init_binder_iterator (&it, quantifier);
  while (btor_has_next_binder_iterator (&it))
  {
    cur = btor_next_binder_iterator (&it);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_QUANTIFIER_NODE (cur));
    param = cur->e[0];
    sym   = btor_get_symbol_exp (btor, param);
    assert (sym);
    len = strlen (sym) + 5;
    buf = btor_malloc (mm, len);
    sprintf (buf, "%s_inv", sym);
    new_param = btor_param_exp (btor, btor_get_exp_width (btor, param), buf);
    btor_free (mm, buf, len);
    btor_map_node (param_substs, param, new_param);
    BTOR_PUSH_STACK (mm, params, cur);
    BTOR_PUSH_STACK (mm, params, new_param);
    if (btor_get_ptr_hash_table (btor->inputs, param))
    {
      btor_remove_ptr_hash_table (btor->inputs, param, 0, 0);
      btor_release_exp (btor, param);
    }
  }

  body   = btor_binder_get_body (quantifier);
  result = btor_substitute_terms (btor, body, param_substs);
  result = BTOR_INVERT_NODE (result); /* push negation down to body */
  btor_delete_node_map (param_substs);

  /* create inverted quantifier prefix */
  while (!BTOR_EMPTY_STACK (params))
  {
    param = BTOR_POP_STACK (params);
    cur   = BTOR_POP_STACK (params);
    assert (BTOR_IS_REGULAR_NODE (param));
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_PARAM_NODE (param));
    assert (BTOR_IS_QUANTIFIER_NODE (cur));
    if (BTOR_IS_FORALL_NODE (cur))
    {
      tmp = btor_exists_exp (btor, param, result);
      /* add existential param to inputs in order to correctly print
       * models.  do not use param here as tmp might be a cached
       * existential quantifier */
      btor_add_ptr_hash_table (btor->inputs, btor_copy_exp (btor, tmp->e[0]));
    }
    else
      tmp = btor_forall_exp (btor, param, result);
    btor_release_exp (btor, result);
    btor_release_exp (btor, param);
    result = tmp;
  }
  BTOR_RELEASE_STACK (mm, params);

  assert (BTOR_IS_REGULAR_NODE (result));
  assert (BTOR_IS_QUANTIFIER_NODE (result));
  return result;
}

static BtorNode *
new_quantifier_exp_node (Btor *btor,
                         BtorNodeKind kind,
                         BtorNode *param,
                         BtorNode *body)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));
  assert (!btor_param_is_bound (param));
  assert (btor_is_bool_sort (&btor->sorts_unique_table,
                             BTOR_REAL_ADDR_NODE (body)->sort_id));
  assert (btor == param->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (body)->btor);

  BtorBinderNode *res;

  BTOR_CNEW (btor->mm, res);
  set_kind (btor, (BtorNode *) res, kind);
  res->bytes   = sizeof *res;
  res->arity   = 2;
  res->sort_id = btor_copy_sort (&btor->sorts_unique_table,
                                 BTOR_REAL_ADDR_NODE (body)->sort_id);
  setup_node_and_add_to_id_table (btor, (BtorNode *) res);
  connect_child_exp (btor, (BtorNode *) res, param, 0);
  connect_child_exp (btor, (BtorNode *) res, body, 1);

  /* curried (non-inverted) quantifiers */
  if (!BTOR_IS_INVERTED_NODE (body) && BTOR_IS_QUANTIFIER_NODE (body))
    res->body = btor_simplify_exp (btor, btor_binder_get_body (body));
  else
    res->body = body;

  /* check if 'res' is parameterized, i.e. if it contains params that are not
   * bound by 'res' */
  remove_param_parameterized (btor, (BtorNode *) res, param);
  if (is_parameterized (btor, (BtorNode *) res)) res->parameterized = 1;

  assert (!BTOR_REAL_ADDR_NODE (res->body)->simplified);
  assert (!BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (res->body)));
  btor_param_set_binder (param, (BtorNode *) res);
  //  mark_cone_quantified (btor, param);
  assert (!btor_get_ptr_hash_table (btor->quantifiers, res));
  (void) btor_add_ptr_hash_table (btor->quantifiers, res);
  return (BtorNode *) res;
}

static BtorNode *
new_node (Btor *btor, BtorNodeKind kind, int arity, BtorNode **e)
{
  assert (btor);
  assert (arity > 0);
  assert (arity <= 3);
  assert (BTOR_IS_BINARY_NODE_KIND (kind) || BTOR_IS_TERNARY_NODE_KIND (kind));
  assert (e);

#ifndef NDEBUG
  if (btor_get_opt (btor, BTOR_OPT_SORT_EXP) > 0
      && BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind))
    assert (arity == 2), assert (BTOR_REAL_ADDR_NODE (e[0])->id
                                 <= BTOR_REAL_ADDR_NODE (e[1])->id);
#endif

  int i;
  BtorBVNode *exp;
  BtorSortUniqueTable *sorts;
  BtorSortId sort;

  sorts = &btor->sorts_unique_table;
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
  setup_node_and_add_to_id_table (btor, exp);

  switch (kind)
  {
    case BTOR_BCOND_NODE:
      sort = btor_copy_sort (sorts, BTOR_REAL_ADDR_NODE (e[1])->sort_id);
      break;

    case BTOR_CONCAT_NODE:
      sort = btor_bitvec_sort (
          sorts,
          btor_get_exp_width (btor, e[0]) + btor_get_exp_width (btor, e[1]));
      break;

    case BTOR_FEQ_NODE:
    case BTOR_BEQ_NODE:
    case BTOR_ULT_NODE: sort = btor_bool_sort (sorts); break;

    case BTOR_APPLY_NODE:
      sort = btor_copy_sort (sorts,
                             btor_get_codomain_fun_sort (sorts, e[0]->sort_id));
      break;

    default:
      assert (kind == BTOR_AND_NODE || kind == BTOR_ADD_NODE
              || kind == BTOR_MUL_NODE || kind == BTOR_SLL_NODE
              || kind == BTOR_SRL_NODE || kind == BTOR_UDIV_NODE
              || kind == BTOR_UREM_NODE);
      sort = btor_copy_sort (sorts, BTOR_REAL_ADDR_NODE (e[0])->sort_id);
  }

  exp->sort_id = sort;

  for (i = 0; i < arity; i++)
    connect_child_exp (btor, (BtorNode *) exp, e[i], i);

  if (kind == BTOR_FEQ_NODE)
  {
    assert (!btor_get_ptr_hash_table (btor->feqs, exp));
    btor_add_ptr_hash_table (btor->feqs, exp)->data.as_int = 0;
  }

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
  BtorNode *a = BTOR_REAL_ADDR_NODE (*(BtorNode **) p);
  BtorNode *b = BTOR_REAL_ADDR_NODE (*(BtorNode **) q);
  return b->id - a->id;
}

int
btor_cmp_exp_by_id_qsort_asc (const void *p, const void *q)
{
  BtorNode *a = BTOR_REAL_ADDR_NODE (*(BtorNode **) p);
  BtorNode *b = BTOR_REAL_ADDR_NODE (*(BtorNode **) q);
  return a->id - b->id;
}

/* Search for constant expression in hash table. Returns 0 if not found. */
static BtorNode **
find_const_exp (Btor *btor, BtorBitVector *bits)
{
  assert (btor);
  assert (bits);

  BtorNode *cur, **result;
  unsigned int hash;

  hash = btor_hash_bv (bits);
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (BTOR_IS_BV_CONST_NODE (cur)
        && btor_get_exp_width (btor, cur) == bits->width
        && !btor_compare_bv (btor_const_get_bits (cur), bits))
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
find_slice_exp (Btor *btor, BtorNode *e0, uint32_t upper, uint32_t lower)
{
  assert (btor);
  assert (e0);
  assert (upper >= lower);

  BtorNode *cur, **result;
  unsigned int hash;

  hash = hash_slice_exp (e0, upper, lower);
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->kind == BTOR_SLICE_NODE && cur->e[0] == e0
        && btor_slice_get_upper (cur) == upper
        && btor_slice_get_lower (cur) == lower)
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

static BtorNode **
find_bv_exp (Btor *btor, BtorNodeKind kind, int arity, BtorNode **e)
{
  bool equal;
  int i;
  unsigned int hash;
  BtorNode *cur, **result;

  assert (kind != BTOR_SLICE_NODE);
  assert (kind != BTOR_BV_CONST_NODE);

  sort_bv_exp (btor, kind, e);
  hash = hash_bv_exp (btor, kind, arity, e);
  hash &= btor->nodes_unique_table.size - 1;

  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->kind == kind && cur->arity == arity)
    {
      equal = true;
      /* special case for bv eq; (= (bvnot a) b) == (= a (bvnot b)) */
      if (kind == BTOR_BEQ_NODE && cur->e[0] == BTOR_INVERT_NODE (e[0])
          && cur->e[1] == BTOR_INVERT_NODE (e[1]))
        break;
      for (i = 0; i < arity && equal; i++)
        if (cur->e[i] != e[i]) equal = false;
      if (equal) break;
#ifndef NDEBUG
      if (btor_get_opt (btor, BTOR_OPT_SORT_EXP) > 0
          && BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind))
        assert (arity == 2),
            assert (e[0] == e[1] || BTOR_INVERT_NODE (e[0]) == e[1]
                    || !(cur->e[0] == e[1] && cur->e[1] == e[0]));
#endif
    }
    result = &(cur->next);
    cur    = *result;
  }
  return result;
}

static int compare_binder_exp (Btor *btor,
                               BtorNode *param,
                               BtorNode *body,
                               BtorNode *binder);

static BtorNode **
find_binder_exp (Btor *btor,
                 BtorNodeKind kind,
                 BtorNode *param,
                 BtorNode *body,
                 unsigned int *binder_hash,
                 bool compare_binders)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  BtorNode *cur, **result;
  unsigned int hash;

  hash = hash_binder_exp (btor, body);
  if (binder_hash) *binder_hash = hash;
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->kind == kind
        && ((param == cur->e[0] && body == cur->e[1])
            || ((!cur->parameterized && compare_binders
                 && compare_binder_exp (btor, param, body, cur)))))
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  assert (!*result || BTOR_IS_BINDER_NODE (BTOR_REAL_ADDR_NODE (*result)));
  return result;
}

static int
compare_binder_exp (Btor *btor,
                    BtorNode *param,
                    BtorNode *body,
                    BtorNode *binder)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));
  assert (BTOR_IS_REGULAR_NODE (binder));
  assert (BTOR_IS_BINDER_NODE (binder));
  assert (!binder->parameterized);

  int i, equal = 0;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, **result, *subst_param, **e, *b0, *b1;
  BtorPtrHashTable *cache, *param_map;
  BtorPtrHashBucket *b, *bb;
  BtorNodePtrStack stack, args;
  BtorNodeIterator it, iit;

  mm          = btor->mm;
  subst_param = binder->e[0];

  if (subst_param->sort_id != param->sort_id
      || BTOR_REAL_ADDR_NODE (body)->sort_id
             != BTOR_REAL_ADDR_NODE (binder->e[1])->sort_id)
    return 0;

  cache = btor_new_ptr_hash_table (mm, 0, 0);

  /* create param map */
  param_map = btor_new_ptr_hash_table (mm, 0, 0);
  btor_add_ptr_hash_table (param_map, param)->data.as_ptr = subst_param;

  if (BTOR_IS_BINDER_NODE (BTOR_REAL_ADDR_NODE (body))
      && BTOR_IS_BINDER_NODE (BTOR_REAL_ADDR_NODE (binder->e[1])))
  {
    btor_init_binder_iterator (&it, body);
    btor_init_binder_iterator (&iit, binder->e[1]);
    while (btor_has_next_binder_iterator (&it))
    {
      if (!btor_has_next_binder_iterator (&iit)) goto NOT_EQUAL;

      b0 = btor_next_binder_iterator (&it);
      b1 = btor_next_binder_iterator (&iit);

      if (b0->sort_id != b1->sort_id || b0->kind != b1->kind) goto NOT_EQUAL;

      param       = b0->e[0];
      subst_param = b1->e[0];
      assert (BTOR_IS_REGULAR_NODE (param));
      assert (BTOR_IS_REGULAR_NODE (subst_param));
      assert (BTOR_IS_PARAM_NODE (param));
      assert (BTOR_IS_PARAM_NODE (subst_param));

      if (param->sort_id != subst_param->sort_id) goto NOT_EQUAL;

      btor_add_ptr_hash_table (param_map, param)->data.as_ptr = subst_param;
    }
  }
  else if (BTOR_IS_BINDER_NODE (BTOR_REAL_ADDR_NODE (body))
           || BTOR_IS_BINDER_NODE (BTOR_REAL_ADDR_NODE (binder->e[1])))
    goto NOT_EQUAL;

  BTOR_INIT_STACK (args);
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, body);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = BTOR_REAL_ADDR_NODE (cur);

    if (!real_cur->parameterized)
    {
      BTOR_PUSH_STACK (mm, args, cur);
      continue;
    }

    b = btor_get_ptr_hash_table (cache, real_cur);

    if (!b)
    {
      b = btor_add_ptr_hash_table (cache, real_cur);
      BTOR_PUSH_STACK (mm, stack, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, real_cur->e[i]);
    }
    else if (!b->data.as_ptr)
    {
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (BTOR_IS_SLICE_NODE (real_cur))
      {
        result = find_slice_exp (btor,
                                 e[0],
                                 btor_slice_get_upper (real_cur),
                                 btor_slice_get_lower (real_cur));
      }
      else if (BTOR_IS_BINDER_NODE (real_cur))
      {
        result = find_binder_exp (btor, real_cur->kind, e[0], e[1], 0, false);
      }
      else if (BTOR_IS_PARAM_NODE (real_cur))
      {
        if ((bb = btor_get_ptr_hash_table (param_map, real_cur)))
          result = (BtorNode **) &bb->data.as_ptr;
        else
          result = &real_cur;
      }
      else
      {
        assert (!BTOR_IS_BINDER_NODE (real_cur));
        result = find_bv_exp (btor, real_cur->kind, real_cur->arity, e);
      }

      if (!*result)
      {
        BTOR_RESET_STACK (args);
        break;
      }

      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, *result));
      b->data.as_ptr = *result;
    }
    else
    {
      assert (b->data.as_ptr);
      BTOR_PUSH_STACK (mm, args, BTOR_COND_INVERT_NODE (cur, b->data.as_ptr));
    }
  }
  assert (BTOR_COUNT_STACK (args) <= 1);

  if (!BTOR_EMPTY_STACK (args)) equal = BTOR_TOP_STACK (args) == binder->e[1];

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, args);
NOT_EQUAL:
  btor_delete_ptr_hash_table (cache);
  btor_delete_ptr_hash_table (param_map);
  return equal;
}

static BtorNode **
find_exp (Btor *btor,
          BtorNodeKind kind,
          int arity,
          BtorNode **e,
          unsigned int *binder_hash)
{
  assert (btor);
  assert (arity > 0);
  assert (e);

#ifndef NDEBUG
  int i;
  for (i = 0; i < arity; i++) assert (e[i]);
#endif

  if (kind == BTOR_LAMBDA_NODE || kind == BTOR_FORALL_NODE
      || kind == BTOR_EXISTS_NODE)
    return find_binder_exp (btor, kind, e[0], e[1], binder_hash, true);
  else if (binder_hash)
    *binder_hash = 0;

  return find_bv_exp (btor, kind, arity, e);
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
      hash             = compute_hash_exp (btor, cur, new_size);
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
btor_const_exp (Btor *btor, BtorBitVector *bits)
{
  assert (btor);
  assert (bits);

  bool inv;
  BtorBitVector *lookupbits;
  BtorNode **lookup;

  inv        = false;
  lookupbits = bits;

  /* normalize constants, constans are always even */
  if (btor_get_bit_bv (bits, 0))
  {
    lookupbits = btor_not_bv (btor->mm, bits);
    inv        = true;
  }

  lookup = find_const_exp (btor, lookupbits);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_const_exp (btor, lookupbits);
    }
    *lookup = new_const_exp_node (btor, lookupbits);
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements += 1;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);

  assert (BTOR_IS_REGULAR_NODE (*lookup));

  if (inv)
  {
    btor_free_bv (btor->mm, lookupbits);
    return BTOR_INVERT_NODE (*lookup);
  }
  return *lookup;
}

static BtorNode *
int_min_exp (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv = btor_new_bv (btor->mm, width);
  btor_set_bit_bv (bv, bv->width - 1, 1);
  result = btor_const_exp (btor, bv);
  btor_free_bv (btor->mm, bv);
  return result;
}

BtorNode *
btor_zero_exp (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv     = btor_new_bv (btor->mm, width);
  result = btor_const_exp (btor, bv);
  btor_free_bv (btor->mm, bv);
  return result;
}

BtorNode *
btor_false_exp (Btor *btor)
{
  assert (btor);
  return btor_zero_exp (btor, 1);
}

BtorNode *
btor_ones_exp (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv     = btor_ones_bv (btor->mm, width);
  result = btor_const_exp (btor, bv);
  btor_free_bv (btor->mm, bv);
  return result;
}

BtorNode *
btor_one_exp (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv     = btor_one_bv (btor->mm, width);
  result = btor_const_exp (btor, bv);
  btor_free_bv (btor->mm, bv);
  return result;
}

BtorNode *
btor_int_exp (Btor *btor, int i, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv     = btor_uint64_to_bv (btor->mm, i, width);
  result = btor_const_exp (btor, bv);
  btor_free_bv (btor->mm, bv);
  return result;
}

BtorNode *
btor_unsigned_exp (Btor *btor, unsigned int u, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorBitVector *bv;
  BtorNode *result;

  bv     = btor_uint64_to_bv (btor->mm, u, width);
  result = btor_const_exp (btor, bv);
  btor_free_bv (btor->mm, bv);
  return result;
}

BtorNode *
btor_true_exp (Btor *btor)
{
  assert (btor);
  return btor_one_exp (btor, 1);
}

BtorNode *
btor_var_exp (Btor *btor, uint32_t width, const char *symbol)
{
  assert (btor);
  assert (width > 0);
  assert (!symbol || !btor_get_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorBVVarNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_BV_VAR_NODE);
  exp->bytes = sizeof *exp;
  setup_node_and_add_to_id_table (btor, exp);
  exp->sort_id = btor_bitvec_sort (&btor->sorts_unique_table, width);
  (void) btor_add_ptr_hash_table (btor->bv_vars, exp);
  if (symbol) btor_set_symbol_exp (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

BtorNode *
btor_param_exp (Btor *btor, uint32_t width, const char *symbol)
{
  assert (btor);
  assert (width > 0);
  assert (!symbol || !btor_get_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorParamNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_PARAM_NODE);
  exp->bytes         = sizeof *exp;
  exp->parameterized = 1;
  exp->sort_id       = btor_bitvec_sort (&btor->sorts_unique_table, width);
  setup_node_and_add_to_id_table (btor, exp);
  if (symbol) btor_set_symbol_exp (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

BtorNode *
btor_array_exp (Btor *btor,
                uint32_t elem_width,
                uint32_t index_width,
                const char *symbol)
{
  assert (btor);
  assert (elem_width > 0);
  assert (index_width > 0);

  BtorNode *exp;
  BtorSortId index_sort, elem_sort, sort, tup;

  index_sort = btor_bitvec_sort (&btor->sorts_unique_table, index_width);
  elem_sort  = btor_bitvec_sort (&btor->sorts_unique_table, elem_width);
  tup        = btor_tuple_sort (&btor->sorts_unique_table, &index_sort, 1);
  sort       = btor_fun_sort (&btor->sorts_unique_table, tup, elem_sort);

  exp           = btor_uf_exp (btor, sort, symbol);
  exp->is_array = 1;
  btor_release_sort (&btor->sorts_unique_table, index_sort);
  btor_release_sort (&btor->sorts_unique_table, elem_sort);
  btor_release_sort (&btor->sorts_unique_table, sort);
  btor_release_sort (&btor->sorts_unique_table, tup);

  return (BtorNode *) exp;
}

BtorNode *
btor_uf_exp (Btor *btor, BtorSortId sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (!symbol || !btor_get_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorUFNode *exp;
  BtorSortUniqueTable *sorts;

  sorts = &btor->sorts_unique_table;
  assert (btor_is_fun_sort (sorts, sort));
  assert (
      btor_is_bitvec_sort (sorts, btor_get_codomain_fun_sort (sorts, sort))
      || btor_is_bool_sort (sorts, btor_get_codomain_fun_sort (sorts, sort)));

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_UF_NODE);
  exp->bytes   = sizeof (*exp);
  exp->sort_id = btor_copy_sort (sorts, sort);
  setup_node_and_add_to_id_table (btor, exp);
  (void) btor_add_ptr_hash_table (btor->ufs, exp);
  if (symbol) btor_set_symbol_exp (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

static BtorNode *
unary_exp_slice_exp (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  int inv;
  BtorNode **lookup, *q = 0;

  exp = btor_simplify_exp (btor, exp);

  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (upper >= lower);
  assert (upper < btor_get_exp_width (btor, exp));

  if (BTOR_IS_INVERTED_NODE (exp)
      && BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (exp)))
  {
    q   = btor_invert_quantifier (btor, BTOR_REAL_ADDR_NODE (exp));
    exp = q;
  }

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0
      && BTOR_IS_INVERTED_NODE (exp))
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
  if (q) btor_release_exp (btor, q);
  if (inv) return BTOR_INVERT_NODE (*lookup);
  return *lookup;
}

BtorNode *
btor_slice_exp_node (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));
  return unary_exp_slice_exp (btor, exp, upper, lower);
}

static BtorNode *
create_exp (Btor *btor, BtorNodeKind kind, uint32_t arity, BtorNode **e)
{
  assert (btor);
  assert (kind);
  assert (arity > 0);
  assert (arity <= 3);
  assert (e);

  uint32_t i;
  unsigned int binder_hash;
  BtorNode **lookup, *simp_e[3], *quant_e[3];

  for (i = 0; i < arity; i++)
  {
    assert (BTOR_REAL_ADDR_NODE (e[i])->btor == btor);
    simp_e[i]  = btor_simplify_exp (btor, e[i]);
    quant_e[i] = 0;

    if (BTOR_IS_INVERTED_NODE (simp_e[i])
        && BTOR_IS_QUANTIFIER_NODE (BTOR_REAL_ADDR_NODE (simp_e[i])))
    {
      simp_e[i] =
          btor_invert_quantifier (btor, BTOR_REAL_ADDR_NODE (simp_e[i]));
      quant_e[i] = simp_e[i];
    }
  }

  lookup = find_exp (btor, kind, arity, simp_e, &binder_hash);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_exp (btor, kind, arity, simp_e, &binder_hash);
    }

    switch (kind)
    {
      case BTOR_LAMBDA_NODE:
        assert (arity == 2);
        *lookup = new_lambda_exp_node (btor, simp_e[0], simp_e[1]);
        btor_get_ptr_hash_table (btor->lambdas, *lookup)->data.as_int =
            binder_hash;
        break;
      case BTOR_FORALL_NODE:
      case BTOR_EXISTS_NODE:
        assert (arity == 2);
        *lookup = new_quantifier_exp_node (btor, kind, e[0], e[1]);
        btor_get_ptr_hash_table (btor->quantifiers, *lookup)->data.as_int =
            binder_hash;
        break;
      case BTOR_ARGS_NODE:
        *lookup = new_args_exp_node (btor, arity, simp_e);
        break;
      default: *lookup = new_node (btor, kind, arity, simp_e);
    }
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_NODE (*lookup));
  for (i = 0; i < arity; i++)
    if (quant_e[i]) btor_release_exp (btor, quant_e[i]);
  //  printf ("created: %s\n", node2string (*lookup));
  return *lookup;
}

BtorNode *
btor_and_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_AND_NODE, 2, e);
}

BtorNode *
btor_eq_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  BtorNodeKind kind;

  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e[0], e[1]));
  if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e[0])))
    kind = BTOR_FEQ_NODE;
  else
    kind = BTOR_BEQ_NODE;
  return create_exp (btor, kind, 2, e);
}

BtorNode *
btor_add_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_ADD_NODE, 2, e);
}

BtorNode *
btor_mul_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_MUL_NODE, 2, e);
}

BtorNode *
btor_ult_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_ULT_NODE, 2, e);
}

BtorNode *
btor_sll_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_SLL_NODE, 2, e);
}

BtorNode *
btor_srl_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_SRL_NODE, 2, e);
}

BtorNode *
btor_udiv_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_UDIV_NODE, 2, e);
}

BtorNode *
btor_urem_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_UREM_NODE, 2, e);
}

BtorNode *
btor_concat_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e[0], e[1]));
  return create_exp (btor, BTOR_CONCAT_NODE, 2, e);
}

BtorNode *
btor_lambda_exp_node (Btor *btor, BtorNode *param, BtorNode *body)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, param);
  e[1] = btor_simplify_exp (btor, body);
  return create_exp (btor, BTOR_LAMBDA_NODE, 2, e);
}

BtorNode *
btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (e_param));
  assert (btor == e_param->btor);
  assert (BTOR_IS_PARAM_NODE (e_param));
  assert (!BTOR_REAL_ADDR_NODE (e_param)->simplified);
  assert (e_exp);
  assert (btor == BTOR_REAL_ADDR_NODE (e_exp)->btor);

  BtorNode *result;
  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_LAMBDA_NODE, e_param, e_exp);
  else
    result = btor_lambda_exp_node (btor, e_param, e_exp);
  assert (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (result)));
  return result;
}

static BtorNode *
quantifier_exp_node (Btor *btor,
                     BtorNodeKind kind,
                     BtorNode *param,
                     BtorNode *body)
{
  assert (btor);
  assert (kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE);
  assert (param);

  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, param);
  e[1] = btor_simplify_exp (btor, body);

  assert (BTOR_IS_REGULAR_NODE (e[0]));
  assert (BTOR_IS_PARAM_NODE (e[0]));
  assert (e[1]);
  assert (btor_is_bool_sort (&btor->sorts_unique_table,
                             BTOR_REAL_ADDR_NODE (e[1])->sort_id));
  return create_exp (btor, kind, 2, e);
}

static BtorNode *
quantifier_exp (Btor *btor, BtorNodeKind kind, BtorNode *param, BtorNode *body)
{
  assert (btor);
  assert (kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE);
  assert (param);

  param = btor_simplify_exp (btor, param);
  body  = btor_simplify_exp (btor, body);

  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));
  assert (body);
  assert (btor_is_bool_sort (&btor->sorts_unique_table,
                             BTOR_REAL_ADDR_NODE (body)->sort_id));
  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_binary_exp (btor, kind, param, body);
  return quantifier_exp_node (btor, kind, param, body);
}

static BtorNode *
quantifier_n_exp (
    Btor *btor, BtorNodeKind kind, BtorNode **params, int n, BtorNode *body)
{
  assert (btor);
  assert (kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE);
  assert (params);
  assert (n > 0);
  assert (body);
  assert (btor == BTOR_REAL_ADDR_NODE (body)->btor);

  int i;
  BtorNode *res, *tmp;

  res = btor_copy_exp (btor, body);
  for (i = n - 1; i >= 0; i--)
  {
    assert (params[i]);
    assert (btor == BTOR_REAL_ADDR_NODE (params[i])->btor);
    assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (params[i])));
    tmp = quantifier_exp (btor, kind, params[i], res);
    btor_release_exp (btor, res);
    res = tmp;
  }
  return res;
}

BtorNode *
btor_forall_exp_node (Btor *btor, BtorNode *param, BtorNode *body)
{
  return quantifier_exp_node (btor, BTOR_FORALL_NODE, param, body);
}

BtorNode *
btor_forall_exp (Btor *btor, BtorNode *param, BtorNode *body)
{
  return quantifier_exp (btor, BTOR_FORALL_NODE, param, body);
}

BtorNode *
btor_forall_n_exp (Btor *btor, BtorNode **params, int n, BtorNode *body)
{
  return quantifier_n_exp (btor, BTOR_FORALL_NODE, params, n, body);
}

BtorNode *
btor_exists_exp_node (Btor *btor, BtorNode *param, BtorNode *body)
{
  return quantifier_exp_node (btor, BTOR_EXISTS_NODE, param, body);
}

BtorNode *
btor_exists_exp (Btor *btor, BtorNode *param, BtorNode *body)
{
  return quantifier_exp (btor, BTOR_EXISTS_NODE, param, body);
}

BtorNode *
btor_exists_n_exp (Btor *btor, BtorNode **params, int n, BtorNode *body)
{
  return quantifier_n_exp (btor, BTOR_EXISTS_NODE, params, n, body);
}

BtorNode *
btor_fun_exp (Btor *btor, uint32_t paramc, BtorNode **params, BtorNode *exp)
{
  assert (btor);
  assert (paramc > 0);
  assert (params);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  assert (!BTOR_IS_UF_NODE (BTOR_REAL_ADDR_NODE (exp)));

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

#define ARGS_MAX_NUM_CHILDREN 3

BtorNode *
btor_args_exp (Btor *btor, uint32_t argc, BtorNode **args)
{
  assert (btor);
  assert (argc > 0);
  assert (args);

  int i, cur_argc, cnt_args, rem_free, num_args;
  BtorNode *e[ARGS_MAX_NUM_CHILDREN];
  BtorNode *result = 0, *last = 0;

  /* arguments fit in one args node */
  if (argc <= ARGS_MAX_NUM_CHILDREN)
  {
    num_args = 1;
    rem_free = ARGS_MAX_NUM_CHILDREN - argc;
    cur_argc = argc;
  }
  /* arguments have to be split into several args nodes.
   * compute number of required args nodes */
  else
  {
    rem_free = argc % (ARGS_MAX_NUM_CHILDREN - 1);
    num_args = argc / (ARGS_MAX_NUM_CHILDREN - 1);
    /* we can store at most 1 more element into 'num_args' nodes
     * without needing an additional args node */
    if (rem_free > 1) num_args += 1;

    assert (num_args > 1);
    /* compute number of arguments in last args node */
    cur_argc = argc - (num_args - 1) * (ARGS_MAX_NUM_CHILDREN - 1);
  }
  cnt_args = cur_argc - 1;

  /* split up args in 'num_args' of args nodes */
  for (i = argc - 1; i >= 0; i--)
  {
    assert (cnt_args >= 0);
    assert (cnt_args <= ARGS_MAX_NUM_CHILDREN);
    assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (args[i])));
    assert (btor == BTOR_REAL_ADDR_NODE (args[i])->btor);
    e[cnt_args] = btor_simplify_exp (btor, args[i]);
    cnt_args -= 1;

    assert (i > 0 || cnt_args < 0);
    if (cnt_args < 0)
    {
      result = create_exp (btor, BTOR_ARGS_NODE, cur_argc, e);

      /* init for next iteration */
      cur_argc    = ARGS_MAX_NUM_CHILDREN;
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

  /* eliminate nested functions */
  if (BTOR_IS_LAMBDA_NODE (e[0]) && e[0]->parameterized)
  {
    btor_assign_args (btor, e[0], args);
    BtorNode *result = btor_beta_reduce_bounded (btor, e[0], 1);
    btor_unassign_params (btor, e[0]);
    return result;
  }
  assert (!BTOR_IS_FUN_COND_NODE (e[0])
          || (!e[0]->e[1]->parameterized && !e[0]->e[2]->parameterized));
  return create_exp (btor, BTOR_APPLY_NODE, 2, e);
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

  // TODO (ma): do we even allow that? can this happen?
  /* if fun was simplified to a constant value, we return a copy of it */
  if (!BTOR_IS_FUN_NODE (fun))
  {
    assert (!BTOR_REAL_ADDR_NODE (fun)->parameterized);
    return btor_copy_exp (btor, fun);
  }

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_binary_exp (btor, BTOR_APPLY_NODE, fun, args);

  return btor_apply_exp_node (btor, fun, args);
}

BtorNode *
btor_apply_exps (Btor *btor, uint32_t argc, BtorNode **args, BtorNode *fun)
{
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (fun);

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
  unsigned i, width, arity;
  BtorNode *e[3], *cond, *lambda;
  BtorNodePtrStack params;
  BtorSort *sort;
  BtorSortUniqueTable *sorts;
  e[0] = btor_simplify_exp (btor, e_cond);
  e[1] = btor_simplify_exp (btor, e_if);
  e[2] = btor_simplify_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e[0], e[1], e[2]));

  /* represent parameterized function conditionals (with parameterized
   * functions) as parameterized function
   * -> gets beta reduced in btor_apply_exp_node */
  if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e[1]))
      && (e[1]->parameterized || e[2]->parameterized))
  {
    sorts = &btor->sorts_unique_table;
    BTOR_INIT_STACK (params);
    assert (btor_is_fun_sort (sorts, e[1]->sort_id));
    arity = btor_get_fun_arity (btor, e[1]);
    sort  = btor_get_sort_by_id (sorts, e[1]->sort_id);
    assert (sort->fun.domain->kind == BTOR_TUPLE_SORT);
    assert (sort->fun.domain->tuple.num_elements == arity);
    for (i = 0; i < arity; i++)
    {
      width = btor_get_width_bitvec_sort (
          sorts, sort->fun.domain->tuple.elements[i]->id);
      BTOR_PUSH_STACK (btor->mm, params, btor_param_exp (btor, width, 0));
    }
    e[1]   = btor_apply_exps (btor, arity, params.start, e[1]);
    e[2]   = btor_apply_exps (btor, arity, params.start, e[2]);
    cond   = create_exp (btor, BTOR_BCOND_NODE, 3, e);
    lambda = btor_fun_exp (btor, arity, params.start, cond);
    while (!BTOR_EMPTY_STACK (params))
      btor_release_exp (btor, BTOR_POP_STACK (params));
    btor_release_exp (btor, e[1]);
    btor_release_exp (btor, e[2]);
    btor_release_exp (btor, cond);
    BTOR_RELEASE_STACK (btor->mm, params);
    return lambda;
  }
  return create_exp (btor, BTOR_BCOND_NODE, 3, e);
}

#if 0
BtorNode *
btor_bv_cond_exp_node (Btor * btor, BtorNode * e_cond, BtorNode * e_if,
		       BtorNode * e_else)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_cond)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_if)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_else)->btor);

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_ternary_exp (btor, BTOR_BCOND_NODE, e_cond, e_if, e_else);

  return btor_cond_exp_node (btor, e_cond, e_if, e_else);
}

// TODO: arbitrary conditionals on functions
BtorNode *
btor_array_cond_exp_node (Btor * btor, BtorNode * e_cond, BtorNode * e_if,
			  BtorNode * e_else)
{
  assert (btor == BTOR_REAL_ADDR_NODE (e_cond)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_if)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_else)->btor);

  BtorNode *cond, *param, *lambda, *app_if, *app_else;

  e_cond = btor_simplify_exp (btor, e_cond);
  e_if = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);

  assert (BTOR_IS_REGULAR_NODE (e_if));
  assert (BTOR_IS_FUN_NODE (e_if));
  assert (BTOR_IS_REGULAR_NODE (e_else));
  assert (BTOR_IS_FUN_NODE (e_else));

  param = btor_param_exp (btor, btor_get_index_exp_width (btor, e_if), 0);
  app_if = btor_apply_exps (btor, 1, &param, e_if); 
  app_else = btor_apply_exps (btor, 1, &param, e_else);
  cond = btor_bv_cond_exp_node (btor, e_cond, app_if, app_else); 
  lambda = btor_lambda_exp (btor, param, cond); 
  lambda->is_array = 1;

  btor_release_exp (btor, param);
  btor_release_exp (btor, app_if);
  btor_release_exp (btor, app_else);
  btor_release_exp (btor, cond);
  
  return lambda;
}
#endif

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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_ADD_NODE, e0, e1);
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
  one    = btor_one_exp (btor, btor_get_exp_width (btor, exp));
  result = btor_add_exp (btor, BTOR_INVERT_NODE (exp), one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_slice_exp (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
  {
    if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)))
      result = btor_rewrite_binary_exp (btor, BTOR_FEQ_NODE, e0, e1);
    else
      result = btor_rewrite_binary_exp (btor, BTOR_BEQ_NODE, e0, e1);
  }
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_AND_NODE, e0, e1);
  else
    result = btor_and_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

static BtorNode *
create_bin_n_exp (Btor *btor,
                  BtorNode *(*func) (Btor *, BtorNode *, BtorNode *),
                  uint32_t argc,
                  BtorNode *args[])
{
  uint32_t i;
  BtorNode *result, *tmp, *arg;

  result = 0;
  for (i = 0; i < argc; i++)
  {
    arg = args[i];
    if (result)
    {
      tmp = func (btor, arg, result);
      btor_release_exp (btor, result);
      result = tmp;
    }
    else
      result = btor_copy_exp (btor, arg);
  }
  assert (result);
  return result;
}

BtorNode *
btor_and_n_exp (Btor *btor, uint32_t argc, BtorNode *args[])
{
  return create_bin_n_exp (btor, btor_and_exp, argc, args);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_CONCAT_NODE, e0, e1);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_ternary_exp (
        btor, BTOR_BCOND_NODE, e_cond, e_if, e_else);

  return btor_cond_exp_node (btor, e_cond, e_if, e_else);
}

BtorNode *
btor_redor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  zero   = btor_zero_exp (btor, btor_get_exp_width (btor, exp));
  result = BTOR_INVERT_NODE (btor_eq_exp (btor, exp, zero));
  btor_release_exp (btor, zero);
  return result;
}

BtorNode *
btor_redxor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *slice, *xor;
  int i, width;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  width = btor_get_exp_width (btor, exp);

  result = btor_slice_exp (btor, exp, 0, 0);
  for (i = 1; i < width; i++)
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

  ones   = btor_ones_exp (btor, btor_get_exp_width (btor, exp));
  result = btor_eq_exp (btor, exp, ones);
  btor_release_exp (btor, ones);
  return result;
}

BtorNode *
btor_uext_exp (Btor *btor, BtorNode *exp, uint32_t width)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp));

  if (width == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (width > 0);
    zero   = btor_zero_exp (btor, width);
    result = btor_concat_exp (btor, zero, exp);
    btor_release_exp (btor, zero);
  }
  return result;
}

BtorNode *
btor_sext_exp (Btor *btor, BtorNode *exp, uint32_t width)
{
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  BtorNode *result, *zero, *ones, *neg, *cond;
  int exp_width;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp));

  if (width == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (width > 0);
    zero      = btor_zero_exp (btor, width);
    ones      = btor_ones_exp (btor, width);
    exp_width = btor_get_exp_width (btor, exp);
    neg       = btor_slice_exp (btor, exp, exp_width - 1, exp_width - 1);
    cond      = btor_cond_exp (btor, neg, ones, zero);
    result    = btor_concat_exp (btor, cond, exp);
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
  assert (btor_get_exp_width (btor, e0) == 1);
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
  assert (btor_get_exp_width (btor, e0) == 1);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width   = btor_get_exp_width (btor, e0);
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, e1, 1);
  add     = btor_add_exp (btor, uext_e1, uext_e2);
  result  = btor_slice_exp (btor, add, width, width);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width       = btor_get_exp_width (btor, e0);
  sign_e1     = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e2     = btor_slice_exp (btor, e1, width - 1, width - 1);
  add         = btor_add_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, add, width - 1, width - 1);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_MUL_NODE, e0, e1);
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
  int i, width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);
  if (width == 1) return btor_zero_exp (btor, 1);
  BTOR_NEWN (btor->mm, temps_e2, width - 1);
  temps_e2[0] = btor_slice_exp (btor, e1, width - 1, width - 1);
  for (i = 1; i < width - 1; i++)
  {
    slice       = btor_slice_exp (btor, e1, width - 1 - i, width - 1 - i);
    temps_e2[i] = btor_or_exp (btor, temps_e2[i - 1], slice);
    btor_release_exp (btor, slice);
  }
  slice  = btor_slice_exp (btor, e0, 1, 1);
  result = btor_and_exp (btor, slice, temps_e2[0]);
  btor_release_exp (btor, slice);
  for (i = 1; i < width - 1; i++)
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
  slice   = btor_slice_exp (btor, mul, width, width);
  or      = btor_or_exp (btor, result, slice);
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, mul);
  btor_release_exp (btor, slice);
  btor_release_exp (btor, result);
  result = or ;
  for (i = 0; i < width - 1; i++) btor_release_exp (btor, temps_e2[i]);
  BTOR_DELETEN (btor->mm, temps_e2, width - 1);
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
  int i, width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);
  if (width == 1) return btor_and_exp (btor, e0, e1);
  if (width == 2)
  {
    sext_e1         = btor_sext_exp (btor, e0, 1);
    sext_e2         = btor_sext_exp (btor, e1, 1);
    mul             = btor_mul_exp (btor, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (btor, mul, width, width);
    slice_n_minus_1 = btor_slice_exp (btor, mul, width - 1, width - 1);
    result          = btor_xor_exp (btor, slice_n, slice_n_minus_1);
    btor_release_exp (btor, sext_e1);
    btor_release_exp (btor, sext_e2);
    btor_release_exp (btor, mul);
    btor_release_exp (btor, slice_n);
    btor_release_exp (btor, slice_n_minus_1);
  }
  else
  {
    sign_e1      = btor_slice_exp (btor, e0, width - 1, width - 1);
    sign_e2      = btor_slice_exp (btor, e1, width - 1, width - 1);
    sext_sign_e1 = btor_sext_exp (btor, sign_e1, width - 1);
    sext_sign_e2 = btor_sext_exp (btor, sign_e2, width - 1);
    xor_sign_e1  = btor_xor_exp (btor, e0, sext_sign_e1);
    xor_sign_e2  = btor_xor_exp (btor, e1, sext_sign_e2);
    BTOR_NEWN (btor->mm, temps_e2, width - 2);
    temps_e2[0] = btor_slice_exp (btor, xor_sign_e2, width - 2, width - 2);
    for (i = 1; i < width - 2; i++)
    {
      slice = btor_slice_exp (btor, xor_sign_e2, width - 2 - i, width - 2 - i);
      temps_e2[i] = btor_or_exp (btor, temps_e2[i - 1], slice);
      btor_release_exp (btor, slice);
    }
    slice  = btor_slice_exp (btor, xor_sign_e1, 1, 1);
    result = btor_and_exp (btor, slice, temps_e2[0]);
    btor_release_exp (btor, slice);
    for (i = 1; i < width - 2; i++)
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
    slice_n         = btor_slice_exp (btor, mul, width, width);
    slice_n_minus_1 = btor_slice_exp (btor, mul, width - 1, width - 1);
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
    for (i = 0; i < width - 2; i++) btor_release_exp (btor, temps_e2[i]);
    BTOR_DELETEN (btor->mm, temps_e2, width - 2);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_ULT_NODE, e0, e1);
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

  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);
  if (width == 1) return btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1));
  s0                 = btor_slice_exp (btor, e0, width - 1, width - 1);
  s1                 = btor_slice_exp (btor, e1, width - 1, width - 1);
  r0                 = btor_slice_exp (btor, e0, width - 2, 0);
  r1                 = btor_slice_exp (btor, e1, width - 2, 0);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_SLL_NODE, e0, e1);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_SRL_NODE, e0, e1);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  width   = btor_get_exp_width (btor, e0);
  sign_e1 = btor_slice_exp (btor, e0, width - 1, width - 1);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width   = btor_get_exp_width (btor, e0);
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, BTOR_INVERT_NODE (e1), 1);
  assert (width < INT_MAX);
  one    = btor_one_exp (btor, width + 1);
  add1   = btor_add_exp (btor, uext_e2, one);
  add2   = btor_add_exp (btor, uext_e1, add1);
  result = BTOR_INVERT_NODE (btor_slice_exp (btor, add2, width, width));
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width       = btor_get_exp_width (btor, e0);
  sign_e1     = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e2     = btor_slice_exp (btor, e1, width - 1, width - 1);
  sub         = btor_sub_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, sub, width - 1, width - 1);
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_UDIV_NODE, e0, e1);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);

  if (width == 1)
    return BTOR_INVERT_NODE (btor_and_exp (btor, BTOR_INVERT_NODE (e0), e1));

  sign_e1 = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e2 = btor_slice_exp (btor, e1, width - 1, width - 1);
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

  int_min = int_min_exp (btor, btor_get_exp_width (btor, e0));
  ones    = btor_ones_exp (btor, btor_get_exp_width (btor, e1));
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

  if (btor_get_opt (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    result = btor_rewrite_binary_exp (btor, BTOR_UREM_NODE, e0, e1);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width = btor_get_exp_width (btor, e0);

  if (width == 1) return btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1));

  sign_e0 = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e1 = btor_slice_exp (btor, e1, width - 1, width - 1);
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
  uint32_t width;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  width     = btor_get_exp_width (btor, e0);
  zero      = btor_zero_exp (btor, width);
  e0_zero   = btor_eq_exp (btor, zero, e0);
  sign_e0   = btor_slice_exp (btor, e0, width - 1, width - 1);
  sign_e1   = btor_slice_exp (btor, e1, width - 1, width - 1);
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

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));
  return btor_apply_exps (btor, 1, &e_index, e_array);
}

BtorNode *
btor_write_exp (Btor *btor,
                BtorNode *e_array,
                BtorNode *e_index,
                BtorNode *e_value)
{
  assert (btor);
  assert (btor_is_array_exp (btor, e_array));
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_index)->btor);
  assert (btor == BTOR_REAL_ADDR_NODE (e_value)->btor);

  BtorNode *param, *e_cond, *e_if, *e_else, *bvcond, *args;
  BtorLambdaNode *lambda;
  BtorPtrHashBucket *b;

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));

  param  = btor_param_exp (btor, btor_get_exp_width (btor, e_index), 0);
  e_cond = btor_eq_exp (btor, param, e_index);
  e_if   = btor_copy_exp (btor, e_value);
  e_else = btor_read_exp (btor, e_array, param);
  bvcond = btor_cond_exp (btor, e_cond, e_if, e_else);
  lambda = (BtorLambdaNode *) btor_lambda_exp (btor, param, bvcond);
  if (!lambda->static_rho)
  {
    lambda->static_rho = btor_new_ptr_hash_table (btor->mm, 0, 0);
    args               = btor_args_exp (btor, 1, &e_index);
    b                  = btor_add_ptr_hash_table (lambda->static_rho, args);
    b->data.as_ptr     = btor_copy_exp (btor, e_value);
  }
  //#ifndef NDEBUG
  //  else
  //    {
  //      if (lambda->static_rho->count == 1)
  //	{
  //	  assert ((args = lambda->static_rho->first->key)
  //		  && args->e[0] == e_index);
  //	  assert (((BtorNode *) lambda->static_rho->first->data.as_ptr)
  //		  == e_value);
  //	}
  //      else
  //	{
  //	  BtorHashTableIterator it;
  //	  btor_init_node_hash_table_iterator (&it, lambda->static_rho);
  //	  while (btor_has_next_node_hash_table_iterator (&it))
  //	    {
  //	      assert (it.bucket->data.as_ptr == e_value);
  //	      (void) btor_next_node_hash_table_iterator (&it);
  //	    }
  //	}
  //    }
  //#endif

  btor_release_exp (btor, e_if);
  btor_release_exp (btor, e_else);
  btor_release_exp (btor, e_cond);
  btor_release_exp (btor, bvcond);
  btor_release_exp (btor, param);

  lambda->is_array = 1;
  return (BtorNode *) lambda;
}

BtorNode *
btor_inc_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, btor_get_exp_width (btor, exp));
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

  one    = btor_one_exp (btor, btor_get_exp_width (btor, exp));
  result = btor_sub_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_create_exp (Btor *btor, BtorNodeKind kind, uint32_t arity, BtorNode **e)
{
  assert (arity > 0);
  assert (arity <= 3);

  switch (kind)
  {
    case BTOR_AND_NODE:
      assert (arity == 2);
      return btor_and_exp (btor, e[0], e[1]);
    case BTOR_BEQ_NODE:
    case BTOR_FEQ_NODE:
      assert (arity == 2);
      return btor_eq_exp (btor, e[0], e[1]);
    case BTOR_ADD_NODE:
      assert (arity == 2);
      return btor_add_exp (btor, e[0], e[1]);
    case BTOR_MUL_NODE:
      assert (arity == 2);
      return btor_mul_exp (btor, e[0], e[1]);
    case BTOR_ULT_NODE:
      assert (arity == 2);
      return btor_ult_exp (btor, e[0], e[1]);
    case BTOR_SLL_NODE:
      assert (arity == 2);
      return btor_sll_exp (btor, e[0], e[1]);
    case BTOR_SRL_NODE:
      assert (arity == 2);
      return btor_srl_exp (btor, e[0], e[1]);
    case BTOR_UDIV_NODE:
      assert (arity == 2);
      return btor_udiv_exp (btor, e[0], e[1]);
    case BTOR_UREM_NODE:
      assert (arity == 2);
      return btor_urem_exp (btor, e[0], e[1]);
    case BTOR_CONCAT_NODE:
      assert (arity == 2);
      return btor_concat_exp (btor, e[0], e[1]);
    case BTOR_APPLY_NODE:
      assert (arity == 2);
      return btor_apply_exp (btor, e[0], e[1]);
    case BTOR_LAMBDA_NODE:
      assert (arity == 2);
      return btor_lambda_exp (btor, e[0], e[1]);
    case BTOR_EXISTS_NODE:
      assert (arity == 2);
      return btor_exists_exp (btor, e[0], e[1]);
    case BTOR_FORALL_NODE:
      assert (arity == 2);
      return btor_forall_exp (btor, e[0], e[1]);
    case BTOR_BCOND_NODE:
      assert (arity == 3);
      return btor_cond_exp (btor, e[0], e[1], e[2]);
    default:
      assert (kind == BTOR_ARGS_NODE);
      return btor_args_exp (btor, arity, e);
  }
  return 0;
}

uint32_t
btor_get_exp_width (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (!BTOR_IS_ARGS_NODE (BTOR_REAL_ADDR_NODE (exp)));
  return btor_get_width_bitvec_sort (&btor->sorts_unique_table,
                                     BTOR_REAL_ADDR_NODE (exp)->sort_id);
}

uint32_t
btor_get_fun_exp_width (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorSortUniqueTable *sorts;
  sorts = &btor->sorts_unique_table;
  assert (btor_is_fun_sort (sorts, exp->sort_id));
  return btor_get_width_bitvec_sort (
      sorts, btor_get_codomain_fun_sort (sorts, exp->sort_id));
}

BtorBitVector *
btor_const_get_bits (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)));
  return ((BtorBVConstNode *) BTOR_REAL_ADDR_NODE (exp))->bits;
}

BtorBitVector *
btor_const_get_invbits (BtorNode *exp)
{
  assert (exp);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)));
  return ((BtorBVConstNode *) BTOR_REAL_ADDR_NODE (exp))->invbits;
}

void
btor_const_set_bits (BtorNode *exp, BtorBitVector *bits)
{
  assert (exp);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)));
  ((BtorBVConstNode *) BTOR_REAL_ADDR_NODE (exp))->bits = bits;
}

void
btor_const_set_invbits (BtorNode *exp, BtorBitVector *bits)
{
  assert (exp);
  assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)));
  ((BtorBVConstNode *) BTOR_REAL_ADDR_NODE (exp))->invbits = bits;
}

bool
btor_is_array_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);

  exp = btor_simplify_exp (btor, exp);
  return exp->is_array == 1;
}

bool
btor_is_uf_array_var_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_UF_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp));
}

bool
btor_is_uf_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_UF_NODE (BTOR_REAL_ADDR_NODE (exp));
}

bool
btor_is_bv_var_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_get_index_exp_width (Btor *btor, BtorNode *e_array)
{
  assert (btor);
  assert (e_array);
  assert (btor == BTOR_REAL_ADDR_NODE (e_array)->btor);

  BtorSortUniqueTable *sorts;

  sorts   = &btor->sorts_unique_table;
  e_array = btor_simplify_exp (btor, e_array);
  assert (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e_array)));
  assert (BTOR_IS_REGULAR_NODE (e_array));
  assert (btor_is_array_sort (sorts, e_array->sort_id)
          || btor_is_fun_sort (sorts, e_array->sort_id));
  return btor_get_width_bitvec_sort (
      sorts, btor_get_index_array_sort (sorts, e_array->sort_id));
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

BtorNode *
btor_get_node_by_id (Btor *btor, int32_t id)
{
  assert (btor);
  assert (id > 0);
  if (id >= BTOR_COUNT_STACK (btor->nodes_id_table)) return 0;
  return BTOR_PEEK_STACK (btor->nodes_id_table, id);
}

BtorNode *
btor_get_node_by_symbol (Btor *btor, const char *sym)
{
  assert (btor);
  assert (sym);
  BtorPtrHashBucket *b;
  // FIXME (ma): const...
  b = btor_get_ptr_hash_table (btor->symbols, (char *) sym);
  if (!b) return 0;
  return b->data.as_ptr;
}

char *
btor_get_symbol_exp (Btor *btor, BtorNode *exp)
{
  /* do not pointer-chase! */
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  BtorPtrHashBucket *b =
      btor_get_ptr_hash_table (btor->node2symbol, BTOR_REAL_ADDR_NODE (exp));
  if (b) return b->data.as_str;
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
  assert (!btor_get_ptr_hash_table (btor->symbols, (char *) symbol));

  BtorPtrHashBucket *b;
  char *sym;

  exp = BTOR_REAL_ADDR_NODE (exp);
  sym = btor_strdup (btor->mm, symbol);
  btor_add_ptr_hash_table (btor->symbols, sym)->data.as_ptr = exp;
  b = btor_get_ptr_hash_table (btor->node2symbol, exp);

  if (b)
  {
    btor_remove_ptr_hash_table (btor->symbols, b->data.as_str, 0, 0);
    btor_freestr (btor->mm, b->data.as_str);
  }
  else
    b = btor_add_ptr_hash_table (btor->node2symbol, exp);

  b->data.as_str = sym;
}

bool
btor_is_param_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (exp));
}

bool
btor_is_fun_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (exp));
}

uint32_t
btor_get_fun_arity (Btor *btor, BtorNode *exp)
{
  (void) btor;
  assert (btor);
  assert (exp);
  assert (btor == BTOR_REAL_ADDR_NODE (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_fun_sort (&btor->sorts_unique_table, exp->sort_id));
  return btor_get_arity_fun_sort (&btor->sorts_unique_table, exp->sort_id);
}

bool
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
  return btor_get_arity_tuple_sort (&btor->sorts_unique_table, exp->sort_id);
}

BtorPtrHashTable *
btor_lambda_get_static_rho (BtorNode *lambda)
{
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  return ((BtorLambdaNode *) lambda)->static_rho;
}

void
btor_lambda_set_static_rho (BtorNode *lambda, BtorPtrHashTable *static_rho)
{
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  ((BtorLambdaNode *) lambda)->static_rho = static_rho;
}

BtorPtrHashTable *
btor_lambda_copy_static_rho (Btor *btor, BtorNode *lambda)
{
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (btor_lambda_get_static_rho (lambda));

  BtorNode *data, *key;
  BtorHashTableIterator it;
  BtorPtrHashTable *static_rho;

  btor_init_node_hash_table_iterator (&it, btor_lambda_get_static_rho (lambda));
  static_rho = btor_new_ptr_hash_table (btor->mm, 0, 0);
  while (btor_has_next_node_hash_table_iterator (&it))
  {
    data = btor_copy_exp (btor, it.bucket->data.as_ptr);
    key  = btor_copy_exp (btor, btor_next_node_hash_table_iterator (&it));
    btor_add_ptr_hash_table (static_rho, key)->data.as_ptr = data;
  }
  return static_rho;
}

BtorNode *
btor_binder_get_body (BtorNode *binder)
{
  assert (BTOR_IS_REGULAR_NODE (binder));
  assert (BTOR_IS_BINDER_NODE (binder));
  return ((BtorBinderNode *) binder)->body;
}

void
btor_binder_set_body (BtorNode *binder, BtorNode *body)
{
  assert (BTOR_IS_REGULAR_NODE (binder));
  assert (BTOR_IS_BINDER_NODE (binder));
  ((BtorBinderNode *) binder)->body = body;
}

uint32_t
btor_slice_get_upper (BtorNode *slice)
{
  assert (BTOR_IS_SLICE_NODE (BTOR_REAL_ADDR_NODE (slice)));
  return ((BtorSliceNode *) BTOR_REAL_ADDR_NODE (slice))->upper;
}

uint32_t
btor_slice_get_lower (BtorNode *slice)
{
  assert (BTOR_IS_SLICE_NODE (BTOR_REAL_ADDR_NODE (slice)));
  return ((BtorSliceNode *) BTOR_REAL_ADDR_NODE (slice))->lower;
}

BtorNode *
btor_param_get_binder (BtorNode *param)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  return ((BtorParamNode *) BTOR_REAL_ADDR_NODE (param))->binder;
}

void
btor_param_set_binder (BtorNode *param, BtorNode *binder)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  assert (!binder || BTOR_IS_BINDER_NODE (BTOR_REAL_ADDR_NODE (binder)));

  BtorNode *q;

  /* param is not bound anymore, remove from exists/forall vars tables */
  if (!binder)
  {
    q = btor_param_get_binder (param);
    if (BTOR_IS_EXISTS_NODE (q))
      btor_remove_ptr_hash_table (param->btor->exists_vars, param, 0, 0);
    else if (BTOR_IS_FORALL_NODE (q))
      btor_remove_ptr_hash_table (param->btor->forall_vars, param, 0, 0);
  }
  /* param is bound, add to exists/forall vars tables */
  else
  {
    if (BTOR_IS_EXISTS_NODE (binder))
      (void) btor_add_ptr_hash_table (param->btor->exists_vars, param);
    else if (BTOR_IS_FORALL_NODE (binder))
      (void) btor_add_ptr_hash_table (param->btor->forall_vars, param);
  }
  ((BtorParamNode *) BTOR_REAL_ADDR_NODE (param))->binder = binder;
}

bool
btor_param_is_bound (BtorNode *param)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  return btor_param_get_binder (param) != 0;
}

BtorNode *
btor_param_get_assigned_exp (BtorNode *param)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  return ((BtorParamNode *) BTOR_REAL_ADDR_NODE (param))->assigned_exp;
}

BtorNode *
btor_param_set_assigned_exp (BtorNode *param, BtorNode *exp)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  assert (!exp
          || BTOR_REAL_ADDR_NODE (param)->sort_id
                 == BTOR_REAL_ADDR_NODE (exp)->sort_id);
  return ((BtorParamNode *) BTOR_REAL_ADDR_NODE (param))->assigned_exp = exp;
}

bool
btor_param_is_exists_var (BtorNode *param)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  return BTOR_IS_EXISTS_NODE (btor_param_get_binder (param));
}

bool
btor_param_is_forall_var (BtorNode *param)
{
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  return BTOR_IS_FORALL_NODE (btor_param_get_binder (param));
}

bool
btor_param_is_free (Btor *btor, BtorNode *param, BtorNode *term)
{
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  BtorPtrHashBucket *b;
  BtorPtrHashTable *t;

  term = BTOR_REAL_ADDR_NODE (term);
  b    = btor_get_ptr_hash_table (btor->parameterized, term);
  if (!b) return true;
  t = b->data.as_ptr;
  return btor_get_ptr_hash_table (t, param) == 0;
}

#ifndef NDEBUG

BtorNode *
btor_trav (BtorNode *n, const char *str)
{
  const char *p;
  for (p = str; *p; p++)
  {
    int i;
    if (!n) return 0;
    n = BTOR_REAL_ADDR_NODE (n);
    i = *p - '0';
    if (i < 0) return 0;
    if (i >= n->arity) return 0;
    n = n->e[i];
  }
  return n;
}

#endif
