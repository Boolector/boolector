/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btornode.h"

#include "btorabort.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbeta.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btorlog.h"
#include "btorrewrite.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btornodeiter.h"
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
   && btor_util_log_2 ((table).size) < BTOR_UNIQUE_TABLE_LIMIT)

/*------------------------------------------------------------------------*/

const char *const g_btor_op2str[BTOR_NUM_OPS_NODE] = {
    [BTOR_INVALID_NODE] = "invalid", [BTOR_CONST_NODE] = "const",
    [BTOR_VAR_NODE] = "var",         [BTOR_PARAM_NODE] = "param",
    [BTOR_BV_SLICE_NODE] = "slice",  [BTOR_BV_AND_NODE] = "and",
    [BTOR_BV_EQ_NODE] = "beq",       [BTOR_FUN_EQ_NODE] = "feq",
    [BTOR_BV_ADD_NODE] = "add",      [BTOR_BV_MUL_NODE] = "mul",
    [BTOR_BV_ULT_NODE] = "ult",      [BTOR_BV_SLL_NODE] = "sll",
    [BTOR_BV_SRL_NODE] = "srl",      [BTOR_BV_UDIV_NODE] = "udiv",
    [BTOR_BV_UREM_NODE] = "urem",    [BTOR_BV_CONCAT_NODE] = "concat",
    [BTOR_APPLY_NODE] = "apply",     [BTOR_FORALL_NODE] = "forall",
    [BTOR_EXISTS_NODE] = "exists",   [BTOR_LAMBDA_NODE] = "lambda",
    [BTOR_COND_NODE] = "cond",       [BTOR_ARGS_NODE] = "args",
    [BTOR_UF_NODE] = "uf",           [BTOR_UPDATE_NODE] = "update",
    [BTOR_PROXY_NODE] = "proxy",
};

/*------------------------------------------------------------------------*/

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};

#define NPRIMES ((uint32_t) (sizeof hash_primes / sizeof *hash_primes))

/*------------------------------------------------------------------------*/

/* do not move these two functions to the header (circular dependency) */

bool
btor_node_is_bv_cond (const BtorNode *exp)
{
  return btor_node_is_cond (exp)
         && btor_sort_is_bv (btor_node_real_addr (exp)->btor,
                                 btor_node_get_sort_id (exp));
}

bool
btor_node_is_fun_cond (const BtorNode *exp)
{
  return btor_node_is_cond (exp)
         && btor_sort_is_fun (btor_node_real_addr (exp)->btor,
                              btor_node_get_sort_id (exp));
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static bool
is_valid_kind (BtorNodeKind kind)
{
  return BTOR_INVALID_NODE <= kind && kind < BTOR_NUM_OPS_NODE;
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

/*------------------------------------------------------------------------*/

bool
btor_node_is_bv_const_one (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  bool result;
  BtorNode *real_exp;
  BtorBitVector *bits;

  exp = btor_simplify_exp (btor, exp);

  if (!btor_node_is_bv_const (exp)) return false;

  real_exp = btor_node_real_addr (exp);
  bits     = btor_node_bv_const_get_bits (real_exp);
  if (btor_node_is_inverted (exp)) bits = btor_bv_not (btor->mm, bits);
  result = btor_bv_is_special_const (bits) == BTOR_SPECIAL_CONST_BV_ONE;
  if (btor_node_is_inverted (exp)) btor_bv_free (btor->mm, bits);

  return result;
}

bool
btor_node_is_bv_const_min_signed (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  bool result;
  BtorNode *real_exp;
  BtorBitVector *bits;

  exp = btor_simplify_exp (btor, exp);

  if (!btor_node_is_bv_const (exp)) return false;

  real_exp = btor_node_real_addr (exp);
  bits     = btor_node_bv_const_get_bits (real_exp);
  if (btor_node_is_inverted (exp)) bits = btor_bv_not (btor->mm, bits);
  result = btor_bv_is_min_signed (bits);
  if (btor_node_is_inverted (exp)) btor_bv_free (btor->mm, bits);

  return result;
}

bool
btor_node_is_bv_const_max_signed (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  bool result;
  BtorNode *real_exp;
  BtorBitVector *bits;

  exp = btor_simplify_exp (btor, exp);

  if (!btor_node_is_bv_const (exp)) return false;

  real_exp = btor_node_real_addr (exp);
  bits     = btor_node_bv_const_get_bits (real_exp);
  if (btor_node_is_inverted (exp)) bits = btor_bv_not (btor->mm, bits);
  result = btor_bv_is_max_signed (bits);
  if (btor_node_is_inverted (exp)) btor_bv_free (btor->mm, bits);

  return result;
}

bool
btor_node_is_neg (Btor *btor, BtorNode *exp, BtorNode **res)
{
  assert (btor);
  assert (exp);

  BtorNode *real_exp;

  real_exp = btor_node_real_addr (exp);

  if (!btor_node_is_bv_add (real_exp)) return false;

  if (btor_node_is_bv_const_one (btor, real_exp->e[0]))
  {
    if (res) *res = btor_node_invert (real_exp->e[1]);
    return true;
  }

  if (btor_node_is_bv_const_one (btor, real_exp->e[1]))
  {
    if (res) *res = btor_node_invert (real_exp->e[0]);
    return true;
  }

  return false;
}

/*------------------------------------------------------------------------*/

static void
inc_exp_ref_counter (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *real_exp;

  (void) btor;
  real_exp = btor_node_real_addr (exp);
  BTOR_ABORT (real_exp->refs == INT32_MAX, "Node reference counter overflow");
  real_exp->refs++;
}

void
btor_node_inc_ext_ref_counter (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *real_exp = btor_node_real_addr (exp);
  BTOR_ABORT (real_exp->ext_refs == INT32_MAX, "Node reference counter overflow");
  real_exp->ext_refs += 1;
  btor->external_refs += 1;
}

void
btor_node_dec_ext_ref_counter (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  btor_node_real_addr (exp)->ext_refs -= 1;
  btor->external_refs -= 1;
}

BtorNode *
btor_node_copy (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);
  inc_exp_ref_counter (btor, exp);
  return exp;
}

/*------------------------------------------------------------------------*/

static inline uint32_t
hash_slice_exp (BtorNode *e, uint32_t upper, uint32_t lower)
{
  uint32_t hash;
  assert (upper >= lower);
  hash = hash_primes[0] * (uint32_t) btor_node_real_addr (e)->id;
  hash += hash_primes[1] * (uint32_t) upper;
  hash += hash_primes[2] * (uint32_t) lower;
  return hash;
}

static inline uint32_t
hash_bv_exp (Btor *btor, BtorNodeKind kind, uint32_t arity, BtorNode *e[])
{
  uint32_t hash = 0;
  uint32_t i;
#ifndef NDEBUG
  if (btor_opt_get (btor, BTOR_OPT_SORT_EXP) > 0
      && btor_node_is_binary_commutative_kind (kind))
    assert (arity == 2), assert (btor_node_real_addr (e[0])->id
                                 <= btor_node_real_addr (e[1])->id);
#else
  (void) btor;
  (void) kind;
#endif
  assert (arity <= NPRIMES);
  for (i = 0; i < arity; i++)
    hash += hash_primes[i] * (uint32_t) btor_node_real_addr (e[i])->id;
  return hash;
}

static uint32_t
hash_binder_exp (Btor *btor,
                 BtorNode *param,
                 BtorNode *body,
                 BtorIntHashTable *params)
{
  assert (btor);
  assert (body);

  uint32_t i;
  uint32_t hash = 0;
  BtorNode *cur, *real_cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *marked, *p;
  BtorPtrHashBucket *b;

  marked = btor_hashint_table_new (btor->mm);
  BTOR_INIT_STACK (btor->mm, visit);
  BTOR_PUSH_STACK (visit, body);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur      = BTOR_POP_STACK (visit);
    real_cur = btor_node_real_addr (cur);

    if (btor_hashint_table_contains (marked, real_cur->id)) continue;

    if (!real_cur->parameterized)
    {
      hash += btor_node_get_id (cur);
      continue;
    }

    /* paramterized lambda already hashed, we can use already computed hash
     * value instead of recomputing it */
    if (btor_node_is_lambda (real_cur))
    {
      hash += btor_hashptr_table_get (btor->lambdas, real_cur)->data.as_int;
      hash += real_cur->kind;
      hash += real_cur->e[0]->kind;
      continue;
    }
    else if (btor_node_is_quantifier (real_cur))
    {
      hash += btor_hashptr_table_get (btor->quantifiers, real_cur)->data.as_int;
      hash += real_cur->kind;
      hash += real_cur->e[0]->kind;
      /* copy parameters of real_cur to params */
      if (params)
      {
        b = btor_hashptr_table_get (btor->parameterized, real_cur);
        if (b)
        {
          assert (b->data.as_ptr);
          p = b->data.as_ptr;
          for (i = 0; i < p->size; i++)
          {
            if (p->keys[i] && p->keys[i] != param->id
                && !btor_hashint_table_contains (params, p->keys[i]))
              btor_hashint_table_add (params, p->keys[i]);
          }
        }
      }
      continue;
    }
    else if (btor_node_is_param (real_cur) && real_cur != param && params)
      btor_hashint_table_add (params, real_cur->id);

    btor_hashint_table_add (marked, real_cur->id);
    hash += btor_node_is_inverted (cur) ? -real_cur->kind : real_cur->kind;
    for (i = 0; i < real_cur->arity; i++)
      BTOR_PUSH_STACK (visit, real_cur->e[i]);
  }
  BTOR_RELEASE_STACK (visit);
  btor_hashint_table_delete (marked);
  return hash;
}

/* Computes hash value of expresssion by children ids */
static uint32_t
compute_hash_exp (Btor *btor, BtorNode *exp, uint32_t table_size)
{
  assert (exp);
  assert (table_size > 0);
  assert (btor_util_is_power_of_2 (table_size));
  assert (btor_node_is_regular (exp));
  assert (!btor_node_is_bv_var (exp));
  assert (!btor_node_is_uf (exp));

  uint32_t hash = 0;

  if (btor_node_is_bv_const (exp))
    hash = btor_bv_hash (btor_node_bv_const_get_bits (exp));
  /* hash for lambdas is computed once during creation. afterwards, we always
   * have to use the saved hash value since hashing of lambdas requires all
   * parameterized nodes and their inputs (cf. hash_binder_exp), which may
   * change at some point. */
  else if (btor_node_is_lambda (exp))
    hash = btor_hashptr_table_get (exp->btor->lambdas, (BtorNode *) exp)
               ->data.as_int;
  else if (btor_node_is_quantifier (exp))
    hash = btor_hashptr_table_get (exp->btor->quantifiers, exp)->data.as_int;
  else if (exp->kind == BTOR_BV_SLICE_NODE)
    hash = hash_slice_exp (exp->e[0],
                           btor_node_bv_slice_get_upper (exp),
                           btor_node_bv_slice_get_lower (exp));
  else
    hash = hash_bv_exp (btor, exp->kind, exp->arity, exp->e);
  hash &= table_size - 1;
  return hash;
}

/*------------------------------------------------------------------------*/

static void
setup_node_and_add_to_id_table (Btor *btor, void *ptr)
{
  assert (btor);
  assert (ptr);

  BtorNode *exp;
  uint32_t id;

  exp = (BtorNode *) ptr;
  assert (!btor_node_is_inverted (exp));
  assert (!exp->id);

  exp->refs = 1;
  exp->btor = btor;
  btor->stats.expressions++;
  id = BTOR_COUNT_STACK (btor->nodes_id_table);
  BTOR_ABORT (id == INT32_MAX, "expression id overflow");
  exp->id = id;
  BTOR_PUSH_STACK (btor->nodes_id_table, exp);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == (size_t) exp->id + 1);
  assert (BTOR_PEEK_STACK (btor->nodes_id_table, exp->id) == exp);
  btor->stats.node_bytes_alloc += exp->bytes;

  if (btor_node_is_apply (exp)) exp->apply_below = 1;
}

/* Enlarges unique table and rehashes expressions. */
static void
enlarge_nodes_unique_table (Btor *btor)
{
  assert (btor);

  BtorMemMgr *mm;
  uint32_t size, new_size, i;
  uint32_t hash;
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
      assert (btor_node_is_regular (cur));
      assert (!btor_node_is_bv_var (cur));
      assert (!btor_node_is_uf (cur));
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

static void
remove_from_nodes_unique_table_exp (Btor *btor, BtorNode *exp)
{
  assert (exp);
  assert (btor_node_is_regular (exp));

  uint32_t hash;
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
    assert (btor_node_is_regular (cur));
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
remove_from_hash_tables (Btor *btor, BtorNode *exp, bool keep_symbol)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (!btor_node_is_invalid (exp));

  BtorHashTableData data;

  switch (exp->kind)
  {
    case BTOR_VAR_NODE:
      btor_hashptr_table_remove (btor->bv_vars, exp, 0, 0);
      break;
    case BTOR_LAMBDA_NODE:
      btor_hashptr_table_remove (btor->lambdas, exp, 0, 0);
      break;
    case BTOR_FORALL_NODE:
    case BTOR_EXISTS_NODE:
      btor_hashptr_table_remove (btor->quantifiers, exp, 0, 0);
      break;
    case BTOR_UF_NODE: btor_hashptr_table_remove (btor->ufs, exp, 0, 0); break;
    case BTOR_FUN_EQ_NODE:
      btor_hashptr_table_remove (btor->feqs, exp, 0, 0);
      break;
    default: break;
  }

  if (!keep_symbol && btor_hashptr_table_get (btor->node2symbol, exp))
  {
    btor_hashptr_table_remove (btor->node2symbol, exp, 0, &data);
    if (data.as_str[0] != 0)
    {
      btor_hashptr_table_remove (btor->symbols, data.as_str, 0, 0);
      btor_mem_freestr (btor->mm, data.as_str);
    }
  }

  if (btor_hashptr_table_get (btor->parameterized, exp))
  {
    btor_hashptr_table_remove (btor->parameterized, exp, 0, &data);
    assert (data.as_ptr);
    btor_hashint_table_delete (data.as_ptr);
  }
}

/*------------------------------------------------------------------------*/

/* Connects child to its parent and updates list of parent pointers.
 * Expressions are inserted at the beginning of the regular parent list
 */
static void
connect_child_exp (Btor *btor, BtorNode *parent, BtorNode *child, uint32_t pos)
{
  assert (btor);
  assert (parent);
  assert (btor_node_is_regular (parent));
  assert (btor == parent->btor);
  assert (child);
  assert (btor == btor_node_real_addr (child)->btor);
  assert (pos <= 2);
  assert (btor_simplify_exp (btor, child) == child);
  assert (!btor_node_is_args (child) || btor_node_is_args (parent)
          || btor_node_is_apply (parent) || btor_node_is_update (parent));

  (void) btor;
  uint32_t tag;
  bool insert_beginning = 1;
  BtorNode *real_child, *first_parent, *last_parent, *tagged_parent;

  /* set specific flags */

  /* set parent parameterized if child is parameterized */
  if (!btor_node_is_binder (parent)
      && btor_node_real_addr (child)->parameterized)
    parent->parameterized = 1;

  // TODO (ma): why don't we bind params here?

  if (btor_node_is_fun_cond (parent) && btor_node_real_addr (child)->is_array)
    parent->is_array = 1;

  if (btor_node_real_addr (child)->lambda_below) parent->lambda_below = 1;

  if (btor_node_real_addr (child)->quantifier_below)
    parent->quantifier_below = 1;

  if (btor_node_real_addr (child)->apply_below) parent->apply_below = 1;

  btor_node_real_addr (child)->parents++;
  inc_exp_ref_counter (btor, child);

  /* update parent lists */

  if (btor_node_is_apply (parent)) insert_beginning = false;

  real_child     = btor_node_real_addr (child);
  parent->e[pos] = child;
  tagged_parent  = btor_node_set_tag (parent, pos);

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
    tag                      = btor_node_get_tag (first_parent);
    btor_node_real_addr (first_parent)->prev_parent[tag] = tagged_parent;
    real_child->first_parent                             = tagged_parent;
  }
  /* add parent at the end of the list */
  else
  {
    last_parent = real_child->last_parent;
    assert (last_parent);
    parent->prev_parent[pos] = last_parent;
    tag                      = btor_node_get_tag (last_parent);
    btor_node_real_addr (last_parent)->next_parent[tag] = tagged_parent;
    real_child->last_parent                             = tagged_parent;
  }
}

/* Disconnects a child from its parent and updates its parent list */
static void
disconnect_child_exp (Btor *btor, BtorNode *parent, uint32_t pos)
{
  assert (btor);
  assert (parent);
  assert (btor_node_is_regular (parent));
  assert (btor == parent->btor);
  assert (!btor_node_is_bv_const (parent));
  assert (!btor_node_is_bv_var (parent));
  assert (!btor_node_is_uf (parent));
  assert (pos <= 2);

  (void) btor;
  BtorNode *first_parent, *last_parent;
  BtorNode *real_child, *tagged_parent;

  tagged_parent = btor_node_set_tag (parent, pos);
  real_child    = btor_node_real_addr (parent->e[pos]);
  real_child->parents--;
  first_parent = real_child->first_parent;
  last_parent  = real_child->last_parent;
  assert (first_parent);
  assert (last_parent);

  /* if a parameter is disconnected from a lambda we have to reset
   * 'lambda_exp' of the parameter in order to keep a valid state */
  if (btor_node_is_binder (parent)
      && pos == 0
      /* if parent gets rebuilt via substitute_and_rebuild, it might
       * result in a new binder term, where the param is already reused.
       * if this is the case param is already bound by a different binder
       * and we are not allowed to reset param->binder to 0. */
      && btor_node_param_get_binder (parent->e[0]) == parent)
    btor_node_param_set_binder (parent->e[0], 0);

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
  assert (btor_node_is_regular (exp));
  assert (!btor_node_is_invalid (exp));
  assert (!exp->unique);
  assert (exp->erased);
  assert (!exp->disconnected);

  uint32_t i;

  for (i = 0; i < exp->arity; i++) disconnect_child_exp (btor, exp, i);
  exp->disconnected = 1;
}

/*------------------------------------------------------------------------*/

/* Delete local data of expression.
 *
 * Virtual reads and simplified expressions have to be handled by the
 * calling function, e.g. 'btor_node_release', to avoid recursion.
 *
 * We use this function to update operator stats
 */
static void
erase_local_data_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  assert (btor_node_is_regular (exp));

  assert (!exp->unique);
  assert (!exp->erased);
  assert (!exp->disconnected);
  assert (!btor_node_is_invalid (exp));

  BtorMemMgr *mm;
  BtorPtrHashTable *static_rho;
  BtorPtrHashTableIterator it;

  mm = btor->mm;
  //  BTORLOG ("%s: %s", __FUNCTION__, btor_util_node2string (exp));

  switch (exp->kind)
  {
    case BTOR_CONST_NODE:
      btor_bv_free (mm, btor_node_bv_const_get_bits (exp));
      if (btor_node_bv_const_get_invbits (exp))
        btor_bv_free (mm, btor_node_bv_const_get_invbits (exp));
      btor_node_bv_const_set_bits (exp, 0);
      btor_node_bv_const_set_invbits (exp, 0);
      break;
    case BTOR_LAMBDA_NODE:
    case BTOR_UPDATE_NODE:
    case BTOR_UF_NODE:
      if (exp->kind == BTOR_LAMBDA_NODE)
      {
        static_rho = btor_node_lambda_get_static_rho (exp);
        if (static_rho)
        {
          btor_iter_hashptr_init (&it, static_rho);
          while (btor_iter_hashptr_has_next (&it))
          {
            btor_node_release (btor, it.bucket->data.as_ptr);
            btor_node_release (btor, btor_iter_hashptr_next (&it));
          }
          btor_hashptr_table_delete (static_rho);
          ((BtorLambdaNode *) exp)->static_rho = 0;
        }
      }
      if (exp->rho)
      {
        btor_hashptr_table_delete (exp->rho);
        exp->rho = 0;
      }
      break;
    case BTOR_COND_NODE:
      if (btor_node_is_fun_cond (exp) && exp->rho)
      {
        btor_hashptr_table_delete (exp->rho);
        exp->rho = 0;
      }
      break;
    default: break;
  }

  if (exp->av)
  {
    btor_aigvec_release_delete (btor->avmgr, exp->av);
    exp->av = 0;
  }
  exp->erased = 1;
}

static void
really_deallocate_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));
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

  if (btor_node_is_bv_const (exp))
  {
    btor_bv_free (btor->mm, btor_node_bv_const_get_bits (exp));
    if (btor_node_bv_const_get_invbits (exp))
      btor_bv_free (btor->mm, btor_node_bv_const_get_invbits (exp));
  }
  assert (btor_node_get_sort_id (exp));
  btor_sort_release (btor, btor_node_get_sort_id (exp));
  btor_node_set_sort_id (exp, 0);

  btor_mem_free (mm, exp, exp->bytes);
}

static void
recursively_release_exp (Btor *btor, BtorNode *root)
{
  assert (btor);
  assert (root);
  assert (btor_node_is_regular (root));
  assert (root->refs == 1);

  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorNode *cur;
  uint32_t i;

  mm = btor->mm;

  BTOR_INIT_STACK (mm, stack);
  cur = root;
  goto RECURSIVELY_RELEASE_NODE_ENTER_WITHOUT_POP;

  do
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (stack));

    if (cur->refs > 1)
      cur->refs--;
    else
    {
    RECURSIVELY_RELEASE_NODE_ENTER_WITHOUT_POP:
      assert (cur->refs == 1);
      assert (!cur->ext_refs || cur->ext_refs == 1);
      assert (cur->parents == 0);

      for (i = 1; i <= cur->arity; i++)
        BTOR_PUSH_STACK (stack, cur->e[cur->arity - i]);

      if (cur->simplified)
      {
        BTOR_PUSH_STACK (stack, cur->simplified);
        cur->simplified = 0;
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
  BTOR_RELEASE_STACK (stack);
}

void
btor_node_release (Btor *btor, BtorNode *root)
{
  assert (btor);
  assert (root);
  assert (btor == btor_node_real_addr (root)->btor);

  root = btor_node_real_addr (root);

  assert (root->refs > 0);

  if (root->refs > 1)
    root->refs--;
  else
    recursively_release_exp (btor, root);
}

/*------------------------------------------------------------------------*/

void
btor_node_set_to_proxy (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (btor == exp->btor);
  assert (exp->simplified);

  uint32_t i;
  BtorNode *e[3];

  remove_from_nodes_unique_table_exp (btor, exp);
  /* also updates op stats */
  erase_local_data_exp (btor, exp);
  assert (exp->arity <= 3);
  BTOR_CLR (e);
  for (i = 0; i < exp->arity; i++) e[i] = exp->e[i];
  remove_from_hash_tables (btor, exp, 1);
  disconnect_children_exp (btor, exp);

  for (i = 0; i < exp->arity; i++) btor_node_release (btor, e[i]);

  set_kind (btor, exp, BTOR_PROXY_NODE);

  exp->disconnected  = 0;
  exp->erased        = 0;
  exp->arity         = 0;
  exp->parameterized = 0;
}

/*------------------------------------------------------------------------*/

void
btor_node_set_btor_id (Btor *btor, BtorNode *exp, int32_t id)
{
  assert (btor);
  assert (exp);
  assert (id);
  assert (btor == btor_node_real_addr (exp)->btor);
  assert (btor_node_is_bv_var (exp) || btor_node_is_uf_array (exp));

  (void) btor;
  BtorNode *real_exp;
  BtorPtrHashBucket *b;

  real_exp = btor_node_real_addr (exp);
  b        = btor_hashptr_table_get (btor->inputs, real_exp);
  assert (b);
  b->data.as_int = id;
}

int32_t
btor_node_get_btor_id (BtorNode *exp)
{
  assert (exp);

  int32_t id = 0;
  Btor *btor;
  BtorNode *real_exp;
  BtorPtrHashBucket *b;

  real_exp = btor_node_real_addr (exp);
  btor     = real_exp->btor;

  if ((b = btor_hashptr_table_get (btor->inputs, real_exp)))
    id = b->data.as_int;
  if (btor_node_is_inverted (exp)) return -id;
  return id;
}

BtorNode *
btor_node_match_by_id (Btor *btor, int32_t id)
{
  assert (btor);
  assert (id > 0);
  if ((size_t) id >= BTOR_COUNT_STACK (btor->nodes_id_table)) return 0;
  BtorNode *exp = BTOR_PEEK_STACK (btor->nodes_id_table, id);
  if (!exp) return 0;
  return btor_node_copy (btor, exp);
}

BtorNode *
btor_node_get_by_id (Btor *btor, int32_t id)
{
  assert (btor);
  bool is_inverted = id < 0;
  id               = abs (id);
  if ((size_t) id >= BTOR_COUNT_STACK (btor->nodes_id_table)) return 0;
  BtorNode *res = BTOR_PEEK_STACK (btor->nodes_id_table, id);
  if (!res) return 0;
  return is_inverted ? btor_node_invert (res) : res;
}

/*------------------------------------------------------------------------*/

char *
btor_node_get_symbol (Btor *btor, const BtorNode *exp)
{
  /* do not pointer-chase! */
  assert (btor);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);
  BtorPtrHashBucket *b;

  b = btor_hashptr_table_get (btor->node2symbol, btor_node_real_addr (exp));
  if (b) return b->data.as_str;
  return 0;
}

void
btor_node_set_symbol (Btor *btor, BtorNode *exp, const char *symbol)
{
  /* do not pointer-chase! */
  assert (btor);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);
  assert (symbol);
  assert (!btor_hashptr_table_get (btor->symbols, (char *) symbol));

  BtorPtrHashBucket *b;
  char *sym;

  exp = btor_node_real_addr (exp);
  sym = btor_mem_strdup (btor->mm, symbol);
  btor_hashptr_table_add (btor->symbols, sym)->data.as_ptr = exp;
  b = btor_hashptr_table_get (btor->node2symbol, exp);

  if (b)
  {
    btor_hashptr_table_remove (btor->symbols, b->data.as_str, 0, 0);
    btor_mem_freestr (btor->mm, b->data.as_str);
  }
  else
    b = btor_hashptr_table_add (btor->node2symbol, exp);

  b->data.as_str = sym;
}

BtorNode *
btor_node_get_by_symbol (Btor *btor, const char *sym)
{
  assert (btor);
  assert (sym);
  BtorPtrHashBucket *b;
  b = btor_hashptr_table_get (btor->symbols, (char *) sym);
  if (!b) return 0;
  return b->data.as_ptr;
}

BtorNode *
btor_node_match_by_symbol (Btor *btor, const char *sym)
{
  assert (btor);
  assert (sym);
  return btor_node_copy (btor, btor_node_get_by_symbol (btor, sym));
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_node_match (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  uint32_t id;
  BtorNode *res;

  id = btor_node_real_addr (exp)->id;
  assert (id > 0);
  if (id >= BTOR_COUNT_STACK (btor->nodes_id_table)) return 0;
  res = btor_node_copy (btor, BTOR_PEEK_STACK (btor->nodes_id_table, id));
  return btor_node_is_inverted (exp) ? btor_node_invert (res) : res;
}

/*------------------------------------------------------------------------*/

/* Compares expressions by id */
int32_t
btor_node_compare_by_id (const BtorNode *exp0, const BtorNode *exp1)
{
  assert (exp0);
  assert (exp1);

  uint32_t id0, id1;

  id0 = btor_node_get_id (exp0);
  id1 = btor_node_get_id (exp1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

int32_t
btor_node_compare_by_id_qsort_desc (const void *p, const void *q)
{
  BtorNode *a = btor_node_real_addr (*(BtorNode **) p);
  BtorNode *b = btor_node_real_addr (*(BtorNode **) q);
  return b->id - a->id;
}

int32_t
btor_node_compare_by_id_qsort_asc (const void *p, const void *q)
{
  BtorNode *a = btor_node_real_addr (*(BtorNode **) p);
  BtorNode *b = btor_node_real_addr (*(BtorNode **) q);
  return a->id - b->id;
}

/* Computes hash value of expression by id */
uint32_t
btor_node_hash_by_id (const BtorNode *exp)
{
  assert (exp);
  return (uint32_t) btor_node_get_id (exp) * 7334147u;
}

/*------------------------------------------------------------------------*/

uint32_t
btor_node_bv_get_width (Btor *btor, const BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (!btor_node_is_fun (exp));
  assert (!btor_node_is_args (exp));
  return btor_sort_bv_get_width (btor, btor_node_get_sort_id (exp));
}

uint32_t
btor_node_fun_get_width (Btor *btor, const BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));

  assert (btor_sort_is_fun (btor, btor_node_get_sort_id (exp)));
  return btor_sort_bv_get_width (
      btor, btor_sort_fun_get_codomain (btor, btor_node_get_sort_id (exp)));
}

uint32_t
btor_node_array_get_index_width (Btor *btor, const BtorNode *e_array)
{
  assert (btor);
  assert (e_array);
  assert (btor == btor_node_real_addr (e_array)->btor);

  assert (btor_sort_is_array (btor, btor_node_get_sort_id (e_array))
          || btor_sort_is_fun (btor, btor_node_get_sort_id (e_array)));
  return btor_sort_bv_get_width (
      btor, btor_sort_array_get_index (btor, btor_node_get_sort_id (e_array)));
}

/*------------------------------------------------------------------------*/

BtorBitVector *
btor_node_bv_const_get_bits (BtorNode *exp)
{
  assert (exp);
  assert (btor_node_is_bv_const (exp));
  return ((BtorBVConstNode *) btor_node_real_addr (exp))->bits;
}

BtorBitVector *
btor_node_bv_const_get_invbits (BtorNode *exp)
{
  assert (exp);
  assert (btor_node_is_bv_const (exp));
  return ((BtorBVConstNode *) btor_node_real_addr (exp))->invbits;
}

void
btor_node_bv_const_set_bits (BtorNode *exp, BtorBitVector *bits)
{
  assert (exp);
  assert (btor_node_is_bv_const (exp));
  ((BtorBVConstNode *) btor_node_real_addr (exp))->bits = bits;
}

void
btor_node_bv_const_set_invbits (BtorNode *exp, BtorBitVector *bits)
{
  assert (exp);
  assert (btor_node_is_bv_const (exp));
  ((BtorBVConstNode *) btor_node_real_addr (exp))->invbits = bits;
}

/*------------------------------------------------------------------------*/

uint32_t
btor_node_fun_get_arity (Btor *btor, BtorNode *exp)
{
  (void) btor;
  assert (btor);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  assert (btor_node_is_regular (exp));
  assert (btor_sort_is_fun (btor, btor_node_get_sort_id (exp)));
  return btor_sort_fun_get_arity (btor, btor_node_get_sort_id (exp));
}

uint32_t
btor_node_args_get_arity (Btor *btor, BtorNode *exp)
{
  (void) btor;
  assert (btor);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);
  exp = btor_simplify_exp (btor, exp);
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_args (exp));
  return btor_sort_tuple_get_arity (btor, btor_node_get_sort_id (exp));
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_node_binder_get_body (BtorNode *binder)
{
  assert (btor_node_is_regular (binder));
  assert (btor_node_is_binder (binder));
  return ((BtorBinderNode *) binder)->body;
}

void
btor_node_binder_set_body (BtorNode *binder, BtorNode *body)
{
  assert (btor_node_is_regular (binder));
  assert (btor_node_is_binder (binder));
  ((BtorBinderNode *) binder)->body = body;
}

/*------------------------------------------------------------------------*/

BtorPtrHashTable *
btor_node_lambda_get_static_rho (BtorNode *lambda)
{
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));
  return ((BtorLambdaNode *) lambda)->static_rho;
}

void
btor_node_lambda_set_static_rho (BtorNode *lambda, BtorPtrHashTable *static_rho)
{
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));
  ((BtorLambdaNode *) lambda)->static_rho = static_rho;
}

BtorPtrHashTable *
btor_node_lambda_copy_static_rho (Btor *btor, BtorNode *lambda)
{
  assert (btor_node_is_regular (lambda));
  assert (btor_node_is_lambda (lambda));
  assert (btor_node_lambda_get_static_rho (lambda));

  BtorNode *data, *key;
  BtorPtrHashTableIterator it;
  BtorPtrHashTable *static_rho;

  btor_iter_hashptr_init (&it, btor_node_lambda_get_static_rho (lambda));
  static_rho = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);
  while (btor_iter_hashptr_has_next (&it))
  {
    data = btor_node_copy (btor, it.bucket->data.as_ptr);
    key  = btor_node_copy (btor, btor_iter_hashptr_next (&it));
    btor_hashptr_table_add (static_rho, key)->data.as_ptr = data;
  }
  return static_rho;
}

void
btor_node_lambda_delete_static_rho (Btor *btor, BtorNode *lambda)
{
  BtorPtrHashTable *static_rho;
  BtorPtrHashTableIterator it;

  static_rho = btor_node_lambda_get_static_rho (lambda);
  if (!static_rho) return;

  btor_iter_hashptr_init (&it, static_rho);
  while (btor_iter_hashptr_has_next (&it))
  {
    btor_node_release (btor, it.bucket->data.as_ptr);
    btor_node_release (btor, btor_iter_hashptr_next (&it));
  }
  btor_hashptr_table_delete (static_rho);
  btor_node_lambda_set_static_rho (lambda, 0);
}

/*------------------------------------------------------------------------*/

uint32_t
btor_node_bv_slice_get_upper (BtorNode *slice)
{
  assert (btor_node_is_bv_slice (slice));
  return ((BtorBVSliceNode *) btor_node_real_addr (slice))->upper;
}

uint32_t
btor_node_bv_slice_get_lower (BtorNode *slice)
{
  assert (btor_node_is_bv_slice (slice));
  return ((BtorBVSliceNode *) btor_node_real_addr (slice))->lower;
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_node_param_get_binder (BtorNode *param)
{
  assert (btor_node_is_param (param));
  return ((BtorParamNode *) btor_node_real_addr (param))->binder;
}

void
btor_node_param_set_binder (BtorNode *param, BtorNode *binder)
{
  assert (btor_node_is_param (param));
  assert (!binder || btor_node_is_binder (binder));

  BtorNode *q;

  /* param is not bound anymore, remove from exists/forall vars tables */
  if (!binder)
  {
    q = btor_node_param_get_binder (param);
    if (q)
    {
      if (btor_node_is_exists (q))
        btor_hashptr_table_remove (param->btor->exists_vars, param, 0, 0);
      else if (btor_node_is_forall (q))
        btor_hashptr_table_remove (param->btor->forall_vars, param, 0, 0);
    }
  }
  /* param is bound, add to exists/forall vars tables */
  else
  {
    if (btor_node_is_exists (binder))
      (void) btor_hashptr_table_add (param->btor->exists_vars, param);
    else if (btor_node_is_forall (binder))
      (void) btor_hashptr_table_add (param->btor->forall_vars, param);
  }
  ((BtorParamNode *) btor_node_real_addr (param))->binder = binder;
}

bool
btor_node_param_is_bound (BtorNode *param)
{
  assert (btor_node_is_param (param));
  return btor_node_param_get_binder (param) != 0;
}

bool
btor_node_param_is_exists_var (BtorNode *param)
{
  assert (btor_node_is_param (param));
  return btor_node_is_exists (btor_node_param_get_binder (param));
}

bool
btor_node_param_is_forall_var (BtorNode *param)
{
  assert (btor_node_is_param (param));
  return btor_node_is_forall (btor_node_param_get_binder (param));
}

BtorNode *
btor_node_param_get_assigned_exp (BtorNode *param)
{
  assert (btor_node_is_param (param));
  return ((BtorParamNode *) btor_node_real_addr (param))->assigned_exp;
}

BtorNode *
btor_node_param_set_assigned_exp (BtorNode *param, BtorNode *exp)
{
  assert (btor_node_is_param (param));
  assert (!exp || btor_node_get_sort_id (param) == btor_node_get_sort_id (exp));
  return ((BtorParamNode *) btor_node_real_addr (param))->assigned_exp = exp;
}

/*------------------------------------------------------------------------*/

static bool
is_sorted_bv_exp (Btor *btor, BtorNodeKind kind, BtorNode *e[])
{
  if (!btor_opt_get (btor, BTOR_OPT_SORT_EXP)) return 1;
  if (!btor_node_is_binary_commutative_kind (kind)) return 1;
  if (e[0] == e[1]) return 1;
  if (btor_node_invert (e[0]) == e[1] && btor_node_is_inverted (e[1])) return 1;
  return btor_node_real_addr (e[0])->id <= btor_node_real_addr (e[1])->id;
}

static void
sort_bv_exp (Btor *btor, BtorNodeKind kind, BtorNode *e[])
{
  if (!is_sorted_bv_exp (btor, kind, e)) BTOR_SWAP (BtorNode *, e[0], e[1]);
}

/*------------------------------------------------------------------------*/

/* Search for constant expression in hash table. Returns 0 if not found. */
static BtorNode **
find_const_exp (Btor *btor, BtorBitVector *bits)
{
  assert (btor);
  assert (bits);

  BtorNode *cur, **result;
  uint32_t hash;

  hash = btor_bv_hash (bits);
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (btor_node_is_regular (cur));
    if (btor_node_is_bv_const (cur)
        && btor_node_bv_get_width (btor, cur) == bits->width
        && !btor_bv_compare (btor_node_bv_const_get_bits (cur), bits))
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
  uint32_t hash;

  hash = hash_slice_exp (e0, upper, lower);
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (btor_node_is_regular (cur));
    if (cur->kind == BTOR_BV_SLICE_NODE && cur->e[0] == e0
        && btor_node_bv_slice_get_upper (cur) == upper
        && btor_node_bv_slice_get_lower (cur) == lower)
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
find_bv_exp (Btor *btor, BtorNodeKind kind, BtorNode *e[], uint32_t arity)
{
  bool equal;
  uint32_t i;
  uint32_t hash;
  BtorNode *cur, **result;

  assert (kind != BTOR_BV_SLICE_NODE);
  assert (kind != BTOR_CONST_NODE);

  sort_bv_exp (btor, kind, e);
  hash = hash_bv_exp (btor, kind, arity, e);
  hash &= btor->nodes_unique_table.size - 1;

  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (btor_node_is_regular (cur));
    if (cur->kind == kind && cur->arity == arity)
    {
      equal = true;
      /* special case for bv eq; (= (bvnot a) b) == (= a (bvnot b)) */
      if (kind == BTOR_BV_EQ_NODE && cur->e[0] == btor_node_invert (e[0])
          && cur->e[1] == btor_node_invert (e[1]))
        break;
      for (i = 0; i < arity && equal; i++)
        if (cur->e[i] != e[i]) equal = false;
      if (equal) break;
#ifndef NDEBUG
      if (btor_opt_get (btor, BTOR_OPT_SORT_EXP) > 0
          && btor_node_is_binary_commutative_kind (kind))
        assert (arity == 2),
            assert (e[0] == e[1] || btor_node_invert (e[0]) == e[1]
                    || !(cur->e[0] == e[1] && cur->e[1] == e[0]));
#endif
    }
    result = &(cur->next);
    cur    = *result;
  }
  return result;
}

static int32_t compare_binder_exp (Btor *btor,
                                   BtorNode *param,
                                   BtorNode *body,
                                   BtorNode *binder,
                                   BtorPtrHashTable *map);

static BtorNode **
find_binder_exp (Btor *btor,
                 BtorNodeKind kind,
                 BtorNode *param,
                 BtorNode *body,
                 uint32_t *binder_hash,
                 BtorIntHashTable *params,
                 BtorPtrHashTable *map)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (btor_node_is_regular (param));
  assert (btor_node_is_param (param));

  BtorNode *cur, **result;
  uint32_t hash;

  hash = hash_binder_exp (btor, param, body, params);
  if (binder_hash) *binder_hash = hash;
  hash &= btor->nodes_unique_table.size - 1;
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (btor_node_is_regular (cur));
    if (cur->kind == kind
        && ((!map && param == cur->e[0] && body == cur->e[1])
            || (((map || !cur->parameterized)
                 && compare_binder_exp (btor, param, body, cur, map)))))
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  assert (!*result || btor_node_is_binder (*result));
  return result;
}

static int32_t
compare_binder_exp (Btor *btor,
                    BtorNode *param,
                    BtorNode *body,
                    BtorNode *binder,
                    BtorPtrHashTable *map)
{
  assert (btor);
  assert (param);
  assert (body);
  assert (btor_node_is_regular (param));
  assert (btor_node_is_param (param));
  assert (btor_node_is_regular (binder));
  assert (btor_node_is_binder (binder));
  assert (!binder->parameterized || map);

  int32_t i, equal = 0;
  BtorMemMgr *mm;
  BtorNode *cur, *real_cur, *result, *subst_param, **e, *b0, *b1;
  BtorPtrHashTable *cache, *param_map;
  BtorPtrHashBucket *b, *bb;
  BtorNodePtrStack stack, args;
  BtorNodeIterator it, iit;
  BtorPtrHashTableIterator h_it;

  mm          = btor->mm;
  subst_param = binder->e[0];

  if (btor_node_get_sort_id (subst_param) != btor_node_get_sort_id (param)
      || btor_node_get_sort_id (body) != btor_node_get_sort_id (binder->e[1]))
    return 0;

  cache = btor_hashptr_table_new (mm, 0, 0);

  /* create param map */
  param_map = btor_hashptr_table_new (mm, 0, 0);
  btor_hashptr_table_add (param_map, param)->data.as_ptr = subst_param;

  if (map)
  {
    btor_iter_hashptr_init (&h_it, map);
    while (btor_iter_hashptr_has_next (&h_it))
    {
      subst_param = h_it.bucket->data.as_ptr;
      cur         = btor_iter_hashptr_next (&h_it);
      btor_hashptr_table_add (param_map, cur)->data.as_ptr = subst_param;
    }
  }

  if (btor_node_is_binder (body) && btor_node_is_binder (binder->e[1])
      && btor_node_is_inverted (body) == btor_node_is_inverted (binder->e[1]))
  {
    btor_iter_binder_init (&it, btor_node_real_addr (body));
    btor_iter_binder_init (&iit, btor_node_real_addr (binder->e[1]));
    while (btor_iter_binder_has_next (&it))
    {
      if (!btor_iter_binder_has_next (&iit)) goto NOT_EQUAL;

      b0 = btor_iter_binder_next (&it);
      b1 = btor_iter_binder_next (&iit);

      if (btor_node_get_sort_id (b0) != btor_node_get_sort_id (b1)
          || b0->kind != b1->kind)
        goto NOT_EQUAL;

      param       = b0->e[0];
      subst_param = b1->e[0];
      assert (btor_node_is_regular (param));
      assert (btor_node_is_regular (subst_param));
      assert (btor_node_is_param (param));
      assert (btor_node_is_param (subst_param));

      if (btor_node_get_sort_id (param) != btor_node_get_sort_id (subst_param))
        goto NOT_EQUAL;

      btor_hashptr_table_add (param_map, param)->data.as_ptr = subst_param;
    }
    body = btor_node_binder_get_body (btor_node_real_addr (body));
  }
  else if (btor_node_is_binder (body) || btor_node_is_binder (binder->e[1]))
    goto NOT_EQUAL;

  BTOR_INIT_STACK (mm, args);
  BTOR_INIT_STACK (mm, stack);
  BTOR_PUSH_STACK (stack, body);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur      = BTOR_POP_STACK (stack);
    real_cur = btor_node_real_addr (cur);

    if (!real_cur->parameterized)
    {
      BTOR_PUSH_STACK (args, cur);
      continue;
    }

    b = btor_hashptr_table_get (cache, real_cur);

    if (!b)
    {
      b = btor_hashptr_table_add (cache, real_cur);

      if (btor_node_is_binder (real_cur))
      {
        result = *find_binder_exp (btor,
                                   real_cur->kind,
                                   real_cur->e[0],
                                   real_cur->e[1],
                                   0,
                                   0,
                                   param_map);
        if (result)
        {
          b->data.as_ptr = result;
          BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
          continue;
        }
        else
        {
          BTOR_RESET_STACK (args);
          break;
        }
      }

      BTOR_PUSH_STACK (stack, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (stack, real_cur->e[i]);
    }
    else if (!b->data.as_ptr)
    {
      assert (!btor_node_is_binder (real_cur));
      assert (BTOR_COUNT_STACK (args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (btor_node_is_bv_slice (real_cur))
      {
        result = *find_slice_exp (btor,
                                  e[0],
                                  btor_node_bv_slice_get_upper (real_cur),
                                  btor_node_bv_slice_get_lower (real_cur));
      }
      else if (btor_node_is_param (real_cur))
      {
        if ((bb = btor_hashptr_table_get (param_map, real_cur)))
          result = bb->data.as_ptr;
        else
          result = real_cur;
      }
      else
      {
        assert (!btor_node_is_binder (real_cur));
        result = *find_bv_exp (btor, real_cur->kind, e, real_cur->arity);
      }

      if (!result)
      {
        BTOR_RESET_STACK (args);
        break;
      }

      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, result));
      b->data.as_ptr = result;
    }
    else
    {
      assert (b->data.as_ptr);
      BTOR_PUSH_STACK (args, btor_node_cond_invert (cur, b->data.as_ptr));
    }
  }
  assert (BTOR_COUNT_STACK (args) <= 1);

  if (!BTOR_EMPTY_STACK (args))
    equal = BTOR_TOP_STACK (args) == btor_node_binder_get_body (binder);

  BTOR_RELEASE_STACK (stack);
  BTOR_RELEASE_STACK (args);
NOT_EQUAL:
  btor_hashptr_table_delete (cache);
  btor_hashptr_table_delete (param_map);
  return equal;
}

static BtorNode **
find_exp (Btor *btor,
          BtorNodeKind kind,
          BtorNode *e[],
          uint32_t arity,
          uint32_t *binder_hash,
          BtorIntHashTable *params)
{
  assert (btor);
  assert (arity > 0);
  assert (e);

#ifndef NDEBUG
  uint32_t i;
  for (i = 0; i < arity; i++) assert (e[i]);
#endif

  if (kind == BTOR_LAMBDA_NODE || kind == BTOR_FORALL_NODE
      || kind == BTOR_EXISTS_NODE)
    return find_binder_exp (btor, kind, e[0], e[1], binder_hash, params, 0);
  else if (binder_hash)
    *binder_hash = 0;

  return find_bv_exp (btor, kind, e, arity);
}

/*------------------------------------------------------------------------*/

static BtorNode *
new_const_exp_node (Btor *btor, BtorBitVector *bits)
{
  assert (btor);
  assert (bits);

  BtorBVConstNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_CONST_NODE);
  exp->bytes = sizeof *exp;
  btor_node_set_sort_id ((BtorNode *) exp,
                         btor_sort_bv (btor, bits->width));
  setup_node_and_add_to_id_table (btor, exp);
  btor_node_bv_const_set_bits ((BtorNode *) exp, btor_bv_copy (btor->mm, bits));
  btor_node_bv_const_set_invbits ((BtorNode *) exp,
                                  btor_bv_not (btor->mm, bits));
  return (BtorNode *) exp;
}

static BtorNode *
new_slice_exp_node (Btor *btor, BtorNode *e0, uint32_t upper, uint32_t lower)
{
  assert (btor);
  assert (e0);
  assert (btor == btor_node_real_addr (e0)->btor);
  assert (upper < btor_node_bv_get_width (btor, e0));
  assert (upper >= lower);

  BtorBVSliceNode *exp = 0;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_BV_SLICE_NODE);
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  exp->upper = upper;
  exp->lower = lower;
  btor_node_set_sort_id ((BtorNode *) exp,
                         btor_sort_bv (btor, upper - lower + 1));
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, (BtorNode *) exp, e0, 0);
  return (BtorNode *) exp;
}

static BtorNode *
new_lambda_exp_node (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (e_param);
  assert (btor_node_is_regular (e_param));
  assert (btor_node_is_param (e_param));
  assert (!btor_node_param_is_bound (e_param));
  assert (e_exp);
  assert (btor == e_param->btor);
  assert (btor == btor_node_real_addr (e_exp)->btor);

  BtorSortId s, domain, codomain;
  BtorSortIdStack param_sorts;
  BtorLambdaNode *lambda_exp;
  BtorTupleSortIterator it;
  BtorPtrHashBucket *b;
  BtorIntHashTable *params;

  BTOR_INIT_STACK (btor->mm, param_sorts);

  BTOR_CNEW (btor->mm, lambda_exp);
  set_kind (btor, (BtorNode *) lambda_exp, BTOR_LAMBDA_NODE);
  lambda_exp->bytes        = sizeof *lambda_exp;
  lambda_exp->arity        = 2;
  lambda_exp->lambda_below = 1;
  setup_node_and_add_to_id_table (btor, (BtorNode *) lambda_exp);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_param, 0);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_exp, 1);

  BTOR_PUSH_STACK (param_sorts, btor_node_get_sort_id (e_param));
  /* curried lambdas (functions) */
  if (btor_node_is_lambda (e_exp))
  {
    btor_node_binder_set_body (
        (BtorNode *) lambda_exp,
        btor_simplify_exp (btor, btor_node_binder_get_body (e_exp)));
    btor_iter_tuple_sort_init (
        &it,
        btor,
        btor_sort_fun_get_domain (btor, btor_node_get_sort_id (e_exp)));
    while (btor_iter_tuple_sort_has_next (&it))
    {
      s = btor_iter_tuple_sort_next (&it);
      BTOR_PUSH_STACK (param_sorts, s);
    }

    if ((b = btor_hashptr_table_get (btor->parameterized, e_exp)))
    {
      params = b->data.as_ptr;
      btor_hashint_table_remove (params, e_param->id);
      btor_hashptr_table_remove (btor->parameterized, e_exp, 0, 0);
      if (params->count > 0)
      {
        btor_hashptr_table_add (btor->parameterized, lambda_exp)->data.as_ptr =
            params;
        lambda_exp->parameterized = 1;
      }
      else
        btor_hashint_table_delete (params);
    }
  }
  else
    btor_node_binder_set_body ((BtorNode *) lambda_exp, e_exp);

  domain =
      btor_sort_tuple (btor, param_sorts.start, BTOR_COUNT_STACK (param_sorts));
  codomain = btor_node_get_sort_id (lambda_exp->body);
  btor_node_set_sort_id ((BtorNode *) lambda_exp,
                         btor_sort_fun (btor, domain, codomain));

  btor_sort_release (btor, domain);
  BTOR_RELEASE_STACK (param_sorts);

  assert (!btor_node_real_addr (lambda_exp->body)->simplified);
  assert (!btor_node_is_lambda (lambda_exp->body));
  assert (!btor_hashptr_table_get (btor->lambdas, lambda_exp));
  (void) btor_hashptr_table_add (btor->lambdas, lambda_exp);
  /* set lambda expression of parameter */
  btor_node_param_set_binder (e_param, (BtorNode *) lambda_exp);
  return (BtorNode *) lambda_exp;
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
  assert (btor_node_is_regular (param));
  assert (btor_node_is_param (param));
  assert (!btor_node_param_is_bound (param));
  assert (btor_sort_is_bool (btor, btor_node_real_addr (body)->sort_id));
  assert (btor == param->btor);
  assert (btor == btor_node_real_addr (body)->btor);

  BtorBinderNode *res;

  BTOR_CNEW (btor->mm, res);
  set_kind (btor, (BtorNode *) res, kind);
  res->bytes            = sizeof *res;
  res->arity            = 2;
  res->quantifier_below = 1;
  res->sort_id = btor_sort_copy (btor, btor_node_real_addr (body)->sort_id);
  setup_node_and_add_to_id_table (btor, (BtorNode *) res);
  connect_child_exp (btor, (BtorNode *) res, param, 0);
  connect_child_exp (btor, (BtorNode *) res, body, 1);

  /* curried (non-inverted) quantifiers */
  if (!btor_node_is_inverted (body) && btor_node_is_quantifier (body))
    res->body = btor_simplify_exp (btor, btor_node_binder_get_body (body));
  else
    res->body = body;

#if 0
  /* check if 'res' is parameterized, i.e. if it contains params that are not
   * bound by 'res' */
  remove_param_parameterized (btor, (BtorNode *) res, param);
  if (is_parameterized (btor, (BtorNode *) res))
    res->parameterized = 1;
#endif

  assert (!btor_node_real_addr (res->body)->simplified);
  assert (!btor_node_is_lambda (res->body));
  btor_node_param_set_binder (param, (BtorNode *) res);
  assert (!btor_hashptr_table_get (btor->quantifiers, res));
  (void) btor_hashptr_table_add (btor->quantifiers, res);
  return (BtorNode *) res;
}

static BtorNode *
new_args_exp_node (Btor *btor, uint32_t arity, BtorNode *e[])
{
  assert (btor);
  assert (arity > 0);
  assert (arity <= 3);
  assert (e);

  uint32_t i;
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
  BTOR_INIT_STACK (btor->mm, sorts);
  for (i = 0; i < arity; i++)
  {
    if (btor_node_is_args (e[i]))
    {
      assert (i == 2);
      assert (btor_node_is_regular (e[i]));
      btor_iter_tuple_sort_init (&it, btor, btor_node_get_sort_id (e[i]));
      while (btor_iter_tuple_sort_has_next (&it))
        BTOR_PUSH_STACK (sorts, btor_iter_tuple_sort_next (&it));
    }
    else
      BTOR_PUSH_STACK (sorts, btor_node_get_sort_id (e[i]));
  }
  btor_node_set_sort_id (
      (BtorNode *) exp,
      btor_sort_tuple (btor, sorts.start, BTOR_COUNT_STACK (sorts)));
  BTOR_RELEASE_STACK (sorts);
  return (BtorNode *) exp;
}

static BtorNode *
new_node (Btor *btor, BtorNodeKind kind, uint32_t arity, BtorNode *e[])
{
  assert (btor);
  assert (arity > 0);
  assert (arity <= 3);
  assert (btor_node_is_binary_kind (kind) || btor_node_is_ternary_kind (kind));
  assert (e);

#ifndef NDEBUG
  if (btor_opt_get (btor, BTOR_OPT_SORT_EXP) > 0
      && btor_node_is_binary_commutative_kind (kind))
    assert (arity == 2), assert (btor_node_real_addr (e[0])->id
                                 <= btor_node_real_addr (e[1])->id);
#endif

  uint32_t i;
  BtorBVNode *exp;
  BtorSortId sort;

#ifdef NDEBUG
  for (i = 0; i < arity; i++)
  {
    assert (e[i]);
    assert (btor == btor_node_real_addr (e[i])->btor);
  }
#endif

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, kind);
  exp->bytes = sizeof (*exp);
  exp->arity = arity;
  setup_node_and_add_to_id_table (btor, exp);

  switch (kind)
  {
    case BTOR_COND_NODE:
      sort = btor_sort_copy (btor, btor_node_get_sort_id (e[1]));
      break;

    case BTOR_BV_CONCAT_NODE:
      sort = btor_sort_bv (btor,
                               btor_node_bv_get_width (btor, e[0])
                                   + btor_node_bv_get_width (btor, e[1]));
      break;

    case BTOR_FUN_EQ_NODE:
    case BTOR_BV_EQ_NODE:
    case BTOR_BV_ULT_NODE: sort = btor_sort_bool (btor); break;

    case BTOR_APPLY_NODE:
      sort = btor_sort_copy (
          btor,
          btor_sort_fun_get_codomain (btor, btor_node_get_sort_id (e[0])));
      break;

    default:
      assert (kind == BTOR_BV_AND_NODE || kind == BTOR_BV_ADD_NODE
              || kind == BTOR_BV_MUL_NODE || kind == BTOR_BV_SLL_NODE
              || kind == BTOR_BV_SRL_NODE || kind == BTOR_BV_UDIV_NODE
              || kind == BTOR_BV_UREM_NODE || kind == BTOR_UPDATE_NODE);
      sort = btor_sort_copy (btor, btor_node_get_sort_id (e[0]));
  }

  btor_node_set_sort_id ((BtorNode *) exp, sort);

  for (i = 0; i < arity; i++)
    connect_child_exp (btor, (BtorNode *) exp, e[i], i);

  if (kind == BTOR_FUN_EQ_NODE)
  {
    assert (!btor_hashptr_table_get (btor->feqs, exp));
    btor_hashptr_table_add (btor->feqs, exp)->data.as_int = 0;
  }

  return (BtorNode *) exp;
}

/*------------------------------------------------------------------------*/

static BtorNode *
create_exp (Btor *btor, BtorNodeKind kind, uint32_t arity, BtorNode *e[])
{
  assert (btor);
  assert (kind);
  assert (arity > 0);
  assert (arity <= 3);
  assert (e);

  uint32_t i;
  uint32_t binder_hash;
  BtorNode **lookup, *simp_e[3];
  BtorIntHashTable *params = 0;

  for (i = 0; i < arity; i++)
  {
    assert (btor_node_real_addr (e[i])->btor == btor);
    simp_e[i] = btor_simplify_exp (btor, e[i]);
  }

  /* collect params only for quantifier/function bodies */
  if ((kind == BTOR_LAMBDA_NODE && !btor_node_is_lambda (e[1]))
      || kind == BTOR_FORALL_NODE || kind == BTOR_EXISTS_NODE)
    params = btor_hashint_table_new (btor->mm);

  lookup = find_exp (btor, kind, simp_e, arity, &binder_hash, params);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_exp (btor, kind, simp_e, arity, &binder_hash, 0);
    }

    switch (kind)
    {
      case BTOR_LAMBDA_NODE:
        assert (arity == 2);
        *lookup = new_lambda_exp_node (btor, simp_e[0], simp_e[1]);
        btor_hashptr_table_get (btor->lambdas, *lookup)->data.as_int =
            binder_hash;
        break;
      case BTOR_FORALL_NODE:
      case BTOR_EXISTS_NODE:
        assert (arity == 2);
        *lookup = new_quantifier_exp_node (btor, kind, e[0], e[1]);
        btor_hashptr_table_get (btor->quantifiers, *lookup)->data.as_int =
            binder_hash;
        break;
      case BTOR_ARGS_NODE:
        *lookup = new_args_exp_node (btor, arity, simp_e);
        break;
      default: *lookup = new_node (btor, kind, arity, simp_e);
    }

    if (params)
    {
      assert (btor_node_is_binder (*lookup));
      if (params->count > 0)
      {
        btor_hashptr_table_add (btor->parameterized, *lookup)->data.as_ptr =
            params;
        (*lookup)->parameterized = 1;
      }
      else
        btor_hashint_table_delete (params);
    }

    assert (btor->nodes_unique_table.num_elements < INT32_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter (btor, *lookup);
    if (params) btor_hashint_table_delete (params);
  }
  assert (btor_node_is_regular (*lookup));
  return *lookup;
}

/*------------------------------------------------------------------------*/

BtorNode *
btor_node_create_bv_const (Btor *btor, const BtorBitVector *bits)
{
  assert (btor);
  assert (bits);

  bool inv;
  BtorBitVector *lookupbits;
  BtorNode **lookup;

  /* normalize constants, constants are always even */
  if (btor_bv_get_bit (bits, 0))
  {
    lookupbits = btor_bv_not (btor->mm, bits);
    inv        = true;
  }
  else
  {
    lookupbits = btor_bv_copy (btor->mm, bits);
    inv        = false;
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
    assert (btor->nodes_unique_table.num_elements < INT32_MAX);
    btor->nodes_unique_table.num_elements += 1;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);

  assert (btor_node_is_regular (*lookup));

  btor_bv_free (btor->mm, lookupbits);

  if (inv) return btor_node_invert (*lookup);
  return *lookup;
}

BtorNode *
btor_node_create_var (Btor *btor, BtorSortId sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));
  assert (!symbol || !btor_hashptr_table_get (btor->symbols, (char *) symbol));

  BtorBVVarNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_VAR_NODE);
  exp->bytes = sizeof *exp;
  setup_node_and_add_to_id_table (btor, exp);
  btor_node_set_sort_id ((BtorNode *) exp, btor_sort_copy (btor, sort));
  (void) btor_hashptr_table_add (btor->bv_vars, exp);
  if (symbol) btor_node_set_symbol (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

BtorNode *
btor_node_create_uf (Btor *btor, BtorSortId sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (!symbol || !btor_hashptr_table_get (btor->symbols, (char *) symbol));

  BtorUFNode *exp;

  assert (btor_sort_is_fun (btor, sort));
  assert (btor_sort_is_bv (btor, btor_sort_fun_get_codomain (btor, sort))
          || btor_sort_is_bool (btor, btor_sort_fun_get_codomain (btor, sort)));

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_UF_NODE);
  exp->bytes = sizeof (*exp);
  btor_node_set_sort_id ((BtorNode *) exp, btor_sort_copy (btor, sort));
  setup_node_and_add_to_id_table (btor, exp);
  (void) btor_hashptr_table_add (btor->ufs, exp);
  if (symbol) btor_node_set_symbol (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

BtorNode *
btor_node_create_param (Btor *btor, BtorSortId sort, const char *symbol)
{
  assert (btor);
  assert (sort);
  assert (btor_sort_is_bv (btor, sort));
  assert (!symbol || !btor_hashptr_table_get (btor->symbols, (char *) symbol));

  BtorParamNode *exp;

  BTOR_CNEW (btor->mm, exp);
  set_kind (btor, (BtorNode *) exp, BTOR_PARAM_NODE);
  exp->bytes         = sizeof *exp;
  exp->parameterized = 1;
  btor_node_set_sort_id ((BtorNode *) exp, btor_sort_copy (btor, sort));
  setup_node_and_add_to_id_table (btor, exp);
  if (symbol) btor_node_set_symbol (btor, (BtorNode *) exp, symbol);
  return (BtorNode *) exp;
}

static BtorNode *
unary_exp_slice_exp (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (btor);
  assert (exp);
  assert (btor == btor_node_real_addr (exp)->btor);

  bool inv;
  BtorNode **lookup;

  exp = btor_simplify_exp (btor, exp);

  assert (!btor_node_is_fun (exp));
  assert (upper >= lower);
  assert (upper < btor_node_bv_get_width (btor, exp));

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0
      && btor_node_is_inverted (exp))
  {
    inv = true;
    exp = btor_node_invert (exp);
  }
  else
    inv = false;

  lookup = find_slice_exp (btor, exp, upper, lower);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_slice_exp (btor, exp, upper, lower);
    }
    *lookup = new_slice_exp_node (btor, exp, upper, lower);
    assert (btor->nodes_unique_table.num_elements < INT32_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (btor_node_is_regular (*lookup));
  if (inv) return btor_node_invert (*lookup);
  return *lookup;
}

BtorNode *
btor_node_create_bv_slice (Btor *btor,
                           BtorNode *exp,
                           uint32_t upper,
                           uint32_t lower)
{
  exp = btor_simplify_exp (btor, exp);
  assert (btor_dbg_precond_slice_exp (btor, exp, upper, lower));
  return unary_exp_slice_exp (btor, exp, upper, lower);
}

BtorNode *
btor_node_create_bv_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_AND_NODE, 2, e);
}

BtorNode *
btor_node_create_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  BtorNodeKind kind;

  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_eq_exp (btor, e[0], e[1]));
  if (btor_node_is_fun (e[0]))
    kind = BTOR_FUN_EQ_NODE;
  else
    kind = BTOR_BV_EQ_NODE;
  return create_exp (btor, kind, 2, e);
}

BtorNode *
btor_node_create_bv_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_ADD_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_MUL_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_ULT_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_SLL_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_SRL_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_UDIV_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_UREM_NODE, 2, e);
}

BtorNode *
btor_node_create_bv_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e0);
  e[1] = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_concat_exp (btor, e[0], e[1]));
  return create_exp (btor, BTOR_BV_CONCAT_NODE, 2, e);
}

BtorNode *
btor_node_create_cond (Btor *btor,
                       BtorNode *e_cond,
                       BtorNode *e_if,
                       BtorNode *e_else)
{
  uint32_t i, arity;
  BtorNode *e[3], *cond, *lambda;
  BtorNodePtrStack params;
  BtorSort *sort;
  e[0] = btor_simplify_exp (btor, e_cond);
  e[1] = btor_simplify_exp (btor, e_if);
  e[2] = btor_simplify_exp (btor, e_else);
  assert (btor_dbg_precond_cond_exp (btor, e[0], e[1], e[2]));

  /* represent parameterized function conditionals (with parameterized
   * functions) as parameterized function
   * -> gets beta reduced in btor_node_create_apply */
  if (btor_node_is_fun (e[1]) && (e[1]->parameterized || e[2]->parameterized))
  {
    BTOR_INIT_STACK (btor->mm, params);
    assert (btor_sort_is_fun (btor, btor_node_get_sort_id (e[1])));
    arity = btor_node_fun_get_arity (btor, e[1]);
    sort  = btor_sort_get_by_id (btor, btor_node_get_sort_id (e[1]));
    assert (sort->fun.domain->kind == BTOR_TUPLE_SORT);
    assert (sort->fun.domain->tuple.num_elements == arity);
    for (i = 0; i < arity; i++)
      BTOR_PUSH_STACK (
          params,
          btor_exp_param (btor, sort->fun.domain->tuple.elements[i]->id, 0));
    e[1]   = btor_exp_apply_n (btor, e[1], params.start, arity);
    e[2]   = btor_exp_apply_n (btor, e[2], params.start, arity);
    cond   = create_exp (btor, BTOR_COND_NODE, 3, e);
    lambda = btor_exp_fun (btor, params.start, arity, cond);
    while (!BTOR_EMPTY_STACK (params))
      btor_node_release (btor, BTOR_POP_STACK (params));
    btor_node_release (btor, e[1]);
    btor_node_release (btor, e[2]);
    btor_node_release (btor, cond);
    BTOR_RELEASE_STACK (params);
    return lambda;
  }
  return create_exp (btor, BTOR_COND_NODE, 3, e);
}

#if 0
BtorNode *
btor_bv_cond_exp_node (Btor * btor, BtorNode * e_cond, BtorNode * e_if,
		       BtorNode * e_else)
{
  assert (btor == btor_node_real_addr (e_cond)->btor);
  assert (btor == btor_node_real_addr (e_if)->btor);
  assert (btor == btor_node_real_addr (e_else)->btor);

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0)
    return btor_rewrite_ternary_exp (btor, BTOR_BCOND_NODE, e_cond, e_if, e_else);

  return btor_node_create_cond (btor, e_cond, e_if, e_else);
}

// TODO: arbitrary conditionals on functions
BtorNode *
btor_array_cond_exp_node (Btor * btor, BtorNode * e_cond, BtorNode * e_if,
			  BtorNode * e_else)
{
  assert (btor == btor_node_real_addr (e_cond)->btor);
  assert (btor == btor_node_real_addr (e_if)->btor);
  assert (btor == btor_node_real_addr (e_else)->btor);

  BtorNode *cond, *param, *lambda, *app_if, *app_else;

  e_cond = btor_simplify_exp (btor, e_cond);
  e_if = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);

  assert (btor_node_is_regular (e_if));
  assert (btor_node_is_fun (e_if));
  assert (btor_node_is_regular (e_else));
  assert (btor_node_is_fun (e_else));

  param = btor_exp_param (btor, btor_node_get_sort_id (e_if), 0);
  app_if = btor_exp_apply_n (btor, e_if, &param, 1); 
  app_else = btor_exp_apply_n (btor, e_else, &param, 1);
  cond = btor_bv_cond_exp_node (btor, e_cond, app_if, app_else); 
  lambda = btor_exp_lambda (btor, param, cond); 
  lambda->is_array = 1;

  btor_node_release (btor, param);
  btor_node_release (btor, app_if);
  btor_node_release (btor, app_else);
  btor_node_release (btor, cond);
  
  return lambda;
}
#endif

/* more than 4 children are not possible as we only have 2 bit for storing
 * the position in the parent pointers */
#define ARGS_MAX_NUM_CHILDREN 3

BtorNode *
btor_node_create_args (Btor *btor, BtorNode *args[], uint32_t argc)
{
  assert (btor);
  assert (argc > 0);
  assert (args);

  int64_t i, cur_argc, cnt_args, rem_free, num_args;
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
    assert (!btor_node_is_fun (args[i]));
    assert (btor == btor_node_real_addr (args[i])->btor);
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

      if (last) btor_node_release (btor, last);

      last = result;
    }
  }

  assert (result);
  return result;
}

BtorNode *
btor_node_create_apply (Btor *btor, BtorNode *fun, BtorNode *args)
{
  assert (btor);
  assert (fun);
  assert (args);
  assert (btor == btor_node_real_addr (fun)->btor);
  assert (btor == btor_node_real_addr (args)->btor);
  assert (btor_dbg_precond_apply_exp (btor, fun, args));

  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, fun);
  e[1] = btor_simplify_exp (btor, args);

  assert (btor_node_is_regular (e[0]));
  assert (btor_node_is_regular (e[1]));
  assert (btor_node_is_fun (e[0]));
  assert (btor_node_is_args (e[1]));

  /* eliminate nested functions */
  if (btor_node_is_lambda (e[0]) && e[0]->parameterized)
  {
    btor_beta_assign_args (btor, e[0], args);
    BtorNode *result = btor_beta_reduce_bounded (btor, e[0], 1);
    btor_beta_unassign_params (btor, e[0]);
    return result;
  }
  assert (!btor_node_is_fun_cond (e[0])
          || (!e[0]->e[1]->parameterized && !e[0]->e[2]->parameterized));
  return create_exp (btor, BTOR_APPLY_NODE, 2, e);
}

BtorNode *
btor_node_create_quantifier (Btor *btor,
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

  assert (btor_node_is_regular (e[0]));
  assert (btor_node_is_param (e[0]));
  assert (e[1]);
  assert (btor_sort_is_bool (btor, btor_node_real_addr (e[1])->sort_id));
  return create_exp (btor, kind, 2, e);
}

BtorNode *
btor_node_create_lambda (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  BtorNode *e[2];
  e[0] = btor_simplify_exp (btor, e_param);
  e[1] = btor_simplify_exp (btor, e_exp);
  return create_exp (btor, BTOR_LAMBDA_NODE, 2, e);
}

BtorNode *
btor_node_create_forall (Btor *btor, BtorNode *param, BtorNode *body)
{
  return btor_node_create_quantifier (btor, BTOR_FORALL_NODE, param, body);
}

BtorNode *
btor_node_create_exists (Btor *btor, BtorNode *param, BtorNode *body)
{
  return btor_node_create_quantifier (btor, BTOR_EXISTS_NODE, param, body);
}

BtorNode *
btor_node_create_update (Btor *btor,
                         BtorNode *fun,
                         BtorNode *args,
                         BtorNode *value)
{
  BtorNode *e[3], *res;
  e[0] = btor_simplify_exp (btor, fun);
  e[1] = btor_simplify_exp (btor, args);
  e[2] = btor_simplify_exp (btor, value);
  assert (btor_node_is_fun (e[0]));
  assert (btor_node_is_args (e[1]));
  assert (!btor_node_is_fun (e[2]));

  if (btor_node_real_addr (e[0])->parameterized
      || btor_node_real_addr (e[1])->parameterized
      || btor_node_real_addr (e[2])->parameterized)
  {
    assert (btor_node_args_get_arity (btor, args) == 1);
    return btor_exp_lambda_write (btor, fun, args->e[0], value);
  }

  res = create_exp (btor, BTOR_UPDATE_NODE, 3, e);
  if (fun->is_array) res->is_array = 1;
  return res;
}

/*========================================================================*/

BtorNodePair *
btor_node_pair_new (Btor *btor, BtorNode *exp1, BtorNode *exp2)
{
  assert (btor);
  assert (exp1);
  assert (exp2);
  assert (btor == btor_node_real_addr (exp1)->btor);
  assert (btor == btor_node_real_addr (exp2)->btor);

  uint32_t id1, id2;
  BtorNodePair *result;

  BTOR_NEW (btor->mm, result);
  id1 = btor_node_get_id (exp1);
  id2 = btor_node_get_id (exp2);
  if (id2 < id1)
  {
    result->node1 = btor_node_copy (btor, exp2);
    result->node2 = btor_node_copy (btor, exp1);
  }
  else
  {
    result->node1 = btor_node_copy (btor, exp1);
    result->node2 = btor_node_copy (btor, exp2);
  }
  return result;
}

void
btor_node_pair_delete (Btor *btor, BtorNodePair *pair)
{
  assert (btor);
  assert (pair);
  btor_node_release (btor, pair->node1);
  btor_node_release (btor, pair->node2);
  BTOR_DELETE (btor->mm, pair);
}

uint32_t
btor_node_pair_hash (const BtorNodePair *pair)
{
  uint32_t result;
  assert (pair);
  result = (uint32_t) btor_node_real_addr (pair->node1)->id;
  result += (uint32_t) btor_node_real_addr (pair->node2)->id;
  result *= 7334147u;
  return result;
}

int32_t
btor_node_pair_compare (const BtorNodePair *pair1, const BtorNodePair *pair2)
{
  assert (pair1);
  assert (pair2);

  int32_t result;

  result = btor_node_get_id (pair1->node1);
  result -= btor_node_get_id (pair2->node1);
  if (result != 0) return result;
  result = btor_node_get_id (pair1->node2);
  result -= btor_node_get_id (pair2->node2);
  return result;
}
