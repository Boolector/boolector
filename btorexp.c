/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010-2011 Armin Biere, FMV, JKU.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "btorexp.h"
#include "../picosat/picosat.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btorrewrite.h"
#include "btorsat.h"
#include "btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

static const char *const g_op2string[] = {
    "invalid", "const",  "var",  "array", "slice", "and",   "beq",
    "aeq",     "add",    "mul",  "ult",   "sll",   "srl",   "udiv",
    "urem",    "concat", "read", "write", "bcond", "acond", "proxy"};

#define BTOR_ABORT_EXP(cond, msg)                   \
  do                                                \
  {                                                 \
    if (cond)                                       \
    {                                               \
      printf ("[btorexp] %s: %s\n", __func__, msg); \
      fflush (stdout);                              \
      exit (BTOR_ERR_EXIT);                         \
    }                                               \
  } while (0)

#define BTOR_INIT_EXP_UNIQUE_TABLE(mm, table) \
  do                                          \
  {                                           \
    assert (mm != NULL);                      \
    (table).size         = 1;                 \
    (table).num_elements = 0;                 \
    BTOR_CNEW (mm, (table).chains);           \
  } while (0)

#define BTOR_RELEASE_EXP_UNIQUE_TABLE(mm, table)     \
  do                                                 \
  {                                                  \
    assert (mm != NULL);                             \
    BTOR_DELETEN (mm, (table).chains, (table).size); \
  } while (0)

#define BTOR_EXP_UNIQUE_TABLE_LIMIT 30
#define BTOR_EXP_UNIQUE_TABLE_PRIME 2000000137u

#define BTOR_EXP_FAILED_EQ_LIMIT 4096

struct BtorUAData
{
  int last_e;
  int eff_width;
  int updated_eff_width; /* boolean flag */
  int refinements;
};

typedef struct BtorUAData BtorUAData;

struct BtorExpPair
{
  BtorExp *exp1;
  BtorExp *exp2;
};

struct BtorPartialParentIterator
{
  BtorExp *cur;
};

typedef struct BtorPartialParentIterator BtorPartialParentIterator;

struct BtorFullParentIterator
{
  BtorExp *cur;
  BtorExp *exp;
  int regular_parents_done;
};

typedef struct BtorFullParentIterator BtorFullParentIterator;

struct BtorSlice
{
  int upper;
  int lower;
};

typedef struct BtorSlice BtorSlice;

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->next_parent[BTOR_GET_TAG_EXP (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->prev_parent[BTOR_GET_TAG_EXP (exp)])

#define BTOR_NEXT_AEQ_ACOND_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->next_aeq_acond_parent[BTOR_GET_TAG_EXP (exp)])

#define BTOR_PREV_AEQ_ACOND_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->prev_aeq_acond_parent[BTOR_GET_TAG_EXP (exp)])

#define BTOR_COND_INVERT_AIG_EXP(exp, aig) \
  ((BtorAIG *) (((unsigned long int) (exp) &1ul) ^ ((unsigned long int) (aig))))

static void add_constraint (Btor *, BtorExp *);
static void run_rewrite_engine (Btor *, int);
static void abstract_domain_bv_variables (Btor *);
static void eliminate_slices_on_bv_vars (Btor *);

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

#ifndef NDEBUG

static int
check_hash_table_proxy_free_dbg (const BtorPtrHashTable *table)
{
  BtorPtrHashBucket *b;
  for (b = table->first; b != NULL; b = b->next)
    if (BTOR_REAL_ADDR_EXP (b->key)->kind == BTOR_PROXY_EXP) return 0;
  return 1;
}

static int
check_all_hash_tables_proxy_free_dbg (const Btor *btor)
{
  if (!check_hash_table_proxy_free_dbg (btor->varsubst_constraints)) return 0;
  if (!check_hash_table_proxy_free_dbg (btor->embedded_constraints)) return 0;
  if (!check_hash_table_proxy_free_dbg (btor->unsynthesized_constraints))
    return 0;
  if (!check_hash_table_proxy_free_dbg (btor->synthesized_constraints))
    return 0;
  return 1;
}

int
btor_precond_slice_exp_dbg (const Btor *btor,
                            const BtorExp *exp,
                            int upper,
                            int lower)
{
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  return 1;
}

int
btor_precond_ext_exp_dbg (const Btor *btor, const BtorExp *exp, int len)
{
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));
  assert (len >= 0);
  return 1;
}

int
btor_precond_regular_unary_bv_exp_dbg (const Btor *btor, const BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  return 1;
}

int
btor_precond_eq_exp_dbg (const Btor *btor, const BtorExp *e0, const BtorExp *e1)
{
  int is_array_e0, is_array_e1;
  BtorExp *real_e0, *real_e1;

  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);

  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);

  assert (real_e0->simplified == NULL);
  assert (real_e1->simplified == NULL);
  assert (is_array_e0 == is_array_e1);
  assert (real_e0->len == real_e1->len);
  assert (real_e0->len > 0);
  assert (!is_array_e0 || real_e0->index_len == real_e1->index_len);
  assert (!is_array_e0 || real_e0->index_len > 0);
  assert (!is_array_e0
          || (BTOR_IS_REGULAR_EXP (e0) && BTOR_IS_REGULAR_EXP (e1)));
  return 1;
}

int
btor_precond_concat_exp_dbg (const Btor *btor,
                             const BtorExp *e0,
                             const BtorExp *e1)
{
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (BTOR_REAL_ADDR_EXP (e0)->simplified == NULL);
  assert (BTOR_REAL_ADDR_EXP (e1)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->len
          <= INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len);
  return 1;
}

int
btor_precond_shift_exp_dbg (const Btor *btor,
                            const BtorExp *e0,
                            const BtorExp *e1)
{
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (BTOR_REAL_ADDR_EXP (e0)->simplified == NULL);
  assert (BTOR_REAL_ADDR_EXP (e1)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  return 1;
}

int
btor_precond_regular_binary_bv_exp_dbg (const Btor *btor,
                                        const BtorExp *e0,
                                        const BtorExp *e1)
{
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (BTOR_REAL_ADDR_EXP (e0)->simplified == NULL);
  assert (BTOR_REAL_ADDR_EXP (e1)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return 1;
}

int
btor_precond_read_exp_dbg (const Btor *btor,
                           const BtorExp *e_array,
                           const BtorExp *e_index)
{
  assert (btor != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (e_array->simplified == NULL);
  assert (BTOR_REAL_ADDR_EXP (e_index)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->len > 0);
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  return 1;
}

int
btor_precond_write_exp_dbg (const Btor *btor,
                            const BtorExp *e_array,
                            const BtorExp *e_index,
                            const BtorExp *e_value)
{
  assert (btor != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (e_value != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (e_array->simplified == NULL);
  assert (BTOR_REAL_ADDR_EXP (e_index)->simplified == NULL);
  assert (BTOR_REAL_ADDR_EXP (e_value)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)));
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->len == BTOR_REAL_ADDR_EXP (e_value)->len);
  assert (BTOR_REAL_ADDR_EXP (e_value)->len > 0);
  return 1;
}

int
btor_precond_cond_exp_dbg (const Btor *btor,
                           const BtorExp *e_cond,
                           const BtorExp *e_if,
                           const BtorExp *e_else)
{
  BtorExp *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;

  assert (btor != NULL);
  assert (e_cond != NULL);
  assert (e_if != NULL);
  assert (e_else != NULL);
  assert (BTOR_REAL_ADDR_EXP (e_cond)->simplified == NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (BTOR_REAL_ADDR_EXP (e_cond)->len == 1);

  real_e_if   = BTOR_REAL_ADDR_EXP (e_if);
  real_e_else = BTOR_REAL_ADDR_EXP (e_else);

  assert (real_e_if->simplified == NULL);
  assert (real_e_else->simplified == NULL);

  is_array_e_if   = BTOR_IS_ARRAY_EXP (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_EXP (real_e_else);

  assert (is_array_e_if == is_array_e_else);
  assert (real_e_if->len == real_e_else->len);
  assert (real_e_if->len > 0);
  assert (!is_array_e_if
          || (BTOR_IS_REGULAR_EXP (e_if) && BTOR_IS_REGULAR_EXP (e_else)));
  assert (!is_array_e_if || e_if->index_len == e_else->index_len);
  assert (!is_array_e_if || e_if->index_len > 0);
  return 1;
}

#endif

static int
compare_int_ptr (const void *p1, const void *p2)
{
  int v1 = *((int *) p1);
  int v2 = *((int *) p2);
  if (v1 < v2) return -1;

  if (v1 > v2) return 1;

  return 0;
}

static void
btor_msg_exp (Btor *btor, char *fmt, ...)
{
  va_list ap;
  fputs ("[btorexp] ", stdout);
  if (btor->inc_enabled) printf ("%d : ", btor->btor_sat_btor_called);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static BtorSlice *
new_slice (Btor *btor, int upper, int lower)
{
  BtorSlice *result;

  assert (btor != NULL);
  assert (upper >= lower);
  assert (lower >= 0);

  BTOR_NEW (btor->mm, result);
  result->upper = upper;
  result->lower = lower;
  return result;
}

static void
delete_slice (Btor *btor, BtorSlice *slice)
{
  assert (btor != NULL);
  assert (slice != NULL);
  BTOR_DELETE (btor->mm, slice);
}

static unsigned int
hash_slice (BtorSlice *slice)
{
  unsigned int result;

  assert (slice != NULL);
  assert (slice->upper >= slice->lower);
  assert (slice->lower >= 0);

  result = (unsigned int) slice->upper;
  result += (unsigned int) slice->lower;
  result *= 7334147u;
  return result;
}

static int
compare_slices (BtorSlice *s1, BtorSlice *s2)
{
  assert (s1 != NULL);
  assert (s2 != NULL);
  assert (s1->upper >= s1->lower);
  assert (s1->lower >= 0);
  assert (s2->upper >= s2->lower);
  assert (s2->lower >= 0);

  if (s1->upper < s2->upper) return -1;

  if (s1->upper > s2->upper) return 1;

  assert (s1->upper == s1->upper);
  if (s1->lower < s2->lower) return -1;

  if (s1->lower > s2->lower) return 1;

  assert (s1->upper == s2->upper && s1->lower == s2->lower);
  return 0;
}

static int
compare_slices_qsort (const void *p1, const void *p2)
{
  return compare_slices (*((BtorSlice **) p1), *((BtorSlice **) p2));
}

static void
inc_exp_ref_counter (Btor *btor, BtorExp *exp)
{
  BtorExp *real_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;
  real_exp = BTOR_REAL_ADDR_EXP (exp);
  BTOR_ABORT_EXP (real_exp->refs == INT_MAX, "Reference counter overflow");
  real_exp->refs++;
}

BtorExp *
btor_copy_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  inc_exp_ref_counter (btor, exp);
  return exp;
}

static BtorUAData *
new_ua_data (Btor *btor, int eff_width)
{
  BtorUAData *result;

  assert (btor != NULL);
  assert (eff_width >= 0);

  BTOR_NEW (btor->mm, result);
  result->last_e            = 0;
  result->eff_width         = eff_width;
  result->updated_eff_width = 0;
  result->refinements       = 0;

  return result;
}

static void
delete_ua_data (Btor *btor, BtorUAData *ua_data)
{
  assert (btor != NULL);
  assert (ua_data != NULL);
  BTOR_DELETE (btor->mm, ua_data);
}

/* Creates an expression pair which can be compared with
 * other expression pairs via the function
 * 'compare_exp_pair'
 */
static BtorExpPair *
new_exp_pair (Btor *btor, BtorExp *exp1, BtorExp *exp2)
{
  int id1, id2;
  BtorExpPair *result;
  assert (btor != NULL);
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  BTOR_NEW (btor->mm, result);
  id1 = BTOR_GET_ID_EXP (exp1);
  id2 = BTOR_GET_ID_EXP (exp2);
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

/* Disconnects a child from its parent and updates its parent list */
static void
disconnect_child_exp (Btor *btor, BtorExp *parent, int pos)
{
  BtorExp *first_parent, *last_parent, *real_first_parent, *real_last_parent;
  BtorExp *child, *real_child, *tagged_parent;
  assert (btor != NULL);
  assert (parent != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (!BTOR_IS_BV_CONST_EXP (parent));
  assert (!BTOR_IS_BV_VAR_EXP (parent));
  assert (!BTOR_IS_ARRAY_VAR_EXP (parent));
  (void) btor;
  tagged_parent = BTOR_TAG_EXP (parent, pos);
  /* special treatment of array children of aeq and acond */
  if (BTOR_IS_ARRAY_EQ_EXP (parent)
      || (BTOR_IS_ARRAY_COND_EXP (parent) && pos != 0))
  {
    child = parent->e[pos];
    assert (BTOR_IS_REGULAR_EXP (child));
    assert (BTOR_IS_ARRAY_EXP (child) || BTOR_IS_PROXY_EXP (child));
    first_parent = child->first_aeq_acond_parent;
    last_parent  = child->last_aeq_acond_parent;
    assert (first_parent != NULL);
    assert (last_parent != NULL);
    real_first_parent = BTOR_REAL_ADDR_EXP (first_parent);
    real_last_parent  = BTOR_REAL_ADDR_EXP (last_parent);
    /* only one parent? */
    if (first_parent == tagged_parent && first_parent == last_parent)
    {
      assert (parent->next_aeq_acond_parent[pos] == NULL);
      assert (parent->prev_aeq_acond_parent[pos] == NULL);
      child->first_aeq_acond_parent = NULL;
      child->last_aeq_acond_parent  = NULL;
    }
    /* is parent first parent in the list? */
    else if (first_parent == tagged_parent)
    {
      assert (parent->next_aeq_acond_parent[pos] != NULL);
      assert (parent->prev_aeq_acond_parent[pos] == NULL);
      child->first_aeq_acond_parent = parent->next_aeq_acond_parent[pos];
      BTOR_PREV_AEQ_ACOND_PARENT (child->first_aeq_acond_parent) = NULL;
    }
    /* is parent last parent in the list? */
    else if (last_parent == tagged_parent)
    {
      assert (parent->next_aeq_acond_parent[pos] == NULL);
      assert (parent->prev_aeq_acond_parent[pos] != NULL);
      child->last_aeq_acond_parent = parent->prev_aeq_acond_parent[pos];
      BTOR_NEXT_AEQ_ACOND_PARENT (child->last_aeq_acond_parent) = NULL;
    }
    /* hang out parent from list */
    else
    {
      assert (parent->next_aeq_acond_parent[pos] != NULL);
      assert (parent->prev_aeq_acond_parent[pos] != NULL);
      BTOR_PREV_AEQ_ACOND_PARENT (parent->next_aeq_acond_parent[pos]) =
          parent->prev_aeq_acond_parent[pos];
      BTOR_NEXT_AEQ_ACOND_PARENT (parent->prev_aeq_acond_parent[pos]) =
          parent->next_aeq_acond_parent[pos];
    }
  }
  else
  {
    real_child   = BTOR_REAL_ADDR_EXP (parent->e[pos]);
    first_parent = real_child->first_parent;
    last_parent  = real_child->last_parent;
    assert (first_parent != NULL);
    assert (last_parent != NULL);
    real_first_parent = BTOR_REAL_ADDR_EXP (first_parent);
    real_last_parent  = BTOR_REAL_ADDR_EXP (last_parent);
    /* special treatment of array children of aeq and acond */
    /* only one parent? */
    if (first_parent == tagged_parent && first_parent == last_parent)
    {
      assert (parent->next_parent[pos] == NULL);
      assert (parent->prev_parent[pos] == NULL);
      real_child->first_parent = NULL;
      real_child->last_parent  = NULL;
    }
    /* is parent first parent in the list? */
    else if (first_parent == tagged_parent)
    {
      assert (parent->next_parent[pos] != NULL);
      assert (parent->prev_parent[pos] == NULL);
      real_child->first_parent                    = parent->next_parent[pos];
      BTOR_PREV_PARENT (real_child->first_parent) = NULL;
    }
    /* is parent last parent in the list? */
    else if (last_parent == tagged_parent)
    {
      assert (parent->next_parent[pos] == NULL);
      assert (parent->prev_parent[pos] != NULL);
      real_child->last_parent                    = parent->prev_parent[pos];
      BTOR_NEXT_PARENT (real_child->last_parent) = NULL;
    }
    /* detach parent from list */
    else
    {
      assert (parent->next_parent[pos] != NULL);
      assert (parent->prev_parent[pos] != NULL);
      BTOR_PREV_PARENT (parent->next_parent[pos]) = parent->prev_parent[pos];
      BTOR_NEXT_PARENT (parent->prev_parent[pos]) = parent->next_parent[pos];
    }
  }
  parent->next_parent[pos] = NULL;
  parent->prev_parent[pos] = NULL;
  parent->e[pos]           = NULL;
}

/* Computes hash value of expresssion by children ids */
static unsigned int
compute_hash_exp (BtorExp *exp, int table_size)
{
  unsigned int hash;
  assert (exp != NULL);
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (!BTOR_IS_BV_VAR_EXP (exp));
  assert (!BTOR_IS_ARRAY_VAR_EXP (exp));
  if (BTOR_IS_BV_CONST_EXP (exp))
    hash = btor_hashstr ((void *) exp->bits);
  else
  {
    switch (exp->arity)
    {
      case 1:
        assert (exp->kind == BTOR_SLICE_EXP);
        hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
               + (unsigned int) exp->upper + (unsigned int) exp->lower;
        break;
      case 2:
        hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
               + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[1])->id;
        break;
      default:
        assert (exp->arity == 3);
        hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
               + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[1])->id
               + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[2])->id;
        break;
    }
  }
  hash = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (table_size - 1);
  return hash;
}

static void
remove_from_unique_table_exp (Btor *btor, BtorExp *exp)
{
  unsigned int hash;
  BtorExp *cur, *prev;

  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));

  if (!exp->unique) return;

  assert (btor != NULL);
  assert (btor->table.num_elements > 0);

  hash = compute_hash_exp (exp, btor->table.size);
  prev = NULL;
  cur  = btor->table.chains[hash];
  while (cur != exp && cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    prev = cur;
    cur  = cur->next;
  }
  assert (cur != NULL);
  if (prev == NULL)
    btor->table.chains[hash] = cur->next;
  else
    prev->next = cur->next;

  btor->table.num_elements--;

  exp->unique = 0; /* NOTE: this is not debugging code ! */
}

static void
remove_from_hash_tables (Btor *btor, BtorExp *exp)
{
  BtorUAData *ua_data;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (exp->kind != BTOR_INVALID_EXP);

  switch (exp->kind)
  {
    case BTOR_BV_VAR_EXP:
      btor_remove_from_ptr_hash_table (btor->bv_vars, exp, 0, 0);
      if (btor->ua.enabled)
      {
        btor_remove_from_ptr_hash_table (
            btor->ua.vars_reads, exp, 0, (BtorPtrHashData *) (void *) &ua_data);
        if (ua_data != NULL) delete_ua_data (btor, ua_data);
      }
      break;
    case BTOR_ARRAY_VAR_EXP:
      btor_remove_from_ptr_hash_table (btor->array_vars, exp, 0, 0);
      break;
    case BTOR_READ_EXP:
      if (btor->ua.enabled)
      {
        btor_remove_from_ptr_hash_table (
            btor->ua.vars_reads, exp, 0, (BtorPtrHashData *) (void *) &ua_data);
        if (ua_data != NULL) delete_ua_data (btor, ua_data);
      }
      break;
    case BTOR_WRITE_EXP:
    case BTOR_ACOND_EXP:
      if (btor->ua.enabled)
        btor_remove_from_ptr_hash_table (btor->ua.writes_aconds, exp, 0, 0);
      break;
    default: break;
  }
}

/* Disconnect children of expression in parent list and if applicable from
 * unique table.  Do not touch local data, nor any reference counts.  The
 * kind of the expression becomes 'BTOR_DISCONNECTED_EXP' in debugging mode.
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
disconnect_children_exp (Btor *btor, BtorExp *exp)
{
  int i;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_EXP (exp));

  assert (exp->kind != BTOR_INVALID_EXP);

  assert (!exp->unique);
  assert (exp->erased);
  assert (!exp->disconnected);

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
erase_local_data_exp (Btor *btor, BtorExp *exp, int free_symbol)
{
  BtorMemMgr *mm;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_EXP (exp));

  assert (!exp->unique);
  assert (!exp->erased);
  assert (!exp->disconnected);
  assert (exp->kind != BTOR_INVALID_EXP);

  mm = btor->mm;

  switch (exp->kind)
  {
    case BTOR_BV_CONST_EXP:
      btor_freestr (mm, exp->bits);
      exp->bits = NULL;
      break;
    case BTOR_ARRAY_VAR_EXP:
      if (free_symbol)
      {
        btor_freestr (mm, exp->symbol);
        exp->symbol = NULL;
      }
      /* fall through wanted */
    case BTOR_WRITE_EXP:
    case BTOR_ACOND_EXP:
      if (exp->rho != NULL)
      {
        btor_delete_ptr_hash_table (exp->rho);
        exp->rho = NULL;
      }
      break;
    case BTOR_BV_VAR_EXP:
      if (free_symbol)
      {
        btor_freestr (mm, exp->symbol);
        exp->symbol = NULL;
      }
      break;
    case BTOR_PROXY_EXP:
      if (free_symbol && exp->symbol != NULL)
      {
        btor_freestr (mm, exp->symbol);
        exp->symbol = NULL;
      }
      break;
    case BTOR_AEQ_EXP:
      if (exp->vreads)
      {
        BTOR_DELETE (mm, exp->vreads);
        exp->vreads = 0;
      }
      break;
    case BTOR_READ_EXP:
      if (exp->vread) btor->stats.vreads--;
      break;
    default: break;
  }

  if (exp->av)
  {
    btor_release_delete_aigvec (btor->avmgr, exp->av);
    exp->av = 0;
  }
  exp->erased = 1;
  btor->ops[exp->kind]--;
}

/* Delete expression from memory.
 */
static void
really_deallocate_exp (Btor *btor, BtorExp *exp)
{
  BtorMemMgr *mm;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_EXP (exp));

  assert (!exp->unique);
  assert (exp->disconnected);
  assert (exp->erased);

  mm = btor->mm;

  exp->kind = BTOR_INVALID_EXP;

  if (exp->bits != NULL) btor_freestr (btor->mm, exp->bits);

  btor_free (mm, exp, exp->bytes);
}

static void
recursively_release_exp (Btor *btor, BtorExp *root)
{
  BtorMemMgr *mm;
  BtorExpPtrStack stack;
  BtorExp *cur;
  int i;

  assert (btor);
  assert (root);
  assert (BTOR_IS_REGULAR_EXP (root));
  assert (root->refs == 1);

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  cur = root;
  goto RECURSIVELY_RELEASE_EXP_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (cur->refs > 1)
      cur->refs--;
    else
    {
    RECURSIVELY_RELEASE_EXP_ENTER_WITHOUT_POP:
      assert (cur->refs == 1);

      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);

      if (cur->simplified)
      {
        assert (btor->rewrite_level > 1);
        BTOR_PUSH_STACK (mm, stack, cur->simplified);
        cur->simplified = NULL;
      }

      if (BTOR_IS_ARRAY_EQ_EXP (cur) && cur->vreads)
      {
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp2);
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp1);
      }

      remove_from_unique_table_exp (btor, cur);
      erase_local_data_exp (btor, cur, 1);

      /* It is safe to access the children here, since they are pushed
       * on the stack and will be release later if necessary.
       */
      remove_from_hash_tables (btor, cur);
      disconnect_children_exp (btor, cur);
      really_deallocate_exp (btor, cur);
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
}

void
btor_release_exp (Btor *btor, BtorExp *root)
{
  assert (btor);
  assert (root);

  root = BTOR_REAL_ADDR_EXP (root);

  assert (root->refs > 0);

  if (root->refs > 1)
    root->refs--;
  else
    recursively_release_exp (btor, root);
}

static void
delete_exp_pair (Btor *btor, BtorExpPair *pair)
{
  assert (btor != NULL);
  assert (pair != NULL);
  btor_release_exp (btor, pair->exp1);
  btor_release_exp (btor, pair->exp2);
  BTOR_DELETE (btor->mm, pair);
}

static unsigned int
hash_exp_pair (BtorExpPair *pair)
{
  unsigned int result;
  assert (pair != NULL);
  result = (unsigned int) BTOR_REAL_ADDR_EXP (pair->exp1)->id;
  result += (unsigned int) BTOR_REAL_ADDR_EXP (pair->exp2)->id;
  result *= 7334147u;
  return result;
}

static int
compare_exp_pair (BtorExpPair *pair1, BtorExpPair *pair2)
{
  int result;
  assert (pair1 != NULL);
  assert (pair2 != NULL);
  result = BTOR_GET_ID_EXP (pair1->exp1);
  result -= BTOR_GET_ID_EXP (pair2->exp1);
  if (result != 0) return result;
  result = BTOR_GET_ID_EXP (pair1->exp2);
  result -= BTOR_GET_ID_EXP (pair2->exp2);
  return result;
}

static void
init_read_parent_iterator (BtorPartialParentIterator *it, BtorExp *exp)
{
  assert (it != NULL);
  assert (exp != NULL);
  it->cur = BTOR_REAL_ADDR_EXP (exp)->first_parent;
}

static void
init_write_parent_iterator (BtorPartialParentIterator *it, BtorExp *exp)
{
  assert (it != NULL);
  assert (exp != NULL);
  it->cur = BTOR_REAL_ADDR_EXP (exp)->last_parent;
}

static void
init_aeq_parent_iterator (BtorPartialParentIterator *it, BtorExp *exp)
{
  assert (it != NULL);
  assert (exp != NULL);
  it->cur = BTOR_REAL_ADDR_EXP (exp)->first_aeq_acond_parent;
}

static void
init_acond_parent_iterator (BtorPartialParentIterator *it, BtorExp *exp)
{
  assert (it != NULL);
  assert (exp != NULL);
  it->cur = BTOR_REAL_ADDR_EXP (exp)->last_aeq_acond_parent;
}

static void
init_full_parent_iterator (BtorFullParentIterator *it, BtorExp *exp)
{
  assert (it != NULL);
  assert (exp != NULL);
  it->exp = exp;
  if (BTOR_REAL_ADDR_EXP (exp)->first_parent != NULL)
  {
    it->regular_parents_done = 0;
    it->cur                  = BTOR_REAL_ADDR_EXP (exp)->first_parent;
  }
  else
  {
    it->regular_parents_done = 1;
    if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)))
      it->cur = BTOR_REAL_ADDR_EXP (exp)->first_aeq_acond_parent;
    else
      it->cur = NULL;
  }
}

static BtorExp *
next_parent_read_parent_iterator (BtorPartialParentIterator *it)
{
  BtorExp *result;
  assert (it != NULL);
  result = it->cur;
  assert (result != NULL);
  it->cur = BTOR_NEXT_PARENT (result);
  /* array child of read is at position 0, so result is not tagged */
  assert (BTOR_IS_REGULAR_EXP (result));
  assert (BTOR_IS_READ_EXP (result));
  return result;
}

static BtorExp *
next_parent_write_parent_iterator (BtorPartialParentIterator *it)
{
  BtorExp *result;
  assert (it != NULL);
  result = it->cur;
  assert (result != NULL);
  it->cur = BTOR_PREV_PARENT (result);
  /* array child of write is at position 0, so result is not tagged */
  assert (BTOR_IS_REGULAR_EXP (result));
  assert (BTOR_IS_WRITE_EXP (result));
  return result;
}

static BtorExp *
next_parent_aeq_parent_iterator (BtorPartialParentIterator *it)
{
  BtorExp *result;
  assert (it != NULL);
  result = it->cur;
  assert (result != NULL);
  it->cur = BTOR_NEXT_AEQ_ACOND_PARENT (result);
  assert (BTOR_IS_ARRAY_EQ_EXP (BTOR_REAL_ADDR_EXP (result)));
  return BTOR_REAL_ADDR_EXP (result);
}

static BtorExp *
next_parent_acond_parent_iterator (BtorPartialParentIterator *it)
{
  BtorExp *result;
  assert (it != NULL);
  result = it->cur;
  assert (result != NULL);
  it->cur = BTOR_PREV_AEQ_ACOND_PARENT (result);
  assert (BTOR_IS_ARRAY_COND_EXP (BTOR_REAL_ADDR_EXP (result)));
  return BTOR_REAL_ADDR_EXP (result);
}

static BtorExp *
next_parent_full_parent_iterator (BtorFullParentIterator *it)
{
  BtorExp *result;
  assert (it != NULL);
  result = it->cur;
  assert (result != NULL);
  if (!it->regular_parents_done)
  {
    it->cur = BTOR_NEXT_PARENT (result);
    /* reached end of regular parent list ? */
    if (it->cur == NULL)
    {
      it->regular_parents_done = 1;
      /* traverse aeq acond parent list */
      if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (it->exp)))
        it->cur = BTOR_REAL_ADDR_EXP (it->exp)->first_aeq_acond_parent;
    }
  }
  else
    it->cur = BTOR_NEXT_AEQ_ACOND_PARENT (result);
  return BTOR_REAL_ADDR_EXP (result);
}

static int
has_next_parent_read_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it != NULL);
  /* array child of read is at position 0, so cur is not tagged */
  return it->cur != NULL && BTOR_IS_READ_EXP (it->cur);
}

static int
has_next_parent_write_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it != NULL);
  /* array child of write is at position 0, so cur is not tagged */
  return it->cur != NULL && BTOR_IS_WRITE_EXP (it->cur);
}

static int
has_next_parent_aeq_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it != NULL);
  return it->cur != NULL && BTOR_IS_ARRAY_EQ_EXP (BTOR_REAL_ADDR_EXP (it->cur));
}

static int
has_next_parent_acond_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it != NULL);
  return it->cur != NULL
         && BTOR_IS_ARRAY_COND_EXP (BTOR_REAL_ADDR_EXP (it->cur));
}

static int
has_next_parent_full_parent_iterator (BtorFullParentIterator *it)
{
  assert (it != NULL);
  return it->cur != NULL;
}

static int
has_parents_exp (Btor *btor, BtorExp *exp)
{
  BtorFullParentIterator it;

  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;

  init_full_parent_iterator (&it, exp);
  return has_next_parent_full_parent_iterator (&it);
}

#if 0
static BtorExp * 
get_parent_if_exactly_one_parent_exp (Btor * btor, BtorExp *exp)
{
  BtorExp *result;
  BtorFullParentIterator it;

  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;

  init_full_parent_iterator (&it, exp);
  if (!has_next_parent_full_parent_iterator(&it))
    return NULL;

  result = next_parent_full_parent_iterator (&it);
  if (has_next_parent_full_parent_iterator (&it))
    return NULL;

  return result;
}
#endif

static void
check_not_simplified_or_const (Btor *btor, BtorExp *exp)
{
#ifndef NDEBUG
  assert (btor != NULL);
  assert (exp != NULL);

  exp = BTOR_REAL_ADDR_EXP (exp);

  if (exp->simplified == NULL) return;

  assert (exp->len == 1);
  while (exp->simplified != NULL) exp = BTOR_REAL_ADDR_EXP (exp->simplified);
  assert (BTOR_IS_BV_CONST_EXP (exp));
#else
  (void) btor;
  (void) exp;
#endif
}

static int
assignment_always_unequal (Btor *btor, BtorExpPair *pair, int *hashed_pair)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int i, len, val1, val2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  BtorExp *exp1, *exp2;
  BtorPtrHashTable *exp_pair_ass_unequal_table;

  assert (btor != NULL);
  assert (pair != NULL);
  assert (hashed_pair != NULL);

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  *hashed_pair = 0;

  exp_pair_ass_unequal_table = btor->exp_pair_ass_unequal_table;
  if (btor_find_in_ptr_hash_table (exp_pair_ass_unequal_table, pair)) return 1;

  exp1 = pair->exp1;
  exp2 = pair->exp2;
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp1)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp2)));
  assert (BTOR_REAL_ADDR_EXP (exp1)->len == BTOR_REAL_ADDR_EXP (exp2)->len);

  av1 = BTOR_REAL_ADDR_EXP (exp1)->av;
  av2 = BTOR_REAL_ADDR_EXP (exp2)->av;
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_EXP (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_EXP (exp2, av2->aigs[i]);

    if (aig1 == BTOR_AIG_TRUE)
      val1 = 1;
    else if (aig1 == BTOR_AIG_FALSE)
      val1 = -1;
    else
      val1 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig1));

    if (val1 != 0) /*  not toplevel assigned or const  */
    {
      if (aig2 == BTOR_AIG_TRUE)
        val2 = 1;
      else if (aig2 == BTOR_AIG_FALSE)
        val2 = -1;
      else
        val2 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig2));

      if (val2 != 0 && val1 != val2)
      {
        (void) btor_insert_in_ptr_hash_table (exp_pair_ass_unequal_table, pair);
        *hashed_pair = 1;
        return 1;
      }
    }
  }
  return 0;
}

/* This function is used to encode a lemma on demand.
 * The stack 'writes' contains intermediate writes.
 * The stack 'aeqs' contains intermediate array equalities (true).
 * The stacks 'aconds' constain intermediate array conditionals.
 */
static void
encode_lemma (Btor *btor,
              BtorPtrHashTable *writes,
              BtorPtrHashTable *aeqs,
              BtorPtrHashTable *aconds_sel1,
              BtorPtrHashTable *aconds_sel2,
              BtorExp *i,
              BtorExp *j,
              BtorExp *a,
              BtorExp *b)
{
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorAIGVec *av_i, *av_j, *av_a, *av_b, *av_w;
  BtorAIG *aig1, *aig2;
  BtorExp *w_index, *cur_write, *aeq, *acond, *cond;
  BtorExpPair *pair;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table, *exp_pair_cnf_eq_id_table;
  BtorPtrHashBucket *bucket, *bucket_temp;
  BtorIntStack clauses;
  BtorIntStack linking_clause;
  int len_a_b, len_i_j_w, e, hashed_pair;
  int k, d_k;
  int a_k = 0;
  int b_k = 0;
  int i_k = 0;
  int j_k = 0;
  int w_k = 0;
  int *lit;
  assert (btor != NULL);
  assert (writes != NULL);
  assert (aeqs != NULL);
  assert (aconds_sel1 != NULL);
  assert (aconds_sel2 != NULL);
  assert (i != NULL);
  assert (j != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (i)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (j)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (a)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (b)));

  btor->stats.lemmas_size_sum +=
      writes->count + aeqs->count + aconds_sel1->count + aconds_sel2->count + 2;

  exp_pair_cnf_diff_id_table = btor->exp_pair_cnf_diff_id_table;
  exp_pair_cnf_eq_id_table   = btor->exp_pair_cnf_eq_id_table;
  mm                         = btor->mm;
  avmgr                      = btor->avmgr;
  amgr                       = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr                       = btor_get_sat_mgr_aig_mgr (amgr);
  av_i                       = BTOR_REAL_ADDR_EXP (i)->av;
  av_j                       = BTOR_REAL_ADDR_EXP (j)->av;
  av_a                       = BTOR_REAL_ADDR_EXP (a)->av;
  av_b                       = BTOR_REAL_ADDR_EXP (b)->av;
  assert (av_i != NULL);
  assert (av_j != NULL);
  assert (av_a != NULL);
  assert (av_b != NULL);
  assert (av_a->len == av_b->len);
  assert (av_i->len == av_j->len);
  len_a_b   = av_a->len;
  len_i_j_w = av_i->len;

  /* i and j have to be synthesized and translated to SAT before */
  assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (i)));
  assert (BTOR_REAL_ADDR_EXP (i)->sat_both_phases);
  assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (j)));
  assert (BTOR_REAL_ADDR_EXP (j)->sat_both_phases);

  BTOR_INIT_STACK (clauses);
  BTOR_INIT_STACK (linking_clause);

  /* encode i != j */
  pair        = new_exp_pair (btor, i, j);
  hashed_pair = 0;
  if (i != j && !assignment_always_unequal (btor, pair, &hashed_pair))
  {
    /* already encoded i != j into SAT ? */
    bucket = btor_find_in_ptr_hash_table (exp_pair_cnf_diff_id_table, pair);
    /* no? */
    if (bucket == NULL)
    {
      /* hash starting cnf id - 1 for d_k */
      d_k = btor_get_last_cnf_id_sat_mgr (smgr);
      assert (d_k != 0);
      btor_insert_in_ptr_hash_table (exp_pair_cnf_diff_id_table, pair)
          ->data.asInt = d_k;
      hashed_pair      = 1;
      for (k = 0; k < len_i_j_w; k++)
      {
        aig1 = BTOR_COND_INVERT_AIG_EXP (i, av_i->aigs[k]);
        aig2 = BTOR_COND_INVERT_AIG_EXP (j, av_j->aigs[k]);
        if (!BTOR_IS_CONST_AIG (aig1))
        {
          i_k = BTOR_GET_CNF_ID_AIG (aig1);
          assert (i_k != 0);
        }
        if (!BTOR_IS_CONST_AIG (aig2))
        {
          j_k = BTOR_GET_CNF_ID_AIG (aig2);
          assert (j_k != 0);
        }
        /* AIGs cannot be inverse of each other as this would imply
         * that i != j which is in contradiction to the conflict that
         * has been detected.
         */
        assert ((((unsigned long int) aig1) ^ ((unsigned long int) aig2))
                != 1ul);
        d_k = btor_next_cnf_id_sat_mgr (smgr);
        assert (d_k != 0);
        BTOR_PUSH_STACK (mm, linking_clause, d_k);
        if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_TRUE)
        {
          if (!BTOR_IS_CONST_AIG (aig1)) BTOR_PUSH_STACK (mm, clauses, i_k);
          if (!BTOR_IS_CONST_AIG (aig2)) BTOR_PUSH_STACK (mm, clauses, j_k);
          BTOR_PUSH_STACK (mm, clauses, -d_k);
          BTOR_PUSH_STACK (mm, clauses, 0);
        }
        if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_FALSE)
        {
          if (!BTOR_IS_CONST_AIG (aig1)) BTOR_PUSH_STACK (mm, clauses, -i_k);
          if (!BTOR_IS_CONST_AIG (aig2)) BTOR_PUSH_STACK (mm, clauses, -j_k);
          BTOR_PUSH_STACK (mm, clauses, -d_k);
          BTOR_PUSH_STACK (mm, clauses, 0);
        }
      }
    }
    else
    {
      /* we have already encoded i != j,
       * we simply reuse all diffs for the linking clause */
      d_k = bucket->data.asInt;
      assert (d_k != 0);
      for (k = 0; k < len_i_j_w; k++)
      {
        d_k++;
        BTOR_PUSH_STACK (mm, linking_clause, d_k);
      }
    }
  }

  if (!hashed_pair) delete_exp_pair (btor, pair);

  /* encode a = b */
  /* a and b have to be synthesized and translated to SAT before */
  assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (a)));
  assert (BTOR_REAL_ADDR_EXP (a)->sat_both_phases);
  assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (b)));
  assert (BTOR_REAL_ADDR_EXP (b)->sat_both_phases);

  pair = new_exp_pair (btor, a, b);
  /* already encoded a = b ? */
  bucket = btor_find_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair);
  /* no ? */
  if (bucket == NULL)
  {
    e = btor_next_cnf_id_sat_mgr (smgr);
    /* hash e */
    btor_insert_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair)->data.asInt =
        e;
    for (k = 0; k < len_a_b; k++)
    {
      aig1 = BTOR_COND_INVERT_AIG_EXP (a, av_a->aigs[k]);
      aig2 = BTOR_COND_INVERT_AIG_EXP (b, av_b->aigs[k]);
      /* if AIGs are equal then the clauses are satisfied */
      if (aig1 != aig2)
      {
        if (!BTOR_IS_CONST_AIG (aig1))
        {
          a_k = BTOR_GET_CNF_ID_AIG (aig1);
          assert (a_k != 0);
        }
        if (!BTOR_IS_CONST_AIG (aig2))
        {
          b_k = BTOR_GET_CNF_ID_AIG (aig2);
          assert (b_k != 0);
        }
        if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_FALSE)
        {
          BTOR_PUSH_STACK (mm, clauses, -e);
          if (!BTOR_IS_CONST_AIG (aig1)) BTOR_PUSH_STACK (mm, clauses, a_k);
          if (!BTOR_IS_CONST_AIG (aig2)) BTOR_PUSH_STACK (mm, clauses, -b_k);
          BTOR_PUSH_STACK (mm, clauses, 0);
        }
        if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_TRUE)
        {
          BTOR_PUSH_STACK (mm, clauses, -e);
          if (!BTOR_IS_CONST_AIG (aig1)) BTOR_PUSH_STACK (mm, clauses, -a_k);
          if (!BTOR_IS_CONST_AIG (aig2)) BTOR_PUSH_STACK (mm, clauses, b_k);
          BTOR_PUSH_STACK (mm, clauses, 0);
        }
      }
    }
  }
  else
  {
    /* we have already encoded a = b into SAT
     * we simply reuse e for the linking clause */
    e = bucket->data.asInt;
    delete_exp_pair (btor, pair);
  }
  assert (e != 0);
  BTOR_PUSH_STACK (mm, linking_clause, e);
  /* encode i != write index premisses */
  for (bucket = writes->last; bucket != NULL; bucket = bucket->prev)
  {
    cur_write = (BtorExp *) bucket->key;
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_EXP (cur_write));
    w_index = cur_write->e[1];
    av_w    = BTOR_REAL_ADDR_EXP (w_index)->av;
    assert (av_w->len == len_i_j_w);

    /* write index has to be synthesized and translated to SAT before */
    assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (w_index)));
    assert (BTOR_REAL_ADDR_EXP (w_index)->sat_both_phases);

    hashed_pair = 0;
    pair        = new_exp_pair (btor, i, w_index);
    if (!assignment_always_unequal (btor, pair, &hashed_pair))
    {
      /* already encoded i != w_index into SAT ? */
      bucket_temp =
          btor_find_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair);
      /* no ? */
      if (bucket_temp == NULL)
      {
        e = btor_next_cnf_id_sat_mgr (smgr);
        btor_insert_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair)
            ->data.asInt = e;
        hashed_pair      = 1;
        for (k = 0; k < len_i_j_w; k++)
        {
          aig1 = BTOR_COND_INVERT_AIG_EXP (i, av_i->aigs[k]);
          aig2 = BTOR_COND_INVERT_AIG_EXP (w_index, av_w->aigs[k]);
          /* if AIGs are equal then clauses are satisfied */
          if (aig1 != aig2)
          {
            if (!BTOR_IS_CONST_AIG (aig1))
            {
              i_k = BTOR_GET_CNF_ID_AIG (aig1);
              assert (i_k != 0);
            }
            if (!BTOR_IS_CONST_AIG (aig2))
            {
              w_k = BTOR_GET_CNF_ID_AIG (aig2);
              assert (w_k != 0);
            }
            if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_FALSE)
            {
              BTOR_PUSH_STACK (mm, clauses, -e);
              if (!BTOR_IS_CONST_AIG (aig1)) BTOR_PUSH_STACK (mm, clauses, i_k);
              if (!BTOR_IS_CONST_AIG (aig2))
                BTOR_PUSH_STACK (mm, clauses, -w_k);
              BTOR_PUSH_STACK (mm, clauses, 0);
            }
            if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_TRUE)
            {
              BTOR_PUSH_STACK (mm, clauses, -e);
              if (!BTOR_IS_CONST_AIG (aig1))
                BTOR_PUSH_STACK (mm, clauses, -i_k);
              if (!BTOR_IS_CONST_AIG (aig2)) BTOR_PUSH_STACK (mm, clauses, w_k);
              BTOR_PUSH_STACK (mm, clauses, 0);
            }
          }
        }
      }
      else
      {
        /* we have already encoded i != w_j into SAT
         * we simply reuse e for the linking clause */
        e = bucket_temp->data.asInt;
      }
      assert (e != 0);
      BTOR_PUSH_STACK (mm, linking_clause, e);
    }

    if (!hashed_pair) delete_exp_pair (btor, pair);
  }

  /* add array equalites in the premisse to linking clause */
  for (bucket = aeqs->last; bucket != NULL; bucket = bucket->prev)
  {
    aeq = (BtorExp *) bucket->key;
    assert (BTOR_IS_REGULAR_EXP (aeq));
    assert (BTOR_IS_ARRAY_EQ_EXP (aeq));
    assert (BTOR_IS_SYNTH_EXP (aeq));
    assert (aeq->av->len == 1);
    assert (!BTOR_IS_INVERTED_AIG (aeq->av->aigs[0]));
    assert (!BTOR_IS_CONST_AIG (aeq->av->aigs[0]));
    assert (BTOR_IS_VAR_AIG (aeq->av->aigs[0]));
    k = -aeq->av->aigs[0]->cnf_id;
    BTOR_PUSH_STACK (mm, linking_clause, k);
  }

  for (bucket = aconds_sel1->last; bucket != NULL; bucket = bucket->prev)
  {
    acond = (BtorExp *) bucket->key;
    assert (BTOR_IS_REGULAR_EXP (acond));
    assert (BTOR_IS_ARRAY_COND_EXP (acond));
    cond = acond->e[0];
    assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (cond)));
    assert (BTOR_REAL_ADDR_EXP (cond)->av->len == 1);
    aig1 = BTOR_REAL_ADDR_EXP (cond)->av->aigs[0];
    /* if AIG is constant (e.g. as a result of AIG optimizations),
     * then we do not have to include it in the premisse */
    if (!BTOR_IS_CONST_AIG (aig1))
    {
      if (BTOR_IS_INVERTED_EXP (cond)) aig1 = BTOR_INVERT_AIG (aig1);
      if (BTOR_IS_INVERTED_AIG (aig1))
        k = BTOR_REAL_ADDR_AIG (aig1)->cnf_id;
      else
        k = -aig1->cnf_id;
      assert (k != 0);
      BTOR_PUSH_STACK (mm, linking_clause, k);
    }
  }

  for (bucket = aconds_sel2->last; bucket != NULL; bucket = bucket->prev)
  {
    acond = (BtorExp *) bucket->key;
    assert (BTOR_IS_REGULAR_EXP (acond));
    assert (BTOR_IS_ARRAY_COND_EXP (acond));
    cond = acond->e[0];
    assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (cond)));
    assert (BTOR_REAL_ADDR_EXP (cond)->av->len == 1);
    aig1 = BTOR_REAL_ADDR_EXP (cond)->av->aigs[0];
    /* if AIG is constant (e.g. as a result of AIG optimizations),
     * then we do not have to include it in the premisse */
    if (!BTOR_IS_CONST_AIG (aig1))
    {
      if (BTOR_IS_INVERTED_EXP (cond)) aig1 = BTOR_INVERT_AIG (aig1);
      if (BTOR_IS_INVERTED_AIG (aig1))
        k = -BTOR_REAL_ADDR_AIG (aig1)->cnf_id;
      else
        k = aig1->cnf_id;
      assert (k != 0);
      BTOR_PUSH_STACK (mm, linking_clause, k);
    }
  }

#ifndef NDEBUG
  /* linking clause must not be true */
  for (lit = linking_clause.start; lit != linking_clause.top; lit++)
    assert (btor_deref_sat (smgr, *lit) != 1);
#endif

  btor->stats.lclause_size_sum += BTOR_COUNT_STACK (linking_clause);

  /* add clauses */
  for (lit = clauses.start; lit != clauses.top; lit++)
    btor_add_sat (smgr, *lit);
  BTOR_RELEASE_STACK (mm, clauses);

  /* add linking clause */
  while (!BTOR_EMPTY_STACK (linking_clause))
  {
    k = BTOR_POP_STACK (linking_clause);
    assert (k != 0);
    if (!btor_fixed_sat (smgr, k)) btor_add_sat (smgr, k);
  }
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, linking_clause);
}

/* Encodes the following array inequality constraint:
 * array1 != array2 <=> EXISTS(i): read(array1, i) != read(array2, i)
 */
static void
encode_array_inequality_virtual_reads (Btor *btor, BtorExp *aeq)
{
  BtorExpPair *vreads;
  BtorExp *read1, *read2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  BtorAIGVecMgr *avmgr;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int len, k, d_k, r1_k, r2_k, e;
  BtorIntStack diffs;
  assert (btor != NULL);
  assert (aeq != NULL);
  assert (BTOR_IS_REGULAR_EXP (aeq));
  assert (BTOR_IS_ARRAY_EQ_EXP (aeq));
  assert (!aeq->sat_both_phases);
  assert (aeq->vreads != NULL);
  mm     = btor->mm;
  avmgr  = btor->avmgr;
  amgr   = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr   = btor_get_sat_mgr_aig_mgr (amgr);
  vreads = aeq->vreads;

  read1 = vreads->exp1;
  assert (BTOR_IS_REGULAR_EXP (read1));
  assert (BTOR_IS_READ_EXP (read1));
  assert (BTOR_IS_SYNTH_EXP (read1));
  assert (!read1->sat_both_phases);

  read2 = vreads->exp2;
  assert (BTOR_IS_REGULAR_EXP (read2));
  assert (BTOR_IS_READ_EXP (read2));
  assert (BTOR_IS_SYNTH_EXP (read2));
  assert (!read2->sat_both_phases);

  assert (read1->e[1] == read2->e[1]);
  assert (BTOR_IS_REGULAR_EXP (read1->e[1]));
  assert (BTOR_IS_BV_VAR_EXP (read1->e[1]));
  assert (read1->len == read2->len);

  av1 = read1->av;
  assert (av1 != NULL);
  av2 = read2->av;
  assert (av2 != NULL);

  /* assign aig cnf indices as there are only variables,
   * no SAT constraints are generated */
  btor_aigvec_to_sat_both_phases (avmgr, aeq->av);
  aeq->sat_both_phases = 1;
  btor_aigvec_to_sat_both_phases (avmgr, av1);
  read1->sat_both_phases = 1;
  btor_aigvec_to_sat_both_phases (avmgr, av2);
  read2->sat_both_phases = 1;

  /* encode !e => r1 != r2 */

  BTOR_INIT_STACK (diffs);
  len = read1->len;

  /* we do not need to hash the diffs as we never use
   * value1 != value2 in a lemma on demand */

  for (k = 0; k < len; k++)
  {
    aig1 = av1->aigs[k];
    assert (!BTOR_IS_INVERTED_AIG (aig1));
    assert (!BTOR_IS_CONST_AIG (aig1));
    assert (BTOR_IS_VAR_AIG (aig1));
    r1_k = aig1->cnf_id;
    assert (r1_k != 0);

    aig2 = av2->aigs[k];
    assert (!BTOR_IS_INVERTED_AIG (aig2));
    assert (!BTOR_IS_CONST_AIG (aig2));
    assert (BTOR_IS_VAR_AIG (aig2));
    r2_k = aig2->cnf_id;
    assert (r2_k != 0);

    d_k = btor_next_cnf_id_sat_mgr (smgr);
    BTOR_PUSH_STACK (mm, diffs, d_k);

    btor_add_sat (smgr, r1_k);
    btor_add_sat (smgr, r2_k);
    btor_add_sat (smgr, -d_k);
    btor_add_sat (smgr, 0);

    btor_add_sat (smgr, -r1_k);
    btor_add_sat (smgr, -r2_k);
    btor_add_sat (smgr, -d_k);
    btor_add_sat (smgr, 0);
  }

  assert (BTOR_IS_SYNTH_EXP (aeq));
  assert (aeq->av->len == 1);
  assert (!BTOR_IS_INVERTED_AIG (aeq->av->aigs[0]));
  assert (!BTOR_IS_CONST_AIG (aeq->av->aigs[0]));
  assert (BTOR_IS_VAR_AIG (aeq->av->aigs[0]));
  e = aeq->av->aigs[0]->cnf_id;
  assert (e != 0);

  assert (!BTOR_EMPTY_STACK (diffs));
  while (!BTOR_EMPTY_STACK (diffs))
  {
    d_k = BTOR_POP_STACK (diffs);
    btor_add_sat (smgr, d_k);
  }
  btor_add_sat (smgr, e);
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, diffs);
}

/* Connects array child to write parent.
 * Writes are appended to the end of the regular parent list.
 */
static void
connect_array_child_write_exp (Btor *btor, BtorExp *parent, BtorExp *child)
{
  BtorExp *last_parent;
  int tag;
  assert (btor != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (BTOR_IS_WRITE_EXP (parent));
  assert (BTOR_IS_REGULAR_EXP (child));
  assert (BTOR_IS_ARRAY_EXP (child));
  (void) btor;
  parent->e[0] = child;
  /* no parent so far? */
  if (child->first_parent == NULL)
  {
    assert (child->last_parent == NULL);
    child->first_parent = parent;
    child->last_parent  = parent;
    assert (parent->prev_parent[0] == NULL);
    assert (parent->next_parent[0] == NULL);
  }
  /* append at the end of the list */
  else
  {
    last_parent = child->last_parent;
    assert (last_parent != NULL);
    parent->prev_parent[0] = last_parent;
    tag                    = BTOR_GET_TAG_EXP (last_parent);
    BTOR_REAL_ADDR_EXP (last_parent)->next_parent[tag] = parent;
    child->last_parent                                 = parent;
  }
}

/* Connects array child to array conditional parent.
 * Array conditionals are appended to the end of the
 * array equality and array conditional parent list.
 */
static void
connect_array_child_acond_exp (Btor *btor,
                               BtorExp *parent,
                               BtorExp *child,
                               int pos)
{
  BtorExp *last_parent, *tagged_parent;
  int tag;
  assert (btor != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (BTOR_IS_ARRAY_COND_EXP (parent));
  assert (BTOR_IS_REGULAR_EXP (child));
  assert (BTOR_IS_ARRAY_EXP (child));
  assert (pos == 1 || pos == 2);
  (void) btor;
  parent->e[pos] = child;
  tagged_parent  = BTOR_TAG_EXP (parent, pos);
  /* no parent so far? */
  if (child->first_aeq_acond_parent == NULL)
  {
    assert (child->last_aeq_acond_parent == NULL);
    child->first_aeq_acond_parent = tagged_parent;
    child->last_aeq_acond_parent  = tagged_parent;
    assert (parent->prev_aeq_acond_parent[pos] == NULL);
    assert (parent->next_aeq_acond_parent[pos] == NULL);
  }
  /* append at the end of the list */
  else
  {
    last_parent = child->last_aeq_acond_parent;
    assert (last_parent != NULL);
    parent->prev_aeq_acond_parent[pos] = last_parent;
    tag                                = BTOR_GET_TAG_EXP (last_parent);
    BTOR_REAL_ADDR_EXP (last_parent)->next_aeq_acond_parent[tag] =
        tagged_parent;
    child->last_aeq_acond_parent = tagged_parent;
  }
}

/* Connects array child to array equality parent.
 * Array equalities are inserted at the beginning of the
 * array equality and array conditional parent list.
 */
static void
connect_array_child_aeq_exp (Btor *btor,
                             BtorExp *parent,
                             BtorExp *child,
                             int pos)
{
  BtorExp *first_parent, *tagged_parent;
  int tag;
  assert (btor != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (BTOR_IS_ARRAY_EQ_EXP (parent));
  assert (BTOR_IS_REGULAR_EXP (child));
  assert (BTOR_IS_ARRAY_EXP (child));
  assert (pos == 0 || pos == 1);
  (void) btor;
  parent->e[pos] = child;
  tagged_parent  = BTOR_TAG_EXP (parent, pos);
  /* no parent so far? */
  if (child->first_aeq_acond_parent == NULL)
  {
    assert (child->last_aeq_acond_parent == NULL);
    child->first_aeq_acond_parent = tagged_parent;
    child->last_aeq_acond_parent  = tagged_parent;
    assert (parent->prev_aeq_acond_parent[pos] == NULL);
    assert (parent->next_aeq_acond_parent[pos] == NULL);
  }
  /* add parent at the beginning of the list */
  else
  {
    first_parent = child->first_aeq_acond_parent;
    assert (first_parent != NULL);
    parent->next_aeq_acond_parent[pos] = first_parent;
    tag                                = BTOR_GET_TAG_EXP (first_parent);
    BTOR_REAL_ADDR_EXP (first_parent)->prev_aeq_acond_parent[tag] =
        tagged_parent;
    child->first_aeq_acond_parent = tagged_parent;
  }
}

static void
update_constraints (Btor *btor, BtorExp *exp)
{
  BtorPtrHashTable *unsynthesized_constraints, *synthesized_constraints;
  BtorPtrHashTable *embedded_constraints, *pos, *neg;
  BtorExp *simplified, *not_simplified, *not_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (exp->simplified != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp->simplified)->simplified == NULL);
  assert (exp->constraint);

  not_exp                   = BTOR_INVERT_EXP (exp);
  simplified                = exp->simplified;
  not_simplified            = BTOR_INVERT_EXP (simplified);
  embedded_constraints      = btor->embedded_constraints;
  unsynthesized_constraints = btor->unsynthesized_constraints;
  synthesized_constraints   = btor->synthesized_constraints;
  pos = neg = NULL;

  /* variable  substitution constraints are handled in a different way */

  if (btor_find_in_ptr_hash_table (unsynthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (pos == NULL);
    pos = unsynthesized_constraints;
  }
  if (btor_find_in_ptr_hash_table (unsynthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (neg == NULL);
    neg = unsynthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (embedded_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (pos == NULL);
    pos = embedded_constraints;
  }
  if (btor_find_in_ptr_hash_table (embedded_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (neg == NULL);
    neg = embedded_constraints;
  }

  if (btor_find_in_ptr_hash_table (synthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (pos == NULL);
    pos = synthesized_constraints;
  }
  if (btor_find_in_ptr_hash_table (synthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (neg == NULL);
    neg = synthesized_constraints;
  }

  if (pos != NULL)
  {
    btor_remove_from_ptr_hash_table (pos, exp, NULL, NULL);
    btor_release_exp (btor, exp);
  }
  if (neg != NULL)
  {
    btor_remove_from_ptr_hash_table (neg, not_exp, NULL, NULL);
    btor_release_exp (btor, not_exp);
  }
  exp->constraint = 0;
}

static void
set_simplified_exp (Btor *btor,
                    BtorExp *exp,
                    BtorExp *simplified,
                    int overwrite)
{
  BtorExp *e[3];
  int i;
  assert (btor);
  assert (exp);
  assert (simplified);
  assert (BTOR_REAL_ADDR_EXP (simplified)->simplified == NULL);
  assert (btor->rewrite_level > 1);

  if (BTOR_IS_INVERTED_EXP (exp))
  {
    exp        = BTOR_INVERT_EXP (exp);
    simplified = BTOR_INVERT_EXP (simplified);
  }

  if (exp->simplified) btor_release_exp (btor, exp->simplified);

  exp->simplified = btor_copy_exp (btor, simplified);

  if (!overwrite) return;

  /* do we have to update a constraint ? */
  if (exp->constraint) update_constraints (btor, exp);

  if (exp->kind == BTOR_AEQ_EXP && exp->vreads)
  {
    btor_release_exp (btor, exp->vreads->exp2);
    btor_release_exp (btor, exp->vreads->exp1);
    BTOR_DELETE (btor->mm, exp->vreads);
    exp->vreads = 0;
  }

  remove_from_unique_table_exp (btor, exp);
  /* also updates op stats */
  erase_local_data_exp (btor, exp, 0);
  btor->ops[BTOR_PROXY_EXP]++;
  for (i = 0; i < exp->arity; i++) e[i] = exp->e[i];
  remove_from_hash_tables (btor, exp);
  disconnect_children_exp (btor, exp);
  for (i = 0; i < exp->arity; i++) btor_release_exp (btor, e[i]);
  exp->kind         = BTOR_PROXY_EXP;
  exp->disconnected = 0;
  exp->erased       = 0;
  exp->arity        = 0;
}

/* Finds most simplified expression and shortens path to it */
static BtorExp *
recursively_pointer_chase_simplified_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *real_exp, *cur, *simplified, *not_simplified, *next;
  int invert;

  assert (btor != NULL);
  assert (exp != NULL);

  real_exp = BTOR_REAL_ADDR_EXP (exp);

  assert (real_exp->simplified != NULL);
  assert (BTOR_REAL_ADDR_EXP (real_exp->simplified)->simplified != NULL);

  /* shorten path to simplified expression */
  invert     = 0;
  simplified = real_exp->simplified;
  do
  {
    if (BTOR_IS_INVERTED_EXP (simplified)) invert = !invert;
    simplified = BTOR_REAL_ADDR_EXP (simplified)->simplified;
  } while (BTOR_REAL_ADDR_EXP (simplified)->simplified != NULL);
  /* 'simplified' is representative element */
  assert (BTOR_REAL_ADDR_EXP (simplified)->simplified == NULL);
  if (invert) simplified = BTOR_INVERT_EXP (simplified);

  invert         = 0;
  not_simplified = BTOR_INVERT_EXP (simplified);
  cur            = btor_copy_exp (btor, real_exp);
  do
  {
    if (BTOR_IS_INVERTED_EXP (cur)) invert = !invert;
    cur  = BTOR_REAL_ADDR_EXP (cur);
    next = btor_copy_exp (btor, cur->simplified);
    set_simplified_exp (btor, cur, invert ? not_simplified : simplified, 0);
    btor_release_exp (btor, cur);
    cur = next;
  } while (BTOR_REAL_ADDR_EXP (cur)->simplified != NULL);
  btor_release_exp (btor, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (BTOR_IS_INVERTED_EXP (exp)) simplified = BTOR_INVERT_EXP (simplified);

  return simplified;
}

BtorExp *
btor_pointer_chase_simplified_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *real_exp;

  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;

  real_exp = BTOR_REAL_ADDR_EXP (exp);

  /* no simplified expression ? */
  if (real_exp->simplified == NULL) return exp;

  /* only one simplified expression ? */
  if (BTOR_REAL_ADDR_EXP (real_exp->simplified)->simplified == NULL)
  {
    if (BTOR_IS_INVERTED_EXP (exp))
      return BTOR_INVERT_EXP (real_exp->simplified);
    return exp->simplified;
  }
  return recursively_pointer_chase_simplified_exp (btor, exp);
}

static int
merge_simplified_exp_const (Btor *btor, BtorExp *a, BtorExp *b)
{
  BtorExp *rep_a, *rep_b, *rep;
  assert (btor != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (btor->rewrite_level > 1);
  assert (BTOR_REAL_ADDR_EXP (a)->len == 1);
  assert (BTOR_REAL_ADDR_EXP (b)->len == 1);
  rep_a = btor_pointer_chase_simplified_exp (btor, a);
  rep_b = btor_pointer_chase_simplified_exp (btor, b);

  assert (rep_a == a || rep_b == b);

  if (rep_a == BTOR_INVERT_EXP (rep_b)) return 0;

  if (BTOR_IS_BV_CONST_EXP (BTOR_REAL_ADDR_EXP (rep_a)))
    rep = rep_a;
  else
    rep = rep_b;

  if (a != rep) set_simplified_exp (btor, a, rep, 0);

  if (b != rep) set_simplified_exp (btor, b, rep, 0);

  return 1;
}

/* Connects child to its parent and updates list of parent pointers.
 * Expressions are inserted at the beginning of the regular parent list
 */
static void
connect_child_exp (Btor *btor, BtorExp *parent, BtorExp *child, int pos)
{
  BtorExp *real_child, *first_parent, *tagged_parent;
  int tag;
  (void) btor;
  assert (btor != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (btor_pointer_chase_simplified_exp (btor, child) == child);
  if (parent->kind == BTOR_WRITE_EXP && pos == 0)
    connect_array_child_write_exp (btor, parent, child);
  else if (BTOR_IS_ARRAY_EQ_EXP (parent))
    connect_array_child_aeq_exp (btor, parent, child, pos);
  else if (BTOR_IS_ARRAY_COND_EXP (parent) && pos != 0)
    connect_array_child_acond_exp (btor, parent, child, pos);
  else
  {
    real_child     = BTOR_REAL_ADDR_EXP (child);
    parent->e[pos] = child;
    tagged_parent  = BTOR_TAG_EXP (parent, pos);
    /* no parent so far? */
    if (real_child->first_parent == NULL)
    {
      assert (real_child->last_parent == NULL);
      real_child->first_parent = tagged_parent;
      real_child->last_parent  = tagged_parent;
      assert (parent->prev_parent[pos] == NULL);
      assert (parent->next_parent[pos] == NULL);
    }
    /* add parent at the beginning of the list */
    else
    {
      first_parent = real_child->first_parent;
      assert (first_parent != NULL);
      parent->next_parent[pos] = first_parent;
      tag                      = BTOR_GET_TAG_EXP (first_parent);
      BTOR_REAL_ADDR_EXP (first_parent)->prev_parent[tag] = tagged_parent;
      real_child->first_parent                            = tagged_parent;
    }
  }
}

static BtorExp *
new_const_exp_node (Btor *btor, const char *bits, int len)
{
  BtorBVConstExp *exp;
  int i;
  assert (btor != NULL);
  assert (bits != NULL);
  assert (len > 0);
  assert ((int) strlen (bits) == len);
  assert (btor_is_const_2vl (btor->mm, bits));
  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_BV_CONST_EXP]++;
  exp->kind  = BTOR_BV_CONST_EXP;
  exp->bytes = sizeof *exp;
  BTOR_NEWN (btor->mm, exp->bits, len + 1);
  for (i = 0; i < len; i++) exp->bits[i] = bits[i];
  exp->bits[len] = '\0';
  exp->len       = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  return (BtorExp *) exp;
}

static BtorExp *
new_slice_exp_node (Btor *btor, BtorExp *e0, int upper, int lower)
{
  BtorBVExp *exp = NULL;

  assert (btor != NULL);
  assert (e0 != NULL);
  assert (upper < BTOR_REAL_ADDR_EXP (e0)->len);
  assert (upper >= lower);
  assert (lower >= 0);

  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_SLICE_EXP]++;
  exp->kind  = BTOR_SLICE_EXP;
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  exp->upper = upper;
  exp->lower = lower;
  exp->len   = upper - lower + 1;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  connect_child_exp (btor, (BtorExp *) exp, e0, 0);
  return (BtorExp *) exp;
}

static void
hash_var_read_for_ua (Btor *btor, BtorExp *exp)
{
  BtorUAData *ua_data;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  assert (BTOR_IS_BV_VAR_EXP (exp) || exp->kind == BTOR_READ_EXP);
  assert (btor->ua.enabled);
  assert (!btor_find_in_ptr_hash_table (btor->ua.vars_reads, exp));

  if (btor->ua.mode == BTOR_UA_GLOBAL_MODE)
    btor_insert_in_ptr_hash_table (btor->ua.vars_reads, exp);
  else
  {
    assert (btor->ua.mode == BTOR_UA_LOCAL_MODE
            || btor->ua.mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
    ua_data = new_ua_data (btor, btor->ua.initial_eff_width);
    btor_insert_in_ptr_hash_table (btor->ua.vars_reads, exp)->data.asPtr =
        ua_data;
  }
}

static BtorExp *
new_binary_exp_node (
    Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1, int len)
{
  BtorBVExp *exp;

  assert (btor != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (kind != BTOR_AEQ_EXP);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (len > 0);

  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  btor->ops[kind]++;
  exp->kind  = kind;
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  connect_child_exp (btor, (BtorExp *) exp, e0, 0);
  connect_child_exp (btor, (BtorExp *) exp, e1, 1);

  if (btor->ua.enabled && kind == BTOR_READ_EXP)
    hash_var_read_for_ua (btor, (BtorExp *) exp);

  return (BtorExp *) exp;
}

static BtorExp *
new_aeq_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  /* we need aeq and acond next and prev fields -> type is BtorExp */
  BtorExp *exp;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_AEQ_EXP]++;
  exp->kind  = BTOR_AEQ_EXP;
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = 1;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  connect_child_exp (btor, exp, e0, 0);
  connect_child_exp (btor, exp, e1, 1);
  return exp;
}

static BtorExp *
new_ternary_exp_node (Btor *btor,
                      BtorExpKind kind,
                      BtorExp *e0,
                      BtorExp *e1,
                      BtorExp *e2,
                      int len)
{
  BtorBVExp *exp;

  assert (btor != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (kind == BTOR_BCOND_EXP);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (len > 0);

  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  btor->ops[kind]++;
  exp->kind  = kind;
  exp->bytes = sizeof *exp;
  exp->arity = 3;
  exp->len   = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  connect_child_exp (btor, (BtorExp *) exp, e0, 0);
  connect_child_exp (btor, (BtorExp *) exp, e1, 1);
  connect_child_exp (btor, (BtorExp *) exp, e2, 2);
  return (BtorExp *) exp;
}

static BtorExp *
new_write_exp_node (Btor *btor,
                    BtorExp *e_array,
                    BtorExp *e_index,
                    BtorExp *e_value)
{
  BtorMemMgr *mm;
  BtorExp *exp;
  assert (btor != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (e_value != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)));
  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_WRITE_EXP]++;
  exp->kind      = BTOR_WRITE_EXP;
  exp->bytes     = sizeof *exp;
  exp->arity     = 3;
  exp->index_len = BTOR_REAL_ADDR_EXP (e_index)->len;
  exp->len       = BTOR_REAL_ADDR_EXP (e_value)->len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  /* append writes to the end of parrent list */
  connect_child_exp (btor, exp, e_array, 0);
  connect_child_exp (btor, exp, e_index, 1);
  connect_child_exp (btor, exp, e_value, 2);

  if (btor->ua.enabled)
    btor_insert_in_ptr_hash_table (btor->ua.writes_aconds, exp);

  return exp;
}

static BtorExp *
new_acond_exp_node (Btor *btor, BtorExp *e_cond, BtorExp *a_if, BtorExp *a_else)
{
  BtorMemMgr *mm;
  BtorExp *exp;
  assert (btor != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (BTOR_IS_REGULAR_EXP (a_if));
  assert (BTOR_IS_REGULAR_EXP (a_else));
  assert (BTOR_IS_ARRAY_EXP (a_if));
  assert (BTOR_IS_ARRAY_EXP (a_else));
  assert (a_if->index_len == a_else->index_len);
  assert (a_if->index_len > 0);
  assert (a_if->len == a_else->len);
  assert (a_if->len > 0);
  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_ACOND_EXP]++;
  exp->kind      = BTOR_ACOND_EXP;
  exp->bytes     = sizeof *exp;
  exp->arity     = 3;
  exp->index_len = a_if->index_len;
  exp->len       = a_if->len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  connect_child_exp (btor, exp, e_cond, 0);
  connect_child_exp (btor, exp, a_if, 1);
  connect_child_exp (btor, exp, a_else, 2);

  if (btor->ua.enabled)
    btor_insert_in_ptr_hash_table (btor->ua.writes_aconds, exp);

  return exp;
}

/* Computes hash value of expression by id */
unsigned int
btor_hash_exp_by_id (BtorExp *exp)
{
  assert (exp != NULL);
  return (unsigned int) BTOR_REAL_ADDR_EXP (exp)->id * 7334147u;
}

/* Compares expressions by id */
int
btor_compare_exp_by_id (BtorExp *exp0, BtorExp *exp1)
{
  int id0, id1;
  assert (exp0 != NULL);
  assert (exp1 != NULL);
  id0 = BTOR_GET_ID_EXP (exp0);
  id1 = BTOR_GET_ID_EXP (exp1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

/* Finds constant expression in hash table. Returns NULL if it could not be
 * found. */
static BtorExp **
find_const_exp (Btor *btor, const char *bits, int len)
{
  BtorExp *cur, **result;
  unsigned int hash;
  assert (btor != NULL);
  assert (bits != NULL);
  assert (len > 0);
  assert ((int) strlen (bits) == len);
  hash   = btor_hashstr ((void *) bits);
  hash   = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (btor->table.size - 1);
  result = btor->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (BTOR_IS_BV_CONST_EXP (cur) && cur->len == len
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

/* Finds slice expression in hash table. Returns NULL if it could not be
 * found. */
static BtorExp **
find_slice_exp (Btor *btor, BtorExp *e0, int upper, int lower)
{
  BtorExp *cur, **result;
  unsigned int hash;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (upper >= lower);
  hash = (((unsigned int) BTOR_REAL_ADDR_EXP (e0)->id + (unsigned int) upper
           + (unsigned int) lower)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (btor->table.size - 1);
  result = btor->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->kind == BTOR_SLICE_EXP && cur->e[0] == e0 && cur->upper == upper
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

/* Finds binary expression in hash table. Returns NULL if it could not be
 * found. */
static BtorExp **
find_binary_exp (Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1)
{
  BtorExp *cur, **result;
  unsigned int hash;
  assert (btor != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (btor->rewrite_level == 0
          || !BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
          || BTOR_REAL_ADDR_EXP (e0)->id <= BTOR_REAL_ADDR_EXP (e1)->id);
  hash = (((unsigned int) BTOR_REAL_ADDR_EXP (e0)->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (e1)->id)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (btor->table.size - 1);
  result = btor->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->kind == kind && cur->e[0] == e0 && cur->e[1] == e1)
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

/* Finds ternary expression in hash table. Returns NULL if it could not be
 * found. */
static BtorExp **
find_ternary_exp (
    Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1, BtorExp *e2)
{
  BtorExp *cur, **result;
  unsigned int hash;
  assert (btor != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  hash = (((unsigned) BTOR_REAL_ADDR_EXP (e0)->id
           + (unsigned) BTOR_REAL_ADDR_EXP (e1)->id
           + (unsigned) BTOR_REAL_ADDR_EXP (e2)->id)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (btor->table.size - 1);
  result = btor->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->kind == kind && cur->e[0] == e0 && cur->e[1] == e1
        && cur->e[2] == e2)
      break;
    else
    {
      result = &(cur->next);
      cur    = *result;
    }
  }
  return result;
}

/* Enlarges unique table and rehashes expressions. */
static void
enlarge_exp_unique_table (Btor *btor)
{
  BtorMemMgr *mm;
  int size, new_size, i;
  unsigned int hash;
  BtorExp *cur, *temp, **new_chains;
  assert (btor != NULL);
  mm       = btor->mm;
  size     = btor->table.size;
  new_size = size << 1;
  assert (new_size / size == 2);
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = btor->table.chains[i];
    while (cur != NULL)
    {
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (!BTOR_IS_BV_VAR_EXP (cur));
      assert (!BTOR_IS_ARRAY_VAR_EXP (cur));
      temp             = cur->next;
      hash             = compute_hash_exp (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BTOR_DELETEN (mm, btor->table.chains, size);
  btor->table.size   = new_size;
  btor->table.chains = new_chains;
}

static void
mark_synth_mark_exp (Btor *btor, BtorExp *exp, int new_mark)
{
  BtorMemMgr *mm;
  BtorExpPtrStack stack;
  BtorExp *cur;
  int i;

  assert (btor != NULL);
  assert (exp != NULL);

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  cur = BTOR_REAL_ADDR_EXP (exp);
  goto MARK_SYNTH_MARK_EXP_ENTER_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
  MARK_SYNTH_MARK_EXP_ENTER_WITHOUT_POP:
    if (cur->synth_mark != new_mark)
    {
      cur->synth_mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

void
btor_mark_exp (Btor *btor, BtorExp *exp, int new_mark)
{
  BtorMemMgr *mm;
  BtorExpPtrStack stack;
  BtorExp *cur;
  int i;

  assert (btor != NULL);
  assert (exp != NULL);

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  cur = BTOR_REAL_ADDR_EXP (exp);
  goto BTOR_MARK_EXP_ENTER_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
  BTOR_MARK_EXP_ENTER_WITHOUT_POP:
    if (cur->mark != new_mark)
    {
      cur->mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

BtorExp *
btor_const_exp (Btor *btor, const char *bits)
{
  BtorExp **lookup;
  int inv, len;
  char *lookupbits;

  assert (btor != NULL);
  assert (bits != NULL);
  assert (*bits != '\0');

  len = (int) strlen (bits);
  assert (len > 0);
  inv        = 0;
  lookupbits = (char *) bits;
  if (btor->rewrite_level > 0)
  {
    /* normalize constants, constants are always even */
    if (bits[len - 1] == '1')
    {
      lookupbits = btor_not_const (btor->mm, bits);
      inv        = 1;
    }
  }
  lookup = find_const_exp (btor, lookupbits, len);
  if (*lookup == NULL)
  {
    if (btor->table.num_elements == btor->table.size
        && btor_log_2_util (btor->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (btor);
      lookup = find_const_exp (btor, lookupbits, len);
    }
    *lookup = new_const_exp_node (btor, lookupbits, len);
    assert (btor->table.num_elements < INT_MAX);
    btor->table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  if (inv)
  {
    btor_delete_const (btor->mm, lookupbits);
    return BTOR_INVERT_EXP (*lookup);
  }
  return *lookup;
}

static BtorExp *
int_min_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  string    = btor_zero_const (btor->mm, len);
  string[0] = '1';
  result    = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_zero_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;

  assert (btor != NULL);
  assert (len > 0);

  string = btor_zero_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_false_exp (Btor *btor)
{
  assert (btor != NULL);
  return btor_zero_exp (btor, 1);
}

BtorExp *
btor_ones_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;

  assert (btor != NULL);
  assert (len > 0);

  string = btor_ones_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_one_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;

  assert (btor != NULL);
  assert (len > 0);

  string = btor_one_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_int_to_exp (Btor *btor, int i, int len)
{
  char *string;
  BtorExp *result;

  assert (btor != NULL);
  assert (len > 0);

  string = btor_int_to_const (btor->mm, i, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_unsigned_to_exp (Btor *btor, unsigned int u, int len)
{
  char *string;
  BtorExp *result;

  assert (btor != NULL);
  assert (len > 0);

  string = btor_unsigned_to_const (btor->mm, u, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_true_exp (Btor *btor)
{
  assert (btor != NULL);
  return btor_one_exp (btor, 1);
}

BtorExp *
btor_var_exp (Btor *btor, int len, const char *symbol)
{
  BtorMemMgr *mm;
  BtorBVVarExp *exp;

  assert (btor != NULL);
  assert (len > 0);
  assert (symbol != NULL);

  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_BV_VAR_EXP]++;
  exp->kind   = BTOR_BV_VAR_EXP;
  exp->bytes  = sizeof *exp;
  exp->symbol = btor_strdup (mm, symbol);
  exp->len    = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  exp->bits = btor_x_const_3vl (btor->mm, len);
  if (btor->ua.enabled) hash_var_read_for_ua (btor, (BtorExp *) exp);
  (void) btor_insert_in_ptr_hash_table (btor->bv_vars, exp);
  return (BtorExp *) exp;
}

BtorExp *
btor_array_exp (Btor *btor, int elem_len, int index_len, const char *symbol)
{
  BtorMemMgr *mm;
  BtorArrayVarExp *exp;

  assert (btor != NULL);
  assert (elem_len > 0);
  assert (index_len > 0);
  assert (symbol != NULL);

  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->stats.expressions++;
  btor->ops[BTOR_ARRAY_VAR_EXP]++;
  exp->kind      = BTOR_ARRAY_VAR_EXP;
  exp->bytes     = sizeof *exp;
  exp->symbol    = btor_strdup (mm, symbol);
  exp->index_len = index_len;
  exp->len       = elem_len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1;
  exp->btor = btor;
  (void) btor_insert_in_ptr_hash_table (btor->array_vars, exp);
  return (BtorExp *) exp;
}

static BtorExp *
unary_exp_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BtorExp **lookup;
  assert (btor != NULL);
  assert (exp != NULL);
  int inv;

  exp = btor_pointer_chase_simplified_exp (btor, exp);

  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);

  if (btor->rewrite_level > 0 && BTOR_IS_INVERTED_EXP (exp))
  {
    inv = 1;
    exp = BTOR_INVERT_EXP (exp);
  }
  else
    inv = 0;

  lookup = find_slice_exp (btor, exp, upper, lower);
  if (*lookup == NULL)
  {
    if (btor->table.num_elements == btor->table.size
        && btor_log_2_util (btor->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (btor);
      lookup = find_slice_exp (btor, exp, upper, lower);
    }
    *lookup = new_slice_exp_node (btor, exp, upper, lower);
    inc_exp_ref_counter (btor, exp);
    assert (btor->table.num_elements < INT_MAX);
    btor->table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  if (inv) return BTOR_INVERT_EXP (*lookup);
  return *lookup;
}

BtorExp *
btor_slice_exp_node (Btor *btor, BtorExp *exp, int upper, int lower)
{
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));
  return unary_exp_slice_exp (btor, exp, upper, lower);
}

static BtorExp *
binary_exp (Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1, int len)
{
  BtorExp **lookup, *temp;
  assert (btor != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (len > 0);

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);

  if (btor->rewrite_level > 0 && BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
      && BTOR_REAL_ADDR_EXP (e1)->id < BTOR_REAL_ADDR_EXP (e0)->id)
  {
    temp = e0;
    e0   = e1;
    e1   = temp;
  }
  assert (btor->rewrite_level == 0
          || !BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
          || BTOR_REAL_ADDR_EXP (e0)->id <= BTOR_REAL_ADDR_EXP (e1)->id);
  lookup = find_binary_exp (btor, kind, e0, e1);
  if (*lookup == NULL)
  {
    if (btor->table.num_elements == btor->table.size
        && btor_log_2_util (btor->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (btor);
      lookup = find_binary_exp (btor, kind, e0, e1);
    }
    if (kind == BTOR_AEQ_EXP)
      *lookup = new_aeq_exp_node (btor, e0, e1);
    else
      *lookup = new_binary_exp_node (btor, kind, e0, e1, len);
    inc_exp_ref_counter (btor, e0);
    inc_exp_ref_counter (btor, e1);
    assert (btor->table.num_elements < INT_MAX);
    btor->table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_and_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_AND_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_eq_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExpKind kind;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)))
    kind = BTOR_AEQ_EXP;
  else
    kind = BTOR_BEQ_EXP;

  return binary_exp (btor, kind, e0, e1, 1);
}

BtorExp *
btor_add_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_ADD_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_mul_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_MUL_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_ult_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_ULT_EXP, e0, e1, 1);
}

BtorExp *
btor_sll_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_SLL_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_srl_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_SRL_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_udiv_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_UDIV_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_urem_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return binary_exp (btor, BTOR_UREM_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
}

BtorExp *
btor_concat_exp_node (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));
  return binary_exp (
      btor,
      BTOR_CONCAT_EXP,
      e0,
      e1,
      BTOR_REAL_ADDR_EXP (e0)->len + BTOR_REAL_ADDR_EXP (e1)->len);
}

BtorExp *
btor_read_exp_node (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));
  return binary_exp (btor, BTOR_READ_EXP, e_array, e_index, e_array->len);
}

static BtorExp *
ternary_exp (Btor *btor,
             BtorExpKind kind,
             BtorExp *e0,
             BtorExp *e1,
             BtorExp *e2,
             int len)
{
  BtorExp **lookup;
  assert (btor != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  e2 = btor_pointer_chase_simplified_exp (btor, e2);

  lookup = find_ternary_exp (btor, kind, e0, e1, e2);
  if (*lookup == NULL)
  {
    if (btor->table.num_elements == btor->table.size
        && btor_log_2_util (btor->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (btor);
      lookup = find_ternary_exp (btor, kind, e0, e1, e2);
    }
    switch (kind)
    {
      case BTOR_WRITE_EXP:
        *lookup = new_write_exp_node (btor, e0, e1, e2);
        break;
      case BTOR_ACOND_EXP:
        *lookup = new_acond_exp_node (btor, e0, e1, e2);
        break;
      default:
        assert (kind == BTOR_BCOND_EXP);
        *lookup = new_ternary_exp_node (btor, kind, e0, e1, e2, len);
        break;
    }
    inc_exp_ref_counter (btor, e0);
    inc_exp_ref_counter (btor, e1);
    inc_exp_ref_counter (btor, e2);
    assert (btor->table.num_elements < INT_MAX);
    btor->table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_write_exp_node (Btor *btor,
                     BtorExp *e_array,
                     BtorExp *e_index,
                     BtorExp *e_value)
{
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  e_value = btor_pointer_chase_simplified_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));
  return ternary_exp (btor, BTOR_WRITE_EXP, e_array, e_index, e_value, 0);
}

BtorExp *
btor_cond_exp_node (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExpKind kind;

  e_cond = btor_pointer_chase_simplified_exp (btor, e_cond);
  e_if   = btor_pointer_chase_simplified_exp (btor, e_if);
  e_else = btor_pointer_chase_simplified_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));

  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if)))
    kind = BTOR_ACOND_EXP;
  else
    kind = BTOR_BCOND_EXP;

  return ternary_exp (
      btor, kind, e_cond, e_if, e_else, BTOR_REAL_ADDR_EXP (e_if)->len);
}

BtorExp *
btor_not_exp (Btor *btor, BtorExp *exp)
{
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  (void) btor;
  inc_exp_ref_counter (btor, exp);
  return BTOR_INVERT_EXP (exp);
}

BtorExp *
btor_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_add_exp (btor, e0, e1);
  else
    result = btor_add_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_neg_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *one;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_add_exp (btor, BTOR_INVERT_EXP (exp), one);
  btor_release_exp (btor, one);
  return result;
}

BtorExp *
btor_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BtorExp *result;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_slice_exp (btor, exp, upper, lower);
  else
    result = btor_slice_exp_node (btor, exp, upper, lower);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_or_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_EXP (
      btor_and_exp (btor, BTOR_INVERT_EXP (e0), BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_eq_exp (btor, e0, e1);
  else
    result = btor_eq_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_and_exp (btor, e0, e1);
  else
    result = btor_and_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_xor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, * or, *and;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  or     = btor_or_exp (btor, e0, e1);
  and    = btor_and_exp (btor, e0, e1);
  result = btor_and_exp (btor, or, BTOR_INVERT_EXP (and));
  btor_release_exp (btor, or);
  btor_release_exp (btor, and);
  return result;
}

BtorExp *
btor_xnor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_EXP (btor_xor_exp (btor, e0, e1));
}

BtorExp *
btor_concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_concat_exp (btor, e0, e1);
  else
    result = btor_concat_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_cond_exp (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExp *result;

  e_cond = btor_pointer_chase_simplified_exp (btor, e_cond);
  e_if   = btor_pointer_chase_simplified_exp (btor, e_if);
  e_else = btor_pointer_chase_simplified_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_cond_exp (btor, e_cond, e_if, e_else);
  else
    result = btor_cond_exp_node (btor, e_cond, e_if, e_else);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_redor_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *zero;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  zero   = btor_zero_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = BTOR_INVERT_EXP (btor_eq_exp (btor, exp, zero));
  btor_release_exp (btor, zero);
  return result;
}

BtorExp *
btor_redxor_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *slice, *xor;
  int i, len;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  len = BTOR_REAL_ADDR_EXP (exp)->len;

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

BtorExp *
btor_redand_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *ones;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  ones   = btor_ones_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_eq_exp (btor, exp, ones);
  btor_release_exp (btor, ones);
  return result;
}

BtorExp *
btor_uext_exp (Btor *btor, BtorExp *exp, int len)
{
  BtorExp *result, *zero;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
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

BtorExp *
btor_sext_exp (Btor *btor, BtorExp *exp, int len)
{
  BtorExp *result, *zero, *ones, *neg, *cond;
  int exp_len;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_ext_exp_dbg (btor, exp, len));

  if (len == 0)
    result = btor_copy_exp (btor, exp);
  else
  {
    assert (len > 0);
    zero    = btor_zero_exp (btor, len);
    ones    = btor_ones_exp (btor, len);
    exp_len = BTOR_REAL_ADDR_EXP (exp)->len;
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

BtorExp *
btor_nand_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_EXP (btor_and_exp (btor, e0, e1));
}

BtorExp *
btor_nor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_EXP (btor_or_exp (btor, e0, e1));
}

BtorExp *
btor_implies_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == 1);
  return BTOR_INVERT_EXP (btor_and_exp (btor, e0, BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_iff_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == 1);
  return btor_eq_exp (btor, e0, e1);
}

BtorExp *
btor_ne_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_EXP (btor_eq_exp (btor, e0, e1));
}

BtorExp *
btor_uaddo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *uext_e1, *uext_e2, *add;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, e1, 1);
  add     = btor_add_exp (btor, uext_e1, uext_e2);
  result  = btor_slice_exp (btor, add, len, len);
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, add);
  return result;
}

BtorExp *
btor_saddo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *sign_result;
  BtorExp *add, *and1, *and2, *or1, *or2;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len         = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1     = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (btor, e1, len - 1, len - 1);
  add         = btor_add_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, add, len - 1, len - 1);
  and1        = btor_and_exp (btor, sign_e1, sign_e2);
  or1         = btor_and_exp (btor, and1, BTOR_INVERT_EXP (sign_result));
  and2 =
      btor_and_exp (btor, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
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

BtorExp *
btor_mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_mul_exp (btor, e0, e1);
  else
    result = btor_mul_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_umulo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *uext_e1, *uext_e2, *mul, *slice, *and, * or, **temps_e2;
  int i, len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_EXP (e0)->len;
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

BtorExp *
btor_smulo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sext_e1, *sext_e2, *sign_e1, *sign_e2, *sext_sign_e1;
  BtorExp *sext_sign_e2, *xor_sign_e1, *xor_sign_e2, *mul, *slice, *slice_n;
  BtorExp *slice_n_minus_1, *xor, *and, * or, **temps_e2;
  int i, len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_EXP (e0)->len;
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

BtorExp *
btor_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_ult_exp (btor, e0, e1);
  else
    result = btor_ult_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_slt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *rest_e1, *rest_e2, *ult;
  BtorExp *e1_signed_only, *e1_e2_pos, *e1_e2_signed, *and1, *and2, * or ;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return btor_and_exp (btor, e0, BTOR_INVERT_EXP (e1));
  sign_e1 = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (btor, e1, len - 1, len - 1);
  /* rest_e1: e0 without sign bit */
  rest_e1 = btor_slice_exp (btor, e0, len - 2, 0);
  /* rest_e2: e1 without sign bit */
  rest_e2 = btor_slice_exp (btor, e1, len - 2, 0);
  /* ult: is rest of e0 < rest of e1 ? */
  ult = btor_ult_exp (btor, rest_e1, rest_e2);
  /* e1_signed_only: only e0 is negative */
  e1_signed_only = btor_and_exp (btor, sign_e1, BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_pos: e0 and e1 are positive */
  e1_e2_pos =
      btor_and_exp (btor, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_signed: e0 and e1 are negative */
  e1_e2_signed = btor_and_exp (btor, sign_e1, sign_e2);
  and1         = btor_and_exp (btor, e1_e2_pos, ult);
  and2         = btor_and_exp (btor, e1_e2_signed, ult);
  or           = btor_or_exp (btor, and1, and2);
  result       = btor_or_exp (btor, e1_signed_only, or);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, sign_e2);
  btor_release_exp (btor, rest_e1);
  btor_release_exp (btor, rest_e2);
  btor_release_exp (btor, ult);
  btor_release_exp (btor, e1_signed_only);
  btor_release_exp (btor, e1_e2_pos);
  btor_release_exp (btor, e1_e2_signed);
  btor_release_exp (btor, and1);
  btor_release_exp (btor, and2);
  btor_release_exp (btor, or);
  return result;
}

BtorExp *
btor_ulte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *ult;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  ult    = btor_ult_exp (btor, e1, e0);
  result = btor_not_exp (btor, ult);
  btor_release_exp (btor, ult);
  return result;
}

BtorExp *
btor_slte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *slt;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  slt    = btor_slt_exp (btor, e1, e0);
  result = btor_not_exp (btor, slt);
  btor_release_exp (btor, slt);
  return result;
}

BtorExp *
btor_ugt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_ult_exp (btor, e1, e0);
}

BtorExp *
btor_sgt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_slt_exp (btor, e1, e0);
}

BtorExp *
btor_ugte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *ult;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  ult    = btor_ult_exp (btor, e0, e1);
  result = btor_not_exp (btor, ult);
  btor_release_exp (btor, ult);
  return result;
}

BtorExp *
btor_sgte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *slt;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  slt    = btor_slt_exp (btor, e0, e1);
  result = btor_not_exp (btor, slt);
  btor_release_exp (btor, slt);
  return result;
}

BtorExp *
btor_sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_sll_exp (btor, e0, e1);
  else
    result = btor_sll_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_srl_exp (btor, e0, e1);
  else
    result = btor_srl_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_sra_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *srl1, *srl2;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (btor, e0, len - 1, len - 1);
  srl1    = btor_srl_exp (btor, e0, e1);
  srl2    = btor_srl_exp (btor, BTOR_INVERT_EXP (e0), e1);
  result  = btor_cond_exp (btor, sign_e1, BTOR_INVERT_EXP (srl2), srl1);
  btor_release_exp (btor, sign_e1);
  btor_release_exp (btor, srl1);
  btor_release_exp (btor, srl2);
  return result;
}

BtorExp *
btor_rol_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sll, *neg_e2, *srl;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  len    = BTOR_REAL_ADDR_EXP (e0)->len;
  sll    = btor_sll_exp (btor, e0, e1);
  neg_e2 = btor_neg_exp (btor, e1);
  srl    = btor_srl_exp (btor, e0, neg_e2);
  result = btor_or_exp (btor, sll, srl);
  btor_release_exp (btor, sll);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, srl);
  return result;
}

BtorExp *
btor_ror_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *srl, *neg_e2, *sll;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  len    = BTOR_REAL_ADDR_EXP (e0)->len;
  srl    = btor_srl_exp (btor, e0, e1);
  neg_e2 = btor_neg_exp (btor, e1);
  sll    = btor_sll_exp (btor, e0, neg_e2);
  result = btor_or_exp (btor, srl, sll);
  btor_release_exp (btor, srl);
  btor_release_exp (btor, neg_e2);
  btor_release_exp (btor, sll);
  return result;
}

BtorExp *
btor_sub_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *neg_e2;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  neg_e2 = btor_neg_exp (btor, e1);
  result = btor_add_exp (btor, e0, neg_e2);
  btor_release_exp (btor, neg_e2);
  return result;
}

BtorExp *
btor_usubo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *uext_e1, *uext_e2, *add1, *add2, *one;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  uext_e1 = btor_uext_exp (btor, e0, 1);
  uext_e2 = btor_uext_exp (btor, BTOR_INVERT_EXP (e1), 1);
  assert (len < INT_MAX);
  one    = btor_one_exp (btor, len + 1);
  add1   = btor_add_exp (btor, uext_e2, one);
  add2   = btor_add_exp (btor, uext_e1, add1);
  result = BTOR_INVERT_EXP (btor_slice_exp (btor, add2, len, len));
  btor_release_exp (btor, uext_e1);
  btor_release_exp (btor, uext_e2);
  btor_release_exp (btor, add1);
  btor_release_exp (btor, add2);
  btor_release_exp (btor, one);
  return result;
}

BtorExp *
btor_ssubo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *sign_result;
  BtorExp *sub, *and1, *and2, *or1, *or2;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len         = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1     = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (btor, e1, len - 1, len - 1);
  sub         = btor_sub_exp (btor, e0, e1);
  sign_result = btor_slice_exp (btor, sub, len - 1, len - 1);
  and1        = btor_and_exp (btor, BTOR_INVERT_EXP (sign_e1), sign_e2);
  or1         = btor_and_exp (btor, and1, sign_result);
  and2        = btor_and_exp (btor, sign_e1, BTOR_INVERT_EXP (sign_e2));
  or2         = btor_and_exp (btor, and2, BTOR_INVERT_EXP (sign_result));
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

BtorExp *
btor_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_udiv_exp (btor, e0, e1);
  else
    result = btor_udiv_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_sdiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *xor, *neg_e1, *neg_e2;
  BtorExp *cond_e1, *cond_e2, *udiv, *neg_udiv;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_EXP (e0)->len;

  if (len == 1)
    return BTOR_INVERT_EXP (btor_and_exp (btor, BTOR_INVERT_EXP (e0), e1));

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

BtorExp *
btor_sdivo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *int_min, *ones, *eq1, *eq2;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  int_min = int_min_exp (btor, BTOR_REAL_ADDR_EXP (e0)->len);
  ones    = btor_ones_exp (btor, BTOR_REAL_ADDR_EXP (e1)->len);
  eq1     = btor_eq_exp (btor, e0, int_min);
  eq2     = btor_eq_exp (btor, e1, ones);
  result  = btor_and_exp (btor, eq1, eq2);
  btor_release_exp (btor, int_min);
  btor_release_exp (btor, ones);
  btor_release_exp (btor, eq1);
  btor_release_exp (btor, eq2);
  return result;
}

BtorExp *
btor_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_urem_exp (btor, e0, e1);
  else
    result = btor_urem_exp_node (btor, e0, e1);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_srem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1;
  BtorExp *cond_e0, *cond_e1, *urem, *neg_urem;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len = BTOR_REAL_ADDR_EXP (e0)->len;

  if (len == 1) return btor_and_exp (btor, e0, BTOR_INVERT_EXP (e1));

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

BtorExp *
btor_smod_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1, *cond_e0, *cond_e1;
  BtorExp *neg_e0_and_e1, *neg_e0_and_neg_e1, *zero, *e0_zero;
  BtorExp *neg_urem, *add1, *add2, *or1, *or2, *e0_and_e1, *e0_and_neg_e1;
  BtorExp *cond_case1, *cond_case2, *cond_case3, *cond_case4, *urem;
  BtorExp *urem_zero, *gadd1, *gadd2;
  int len;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  zero    = btor_zero_exp (btor, len);
  e0_zero = btor_eq_exp (btor, zero, e0);
  sign_e0 = btor_slice_exp (btor, e0, len - 1, len - 1);
  sign_e1 = btor_slice_exp (btor, e1, len - 1, len - 1);
  neg_e0  = btor_neg_exp (btor, e0);
  neg_e1  = btor_neg_exp (btor, e1);
  e0_and_e1 =
      btor_and_exp (btor, BTOR_INVERT_EXP (sign_e0), BTOR_INVERT_EXP (sign_e1));
  e0_and_neg_e1     = btor_and_exp (btor, BTOR_INVERT_EXP (sign_e0), sign_e1);
  neg_e0_and_e1     = btor_and_exp (btor, sign_e0, BTOR_INVERT_EXP (sign_e1));
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

BtorExp *
btor_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BtorExp *result;

  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_read_exp (btor, e_array, e_index);
  else
    result = btor_read_exp_node (btor, e_array, e_index);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_write_exp (Btor *btor,
                BtorExp *e_array,
                BtorExp *e_index,
                BtorExp *e_value)
{
  BtorExp *result;

  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  e_value = btor_pointer_chase_simplified_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_write_exp (btor, e_array, e_index, e_value);
  else
    result = btor_write_exp_node (btor, e_array, e_index, e_value);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_next_exp_bmc (Btor *btor,
                   BtorPtrHashTable *reg_table,
                   BtorExp *root,
                   int k,
                   BtorPtrHashTable *input_table)
{
  BtorExp *cur, *result, *e0, *e1, *e2, *cur_result, *var;
  BtorExp *(*bin_func) (Btor *, BtorExp *, BtorExp *);
  BtorExpPtrStack stack;
  BtorPtrHashTable *build_table;
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  char *var_name;
  int var_name_len;
  assert (btor != NULL);
  assert (reg_table != NULL);
  assert (root != NULL);
  assert (k >= 0);
  assert (input_table != NULL);
  assert (reg_table->count > 0u);

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  build_table = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  assert (BTOR_REAL_ADDR_EXP (root)->mark == 0);
  assert (BTOR_REAL_ADDR_EXP (root)->simplified == NULL);

  BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (root));
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur));

    if (cur->mark == 2) continue;

    if (cur->mark == 0)
    {
      if (BTOR_IS_BV_CONST_EXP (cur))
      {
        btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
            btor_copy_exp (btor, cur);
        cur->mark = 2;
      }
      else if (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur))
      {
        bucket = btor_find_in_ptr_hash_table (reg_table, cur);
        if (bucket == NULL)
        {
          /* no register -> input variable
           * we have to look if input has already been instantiated
           * before
           */
          bucket = btor_find_in_ptr_hash_table (input_table, cur);
          if (bucket == NULL)
          {
            if (BTOR_IS_BV_VAR_EXP (cur))
            {
              assert (cur->symbol != NULL);
              var_name_len =
                  strlen (cur->symbol) + btor_num_digits_util (k) + 2;
              BTOR_NEWN (mm, var_name, var_name_len);
              sprintf (var_name, "%s_%d", cur->symbol, k);
              var = btor_var_exp (btor, cur->len, var_name);
              BTOR_DELETEN (mm, var_name, var_name_len);
            }
            else
            {
              assert (BTOR_IS_ARRAY_VAR_EXP (cur));
              var_name_len =
                  strlen (cur->symbol) + btor_num_digits_util (k) + 2;
              BTOR_NEWN (mm, var_name, var_name_len);
              sprintf (var_name, "%s_%d", cur->symbol, k);
              var = btor_array_exp (btor, cur->len, cur->index_len, var_name);
              BTOR_DELETEN (mm, var_name, var_name_len);
            }
            btor_insert_in_ptr_hash_table (input_table, cur)->data.asPtr = var;
            btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
                btor_copy_exp (btor, var);
          }
          else
          {
            assert (bucket->data.asPtr != NULL);
            btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
                btor_copy_exp (btor, (BtorExp *) bucket->data.asPtr);
          }
        }
        else
        {
          assert (bucket->data.asPtr != NULL);
          btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
              btor_copy_exp (btor, (BtorExp *) bucket->data.asPtr);
        }
        cur->mark = 2;
      }
      else
      {
        cur->mark = 1;
        BTOR_PUSH_STACK (mm, stack, cur);
        switch (cur->arity)
        {
          case 1:
            BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur->e[0]));
            break;
          case 2:
            BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur->e[1]));
            BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur->e[0]));
            break;
          default:
            assert (cur->arity == 3);
            BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur->e[2]));
            BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur->e[1]));
            BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur->e[0]));
            break;
        }
      }
    }
    else
    {
      assert (cur->mark == 1);
      assert (!BTOR_IS_BV_VAR_EXP (cur) && !BTOR_IS_BV_CONST_EXP (cur)
              && !BTOR_IS_ARRAY_VAR_EXP (cur));
      switch (cur->arity)
      {
        case 1:
          assert (cur->kind == BTOR_SLICE_EXP);
          bucket = btor_find_in_ptr_hash_table (build_table,
                                                BTOR_REAL_ADDR_EXP (cur->e[0]));
          assert (bucket != NULL);
          assert (bucket->data.asPtr != NULL);
          e0 = (BtorExp *) bucket->data.asPtr;
          if (BTOR_IS_INVERTED_EXP (cur->e[0])) e0 = BTOR_INVERT_EXP (e0);
          cur_result = btor_slice_exp (btor, e0, cur->upper, cur->lower);
          break;

        case 2:
          bucket = btor_find_in_ptr_hash_table (build_table,
                                                BTOR_REAL_ADDR_EXP (cur->e[0]));
          assert (bucket != NULL);
          assert (bucket->data.asPtr != NULL);
          e0 = (BtorExp *) bucket->data.asPtr;
          if (BTOR_IS_INVERTED_EXP (cur->e[0])) e0 = BTOR_INVERT_EXP (e0);
          bucket = btor_find_in_ptr_hash_table (build_table,
                                                BTOR_REAL_ADDR_EXP (cur->e[1]));
          assert (bucket != NULL);
          assert (bucket->data.asPtr != NULL);
          e1 = (BtorExp *) bucket->data.asPtr;
          if (BTOR_IS_INVERTED_EXP (cur->e[1])) e1 = BTOR_INVERT_EXP (e1);
          switch (cur->kind)
          {
            case BTOR_AND_EXP: bin_func = btor_and_exp; break;
            case BTOR_BEQ_EXP:
            case BTOR_AEQ_EXP: bin_func = btor_eq_exp; break;
            case BTOR_ADD_EXP: bin_func = btor_add_exp; break;
            case BTOR_MUL_EXP: bin_func = btor_mul_exp; break;
            case BTOR_ULT_EXP: bin_func = btor_ult_exp; break;
            case BTOR_SLL_EXP: bin_func = btor_sll_exp; break;
            case BTOR_SRL_EXP: bin_func = btor_srl_exp; break;
            case BTOR_UDIV_EXP: bin_func = btor_udiv_exp; break;
            case BTOR_UREM_EXP: bin_func = btor_urem_exp; break;
            case BTOR_CONCAT_EXP: bin_func = btor_concat_exp; break;
            default:
              assert (BTOR_IS_READ_EXP (cur));
              bin_func = btor_read_exp;
              break;
          }
          cur_result = bin_func (btor, e0, e1);
          break;

        default:
          assert (cur->arity == 3);
          bucket = btor_find_in_ptr_hash_table (build_table,
                                                BTOR_REAL_ADDR_EXP (cur->e[0]));
          assert (bucket != NULL);
          assert (bucket->data.asPtr != NULL);
          e0 = (BtorExp *) bucket->data.asPtr;
          if (BTOR_IS_INVERTED_EXP (cur->e[0])) e0 = BTOR_INVERT_EXP (e0);
          bucket = btor_find_in_ptr_hash_table (build_table,
                                                BTOR_REAL_ADDR_EXP (cur->e[1]));
          assert (bucket != NULL);
          assert (bucket->data.asPtr != NULL);
          e1 = (BtorExp *) bucket->data.asPtr;
          if (BTOR_IS_INVERTED_EXP (cur->e[1])) e1 = BTOR_INVERT_EXP (e1);
          bucket = btor_find_in_ptr_hash_table (build_table,
                                                BTOR_REAL_ADDR_EXP (cur->e[2]));
          assert (bucket != NULL);
          assert (bucket->data.asPtr != NULL);
          e2 = (BtorExp *) bucket->data.asPtr;
          if (BTOR_IS_INVERTED_EXP (cur->e[2])) e2 = BTOR_INVERT_EXP (e2);
          if (BTOR_IS_WRITE_EXP (cur))
            cur_result = btor_write_exp (btor, e0, e1, e2);
          else
          {
            assert (cur->kind == BTOR_BCOND_EXP || cur->kind == BTOR_ACOND_EXP);
            cur_result = btor_cond_exp (btor, e0, e1, e2);
          }
          break;
      }
      btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr = cur_result;
      cur->mark                                                    = 2;
    }
  }
  btor_mark_exp (btor, root, 0);

  bucket = btor_find_in_ptr_hash_table (build_table, BTOR_REAL_ADDR_EXP (root));
  assert (bucket != NULL);
  assert (bucket->data.asPtr != NULL);
  result = btor_copy_exp (btor, (BtorExp *) bucket->data.asPtr);

  if (BTOR_IS_INVERTED_EXP (root)) result = BTOR_INVERT_EXP (result);

  /* cleanup */
  for (bucket = build_table->first; bucket != NULL; bucket = bucket->next)
  {
    assert (bucket->data.asPtr != NULL);
    btor_release_exp (btor, (BtorExp *) bucket->data.asPtr);
  }
  btor_delete_ptr_hash_table (build_table);

  BTOR_RELEASE_STACK (mm, stack);

  return result;
}

BtorExp *
btor_inc_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *one, *result;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_add_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

BtorExp *
btor_dec_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *one, *result;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_sub_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

int
btor_get_exp_len (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return BTOR_REAL_ADDR_EXP (exp)->len;
}

int
btor_is_array_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  return BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp));
}

int
btor_get_index_exp_len (Btor *btor, BtorExp *e_array)
{
  assert (btor != NULL);
  assert (e_array != NULL);
  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  assert (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)));
  assert (BTOR_IS_REGULAR_EXP (e_array));
  return e_array->index_len;
}

char *
btor_get_symbol_exp (Btor *btor, BtorExp *exp)
{
  /* do not pointer-chase! */
  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;
  return BTOR_REAL_ADDR_EXP (exp)->symbol;
}

#define BTOR_PUSH_EXP_IF_NOT_MARKED(e)         \
  do                                           \
  {                                            \
    BtorExp *child = BTOR_REAL_ADDR_EXP ((e)); \
    if (child->mark) break;                    \
    child->mark = 1;                           \
    BTOR_PUSH_STACK (mm, stack, child);        \
  } while (0)

static int
btor_cmp_id (const void *p, const void *q)
{
  BtorExp *a = *(BtorExp **) p;
  BtorExp *b = *(BtorExp **) q;
  return a->id - b->id;
}

static void
dump_exps (Btor *btor, FILE *file, BtorExp **roots, int nroots)
{
  BtorMemMgr *mm = btor->mm;
  int next, i, j, maxid, id;
  BtorExpPtrStack stack;
  BtorExp *e, *root;
  char idbuffer[20];
  const char *op;

  assert (btor != NULL);
  assert (file != NULL);
  assert (roots != NULL);
  assert (nroots > 0);

  BTOR_INIT_STACK (stack);

  for (i = 0; i < nroots; i++)
  {
    root = roots[i];
    assert (root != NULL);
    BTOR_PUSH_EXP_IF_NOT_MARKED (root);
  }

  next = 0;

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_EXP (e));
    assert (e->mark);

    if (e->kind == BTOR_PROXY_EXP)
      BTOR_PUSH_EXP_IF_NOT_MARKED (e->simplified);
    else
    {
      for (i = 0; i < e->arity; i++) BTOR_PUSH_EXP_IF_NOT_MARKED (e->e[i]);
    }
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;

  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof e, btor_cmp_id);

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_EXP (e));

    fprintf (file, "%d ", e->id);

    switch (e->kind)
    {
      case BTOR_ADD_EXP: op = "add"; goto PRINT;
      case BTOR_AND_EXP: op = "and"; goto PRINT;
      case BTOR_CONCAT_EXP: op = "concat"; goto PRINT;
      case BTOR_BCOND_EXP: op = "cond"; goto PRINT;
      case BTOR_BEQ_EXP:
      case BTOR_AEQ_EXP: op = "eq"; goto PRINT;
      case BTOR_MUL_EXP: op = "mul"; goto PRINT;
      case BTOR_PROXY_EXP: op = "proxy"; goto PRINT;
      case BTOR_READ_EXP: op = "read"; goto PRINT;
      case BTOR_SLL_EXP: op = "sll"; goto PRINT;
      case BTOR_SRL_EXP: op = "srl"; goto PRINT;
      case BTOR_UDIV_EXP: op = "udiv"; goto PRINT;
      case BTOR_ULT_EXP: op = "ult"; goto PRINT;
      case BTOR_UREM_EXP:
        op = "urem";
      PRINT:
        fputs (op, file);
        fprintf (file, " %d", e->len);

        if (e->kind == BTOR_PROXY_EXP)
          fprintf (file, " %d", BTOR_GET_ID_EXP (e->simplified));
        else
          for (j = 0; j < e->arity; j++)
            fprintf (file, " %d", BTOR_GET_ID_EXP (e->e[j]));
        break;

      case BTOR_SLICE_EXP:
        fprintf (file,
                 "slice %d %d %d %d",
                 e->len,
                 BTOR_GET_ID_EXP (e->e[0]),
                 e->upper,
                 e->lower);
        break;

      case BTOR_ARRAY_VAR_EXP:
        fprintf (file, "array %d %d", e->len, e->index_len);
        break;

      case BTOR_WRITE_EXP:
        fprintf (file,
                 "write %d %d %d %d %d",
                 e->len,
                 e->index_len,
                 BTOR_GET_ID_EXP (e->e[0]),
                 BTOR_GET_ID_EXP (e->e[1]),
                 BTOR_GET_ID_EXP (e->e[2]));
        break;

      case BTOR_ACOND_EXP:
        fprintf (file,
                 "acond %d %d %d %d %d",
                 e->len,
                 e->index_len,
                 BTOR_GET_ID_EXP (e->e[0]),
                 BTOR_GET_ID_EXP (e->e[1]),
                 BTOR_GET_ID_EXP (e->e[2]));
        break;

      case BTOR_BV_CONST_EXP:
        fprintf (file, "const %d %s", e->len, e->bits);
        break;

      default:
      case BTOR_BV_VAR_EXP:
        assert (e->kind == BTOR_BV_VAR_EXP);
        fprintf (file, "var %d", e->len);
        sprintf (idbuffer, "%d", e->id);
        assert (e->symbol);
        if (strcmp (e->symbol, idbuffer)) fprintf (file, " %s", e->symbol);
        break;
    }

    fputc ('\n', file);
  }

  BTOR_RELEASE_STACK (mm, stack);

  maxid = 0;
  for (i = 0; i < nroots; i++)
  {
    root = roots[i];
    e    = BTOR_REAL_ADDR_EXP (root);
    if (e->id > maxid) maxid = e->id;
  }

  for (i = 0; i < nroots; i++)
  {
    id = maxid + i;
    BTOR_ABORT_EXP (id == INT_MAX, "expression id overflow");

    root = roots[i];
    fprintf (file, "%d root %d %d\n", id + 1, e->len, BTOR_GET_ID_EXP (root));
  }
}

void
btor_dump_exps (Btor *btor, FILE *file, BtorExp **roots, int nroots)
{
#ifndef NDEBUG
  int i;
  assert (btor != NULL);
  assert (file != NULL);
  assert (roots != NULL);
  assert (nroots > 0);
  for (i = 0; i < nroots; i++) assert (roots[i] != NULL);
#endif

  dump_exps (btor, file, roots, nroots);
}

void
btor_dump_exp (Btor *btor, FILE *file, BtorExp *root)
{
  assert (btor != NULL);
  assert (file != NULL);
  assert (root != NULL);
  dump_exps (btor, file, &root, 1);
}

void
btor_dump_exps_after_global_rewriting (Btor *btor, FILE *file)
{
  BtorExp *temp, **new_roots;
  BtorPtrHashBucket *b;
  int new_nroots, i;
  assert (!btor->inc_enabled);
  assert (!btor->model_gen);
  assert (btor->rewrite_level > 1);

  run_rewrite_engine (btor, 1);

  if (btor->inconsistent)
  {
    temp = btor_false_exp (btor);
    btor_dump_exp (btor, file, temp);
    btor_release_exp (btor, temp);
  }
  else if (btor->unsynthesized_constraints->count == 0u)
  {
    temp = btor_true_exp (btor);
    btor_dump_exp (btor, file, temp);
    btor_release_exp (btor, temp);
  }
  else
  {
    new_nroots = (int) btor->unsynthesized_constraints->count;
    BTOR_NEWN (btor->mm, new_roots, new_nroots);
    i = 0;
    for (b = btor->unsynthesized_constraints->first; b != NULL; b = b->next)
      new_roots[i++] = (BtorExp *) b->key;
    dump_exps (btor, file, new_roots, new_nroots);
    BTOR_DELETEN (btor->mm, new_roots, new_nroots);
  }
}

void
btor_vis_exp (Btor *btor, BtorExp *exp)
{
  int save_res_to_avoid_warning;
  char cmd[100], *path;
  static int idx = 0; /* TODO: make this non static */
  FILE *file;
  sprintf (cmd, "btorvis ");
  path = cmd + strlen (cmd);
  sprintf (path, "/tmp/btorvisexp.%d.btor", idx++);
  file = fopen (path, "w");
  btor_dump_exp (btor, file, exp);
  fclose (file);
  strcat (cmd, "&");
  save_res_to_avoid_warning = system (cmd);
}

static void
btor_dump_smt_id (BtorExp *e, FILE *file)
{
  const char *type, *sym;
  BtorExp *u;

  u = BTOR_REAL_ADDR_EXP (e);

  if (u != e) fputs ("(bvnot ", file);

  if (BTOR_IS_BV_VAR_EXP (u))
  {
    sym = u->symbol;
    if (!isdigit (sym[0]))
    {
      fputs (sym, file);
      goto CLOSE;
    }

    type = "v";
  }
  else if (BTOR_IS_ARRAY_VAR_EXP (u))
    type = "a";
  else
    type = "?e";

  fprintf (file, "%s%d", type, u->id);

CLOSE:
  if (u != e) fputc (')', file);
}

void
btor_dump_smt (Btor *btor, FILE *file, BtorExp *root)
{
  int next, i, j, arrays, lets, pad;
  BtorMemMgr *mm = btor->mm;
  BtorExpPtrStack stack;
  const char *op;
  char *tmp;
  BtorExp *e;

  assert (btor != NULL);
  assert (file != NULL);
  assert (root != NULL);

  BTOR_INIT_STACK (stack);
  BTOR_PUSH_EXP_IF_NOT_MARKED (root);

  arrays = 0;
  next   = 0;

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_EXP (e));
    assert (e->mark);

    if (BTOR_IS_BV_CONST_EXP (e)) continue;

    if (BTOR_IS_BV_VAR_EXP (e)) continue;

    if (BTOR_IS_ARRAY_VAR_EXP (e))
    {
      arrays = 1;
      continue;
    }

    for (i = 0; i < e->arity; i++) BTOR_PUSH_EXP_IF_NOT_MARKED (e->e[i]);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;

  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof e, btor_cmp_id);

  fputs ("(benchmark ", file);
  if (BTOR_IS_INVERTED_EXP (root)) fputs ("not", file);
  fprintf (file, "root%d\n", BTOR_REAL_ADDR_EXP (root)->id);

  if (arrays)
    fputs (":logic QF_AUFBV\n", file);
  else
    fputs (":logic QF_BV\n", file);

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_EXP (e));

    if (!BTOR_IS_BV_VAR_EXP (e) && !BTOR_IS_ARRAY_VAR_EXP (e)) continue;

    fputs (":extrafuns ((", file);
    btor_dump_smt_id (e, file);

    if (BTOR_IS_BV_VAR_EXP (e))
      fprintf (file, " BitVec[%d]))\n", e->len);
    else
      fprintf (file, " Array[%d:%d]))\n", e->index_len, e->len);
  }

  fputs (":formula\n", file);

  lets = 0;

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_EXP (e));

    if (BTOR_IS_BV_VAR_EXP (e) || BTOR_IS_ARRAY_VAR_EXP (e)) continue;

    lets++;

    fputs ("(let (", file);
    btor_dump_smt_id (e, file);
    fputc (' ', file);

    if (e->kind == BTOR_BV_CONST_EXP)
    {
      tmp = btor_const_to_decimal (mm, e->bits);
      fprintf (file, "bv%s[%d]", tmp, e->len);
      btor_freestr (mm, tmp);
    }
    else if (e->kind == BTOR_SLICE_EXP)
    {
      fprintf (file, "(extract[%d:%d] ", e->upper, e->lower);
      btor_dump_smt_id (e->e[0], file);
      fputc (')', file);
    }
    else if (e->kind == BTOR_SLL_EXP || e->kind == BTOR_SRL_EXP)
    {
      fputc ('(', file);

      if (e->kind == BTOR_SRL_EXP)
        fputs ("bvlshr", file);
      else
        fputs ("bvshl", file);

      fputc (' ', file);
      btor_dump_smt_id (e->e[0], file);
      fputc (' ', file);

      assert (e->len > 1);
      pad = e->len - BTOR_REAL_ADDR_EXP (e->e[1])->len;
      fprintf (file, " (zero_extend[%d] ", pad);

      btor_dump_smt_id (e->e[1], file);

      fputs ("))", file);
    }
    else if (BTOR_IS_ARRAY_OR_BV_COND_EXP (e))
    {
      fputs ("(ite (= bv1[1] ", file);
      btor_dump_smt_id (e->e[0], file);
      fputs (") ", file);
      btor_dump_smt_id (e->e[1], file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[2], file);
      fputc (')', file);
    }
    else if (BTOR_IS_ARRAY_OR_BV_EQ_EXP (e) || e->kind == BTOR_ULT_EXP)
    {
      fputs ("(ite (", file);
      if (e->kind == BTOR_ULT_EXP)
        fputs ("bvult", file);
      else
        fputc ('=', file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[0], file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[1], file);
      fputs (") bv1[1] bv0[1])", file);
    }
    else
    {
      fputc ('(', file);

      switch (e->kind)
      {
        case BTOR_AND_EXP: op = "bvand"; break;
        case BTOR_ADD_EXP: op = "bvadd"; break;
        case BTOR_MUL_EXP: op = "bvmul"; break;
        case BTOR_UDIV_EXP: op = "bvudiv"; break;
        case BTOR_UREM_EXP: op = "bvurem"; break;
        case BTOR_CONCAT_EXP: op = "concat"; break;
        case BTOR_READ_EXP: op = "select"; break;

        default:
        case BTOR_WRITE_EXP:
          assert (e->kind == BTOR_WRITE_EXP);
          op = "store";
          break;
      }

      fputs (op, file);

      for (j = 0; j < e->arity; j++)
      {
        fputc (' ', file);
        btor_dump_smt_id (e->e[j], file);
      }

      fputc (')', file);
    }

    fputs (")\n", file);
  }

  fputs ("(not (= ", file);
  btor_dump_smt_id (root, file);
  fprintf (file, " bv0[%d]))\n", BTOR_REAL_ADDR_EXP (root)->len);

  for (i = 0; i < lets + 1; i++) fputc (')', file);

  fputc ('\n', file);

  BTOR_RELEASE_STACK (mm, stack);
}

Btor *
btor_new_btor (void)
{
  BtorMemMgr *mm;
  Btor *btor;
  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, btor);
  btor->mm = mm;
  BTOR_INIT_EXP_UNIQUE_TABLE (mm, btor->table);
  btor->avmgr   = btor_new_aigvec_mgr (mm);
  btor->bv_vars = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  btor->array_vars =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->id                = 1;
  btor->bv_lambda_id      = 1;
  btor->array_lambda_id   = 1;
  btor->valid_assignments = 1;
  btor->rewrite_level     = 3;
  btor->vread_index_id    = 1;

  btor->exp_pair_cnf_diff_id_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  btor->exp_pair_cnf_eq_id_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  btor->exp_pair_ass_unequal_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  btor->varsubst_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->embedded_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->unsynthesized_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->synthesized_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->assumptions =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_INIT_STACK (btor->arrays_with_model);
  BTOR_INIT_STACK (btor->replay_constraints);
  return btor;
}

void
btor_set_rewrite_level_btor (Btor *btor, int rewrite_level)
{
  assert (btor != NULL);
  assert (btor->rewrite_level >= 0);
  assert (btor->rewrite_level <= 3);
  assert (btor->id == 1);
  btor->rewrite_level = rewrite_level;
}

void
btor_enable_model_gen (Btor *btor)
{
  assert (btor != NULL);
  assert (btor->id == 1);
  if (!btor->model_gen)
  {
    btor->model_gen = 1;
    btor->var_rhs =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
  }
}

void
btor_enable_inc_usage (Btor *btor)
{
  assert (btor != NULL);
  assert (btor->btor_sat_btor_called == 0);
  btor->inc_enabled = 1;
}

void
btor_enable_under_approx (Btor *btor)
{
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (btor->id == 1);
  assert (!btor->ua.enabled);

  mm = btor->mm;

  btor->ua.enabled           = 1;
  btor->ua.initial_eff_width = 1;
  btor->ua.global_eff_width  = 1;
  btor->ua.vars_reads =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->ua.writes_aconds =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

void
btor_set_under_approx_initial_effective_width (Btor *btor,
                                               int initial_eff_width)
{
  assert (btor != NULL);
  assert (btor->id == 1);
  assert (initial_eff_width > 0);
  btor->ua.initial_eff_width = initial_eff_width;
  btor->ua.global_eff_width  = initial_eff_width;
}

void
btor_set_under_approx_mode (Btor *btor, BtorUAMode mode)
{
  assert (btor != NULL);
  assert (btor->id == 1);
  btor->ua.mode = mode;
}

void
btor_set_under_approx_ref (Btor *btor, BtorUARef ref)
{
  assert (btor != NULL);
  assert (btor->id == 1);
  btor->ua.ref = ref;
}

void
btor_set_under_approx_enc (Btor *btor, BtorUAEnc enc)
{
  assert (btor != NULL);
  assert (btor->id == 1);
  btor->ua.enc = enc;
}

void
btor_set_replay_btor (Btor *btor, int replay)
{
  assert (btor != NULL);
  assert (btor->varsubst_constraints->count + btor->embedded_constraints->count
              + btor->unsynthesized_constraints->count
              + btor->synthesized_constraints->count + btor->assumptions->count
          == 0u);
  btor->replay = replay;
}

void
btor_set_verbosity_btor (Btor *btor, int verbosity)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;

  assert (btor != NULL);
  assert (btor->verbosity >= -1);
  assert (btor->verbosity <= 3);
  assert (btor->id == 1);
  btor->verbosity = verbosity;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);
  btor_set_verbosity_aigvec_mgr (avmgr, verbosity);
  btor_set_verbosity_aig_mgr (amgr, verbosity);
  btor_set_verbosity_sat_mgr (smgr, verbosity);
}

void
btor_delete_btor (Btor *btor)
{
  BtorMemMgr *mm;
  BtorPtrHashBucket *b;
  int i;

  assert (btor != NULL);

  mm = btor->mm;

  for (b = btor->exp_pair_cnf_diff_id_table->first; b != NULL; b = b->next)
    delete_exp_pair (btor, (BtorExpPair *) b->key);
  btor_delete_ptr_hash_table (btor->exp_pair_cnf_diff_id_table);

  for (b = btor->exp_pair_cnf_eq_id_table->first; b != NULL; b = b->next)
    delete_exp_pair (btor, (BtorExpPair *) b->key);
  btor_delete_ptr_hash_table (btor->exp_pair_cnf_eq_id_table);

  for (b = btor->exp_pair_ass_unequal_table->first; b != NULL; b = b->next)
    delete_exp_pair (btor, (BtorExpPair *) b->key);
  btor_delete_ptr_hash_table (btor->exp_pair_ass_unequal_table);

  /* delete constraints and assumptions */

  for (b = btor->varsubst_constraints->first; b != NULL; b = b->next)
  {
    btor_release_exp (btor, (BtorExp *) b->key);
    btor_release_exp (btor, (BtorExp *) b->data.asPtr);
  }
  btor_delete_ptr_hash_table (btor->varsubst_constraints);

  for (b = btor->embedded_constraints->first; b != NULL; b = b->next)
    btor_release_exp (btor, (BtorExp *) b->key);
  btor_delete_ptr_hash_table (btor->embedded_constraints);

  for (b = btor->unsynthesized_constraints->first; b != NULL; b = b->next)
    btor_release_exp (btor, (BtorExp *) b->key);
  btor_delete_ptr_hash_table (btor->unsynthesized_constraints);

  for (b = btor->synthesized_constraints->first; b != NULL; b = b->next)
    btor_release_exp (btor, (BtorExp *) b->key);
  btor_delete_ptr_hash_table (btor->synthesized_constraints);

  for (b = btor->assumptions->first; b != NULL; b = b->next)
    btor_release_exp (btor, (BtorExp *) b->key);
  btor_delete_ptr_hash_table (btor->assumptions);

  if (btor->model_gen)
  {
    for (b = btor->var_rhs->first; b != NULL; b = b->next)
      btor_release_exp (btor, (BtorExp *) b->key);
    btor_delete_ptr_hash_table (btor->var_rhs);
  }

  for (i = 0; i < BTOR_COUNT_STACK (btor->replay_constraints); i++)
    btor_release_exp (btor, btor->replay_constraints.start[i]);
  BTOR_RELEASE_STACK (mm, btor->replay_constraints);

  BTOR_RELEASE_STACK (mm, btor->arrays_with_model);

  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKEXP")
          || btor->table.num_elements == 0);
  BTOR_RELEASE_EXP_UNIQUE_TABLE (mm, btor->table);
  btor_delete_ptr_hash_table (btor->bv_vars);
  btor_delete_ptr_hash_table (btor->array_vars);

  if (btor->ua.enabled)
  {
    assert (btor->ua.vars_reads->count == 0u);
    btor_delete_ptr_hash_table (btor->ua.vars_reads);
    assert (btor->ua.writes_aconds->count == 0u);
    btor_delete_ptr_hash_table (btor->ua.writes_aconds);
  }

  btor_delete_aigvec_mgr (btor->avmgr);
  assert (btor->rec_rw_calls == 0);
  BTOR_DELETE (mm, btor);
  btor_delete_mem_mgr (mm);
}

static int
constraints_stats_changes (Btor *btor)
{
  int res;

  if (btor->stats.old.constraints.varsubst
      && !btor->varsubst_constraints->count)
    return INT_MAX;

  if (btor->stats.old.constraints.embedded
      && !btor->embedded_constraints->count)
    return INT_MAX;

  if (btor->stats.old.constraints.unsynthesized
      && !btor->unsynthesized_constraints->count)
    return INT_MAX;

  res = abs (btor->stats.old.constraints.varsubst
             - btor->varsubst_constraints->count);

  res += abs (btor->stats.old.constraints.embedded
              - btor->embedded_constraints->count);

  res += abs (btor->stats.old.constraints.unsynthesized
              - btor->unsynthesized_constraints->count);

  res += abs (btor->stats.old.constraints.synthesized
              - btor->synthesized_constraints->count);

  return res;
}

static void
report_constraint_stats (Btor *btor, int force)
{
  int changes;

  if (!force)
  {
    if (btor->verbosity <= 0) return;

    changes = constraints_stats_changes (btor);

    if (btor->verbosity == 1 && changes < 10000) return;

    if (btor->verbosity == 2 && changes < 1000) return;

    if (btor->verbosity == 3 && changes < 100) return;
  }

  btor_msg_exp (btor,
                "%d/%d/%d/%d constraints %d/%d/%d/%d %.1f MB",
                btor->stats.constraints.varsubst,
                btor->stats.constraints.embedded,
                btor->stats.constraints.unsynthesized,
                btor->stats.constraints.synthesized,
                btor->varsubst_constraints->count,
                btor->embedded_constraints->count,
                btor->unsynthesized_constraints->count,
                btor->synthesized_constraints->count,
                btor->mm->allocated / (double) (1 << 20));

  btor->stats.old.constraints.varsubst = btor->varsubst_constraints->count;
  btor->stats.old.constraints.embedded = btor->embedded_constraints->count;
  btor->stats.old.constraints.unsynthesized =
      btor->unsynthesized_constraints->count;
  btor->stats.old.constraints.synthesized =
      btor->synthesized_constraints->count;
}

static void
update_max_basic_ua_stats (Btor *btor, int *max, int val)
{
  assert (btor != NULL);
  assert (max != NULL);
  assert (*max >= 0);
  assert (val > 0);
  (void) btor;

  if (val > *max) *max = val;
}

static void
update_min_basic_ua_stats (Btor *btor, int *min, int val)
{
  assert (btor != NULL);
  assert (min != NULL);
  assert (*min >= 0);
  assert (val > 0);
  (void) btor;

  if (val < *min || *min == 0) *min = val;
}

static void
compute_basic_ua_stats (Btor *btor,
                        unsigned int *num_vars,
                        unsigned int *num_reads,
                        unsigned long long int *sum_var_refs,
                        unsigned long long int *sum_read_refs,
                        unsigned long long int *sum_refs,
                        double *avg_var_refs,
                        double *avg_read_refs,
                        double *avg_refs,
                        int *max_var_width,
                        int *max_read_width,
                        int *max_width,
                        int *min_var_width,
                        int *min_read_width,
                        int *min_width,
                        int *max_var_eff_width,
                        int *max_read_eff_width,
                        int *max_eff_width,
                        int *min_var_eff_width,
                        int *min_read_eff_width,
                        int *min_eff_width,
                        double *avg_var_width,
                        double *avg_read_width,
                        double *avg_var_eff_width,
                        double *avg_read_eff_width,
                        double *avg_width,
                        double *avg_eff_width)
{
  BtorPtrHashBucket *b;
  BtorExp *cur;
  BtorUAData *data = NULL;
  BtorUAMode ua_mode;
  unsigned long long int sum_var_width;
  unsigned long long int sum_read_width;
  unsigned long long int sum_var_eff_width;
  unsigned long long int sum_read_eff_width;

  assert (btor != NULL);
  assert (num_vars != NULL);
  assert (num_reads != NULL);
  assert (sum_var_refs != NULL);
  assert (sum_read_refs != NULL);
  assert (sum_refs != NULL);
  assert (avg_var_refs != NULL);
  assert (avg_read_refs != NULL);
  assert (avg_refs != NULL);
  assert (max_var_width != NULL);
  assert (max_read_width != NULL);
  assert (max_width != NULL);
  assert (min_var_width != NULL);
  assert (min_read_width != NULL);
  assert (min_width != NULL);

  assert (max_var_eff_width != NULL);
  assert (max_read_eff_width != NULL);
  assert (max_eff_width != NULL);
  assert (min_var_eff_width != NULL);
  assert (min_read_eff_width != NULL);
  assert (min_eff_width != NULL);

  assert (avg_var_width != NULL);
  assert (avg_read_width != NULL);
  assert (avg_var_eff_width != NULL);
  assert (avg_read_eff_width != NULL);
  assert (avg_width != NULL);
  assert (avg_eff_width != NULL);

  assert (btor->ua.enabled);

  ua_mode = btor->ua.mode;

  sum_var_width      = 0llu;
  sum_read_width     = 0llu;
  sum_var_eff_width  = 0llu;
  sum_read_eff_width = 0llu;

  *num_vars       = 0u;
  *num_reads      = 0u;
  *sum_var_refs   = 0llu;
  *sum_read_refs  = 0llu;
  *sum_refs       = 0llu;
  *max_var_width  = 0;
  *max_read_width = 0;
  *max_width      = 0;
  *min_var_width  = 0;
  *min_read_width = 0;
  *min_width      = 0;

  *max_var_eff_width  = 0;
  *max_read_eff_width = 0;
  *max_eff_width      = 0;
  *min_var_eff_width  = 0;
  *min_read_eff_width = 0;
  *min_eff_width      = 0;

  *avg_var_refs       = 0.0;
  *avg_read_refs      = 0.0;
  *avg_refs           = 0.0;
  *avg_var_width      = 0.0;
  *avg_read_width     = 0.0;
  *avg_var_eff_width  = 0.0;
  *avg_read_eff_width = 0.0;
  *avg_width          = 0.0;
  *avg_eff_width      = 0.0;

  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

    if (!cur->reachable && !cur->vread && !cur->vread_index) continue;

    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      data = (BtorUAData *) b->data.asPtr;
      assert (data != NULL);
    }

    update_min_basic_ua_stats (btor, min_width, cur->len);
    update_max_basic_ua_stats (btor, max_width, cur->len);
    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      update_min_basic_ua_stats (btor, min_eff_width, data->eff_width);
      update_max_basic_ua_stats (btor, max_eff_width, data->eff_width);

      *sum_refs += data->refinements;
    }

    if (BTOR_IS_BV_VAR_EXP (cur))
    {
      sum_var_width += cur->len;

      update_min_basic_ua_stats (btor, min_var_width, cur->len);
      update_max_basic_ua_stats (btor, max_var_width, cur->len);
      if (ua_mode != BTOR_UA_GLOBAL_MODE)
      {
        update_min_basic_ua_stats (btor, min_var_eff_width, data->eff_width);
        update_max_basic_ua_stats (btor, max_var_eff_width, data->eff_width);

        sum_var_eff_width += data->eff_width;
        *sum_var_refs += data->refinements;
      }
      *num_vars += 1;
    }
    else
    {
      sum_read_width += cur->len;

      update_min_basic_ua_stats (btor, min_read_width, cur->len);
      update_max_basic_ua_stats (btor, max_read_width, cur->len);

      if (ua_mode != BTOR_UA_GLOBAL_MODE)
      {
        update_min_basic_ua_stats (btor, min_read_eff_width, data->eff_width);
        update_max_basic_ua_stats (btor, max_read_eff_width, data->eff_width);

        sum_read_eff_width += data->eff_width;
        *sum_read_refs += data->refinements;
      }
      *num_reads += 1;
    }
  }

  if (*num_vars)
  {
    *avg_var_width = (double) sum_var_width / (double) *num_vars;
    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      *avg_var_refs      = (double) *sum_var_refs / (double) *num_vars;
      *avg_var_eff_width = (double) sum_var_eff_width / (double) *num_vars;
    }
  }

  if (*num_reads)
  {
    *avg_read_width = (double) sum_read_width / (double) *num_reads;
    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      *avg_read_refs      = (double) *sum_read_refs / (double) *num_reads;
      *avg_read_eff_width = (double) sum_read_eff_width / (double) *num_reads;
    }
  }

  if (*num_vars || *num_reads)
  {
    *avg_width = (double) (sum_var_width + sum_read_width)
                 / (double) (*num_vars + *num_reads);
    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      *avg_eff_width = (double) (sum_var_eff_width + sum_read_eff_width)
                       / (double) (*num_vars + *num_reads);
      *avg_refs = (double) *sum_refs / (double) (*num_vars + *num_reads);
    }
  }
}

/* we do not count proxies */
static int
number_of_ops (Btor *btor)
{
  int i, result;
  assert (btor != NULL);

  result = 0;
  for (i = 1; i < BTOR_NUM_OPS_EXP - 1; i++) result += btor->ops[i];

  return result;
}

void
btor_print_stats_btor (Btor *btor)
{
  double avg_var_refs, avg_read_refs, avg_var_width, avg_read_width, avg_refs;
  double avg_var_eff_width, avg_read_eff_width, avg_width, avg_eff_width;
  unsigned int num_vars, num_reads;
  unsigned long long int sum_var_refs, sum_read_refs, sum_refs;
  int max_var_width, max_read_width, min_var_width, min_read_width;
  int max_var_eff_width, max_read_eff_width, min_var_eff_width;
  int min_read_eff_width, verbosity, min_width;
  int max_width, min_eff_width, max_eff_width, i;
  int num_final_ops;
  BtorUAMode ua_mode;

  assert (btor != NULL);
  // assert (btor->verbosity > 0);

  ua_mode   = btor->ua.mode;
  verbosity = btor->verbosity;

  report_constraint_stats (btor, 1);
  btor_msg_exp (
      btor, "variable substitutions: %d", btor->stats.var_substitutions);
  btor_msg_exp (
      btor, "array substitutions: %d", btor->stats.array_substitutions);
  btor_msg_exp (btor,
                "embedded constraint substitutions: %d",
                btor->stats.ec_substitutions);
  btor_msg_exp (btor, "assumptions: %u", btor->assumptions->count);
  if (btor->ops[BTOR_AEQ_EXP])
    btor_msg_exp (btor, "virtual reads: %d", btor->stats.vreads);

  if (verbosity > 2)
  {
    btor_msg_exp (btor, "max rec. RW: %d", btor->stats.max_rec_rw_calls);
    btor_msg_exp (btor, "domain abstractions: %d", btor->stats.domain_abst);
#if BTOR_ENABLE_PROBING_OPT
    btor_msg_exp (btor, "probed equalites: %d", btor->stats.probed_equalities);
#endif
    btor_msg_exp (
        btor, "unconstrained bv propagations: %d", btor->stats.bv_uc_props);
    btor_msg_exp (btor,
                  "unconstrained array propagations: %d",
                  btor->stats.array_uc_props);
    btor_msg_exp (btor,
                  "number of expressions ever created: %lld",
                  btor->stats.expressions);
    num_final_ops = number_of_ops (btor);
    assert (num_final_ops >= 0);
    btor_msg_exp (btor, "number of final expressions: %d", num_final_ops);
    if (num_final_ops > 0)
      for (i = 1; i < BTOR_NUM_OPS_EXP - 1; i++)
        if (btor->ops[i])
          btor_msg_exp (btor, " %s:%d", g_op2string[i], btor->ops[i]);
  }

  if (btor->ua.enabled)
  {
    btor_msg_exp (btor, "");
    btor_msg_exp (btor, "under-approximation (UA) statistics:");
    btor_msg_exp (btor, " UA refinements: %d", btor->stats.ua_refinements);
    if (ua_mode == BTOR_UA_GLOBAL_MODE)
      btor_msg_exp (btor,
                    " global effective bit-width (final): %d",
                    btor->ua.global_eff_width);

    if (verbosity < 2) goto BTOR_CONTINUE_BASIC_STATS_OUTPUT;

    compute_basic_ua_stats (btor,
                            &num_vars,
                            &num_reads,
                            &sum_var_refs,
                            &sum_read_refs,
                            &sum_refs,
                            &avg_var_refs,
                            &avg_read_refs,
                            &avg_refs,
                            &max_var_width,
                            &max_read_width,
                            &max_width,
                            &min_var_width,
                            &min_read_width,
                            &min_width,
                            &max_var_eff_width,
                            &max_read_eff_width,
                            &max_eff_width,
                            &min_var_eff_width,
                            &min_read_eff_width,
                            &min_eff_width,
                            &avg_var_width,
                            &avg_read_width,
                            &avg_var_eff_width,
                            &avg_read_eff_width,
                            &avg_width,
                            &avg_eff_width);

    btor_msg_exp (btor, "");
    btor_msg_exp (btor, " reachable vars (after rewriting): %d", num_vars);
    if (num_vars > 0)
    {
      btor_msg_exp (btor,
                    "  vars orig. width: %d %d %.1f",
                    min_var_width,
                    max_var_width,
                    avg_var_width);
      if (ua_mode != BTOR_UA_GLOBAL_MODE)
      {
        btor_msg_exp (btor,
                      "  vars eff. width: %d %d %.1f",
                      min_var_eff_width,
                      max_var_eff_width,
                      avg_var_eff_width);
        btor_msg_exp (
            btor, "  total number of refinements: %llu", sum_var_refs);
        btor_msg_exp (btor, "  avg refinements: %.1f", avg_var_refs);
      }
    }

    btor_msg_exp (btor, "");
    btor_msg_exp (btor, " reachable reads (after rewriting): %d", num_reads);
    if (num_reads > 0)
    {
      btor_msg_exp (btor,
                    "  reads orig. width: %d %d %.1f",
                    min_read_width,
                    max_read_width,
                    avg_read_width);
      if (ua_mode != BTOR_UA_GLOBAL_MODE)
      {
        btor_msg_exp (btor,
                      "  reads eff. width: %d %d %.1f",
                      min_read_eff_width,
                      max_read_eff_width,
                      avg_read_eff_width);
        btor_msg_exp (
            btor, "  total number of refinements: %llu", sum_read_refs);
        btor_msg_exp (btor, "  avg refinements: %.1f", avg_read_refs);
      }
    }

    if (num_vars != 0 && num_reads != 0)
    {
      btor_msg_exp (btor, "");
      btor_msg_exp (btor,
                    " reachable vars + reads (after rewriting): %d",
                    num_vars + num_reads);
      btor_msg_exp (btor,
                    "  vars + reads orig. width: %d %d %.1f",
                    min_width,
                    max_width,
                    avg_width);
      if (ua_mode != BTOR_UA_GLOBAL_MODE)
      {
        btor_msg_exp (btor,
                      "  vars + reads eff. width: %d %d %.1f",
                      min_eff_width,
                      max_eff_width,
                      avg_eff_width);
        btor_msg_exp (btor, "  total number of refinements: %llu", sum_refs);
        btor_msg_exp (btor, "  avg refinements: %.1f", avg_refs);
      }
    }
  }

BTOR_CONTINUE_BASIC_STATS_OUTPUT:

  btor_msg_exp (btor, "");
  btor_msg_exp (btor, "lemmas on demand statistics:");
  btor_msg_exp (btor, " LOD refinements: %d", btor->stats.lod_refinements);
  if (btor->stats.lod_refinements)
  {
    btor_msg_exp (btor,
                  " array axiom 1 conflicts: %d",
                  btor->stats.array_axiom_1_conflicts);
    btor_msg_exp (btor,
                  " array axiom 2 conflicts: %d",
                  btor->stats.array_axiom_2_conflicts);
    btor_msg_exp (btor,
                  " average lemma size: %.1f",
                  BTOR_AVERAGE_UTIL (btor->stats.lemmas_size_sum,
                                     btor->stats.lod_refinements));
    btor_msg_exp (btor,
                  " average linking clause size: %.1f",
                  BTOR_AVERAGE_UTIL (btor->stats.lclause_size_sum,
                                     btor->stats.lod_refinements));
  }
  btor_msg_exp (btor, "");

  btor_msg_exp (
      btor, "linear constraint equations: %d", btor->stats.linear_equations);
  btor_msg_exp (btor, "add normalizations: %d", btor->stats.adds_normalized);
  btor_msg_exp (btor, "mul normalizations: %d", btor->stats.muls_normalized);
  btor_msg_exp (btor,
                "read over write propagations during construction: %d",
                btor->stats.read_props_construct);
  btor_msg_exp (btor,
                "synthesis assignment inconsistencies: %d",
                btor->stats.synthesis_assignment_inconsistencies);
}

BtorMemMgr *
btor_get_mem_mgr_btor (const Btor *btor)
{
  assert (btor != NULL);
  return btor->mm;
}

BtorAIGVecMgr *
btor_get_aigvec_mgr_btor (const Btor *btor)
{
  assert (btor != NULL);
  return btor->avmgr;
}

static BtorExp *
vread_index_exp (Btor *btor, int len)
{
  char *symbol;
  size_t bytes;
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  BTOR_ABORT_EXP (btor->id == INT_MAX, "vread index id overflow");
  bytes = 6 + btor_num_digits_util (btor->vread_index_id) + 1;
  bytes *= sizeof (char);
  symbol = (char *) btor_malloc (btor->mm, bytes);
  sprintf (symbol, "vindex%d", btor->vread_index_id);
  btor->vread_index_id++;
  result = btor_var_exp (btor, len, symbol);
  btor_free (btor->mm, symbol, bytes);
  return result;
}

static void
synthesize_array_equality (Btor *btor, BtorExp *aeq)
{
  BtorExp *index, *read1, *read2;
  BtorAIGVecMgr *avmgr;
  assert (btor != NULL);
  assert (aeq != NULL);
  assert (BTOR_IS_REGULAR_EXP (aeq));
  assert (BTOR_IS_ARRAY_EQ_EXP (aeq));
  assert (!BTOR_IS_SYNTH_EXP (aeq));
  avmgr   = btor->avmgr;
  aeq->av = btor_var_aigvec (avmgr, 1);
  /* generate virtual reads */
  index              = vread_index_exp (btor, aeq->e[0]->index_len);
  index->vread_index = 1;

  /* we do not want read optimizations for the virtual
   * reads (e.g. rewriting of reads on array conditionals),
   * so we call 'btor_read_exp_node' directly
   */
  read1 = btor_read_exp_node (btor, aeq->e[0], index);
  read2 = btor_read_exp_node (btor, aeq->e[1], index);

  /* mark them as virtual */
  read1->vread = 1;
  read2->vread = 1;

  aeq->vreads = new_exp_pair (btor, read1, read2);

  read1->av = btor_var_aigvec (avmgr, read1->len);
  btor->stats.vreads++;
  if (read1 != read2)
  {
    read2->av = btor_var_aigvec (avmgr, read2->len);
    btor->stats.vreads++;
  }

  encode_array_inequality_virtual_reads (btor, aeq);

  btor_release_exp (btor, index);
  btor_release_exp (btor, read1);
  btor_release_exp (btor, read2);
}

#if 0
static void
set_flags_and_synth_aeq (Btor * btor, BtorExp * exp)
{
  BtorExpPtrStack stack;
  BtorExp *cur;
  BtorMemMgr *mm;
  assert (btor != NULL);
  assert (exp != NULL);
  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, exp);
  do
    {
      cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
      if (!cur->reachable)
        {
          cur->reachable = 1;
          switch (cur->arity)
            {
            case 0:
              break;
            case 1:
              BTOR_PUSH_STACK (mm, stack, cur->e[0]);
              break;
            case 2:
              if (BTOR_IS_ARRAY_EQ_EXP (cur))
		synthesize_array_equality (btor, cur);
              BTOR_PUSH_STACK (mm, stack, cur->e[1]);
              BTOR_PUSH_STACK (mm, stack, cur->e[0]);
              break;
            default:
              assert (cur->arity = 3);
              BTOR_PUSH_STACK (mm, stack, cur->e[2]);
              BTOR_PUSH_STACK (mm, stack, cur->e[1]);
              BTOR_PUSH_STACK (mm, stack, cur->e[0]);
              break;
            }
        }
    }
  while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
}
#endif

#ifndef BTOR_NO_3VL

static void
propagate_3vl_to_aigvec (Btor *btor, BtorExp *exp)
{
  BtorAIGVec *av;
  BtorAIGMgr *amgr;
  char *bits;
  int i, len;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  assert (exp->bits != NULL);
  assert (exp->av != NULL);
  assert (btor->rewrite_level > 1);

  av   = exp->av;
  len  = av->len;
  bits = exp->bits;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  for (i = 0; i < len; i++)
  {
    assert (!(av->aigs[i] == BTOR_AIG_TRUE && bits[i] == '0'));
    assert (!(av->aigs[i] == BTOR_AIG_FALSE && bits[i] == '1'));
    assert (bits[i] == '0' || bits[i] == '1' || bits[i] == 'x');

    if (!BTOR_IS_CONST_AIG (av->aigs[i]) && bits[i] != 'x')
    {
      btor_release_aig (amgr, av->aigs[i]);
      if (bits[i] == '0')
        av->aigs[i] = BTOR_AIG_FALSE;
      else
        av->aigs[i] = BTOR_AIG_TRUE;
    }
  }
}

#endif

static void
synthesize_exp (Btor *btor, BtorExp *exp, BtorPtrHashTable *backannoation)
{
  BtorExpPtrStack exp_stack;
  BtorExp *cur;
  BtorAIGVec *av0, *av1, *av2;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashBucket *b;
  char *indexed_name;
  const char *name;
  unsigned int count;
  int same_children_mem, i, len;
  int invert_av0 = 0;
  int invert_av1 = 0;
  int invert_av2 = 0;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (!BTOR_IS_WRITE_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (!BTOR_IS_ARRAY_COND_EXP (BTOR_REAL_ADDR_EXP (exp)));

  mm    = btor->mm;
  avmgr = btor->avmgr;
  count = 0;

  BTOR_INIT_STACK (exp_stack);
  cur = BTOR_REAL_ADDR_EXP (exp);
  goto SYNTHESIZE_EXP_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (exp_stack));
  SYNTHESIZE_EXP_ENTER_WITHOUT_POP:
    assert (cur->synth_mark >= 0);
    assert (cur->synth_mark <= 2);
    if (!BTOR_IS_SYNTH_EXP (cur) && cur->synth_mark < 2)
    {
      count++;

      if (cur->synth_mark == 0)
      {
        cur->reachable = 1;
        if (BTOR_IS_BV_CONST_EXP (cur))
          cur->av = btor_const_aigvec (avmgr, cur->bits);
        else if (BTOR_IS_BV_VAR_EXP (cur))
        {
          cur->av = btor_var_aigvec (avmgr, cur->len);
          if (backannoation)
          {
            name         = btor_get_symbol_exp (btor, cur);
            len          = (int) strlen (name) + 40;
            indexed_name = btor_malloc (mm, len);
            for (i = 0; i < cur->av->len; i++)
            {
              b = btor_insert_in_ptr_hash_table (backannoation,
                                                 cur->av->aigs[i]);
              assert (b->key == cur->av->aigs[i]);
              sprintf (indexed_name, "%s[%d]", name, i);
              b->data.asStr = btor_strdup (mm, indexed_name);
            }
            btor_free (mm, indexed_name, len);
          }
        }
        else if (BTOR_IS_ARRAY_VAR_EXP (cur))
        {
          /* nothing to synthesize for array base case */
        }
        else if (BTOR_IS_WRITE_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur)
                 || BTOR_IS_ARRAY_COND_EXP (cur))
        {
          goto REGULAR_CASE;
        }
        else
        {
          /* writes cannot be reached directly
           * we stop the synthesis as soon
           * we reach reads or array equalities.
           * if we synthesize writes later,
           * we only synthesize its index
           * and value, but not the write itself
           * if there are no reads or array
           * equalities on a write, then
           * it is not reachable
           */
          assert (!BTOR_IS_WRITE_EXP (cur));

          /* atomic arrays and array conditionals
           * should also not be reached directly */
          assert (!BTOR_IS_ARRAY_VAR_EXP (cur));
          assert (!BTOR_IS_ARRAY_COND_EXP (cur));

          /* special cases */
          if (BTOR_IS_READ_EXP (cur))
          {
            cur->av = btor_var_aigvec (avmgr, cur->len);
            assert (BTOR_IS_REGULAR_EXP (cur->e[0]));
            assert (BTOR_IS_ARRAY_EXP (cur->e[0]));
            goto REGULAR_CASE;
          }
          else if (BTOR_IS_ARRAY_EQ_EXP (cur))
          {
            /* generate virtual reads and create AIG
             * variable for array equality */
            synthesize_array_equality (btor, cur);
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
            BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
            goto REGULAR_CASE;
          }
          else
          {
          REGULAR_CASE:
            /* regular cases */
            cur->synth_mark = 1;
            BTOR_PUSH_STACK (mm, exp_stack, cur);
            for (i = cur->arity - 1; i >= 0; i--)
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[i]);
          }
        }
      }
      else
      {
        assert (cur->synth_mark == 1);
        cur->synth_mark = 2;
        assert (!BTOR_IS_READ_EXP (cur));
        switch (cur->arity)
        {
          case 1:
            assert (cur->kind == BTOR_SLICE_EXP);
            invert_av0 = BTOR_IS_INVERTED_EXP (cur->e[0]);
            av0        = BTOR_REAL_ADDR_EXP (cur->e[0])->av;
            if (invert_av0) btor_invert_aigvec (avmgr, av0);
            cur->av = btor_slice_aigvec (avmgr, av0, cur->upper, cur->lower);
            /* invert back if necessary */
            if (invert_av0) btor_invert_aigvec (avmgr, av0);
            break;
          case 2:
            /* we have to check if the children are
             * in the same memory place
             * if they are in the same memory place,
             * then we need to allocate memory for the
             * AIG vectors
             * if they are not, then we can invert them
             * in place and invert them back afterwards
             * (only if necessary)  */
            same_children_mem = BTOR_REAL_ADDR_EXP (cur->e[0])
                                == BTOR_REAL_ADDR_EXP (cur->e[1]);
            if (same_children_mem)
            {
              av0 = BTOR_AIGVEC_EXP (btor, cur->e[0]);
              av1 = BTOR_AIGVEC_EXP (btor, cur->e[1]);
            }
            else
            {
              invert_av0 = BTOR_IS_INVERTED_EXP (cur->e[0]);
              av0        = BTOR_REAL_ADDR_EXP (cur->e[0])->av;
              if (invert_av0) btor_invert_aigvec (avmgr, av0);
              invert_av1 = BTOR_IS_INVERTED_EXP (cur->e[1]);
              av1        = BTOR_REAL_ADDR_EXP (cur->e[1])->av;
              if (invert_av1) btor_invert_aigvec (avmgr, av1);
            }
            switch (cur->kind)
            {
              case BTOR_AND_EXP:
                cur->av = btor_and_aigvec (avmgr, av0, av1);
                break;
              case BTOR_BEQ_EXP:
                cur->av = btor_eq_aigvec (avmgr, av0, av1);
                break;
              case BTOR_ADD_EXP:
                cur->av = btor_add_aigvec (avmgr, av0, av1);
                break;
              case BTOR_MUL_EXP:
                cur->av = btor_mul_aigvec (avmgr, av0, av1);
                break;
              case BTOR_ULT_EXP:
                cur->av = btor_ult_aigvec (avmgr, av0, av1);
                break;
              case BTOR_SLL_EXP:
                cur->av = btor_sll_aigvec (avmgr, av0, av1);
                break;
              case BTOR_SRL_EXP:
                cur->av = btor_srl_aigvec (avmgr, av0, av1);
                break;
              case BTOR_UDIV_EXP:
                cur->av = btor_udiv_aigvec (avmgr, av0, av1);
                break;
              case BTOR_UREM_EXP:
                cur->av = btor_urem_aigvec (avmgr, av0, av1);
                break;
              default:
                assert (cur->kind == BTOR_CONCAT_EXP);
                cur->av = btor_concat_aigvec (avmgr, av0, av1);
                break;
            }

            if (same_children_mem)
            {
              btor_release_delete_aigvec (avmgr, av0);
              btor_release_delete_aigvec (avmgr, av1);
            }
            else
            {
              /* invert back if necessary */
              if (invert_av0) btor_invert_aigvec (avmgr, av0);
              if (invert_av1) btor_invert_aigvec (avmgr, av1);
            }
            break;
          default:
            assert (cur->arity == 3);
            if (BTOR_IS_BV_COND_EXP (cur))
            {
              same_children_mem = BTOR_REAL_ADDR_EXP (cur->e[0])
                                      == BTOR_REAL_ADDR_EXP (cur->e[1])
                                  || BTOR_REAL_ADDR_EXP (cur->e[0])
                                         == BTOR_REAL_ADDR_EXP (cur->e[2])
                                  || BTOR_REAL_ADDR_EXP (cur->e[1])
                                         == BTOR_REAL_ADDR_EXP (cur->e[2]);
              if (same_children_mem)
              {
                av0 = BTOR_AIGVEC_EXP (btor, cur->e[0]);
                av1 = BTOR_AIGVEC_EXP (btor, cur->e[1]);
                av2 = BTOR_AIGVEC_EXP (btor, cur->e[2]);
              }
              else
              {
                invert_av0 = BTOR_IS_INVERTED_EXP (cur->e[0]);
                av0        = BTOR_REAL_ADDR_EXP (cur->e[0])->av;
                if (invert_av0) btor_invert_aigvec (avmgr, av0);
                invert_av1 = BTOR_IS_INVERTED_EXP (cur->e[1]);
                av1        = BTOR_REAL_ADDR_EXP (cur->e[1])->av;
                if (invert_av1) btor_invert_aigvec (avmgr, av1);
                invert_av2 = BTOR_IS_INVERTED_EXP (cur->e[2]);
                av2        = BTOR_REAL_ADDR_EXP (cur->e[2])->av;
                if (invert_av2) btor_invert_aigvec (avmgr, av2);
              }
              cur->av = btor_cond_aigvec (avmgr, av0, av1, av2);
              if (same_children_mem)
              {
                btor_release_delete_aigvec (avmgr, av2);
                btor_release_delete_aigvec (avmgr, av1);
                btor_release_delete_aigvec (avmgr, av0);
              }
              else
              {
                /* invert back if necessary */
                if (invert_av0) btor_invert_aigvec (avmgr, av0);
                if (invert_av1) btor_invert_aigvec (avmgr, av1);
                if (invert_av2) btor_invert_aigvec (avmgr, av2);
              }
            }
            break;
        }

#ifndef BTOR_NO_3VL
        if (btor->rewrite_level > 1 && !BTOR_IS_ARRAY_EXP (cur))
          propagate_3vl_to_aigvec (btor, cur);
#endif
      }
    }
  } while (!BTOR_EMPTY_STACK (exp_stack));

  BTOR_RELEASE_STACK (mm, exp_stack);
  mark_synth_mark_exp (btor, exp, 0);

  if (count > 0 && btor->verbosity > 2)
    btor_msg_exp (btor, "synthesized %u expressions into AIG vectors", count);
}

static BtorAIG *
exp_to_aig (Btor *btor, BtorExp *exp)
{
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorAIGVec *av;
  BtorAIG *result;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  mm    = btor->mm;
  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);

  synthesize_exp (btor, exp, 0);
  av = BTOR_REAL_ADDR_EXP (exp)->av;

  assert (av);
  assert (av->len == 1);

  result = av->aigs[0];

  if (BTOR_IS_INVERTED_EXP (exp))
    result = btor_not_aig (amgr, result);
  else
    result = btor_copy_aig (amgr, result);

  return result;
}

BtorAIGVec *
btor_exp_to_aigvec (Btor *btor, BtorExp *exp, BtorPtrHashTable *backannotation)
{
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *result;

  assert (exp != NULL);

  mm    = btor->mm;
  avmgr = btor->avmgr;

  synthesize_exp (btor, exp, backannotation);
  result = BTOR_REAL_ADDR_EXP (exp)->av;
  assert (result);

  if (BTOR_IS_INVERTED_EXP (exp))
    result = btor_not_aigvec (avmgr, result);
  else
    result = btor_copy_aigvec (avmgr, result);

  return result;
}

/* Compares the assignments of two expressions. */
static int
compare_assignments (BtorExp *exp1, BtorExp *exp2)
{
  int return_val, val1, val2, i, len;
  Btor *btor;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp1)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp2)));
  assert (BTOR_REAL_ADDR_EXP (exp1)->len == BTOR_REAL_ADDR_EXP (exp2)->len);
  assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (exp1)));
  assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (exp2)));
  btor = BTOR_REAL_ADDR_EXP (exp1)->btor;
  assert (btor != NULL);
  return_val = 0;
  avmgr      = btor->avmgr;
  amgr       = btor_get_aig_mgr_aigvec_mgr (avmgr);
  av1        = BTOR_REAL_ADDR_EXP (exp1)->av;
  av2        = BTOR_REAL_ADDR_EXP (exp2)->av;
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_EXP (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_EXP (exp2, av2->aigs[i]);

    val1 = btor_get_assignment_aig (amgr, aig1);
    assert (val1 == -1 || val1 == 1);

    val2 = btor_get_assignment_aig (amgr, aig2);
    assert (val2 == -1 || val2 == 1);

    if (val1 < val2)
    {
      return_val = -1;
      break;
    }

    if (val2 < val1)
    {
      return_val = 1;
      break;
    }
  }
  return return_val;
}

static unsigned int
hash_assignment (BtorExp *exp)
{
  unsigned int hash;
  Btor *btor;
  BtorAIGVecMgr *avmgr;
  BtorExp *real_exp;
  BtorAIGVec *av;
  int invert_av;
  char *assignment;
  assert (exp != NULL);
  real_exp  = BTOR_REAL_ADDR_EXP (exp);
  btor      = real_exp->btor;
  avmgr     = btor->avmgr;
  av        = real_exp->av;
  invert_av = BTOR_IS_INVERTED_EXP (exp);
  if (invert_av) btor_invert_aigvec (avmgr, av);
  assignment = btor_assignment_aigvec (avmgr, av);
  hash       = btor_hashstr (assignment);
  btor_freestr (btor->mm, assignment);
  /* invert back if necessary */
  if (invert_av) btor_invert_aigvec (avmgr, av);
  return hash;
}

/* This function breath first searches the shortest path from a read to an array
 * After the function is completed the parent pointers can be followed
 * from the array to the read
 */
static void
bfs (Btor *btor, BtorExp *acc, BtorExp *array)
{
  BtorExp *cur, *next, *cur_aeq, *cond, *index;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorExpPtrQueue queue;
  BtorExpPtrStack unmark_stack;
  BtorPartialParentIterator it;
  int found, assignment, has_array_equalities;
  assert (btor != NULL);
  assert (acc != NULL);
  assert (array != NULL);
  assert (BTOR_IS_REGULAR_EXP (acc));
  assert (BTOR_IS_ACC_EXP (acc));
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  found = 0;
  assert (btor->ops[BTOR_AEQ_EXP] >= 0);
  has_array_equalities = btor->ops[BTOR_AEQ_EXP] > 0;
  mm                   = btor->mm;
  index                = BTOR_GET_INDEX_ACC_EXP (acc);
  amgr                 = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  cur                  = BTOR_ACC_TARGET_EXP (acc);
  assert (BTOR_IS_REGULAR_EXP (cur));
  assert (BTOR_IS_ARRAY_EXP (cur));
  assert (cur->mark == 0);
  cur->parent = acc;
  cur->mark   = 1;

  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_QUEUE (queue);
  BTOR_ENQUEUE (mm, queue, cur);
  BTOR_PUSH_STACK (mm, unmark_stack, cur);
  do
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_ARRAY_EXP (cur));

    if (cur == array)
    {
      found = 1;
      break;
    }

    /* lazy_synthesize_and_encode_acc_exp sets the 'sat_both_phases' flag.
     * If this flag is not set, we have to find an other way
     * to the conflict. */
    if (BTOR_IS_WRITE_EXP (cur) && cur->e[0]->mark == 0
        && BTOR_REAL_ADDR_EXP (cur->e[1])->sat_both_phases
        && compare_assignments (cur->e[1], index) != 0)
    {
      assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (cur->e[1])));
      next         = cur->e[0];
      next->mark   = 1;
      next->parent = cur;
      BTOR_ENQUEUE (mm, queue, next);
      BTOR_PUSH_STACK (mm, unmark_stack, next);
    }
    /* lazy_synthesize_and_encode_acond_exp sets the 'sat_both_phases' flag.
     * If this flag is not set, we have to find an other way
     * to the conflict. */
    else if (BTOR_IS_ARRAY_COND_EXP (cur)
             && BTOR_REAL_ADDR_EXP (cur->e[0])->sat_both_phases)
    {
      assert (BTOR_IS_SYNTH_EXP (cur->e[0]));
      /* check assignment to determine which array to choose */
      cond       = cur->e[0];
      assignment = btor_get_assignment_aig (
          amgr, BTOR_REAL_ADDR_EXP (cond)->av->aigs[0]);
      assert (assignment == 1 || assignment == -1);
      if (BTOR_IS_INVERTED_EXP (cond)) assignment = -assignment;
      if (assignment == 1)
        next = cur->e[1];
      else
        next = cur->e[2];
      if (next->mark == 0)
      {
        next->mark   = 1;
        next->parent = cur;
        BTOR_ENQUEUE (mm, queue, next);
        BTOR_PUSH_STACK (mm, unmark_stack, next);
      }
    }
    if (has_array_equalities)
    {
      /* enqueue all arrays which are reachable via equality
       * where equality is set to true by the SAT solver */
      init_aeq_parent_iterator (&it, cur);
      while (has_next_parent_aeq_parent_iterator (&it))
      {
        cur_aeq = next_parent_aeq_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_aeq));
        check_not_simplified_or_const (btor, cur_aeq);
        if (cur_aeq->reachable && cur_aeq->mark == 0)
        {
          /* array equalities are synthesized eagerly */
          assert (BTOR_IS_SYNTH_EXP (cur_aeq));
          assert (cur_aeq->sat_both_phases);
          assert (cur_aeq->len == 1);
          if (btor_get_assignment_aig (amgr, cur_aeq->av->aigs[0]) == 1)
          {
            /* we need the other child */
            if (cur_aeq->e[0] == cur)
              next = cur_aeq->e[1];
            else
              next = cur_aeq->e[0];
            assert (BTOR_IS_REGULAR_EXP (next));
            assert (BTOR_IS_ARRAY_EXP (next));
            if (next->mark == 0)
            {
              /* set parent of array equality */
              cur_aeq->parent = cur;
              next->parent    = cur_aeq;
              next->mark      = 1;
              BTOR_ENQUEUE (mm, queue, next);
              BTOR_PUSH_STACK (mm, unmark_stack, next);
            }
          }
        }
      }
      /* search upwards */
      init_acond_parent_iterator (&it, cur);
      while (has_next_parent_acond_parent_iterator (&it))
      {
        next = next_parent_acond_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (next));
        assert (BTOR_IS_ARRAY_EXP (next));
        assert (next->simplified == NULL);
        /* lazy_synthesize_and_encode_acc_exp sets the
         * 'sat_both_phases' flag.
         * If this flag is not set, we have to find an other way
         * to the conflict. */
        if (next->reachable && next->mark == 0
            && BTOR_REAL_ADDR_EXP (next->e[0])->sat_both_phases)
        {
          cond       = next->e[0];
          assignment = btor_get_assignment_aig (
              amgr, BTOR_REAL_ADDR_EXP (cond)->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
          if (BTOR_IS_INVERTED_EXP (cond)) assignment = -assignment;
          /* search upwards only if array has been selected */
          if ((assignment == 1 && cur == next->e[1])
              || (assignment == -1 && cur == next->e[2]))
          {
            next->mark   = 1;
            next->parent = cur;
            BTOR_ENQUEUE (mm, queue, next);
            BTOR_PUSH_STACK (mm, unmark_stack, next);
          }
        }
      }
      init_write_parent_iterator (&it, cur);
      while (has_next_parent_write_parent_iterator (&it))
      {
        next = next_parent_write_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (next));
        assert (BTOR_IS_ARRAY_EXP (next));
        assert (next->simplified == NULL);
        if (next->reachable && next->mark == 0)
        {
          /* search upwards only if write has been synthesized and
           * assignments to the indices are unequal
           */
          if (BTOR_REAL_ADDR_EXP (next->e[1])->sat_both_phases
              && compare_assignments (next->e[1], index) != 0)
          {
            next->mark   = 1;
            next->parent = cur;
            BTOR_ENQUEUE (mm, queue, next);
            BTOR_PUSH_STACK (mm, unmark_stack, next);
          }
        }
      }
    }
  } while (!BTOR_EMPTY_QUEUE (queue));
  assert (found);
  BTOR_RELEASE_QUEUE (mm, queue);
  /* reset mark flags */
  assert (!BTOR_EMPTY_STACK (unmark_stack));
  do
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_ARRAY_EXP (cur) || BTOR_IS_ARRAY_EQ_EXP (cur)
            || BTOR_IS_ARRAY_COND_EXP (cur));
    cur->mark = 0;
  } while (!BTOR_EMPTY_STACK (unmark_stack));
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static int
propagated_upwards (Btor *btor, BtorExp *exp)
{
  BtorExp *parent;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (BTOR_IS_ARRAY_EXP (exp) || BTOR_IS_WRITE_EXP (exp)
          || BTOR_IS_ARRAY_COND_EXP (exp) || BTOR_IS_ARRAY_EQ_EXP (exp));
  assert (exp->parent != NULL);
  (void) btor;
  parent = exp->parent;
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (BTOR_IS_ARRAY_EXP (parent) || BTOR_IS_ACC_EXP (parent)
          || BTOR_IS_ARRAY_COND_EXP (parent) || BTOR_IS_ARRAY_EQ_EXP (parent));
  if (BTOR_IS_WRITE_EXP (exp) && exp->e[0] == parent) return 1;
  if (BTOR_IS_ARRAY_COND_EXP (exp)
      && (exp->e[1] == parent || exp->e[2] == parent))
    return 1;
  if (BTOR_IS_ARRAY_EQ_EXP (exp))
  {
    assert (exp->e[0] == parent || exp->e[1] == parent);
    return 1;
  }
  return 0;
}

/* Adds lemma on demand
 * 'array' is the array where the conflict has been detected
 */
static void
add_lemma (Btor *btor, BtorExp *array, BtorExp *acc1, BtorExp *acc2)
{
  BtorPtrHashTable *writes, *aeqs, *aconds_sel1, *aconds_sel2;
  BtorExp *cur, *cond, *prev, *acc;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  int assignment;
  assert (btor != NULL);
  assert (array != NULL);
  assert (acc1 != NULL);
  assert (acc2 != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_REGULAR_EXP (acc1));
  assert (BTOR_IS_REGULAR_EXP (acc2));
  assert (BTOR_IS_ARRAY_EXP (array));
  assert (BTOR_IS_ACC_EXP (acc1));
  assert (BTOR_IS_ACC_EXP (acc2));

  mm   = btor->mm;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  /* collect intermediate writes, array equalities and array conditionals
   * as premisses for McCarthy constraint */
  writes      = btor_new_ptr_hash_table (mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);
  aeqs        = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
  aconds_sel1 = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  aconds_sel2 = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  for (acc = acc1; acc != NULL; acc = acc == acc1 ? acc2 : NULL)
  {
    bfs (btor, acc, array);
    prev = NULL;
    for (cur = array; cur != acc; cur = cur->parent)
    {
      assert (cur != NULL);
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (BTOR_IS_ARRAY_EXP (cur) || BTOR_IS_ARRAY_EQ_EXP (cur)
              || BTOR_IS_ARRAY_COND_EXP (cur) || BTOR_IS_ACC_EXP (cur));
      if ((prev == NULL && propagated_upwards (btor, cur))
          || (prev != NULL
              && !(propagated_upwards (btor, prev)
                   && !propagated_upwards (btor, cur))))
      {
        if (BTOR_IS_WRITE_EXP (cur))
        {
          if (!btor_find_in_ptr_hash_table (writes, cur))
            btor_insert_in_ptr_hash_table (writes, cur);
        }
        else if (BTOR_IS_ARRAY_EQ_EXP (cur))
        {
          if (!btor_find_in_ptr_hash_table (aeqs, cur))
            btor_insert_in_ptr_hash_table (aeqs, cur);
        }
        else if (BTOR_IS_ARRAY_COND_EXP (cur))
        {
          cond = cur->e[0];
          assert (btor->rewrite_level == 0
                  || !BTOR_IS_BV_CONST_EXP (BTOR_REAL_ADDR_EXP (cond)));
          if (!BTOR_IS_BV_CONST_EXP (BTOR_REAL_ADDR_EXP (cond)))
          {
            assignment = btor_get_assignment_aig (
                amgr, BTOR_REAL_ADDR_EXP (cond)->av->aigs[0]);
            assert (assignment == 1 || assignment == -1);
            if (BTOR_IS_INVERTED_EXP (cond)) assignment = -assignment;
            if (assignment == 1)
            {
              if (!btor_find_in_ptr_hash_table (aconds_sel1, cur))
                btor_insert_in_ptr_hash_table (aconds_sel1, cur);
            }
            else
            {
              if (!btor_find_in_ptr_hash_table (aconds_sel2, cur))
                btor_insert_in_ptr_hash_table (aconds_sel2, cur);
            }
          }
        }
      }
      prev = cur;
    }
  }

  encode_lemma (btor,
                writes,
                aeqs,
                aconds_sel1,
                aconds_sel2,
                BTOR_GET_INDEX_ACC_EXP (acc1),
                BTOR_GET_INDEX_ACC_EXP (acc2),
                BTOR_GET_VALUE_ACC_EXP (acc1),
                BTOR_GET_VALUE_ACC_EXP (acc2));
  btor_delete_ptr_hash_table (writes);
  btor_delete_ptr_hash_table (aeqs);
  btor_delete_ptr_hash_table (aconds_sel1);
  btor_delete_ptr_hash_table (aconds_sel2);
}

/* checks array axiom 2 */
static int
find_array_axiom_2_conflict (Btor *btor,
                             BtorExp *acc,
                             BtorExp *write,
                             int *indices_equal)
{
  assert (btor != NULL);
  assert (acc != NULL);
  assert (write != NULL);
  assert (indices_equal != NULL);
  assert (BTOR_IS_REGULAR_EXP (acc));
  assert (BTOR_IS_REGULAR_EXP (write));
  assert (BTOR_IS_ACC_EXP (acc));
  assert (BTOR_IS_WRITE_EXP (write));
  (void) btor;
  if ((*indices_equal =
           compare_assignments (BTOR_GET_INDEX_ACC_EXP (acc), write->e[1]) == 0)
      && compare_assignments (BTOR_GET_VALUE_ACC_EXP (acc), write->e[2]) != 0)
    return 1;
  return 0;
}

/* reads assumptions to the SAT solver */
static int
add_again_assumptions (Btor *btor)
{
  BtorExp *exp;
  BtorPtrHashBucket *b;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  assert (btor != NULL);
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  for (b = btor->assumptions->first; b != NULL; b = b->next)
  {
    assert (BTOR_REAL_ADDR_EXP ((BtorExp *) b->key)->len == 1);
    exp = (BtorExp *) b->key;
    exp = btor_pointer_chase_simplified_exp (btor, exp);
    aig = exp_to_aig (btor, exp);
    if (aig == BTOR_AIG_FALSE) return 1;
    btor_aig_to_sat (amgr, aig);
    if (aig != BTOR_AIG_TRUE)
    {
      assert (BTOR_REAL_ADDR_AIG (aig)->cnf_id != 0);
      btor_assume_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
      btor_release_aig (amgr, aig);
    }
  }

  return 0;
}

static void
read_under_approx_assumptions (Btor *btor)
{
  BtorSATMgr *smgr;
  BtorUAData *data;
  BtorPtrHashBucket *b;

  assert (btor != NULL);
  assert (btor->ua.enabled);

  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));

  if (btor->ua.mode == BTOR_UA_GLOBAL_MODE)
  {
    if (btor->ua.global_last_e != 0)
      btor_assume_sat (smgr, btor->ua.global_last_e);
  }
  else
  {
    assert (btor->ua.mode == BTOR_UA_LOCAL_MODE
            || btor->ua.mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
    for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
    {
      data = (BtorUAData *) b->data.asPtr;
      if (data->last_e != 0) btor_assume_sat (smgr, data->last_e);
    }
  }
}

/* updates SAT assignments, reads assumptions and
 * returns if an assignment has changed
 */
static int
update_sat_assignments (Btor *btor)
{
  int result, found_assumption_false;
  BtorSATMgr *smgr = NULL;
  assert (btor != NULL);
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  found_assumption_false = add_again_assumptions (btor);
  assert (!found_assumption_false);
  result = btor_sat_sat (smgr);
  assert (result == BTOR_SAT);
  return btor_changed_sat (smgr);
}

/* synthesizes and fully encodes index and value of access expression into SAT
 * (if necessary)
 * it returns if encoding changed assignments made so far
 */
static int
lazy_synthesize_and_encode_acc_exp (Btor *btor, BtorExp *acc, int force_update)
{
  BtorExp *index, *value;
  int changed_assignments, update;
  BtorAIGVecMgr *avmgr = NULL;

  assert (btor != NULL);
  assert (acc != NULL);
  assert (BTOR_IS_REGULAR_EXP (acc));
  assert (BTOR_IS_ACC_EXP (acc));
  changed_assignments = 0;
  update              = 0;
  avmgr               = btor->avmgr;
  index               = BTOR_GET_INDEX_ACC_EXP (acc);
  value               = BTOR_GET_VALUE_ACC_EXP (acc);

  if (!BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (index)))
  {
    // abort (); // TODO before removing it ....
    synthesize_exp (btor, index, NULL);
  }
  if (!BTOR_REAL_ADDR_EXP (index)->sat_both_phases)
  {
    // abort (); // TODO before removing it ....
    update = 1;
    btor_aigvec_to_sat_both_phases (avmgr, BTOR_REAL_ADDR_EXP (index)->av);
    BTOR_REAL_ADDR_EXP (index)->sat_both_phases = 1;
  }
  if (!BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (value)))
  {
    // abort (); // TODO before removing it ....
    synthesize_exp (btor, value, NULL);
  }
  if (!BTOR_REAL_ADDR_EXP (value)->sat_both_phases)
  {
    update = 1;
    btor_aigvec_to_sat_both_phases (avmgr, BTOR_REAL_ADDR_EXP (value)->av);
    BTOR_REAL_ADDR_EXP (value)->sat_both_phases = 1;
  }
  /* update assignments if necessary */
  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);
  return changed_assignments;
}

static int
lazy_synthesize_and_encode_acond_exp (Btor *btor,
                                      BtorExp *acond,
                                      int force_update)
{
  BtorExp *cond;
  int changed_assignments, update;
  BtorAIGVecMgr *avmgr;

  avmgr = btor->avmgr;
  assert (btor != NULL);
  assert (acond != NULL);
  assert (BTOR_IS_REGULAR_EXP (acond));
  assert (BTOR_IS_ARRAY_COND_EXP (acond));
  changed_assignments = 0;
  update              = 0;
  cond                = acond->e[0];
  assert (cond != NULL);
  if (!BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (cond)))
  {
    // abort (); // TODO before removing it ....
    synthesize_exp (btor, cond, NULL);
  }
  if (!BTOR_REAL_ADDR_EXP (cond)->sat_both_phases)
  {
    // abort (); // TODO before removing it ....
    update = 1;
    btor_aigvec_to_sat_both_phases (avmgr, BTOR_REAL_ADDR_EXP (cond)->av);
    BTOR_REAL_ADDR_EXP (cond)->sat_both_phases = 1;
  }
  /* update assignments if necessary */
  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);
  return changed_assignments;
}

static int
process_working_stack (Btor *btor,
                       BtorExpPtrStack *stack,
                       BtorExpPtrStack *cleanup_stack,
                       int *assignments_changed)
{
  BtorPartialParentIterator it;
  BtorExp *acc, *index, *value, *array, *hashed_acc, *hashed_value;
  BtorExp *cur_aeq, *cond, *next;
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  int assignment, indices_equal, has_array_equalities;
  assert (btor != NULL);
  assert (stack != NULL);
  assert (assignments_changed != NULL);
  assert (btor->ops[BTOR_AEQ_EXP] >= 0);
  has_array_equalities = btor->ops[BTOR_AEQ_EXP] > 0;
  mm                   = btor->mm;
  amgr                 = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  while (!BTOR_EMPTY_STACK (*stack))
  {
    array = BTOR_POP_STACK (*stack);
    assert (BTOR_IS_REGULAR_EXP (array));
    assert (BTOR_IS_ARRAY_EXP (array));
    assert (array->simplified == NULL);
    assert (!BTOR_EMPTY_STACK (*stack));
    acc = BTOR_POP_STACK (*stack);
    assert (BTOR_IS_REGULAR_EXP (acc));
    assert (BTOR_IS_ACC_EXP (acc));
    check_not_simplified_or_const (btor, acc);
    /* synthesize index and value if necessary */
    *assignments_changed = lazy_synthesize_and_encode_acc_exp (btor, acc, 1);
    index                = BTOR_GET_INDEX_ACC_EXP (acc);
    check_not_simplified_or_const (btor, index);
    value = BTOR_GET_VALUE_ACC_EXP (acc);
    check_not_simplified_or_const (btor, value);
    if (*assignments_changed) return 0;
    /* hash table lookup */
    if (array->rho == NULL)
    {
      array->rho = btor_new_ptr_hash_table (
          mm, (BtorHashPtr) hash_assignment, (BtorCmpPtr) compare_assignments);
      BTOR_PUSH_STACK (mm, *cleanup_stack, array);
    }
    else
    {
      /* check array axiom 1 */
      bucket = btor_find_in_ptr_hash_table (array->rho, index);
      if (bucket != NULL)
      {
        hashed_acc = (BtorExp *) bucket->data.asPtr;
        assert (BTOR_IS_REGULAR_EXP (hashed_acc));
        assert (BTOR_IS_ACC_EXP (hashed_acc));
        hashed_value = BTOR_GET_VALUE_ACC_EXP (hashed_acc);
        /* we have to check if values are equal */
        if (compare_assignments (hashed_value, value) != 0)
        {
          btor->stats.array_axiom_1_conflicts++;
          add_lemma (btor, array, hashed_acc, acc);
          return 1;
        }
        /* in the other case we have already dealt with a representative
         * with same index assignment and same value assignment */
        else
          continue;
      }
    }
    if (BTOR_IS_WRITE_EXP (array))
    {
      *assignments_changed =
          lazy_synthesize_and_encode_acc_exp (btor, array, 1);
      if (*assignments_changed) return 0;
      /* check array axiom 2 */
      if (find_array_axiom_2_conflict (btor, acc, array, &indices_equal))
      {
        btor->stats.array_axiom_2_conflicts++;
        add_lemma (btor, array, acc, array);
        return 1;
      }
      else if (!indices_equal)
      {
        /* propagate down */
        assert (BTOR_IS_REGULAR_EXP (array->e[0]));
        assert (BTOR_IS_ARRAY_EXP (array->e[0]));
        assert (array->e[0]->simplified == NULL);
        BTOR_PUSH_STACK (mm, *stack, acc);
        BTOR_PUSH_STACK (mm, *stack, array->e[0]);
      }
    }
    else if (BTOR_IS_ARRAY_COND_EXP (array))
    {
      *assignments_changed =
          lazy_synthesize_and_encode_acond_exp (btor, array, 1);
      if (*assignments_changed) return 0;
      cond = array->e[0];
      check_not_simplified_or_const (btor, index);
      assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (cond)));
      assignment = btor_get_assignment_aig (
          amgr, BTOR_REAL_ADDR_EXP (cond)->av->aigs[0]);
      assert (assignment == 1 || assignment == -1);
      if (BTOR_IS_INVERTED_EXP (cond)) assignment = -assignment;
      /* propagate down */
      BTOR_PUSH_STACK (mm, *stack, acc);
      if (assignment == 1)
      {
        assert (BTOR_IS_REGULAR_EXP (array->e[1]));
        assert (BTOR_IS_ARRAY_EXP (array->e[1]));
        assert (array->e[1]->simplified == NULL);
        BTOR_PUSH_STACK (mm, *stack, array->e[1]);
      }
      else
      {
        assert (BTOR_IS_REGULAR_EXP (array->e[2]));
        assert (BTOR_IS_ARRAY_EXP (array->e[2]));
        assert (array->e[2]->simplified == NULL);
        BTOR_PUSH_STACK (mm, *stack, array->e[2]);
      }
    }
    assert (array->rho != NULL);
    /* insert into hash table */
    btor_insert_in_ptr_hash_table (array->rho, index)->data.asPtr = acc;
    if (has_array_equalities)
    {
      /* propagate pairs wich are reachable via array equality */
      init_aeq_parent_iterator (&it, array);
      while (has_next_parent_aeq_parent_iterator (&it))
      {
        cur_aeq = next_parent_aeq_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_aeq));
        check_not_simplified_or_const (btor, cur_aeq);
        if (cur_aeq->reachable)
        {
          assert (BTOR_IS_SYNTH_EXP (cur_aeq));
          assert (cur_aeq->sat_both_phases);
          assert (!BTOR_IS_INVERTED_AIG (cur_aeq->av->aigs[0]));
          assert (!BTOR_IS_CONST_AIG (cur_aeq->av->aigs[0]));
          assert (BTOR_IS_VAR_AIG (cur_aeq->av->aigs[0]));
          if (btor_get_assignment_aig (amgr, cur_aeq->av->aigs[0]) == 1)
          {
            /* we need the other child */
            if (cur_aeq->e[0] == array)
              next = cur_aeq->e[1];
            else
              next = cur_aeq->e[0];
            assert (BTOR_IS_REGULAR_EXP (next));
            assert (BTOR_IS_ARRAY_EXP (next));
            assert (next->simplified == NULL);
            BTOR_PUSH_STACK (mm, *stack, acc);
            BTOR_PUSH_STACK (mm, *stack, next);
          }
        }
      }
      /* propagate upwards */
      init_acond_parent_iterator (&it, array);
      while (has_next_parent_acond_parent_iterator (&it))
      {
        next = next_parent_acond_parent_iterator (&it);
        assert (next->simplified == NULL);
        if (next->reachable)
        {
          assert (BTOR_IS_REGULAR_EXP (next));
          assert (BTOR_IS_ARRAY_EXP (next));
          *assignments_changed =
              lazy_synthesize_and_encode_acond_exp (btor, next, 1);
          if (*assignments_changed) return 0;
          cond       = next->e[0];
          assignment = btor_get_assignment_aig (
              amgr, BTOR_REAL_ADDR_EXP (cond)->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
          if (BTOR_IS_INVERTED_EXP (cond)) assignment = -assignment;
          /* propagate upwards only if array has been selected
           * by the condition */
          if ((assignment == 1 && array == next->e[1])
              || (assignment == -1 && array == next->e[2]))
          {
            BTOR_PUSH_STACK (mm, *stack, acc);
            BTOR_PUSH_STACK (mm, *stack, next);
          }
        }
      }
      init_write_parent_iterator (&it, array);
      while (has_next_parent_write_parent_iterator (&it))
      {
        next = next_parent_write_parent_iterator (&it);
        assert (next->simplified == NULL);
        if (next->reachable)
        {
          assert (BTOR_IS_REGULAR_EXP (next));
          assert (BTOR_IS_ARRAY_EXP (next));
          *assignments_changed =
              lazy_synthesize_and_encode_acc_exp (btor, next, 1);
          if (*assignments_changed) return 0;
          /* propagate upwards only if assignments to the
           * indices are unequal */
          if (compare_assignments (next->e[1], index) != 0)
          {
            BTOR_PUSH_STACK (mm, *stack, acc);
            BTOR_PUSH_STACK (mm, *stack, next);
          }
        }
      }
    }
  }
  return 0;
}

/* searches the top arrays where the conflict check begins
 * and pushes them on the stack
 */
static void
search_top_arrays (Btor *btor, BtorExpPtrStack *top_arrays)
{
  BtorPartialParentIterator it;
  BtorExp *cur_array, *cur_parent;
  BtorExpPtrStack stack, unmark_stack;
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  int found_top;
  assert (btor != NULL);
  assert (top_arrays != NULL);
  assert (BTOR_COUNT_STACK (*top_arrays) == 0);
  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  for (bucket = btor->array_vars->first; bucket; bucket = bucket->next)
  {
    cur_array = (BtorExp *) bucket->key;
    assert (BTOR_IS_ARRAY_VAR_EXP (cur_array));
    assert (cur_array->simplified == NULL);
    if (cur_array->reachable) BTOR_PUSH_STACK (mm, stack, cur_array);
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_array = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->reachable);
    assert (cur_array->simplified == NULL);
    assert (cur_array->array_mark == 0 || cur_array->array_mark == 1);
    if (cur_array->array_mark == 0)
    {
      cur_array->array_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur_array);
      found_top = 1;
      /* ATTENTION: There can be write and array conditional parents
       * although they are not reachable from root.
       * For example the parser might still
       * have a reference to a write, thus it is still in the parent list.
       * We use the reachable flag to determine with which writes
       * and array conditionals we have to deal with.
       */
      /* push writes on stack */
      init_write_parent_iterator (&it, cur_array);
      while (has_next_parent_write_parent_iterator (&it))
      {
        cur_parent = next_parent_write_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        assert (cur_parent->simplified == NULL);
        if (cur_parent->reachable)
        {
          found_top = 0;
          assert (cur_parent->array_mark == 0);
          BTOR_PUSH_STACK (mm, stack, cur_parent);
        }
      }
      /* push array conditionals on stack */
      init_acond_parent_iterator (&it, cur_array);
      while (has_next_parent_acond_parent_iterator (&it))
      {
        cur_parent = next_parent_acond_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        assert (cur_parent->simplified == NULL);
        if (cur_parent->reachable)
        {
          found_top = 0;
          BTOR_PUSH_STACK (mm, stack, cur_parent);
        }
      }
      if (found_top) BTOR_PUSH_STACK (mm, *top_arrays, cur_array);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);

  /* reset array marks of arrays */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur_array = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->array_mark == 1);
    cur_array->array_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static int
check_and_resolve_conflicts (Btor *btor, BtorExpPtrStack *top_arrays)
{
  BtorExpPtrStack array_stack, cleanup_stack, working_stack, unmark_stack;
  BtorPartialParentIterator it;
  BtorMemMgr *mm;
  BtorExp *cur_array, *cur_parent, **top, **temp;
  int found_conflict, changed_assignments, has_array_equalities;
  assert (btor != NULL);
  assert (top_arrays != NULL);
  found_conflict = 0;
  mm             = btor->mm;
  assert (btor->ops[BTOR_AEQ_EXP] >= 0);
  has_array_equalities = btor->ops[BTOR_AEQ_EXP] > 0;
BTOR_READ_WRITE_ARRAY_CONFLICT_CHECK:
  assert (!found_conflict);
  changed_assignments = 0;
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (working_stack);
  BTOR_INIT_STACK (cleanup_stack);
  BTOR_INIT_STACK (array_stack);

  /* push all top arrays on the stack */
  top = top_arrays->top;
  for (temp = top_arrays->start; temp != top; temp++)
  {
    cur_array = *temp;
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->reachable);
    assert (cur_array->simplified == NULL);
    BTOR_PUSH_STACK (mm, array_stack, cur_array);
  }

  while (!BTOR_EMPTY_STACK (array_stack))
  {
    cur_array = BTOR_POP_STACK (array_stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->reachable);
    assert (cur_array->simplified == NULL);
    assert (cur_array->array_mark == 0 || cur_array->array_mark == 1);
    if (cur_array->array_mark == 0)
    {
      cur_array->array_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur_array);
      if (BTOR_IS_WRITE_EXP (cur_array))
      {
        BTOR_PUSH_STACK (mm, array_stack, cur_array->e[0]);
        if (has_array_equalities)
        {
          /* propagate writes as reads if there are array equalities */
          BTOR_PUSH_STACK (mm, working_stack, cur_array);
          BTOR_PUSH_STACK (mm, working_stack, cur_array);
          found_conflict = process_working_stack (
              btor, &working_stack, &cleanup_stack, &changed_assignments);
          if (found_conflict || changed_assignments)
            goto BTOR_READ_WRITE_ARRAY_CONFLICT_CLEANUP;
        }
      }
      else if (BTOR_IS_ARRAY_COND_EXP (cur_array))
      {
        BTOR_PUSH_STACK (mm, array_stack, cur_array->e[2]);
        BTOR_PUSH_STACK (mm, array_stack, cur_array->e[1]);
      }
      init_read_parent_iterator (&it, cur_array);
      while (has_next_parent_read_parent_iterator (&it))
      {
        cur_parent = next_parent_read_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        /* we only process reachable or virtual reads */
        check_not_simplified_or_const (btor, cur_parent);
        if (cur_parent->reachable || cur_parent->vread)
        {
          /* push read-array pair on working stack */
          BTOR_PUSH_STACK (mm, working_stack, cur_parent);
          BTOR_PUSH_STACK (mm, working_stack, cur_array);
          found_conflict = process_working_stack (
              btor, &working_stack, &cleanup_stack, &changed_assignments);
          if (found_conflict || changed_assignments)
            goto BTOR_READ_WRITE_ARRAY_CONFLICT_CLEANUP;
        }
      }
    }
  }
BTOR_READ_WRITE_ARRAY_CONFLICT_CLEANUP:
  while (!BTOR_EMPTY_STACK (cleanup_stack))
  {
    cur_array = BTOR_POP_STACK (cleanup_stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->rho != NULL);

    if (found_conflict || changed_assignments)
    {
      btor_delete_ptr_hash_table (cur_array->rho);
      cur_array->rho = NULL;
    }
    else
    {
      /* remember arrays for incremental usage */
      BTOR_PUSH_STACK (mm, btor->arrays_with_model, cur_array);
    }
  }
  BTOR_RELEASE_STACK (mm, cleanup_stack);

  BTOR_RELEASE_STACK (mm, working_stack);
  BTOR_RELEASE_STACK (mm, array_stack);

  /* reset array marks of arrays */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur_array = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->array_mark == 1);
    cur_array->array_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);

  /* restart? (assignments changed during lazy synthesis and encoding) */
  if (changed_assignments)
  {
    btor->stats.synthesis_assignment_inconsistencies++;
    goto BTOR_READ_WRITE_ARRAY_CONFLICT_CHECK;
  }
  return found_conflict;
}

static void
btor_reset_assumptions (Btor *btor)
{
  BtorPtrHashBucket *bucket;
  assert (btor != NULL);
  for (bucket = btor->assumptions->first; bucket != NULL; bucket = bucket->next)
    btor_release_exp (btor, (BtorExp *) bucket->key);
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
btor_reset_array_models (Btor *btor)
{
  BtorExp *cur;
  int i;

  assert (btor != NULL);

  for (i = 0; i < BTOR_COUNT_STACK (btor->arrays_with_model); i++)
  {
    cur = btor->arrays_with_model.start[i];
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_ARRAY_EXP (cur));
    assert (cur->rho != NULL);
    btor_delete_ptr_hash_table (cur->rho);
    cur->rho = NULL;
  }
  BTOR_RESET_STACK (btor->arrays_with_model);
}

static void
btor_reset_incremental_usage (Btor *btor)
{
  assert (btor != NULL);

  btor_reset_assumptions (btor);
  btor_reset_array_models (btor);
  btor->valid_assignments = 0;
}

/* check if left does not occur on the right side */
static int
occurrence_check (Btor *btor, BtorExp *left, BtorExp *right)
{
  BtorExp *cur, *real_left;
  BtorExpPtrStack stack, unmark_stack;
  int is_cyclic, i;
  BtorMemMgr *mm;
  assert (btor != NULL);
  assert (left != NULL);
  assert (right != NULL);

  is_cyclic = 0;
  mm        = btor->mm;
  real_left = BTOR_REAL_ADDR_EXP (left);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  cur = BTOR_REAL_ADDR_EXP (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    assert (cur->aux_mark == 0 || cur->aux_mark == 1);
    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur);
      if (cur == real_left)
      {
        is_cyclic = 1;
        break;
      }
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (cur->aux_mark == 1);
    cur->aux_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);

  return is_cyclic;
}

static BtorExp *
rebuild_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  switch (exp->kind)
  {
    case BTOR_BV_CONST_EXP:
    case BTOR_BV_VAR_EXP:
    case BTOR_ARRAY_VAR_EXP: return btor_copy_exp (btor, exp->simplified);
    case BTOR_SLICE_EXP:
      return btor_slice_exp (btor, exp->e[0], exp->upper, exp->lower);
    case BTOR_AND_EXP: return btor_and_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_BEQ_EXP:
    case BTOR_AEQ_EXP: return btor_eq_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ADD_EXP: return btor_add_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_MUL_EXP: return btor_mul_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ULT_EXP: return btor_ult_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SLL_EXP: return btor_sll_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SRL_EXP: return btor_srl_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UDIV_EXP: return btor_udiv_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UREM_EXP: return btor_urem_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_CONCAT_EXP: return btor_concat_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_READ_EXP: return btor_read_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_WRITE_EXP:
      return btor_write_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
    default:
      assert (BTOR_IS_ARRAY_OR_BV_COND_EXP (exp));
      return btor_cond_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
  }
}

/* TODO move to 'btorconst.c' ?
 */
static int
is_odd_constant (BtorExp *exp)
{
  if (BTOR_IS_INVERTED_EXP (exp)) return 0;

  if (exp->kind != BTOR_BV_CONST_EXP) return 0;

  return exp->bits[exp->len - 1] == '1';
}

#if 0
static int
is_true_exp (Btor *btor, BtorExp * exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;

  if (BTOR_REAL_ADDR_EXP (exp)->len != 1)
    return 0;

  if (BTOR_REAL_ADDR_EXP (exp)->kind != BTOR_BV_CONST_EXP)
    return 0;

  if (BTOR_IS_INVERTED_EXP (exp))
    return BTOR_REAL_ADDR_EXP (exp)->bits[0] == '0';

  return exp->bits[0] == '1';
}
#endif

/* Can we rewrite 'term' as 'factor*lhs + rhs' where 'lhs' is a variable,
 * and 'factor' is odd?  We check whether this is possible but do not use
 * more than 'bound' recursive calls.
 */
static int
rewrite_linear_term_bounded (Btor *btor,
                             BtorExp *term,
                             char **factor_ptr,
                             BtorExp **lhs_ptr,
                             BtorExp **rhs_ptr,
                             int *bound_ptr)
{
  BtorExp *tmp, *other;
  char *factor;

  if (*bound_ptr <= 0) return 0;

  *bound_ptr -= 1;

  if (BTOR_IS_INVERTED_EXP (term))
  {
    /* term = ~subterm
     *      = -1 - subterm
     *      = -1 - (factor * lhs + rhs)
     *      = (-factor) * lhs + (-1 -rhs)
     *      = (-factor) * lhs + ~rhs
     */
    if (!rewrite_linear_term_bounded (
            btor, BTOR_INVERT_EXP (term), &factor, lhs_ptr, rhs_ptr, bound_ptr))
      return 0;

    *rhs_ptr    = BTOR_INVERT_EXP (*rhs_ptr);
    *factor_ptr = btor_neg_const (btor->mm, factor);
    btor_delete_const (btor->mm, factor);
  }
  else if (term->kind == BTOR_ADD_EXP)
  {
    if (rewrite_linear_term_bounded (
            btor, term->e[0], factor_ptr, lhs_ptr, &tmp, bound_ptr))
    {
      /* term = e0 + e1
       *      = (factor * lhs + rhs) + e1
       *      = factor * lhs + (e1 + rhs)
       */
      other = term->e[1];
    }
    else if (rewrite_linear_term_bounded (
                 btor, term->e[1], factor_ptr, lhs_ptr, &tmp, bound_ptr))
    {
      /* term = e0 + e1
       *      = e0 + (factor * lhs + rhs)
       *      = factor * lhs + (e0 + rhs)
       */
      other = term->e[0];
    }
    else
      return 0;

    *rhs_ptr = btor_add_exp (btor, other, tmp);
    btor_release_exp (btor, tmp);
  }
  else if (term->kind == BTOR_MUL_EXP)
  {
    if (is_odd_constant (term->e[0]))
    {
      if (!rewrite_linear_term_bounded (
              btor, term->e[1], &factor, lhs_ptr, &tmp, bound_ptr))
        return 0;

      /* term = e0 * e1
       *      = e0 * (factor * lhs + rhs)
       *      = (e0 * factor) * lhs + e0 * rhs
       *      = (other * factor) * lhs + other * rhs
       */
      other = term->e[0];
    }
    else if (is_odd_constant (term->e[1]))
    {
      if (!rewrite_linear_term_bounded (
              btor, term->e[0], &factor, lhs_ptr, &tmp, bound_ptr))
        return 0;

      /* term = e0 * e1
       *      = (factor * lhs + rhs) * e1
       *      = (e1 * factor) * lhs + e1 * rhs
       *      = (other * factor) * lhs + other * rhs
       */
      other = term->e[1];
    }
    else
      return 0;

    assert (!BTOR_IS_INVERTED_EXP (other));
    *factor_ptr = btor_mul_const (btor->mm, other->bits, factor);
    btor_delete_const (btor->mm, factor);
    *rhs_ptr = btor_mul_exp (btor, other, tmp);
    btor_release_exp (btor, tmp);
  }
  else if (term->kind == BTOR_BV_VAR_EXP)
  {
    *lhs_ptr    = btor_copy_exp (btor, term);
    *rhs_ptr    = btor_zero_exp (btor, term->len);
    *factor_ptr = btor_one_const (btor->mm, term->len);
  }
  else
    return 0;

  return 1;
}

static int
rewrite_linear_term (
    Btor *btor, BtorExp *term, char **fp, BtorExp **lp, BtorExp **rp)
{
  int bound = 100, res;
  res       = rewrite_linear_term_bounded (btor, term, fp, lp, rp, &bound);
  if (res) btor->stats.linear_equations++;
  return res;
}

static int
is_embedded_constraint_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  return BTOR_REAL_ADDR_EXP (exp)->len == 1 && has_parents_exp (btor, exp);
}

static BtorExp *
lambda_var_exp (Btor *btor, int len)
{
  BtorExp *result;
  char *name;
  int string_len;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (len > 0);

  mm = btor->mm;

  string_len = btor_num_digits_util (btor->bv_lambda_id) + 11;
  BTOR_NEWN (mm, name, string_len);
  sprintf (name, "bvlambda_%d_", btor->bv_lambda_id);
  btor->bv_lambda_id++;
  result = btor_var_exp (btor, len, name);
  BTOR_DELETEN (mm, name, string_len);
  return result;
}

#if 0
static BtorExp *
lambda_array_exp (Btor * btor, int elem_len, int index_len)
{
  BtorExp *result;
  char *name;
  int string_len;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (elem_len > 0);
  assert (index_len > 0);

  mm = btor->mm;

  string_len = btor_num_digits_util (btor->array_lambda_id) + 14;
  BTOR_NEWN (mm, name, string_len);
  sprintf (name, "arraylambda_%d_", btor->array_lambda_id);
  btor->array_lambda_id++;
  result = btor_array_exp (btor, elem_len, index_len, name);
  BTOR_DELETEN (mm, name, string_len);
  return result;
}
#endif

enum BtorSubstCompKind
{
  BTOR_SUBST_COMP_ULT_KIND,
  BTOR_SUBST_COMP_ULTE_KIND,
  BTOR_SUBST_COMP_UGT_KIND,
  BTOR_SUBST_COMP_UGTE_KIND
};

typedef enum BtorSubstCompKind BtorSubstCompKind;

static BtorSubstCompKind
reverse_subst_comp_kind (Btor *btor, BtorSubstCompKind comp)
{
  assert (btor != NULL);
  (void) btor;
  switch (comp)
  {
    case BTOR_SUBST_COMP_ULT_KIND: return BTOR_SUBST_COMP_UGT_KIND;
    case BTOR_SUBST_COMP_ULTE_KIND: return BTOR_SUBST_COMP_UGTE_KIND;
    case BTOR_SUBST_COMP_UGT_KIND: return BTOR_SUBST_COMP_ULT_KIND;
    default:
      assert (comp == BTOR_SUBST_COMP_UGTE_KIND);
      return BTOR_SUBST_COMP_ULTE_KIND;
  }
}

static void
insert_unsynthesized_constraint (Btor *btor, BtorExp *exp)
{
  BtorPtrHashTable *uc;
  assert (btor != NULL);
  assert (exp != NULL);
  uc = btor->unsynthesized_constraints;
  if (!btor_find_in_ptr_hash_table (uc, exp))
  {
    inc_exp_ref_counter (btor, exp);
    (void) btor_insert_in_ptr_hash_table (uc, exp);
    BTOR_REAL_ADDR_EXP (exp)->constraint = 1;
    btor->stats.constraints.unsynthesized++;
  }
}

static void
insert_embedded_constraint (Btor *btor, BtorExp *exp)
{
  BtorPtrHashTable *embedded_constraints;
  assert (btor != NULL);
  assert (exp != NULL);
  embedded_constraints = btor->embedded_constraints;
  if (!btor_find_in_ptr_hash_table (embedded_constraints, exp))
  {
    inc_exp_ref_counter (btor, exp);
    (void) btor_insert_in_ptr_hash_table (embedded_constraints, exp);
    BTOR_REAL_ADDR_EXP (exp)->constraint = 1;
    btor->stats.constraints.embedded++;
  }
}

static void
insert_varsubst_constraint (Btor *btor, BtorExp *left, BtorExp *right)
{
  BtorExp *eq;
  BtorPtrHashTable *vsc;
  BtorPtrHashBucket *bucket;
  int subst;

  assert (btor != NULL);
  assert (left != NULL);
  assert (right != NULL);

  subst  = 1;
  vsc    = btor->varsubst_constraints;
  bucket = btor_find_in_ptr_hash_table (vsc, left);

  if (bucket == NULL)
  {
    if (btor->model_gen && !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (right)))
    {
      if (!btor_find_in_ptr_hash_table (btor->var_rhs, left))
      {
        btor_insert_in_ptr_hash_table (btor->var_rhs, left);
        inc_exp_ref_counter (btor, left);
      }
    }

    inc_exp_ref_counter (btor, left);
    inc_exp_ref_counter (btor, right);
    btor_insert_in_ptr_hash_table (vsc, left)->data.asPtr = right;
    /* do not set constraint flag, as they are gone after substitution
     * and treated differently */
    btor->stats.constraints.varsubst++;
  }
  /* if v = t_1 is already in varsubst, we
   * have to synthesize v = t_2 */
  else if (right != (BtorExp *) bucket->data.asPtr)
  {
    eq = btor_eq_exp (btor, left, right);
    insert_unsynthesized_constraint (btor, eq);
    btor_release_exp (btor, eq);
  }
}

/* checks if we can substitute and normalizes arguments to substitution */
static int
normalize_substitution (Btor *btor,
                        BtorExp *exp,
                        BtorExp **left_result,
                        BtorExp **right_result)
{
  BtorExp *left, *right, *real_left, *real_right, *tmp, *inv, *var, *lambda;
  BtorExp *const_exp, *real_exp;
  int leadings;
  char *ic, *fc, *bits;
  BtorMemMgr *mm;
  BtorSubstCompKind comp;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (left_result != NULL);
  assert (right_result != NULL);
  assert (btor->rewrite_level > 1);
  assert (btor_pointer_chase_simplified_exp (btor, exp) == exp);

  mm = btor->mm;

  if (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)))
  {
    assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
    if (BTOR_IS_INVERTED_EXP (exp))
    {
      *left_result  = BTOR_REAL_ADDR_EXP (exp);
      *right_result = btor_zero_exp (btor, 1);
    }
    else
    {
      *left_result  = exp;
      *right_result = btor_one_exp (btor, 1);
    }
    inc_exp_ref_counter (btor, *left_result);
    return 1;
  }

  if (BTOR_REAL_ADDR_EXP (exp)->kind == BTOR_ULT_EXP
      && (BTOR_IS_BV_VAR_EXP (
              BTOR_REAL_ADDR_EXP (BTOR_REAL_ADDR_EXP (exp)->e[0]))
          || BTOR_IS_BV_VAR_EXP (
                 BTOR_REAL_ADDR_EXP (BTOR_REAL_ADDR_EXP (exp)->e[1]))))
  {
    real_exp = BTOR_REAL_ADDR_EXP (exp);

    if (BTOR_IS_INVERTED_EXP (exp))
      comp = BTOR_SUBST_COMP_UGTE_KIND;
    else
      comp = BTOR_SUBST_COMP_ULT_KIND;

    if (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (real_exp->e[0])))
    {
      var   = real_exp->e[0];
      right = real_exp->e[1];
    }
    else
    {
      assert (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (real_exp->e[1])));
      var   = real_exp->e[1];
      right = real_exp->e[0];
      comp  = reverse_subst_comp_kind (btor, comp);
    }

    /* ~a comp b is equal to a reverse_comp ~b,
     * where comp in ult, ulte, ugt, ugte
     * (e.g. reverse_comp of ult is ugt) */
    if (BTOR_IS_INVERTED_EXP (var))
    {
      var   = BTOR_REAL_ADDR_EXP (var);
      right = BTOR_INVERT_EXP (right);
      comp  = reverse_subst_comp_kind (btor, comp);
    }

    /* we do not create a lambda if variable is already in substitution
     * table */
    assert (!BTOR_IS_INVERTED_EXP (var));
    if (btor_find_in_ptr_hash_table (btor->varsubst_constraints, var)) return 0;

#ifdef BTOR_NO_3VL
    if (!BTOR_IS_BV_CONST_EXP (BTOR_REAL_ADDR_EXP (right))) return 0;
#endif

    if (BTOR_IS_INVERTED_EXP (right))
      bits = btor_not_const_3vl (mm, BTOR_REAL_ADDR_EXP (right)->bits);
    else
      bits = btor_copy_const (mm, right->bits);

    if (comp == BTOR_SUBST_COMP_ULT_KIND || comp == BTOR_SUBST_COMP_ULTE_KIND)
    {
      leadings = btor_get_num_leading_zeros_const (btor->mm, bits);
      if (leadings > 0)
      {
        const_exp = btor_zero_exp (btor, leadings);
        lambda    = lambda_var_exp (btor, var->len - leadings);
        tmp       = btor_concat_exp (btor, const_exp, lambda);
        insert_varsubst_constraint (btor, var, tmp);
        btor_release_exp (btor, const_exp);
        btor_release_exp (btor, lambda);
        btor_release_exp (btor, tmp);
      }
    }
    else
    {
      assert (comp == BTOR_SUBST_COMP_UGT_KIND
              || comp == BTOR_SUBST_COMP_UGTE_KIND);
      leadings = btor_get_num_leading_ones_const (btor->mm, bits);
      if (leadings > 0)
      {
        const_exp = btor_ones_exp (btor, leadings);
        lambda    = lambda_var_exp (btor, var->len - leadings);
        tmp       = btor_concat_exp (btor, const_exp, lambda);
        insert_varsubst_constraint (btor, var, tmp);
        btor_release_exp (btor, const_exp);
        btor_release_exp (btor, lambda);
        btor_release_exp (btor, tmp);
      }
    }

    btor_delete_const (btor->mm, bits);
    return 0;
  }

  /* in the boolean case a != b is the same as a == ~b */
  if (BTOR_IS_INVERTED_EXP (exp)
      && BTOR_REAL_ADDR_EXP (exp)->kind == BTOR_BEQ_EXP
      && BTOR_REAL_ADDR_EXP (BTOR_REAL_ADDR_EXP (exp)->e[0])->len == 1)
  {
    left  = BTOR_REAL_ADDR_EXP (exp)->e[0];
    right = BTOR_REAL_ADDR_EXP (exp)->e[1];

    if (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (left)))
    {
      *left_result  = btor_copy_exp (btor, left);
      *right_result = BTOR_INVERT_EXP (btor_copy_exp (btor, right));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }

    if (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (right)))
    {
      *left_result  = btor_copy_exp (btor, right);
      *right_result = BTOR_INVERT_EXP (btor_copy_exp (btor, left));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }
  }

  if (BTOR_IS_INVERTED_EXP (exp) || !BTOR_IS_ARRAY_OR_BV_EQ_EXP (exp)) return 0;

  left       = exp->e[0];
  right      = exp->e[1];
  real_left  = BTOR_REAL_ADDR_EXP (left);
  real_right = BTOR_REAL_ADDR_EXP (right);

  if (!BTOR_IS_BV_VAR_EXP (real_left) && !BTOR_IS_BV_VAR_EXP (real_right)
      && !BTOR_IS_ARRAY_VAR_EXP (real_left)
      && !BTOR_IS_ARRAY_VAR_EXP (real_right))
  {
    if (rewrite_linear_term (btor, left, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, right, tmp);
    else if (rewrite_linear_term (btor, right, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, left, tmp);
    else
      return 0;

    btor_release_exp (btor, tmp);
    ic = btor_inverse_const (btor->mm, fc);
    btor_delete_const (btor->mm, fc);
    inv = btor_const_exp (btor, ic);
    btor_delete_const (btor->mm, ic);
    tmp = btor_mul_exp (btor, *right_result, inv);
    btor_release_exp (btor, inv);
    btor_release_exp (btor, *right_result);
    *right_result = tmp;
  }
  else
  {
    if ((!BTOR_IS_BV_VAR_EXP (real_left) && BTOR_IS_BV_VAR_EXP (real_right))
        || (!BTOR_IS_ARRAY_VAR_EXP (real_left)
            && BTOR_IS_ARRAY_VAR_EXP (real_right)))
    {
      *left_result  = right;
      *right_result = left;
    }
    else
    {
      *left_result  = left;
      *right_result = right;
    }

    btor_copy_exp (btor, left);
    btor_copy_exp (btor, right);
  }

BTOR_NORMALIZE_SUBST_RESULT:
  if (BTOR_IS_INVERTED_EXP (*left_result))
  {
    *left_result  = BTOR_INVERT_EXP (*left_result);
    *right_result = BTOR_INVERT_EXP (*right_result);
  }

  if (occurrence_check (btor, *left_result, *right_result))
  {
    btor_release_exp (btor, *left_result);
    btor_release_exp (btor, *right_result);
    return 0;
  }

  return 1;
}

static void
insert_new_constraint (Btor *btor, BtorExp *exp)
{
  BtorExp *left, *right, *exp_true, *real_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  if (btor->inconsistent) return;

  exp      = btor_pointer_chase_simplified_exp (btor, exp);
  real_exp = BTOR_REAL_ADDR_EXP (exp);

  if (BTOR_IS_BV_CONST_EXP (real_exp))
  {
    if ((BTOR_IS_INVERTED_EXP (exp) && real_exp->bits[0] == '1')
        || (!BTOR_IS_INVERTED_EXP (exp) && real_exp->bits[0] == '0'))
    {
      btor->inconsistent = 1;
      return;
    }
    else
    {
      /* we do not add true */
      assert ((BTOR_IS_INVERTED_EXP (exp) && real_exp->bits[0] == '0')
              || (!BTOR_IS_INVERTED_EXP (exp) && real_exp->bits[0] == '1'));
      return;
    }
  }

  // if (!btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp))
  {
    if (btor->rewrite_level > 1)
    {
      if (normalize_substitution (btor, exp, &left, &right))
      {
        insert_varsubst_constraint (btor, left, right);
        btor_release_exp (btor, left);
        btor_release_exp (btor, right);
      }
      else
      {
        exp_true = btor_true_exp (btor);
        if (merge_simplified_exp_const (btor, exp, exp_true))
        {
          if (is_embedded_constraint_exp (btor, exp))
            insert_embedded_constraint (btor, exp);
          else
            insert_unsynthesized_constraint (btor, exp);
        }
        else
          btor->inconsistent = 1;
        btor_release_exp (btor, exp_true);
      }
    }
    else
      insert_unsynthesized_constraint (btor, exp);

    report_constraint_stats (btor, 0);
  }
}

static void
add_constraint (Btor *btor, BtorExp *exp)
{
  BtorExp *cur, *child;
  BtorExpPtrStack stack;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (exp != NULL);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  mm = btor->mm;
  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_EXP (exp) && exp->kind == BTOR_AND_EXP)
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_EXP (cur));
      assert (cur->kind == BTOR_AND_EXP);
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_EXP (child) && child->kind == BTOR_AND_EXP)
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_EXP (child) && child->kind == BTOR_AND_EXP)
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (mm, stack);
    btor_mark_exp (btor, exp, 0);
  }
  else
    insert_new_constraint (btor, exp);
}

void
btor_add_constraint_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  if (btor->replay)
    BTOR_PUSH_STACK (
        btor->mm, btor->replay_constraints, btor_copy_exp (btor, exp));

  add_constraint (btor, exp);
}

void
btor_replay_btor (Btor *btor, FILE *file)
{
  BtorExp *result, *temp;
  BtorPtrHashBucket *b;
  int i;

  assert (btor != NULL);
  assert (file != NULL);

  result = btor_true_exp (btor);
  for (i = 0; i < BTOR_COUNT_STACK (btor->replay_constraints); i++)
  {
    temp = btor_and_exp (btor, result, btor->replay_constraints.start[i]);
    btor_release_exp (btor, result);
    result = temp;
  }
  for (b = btor->assumptions->first; b != NULL; b = b->next)
  {
    temp = btor_and_exp (btor, result, (BtorExp *) b->key);
    btor_release_exp (btor, result);
    result = temp;
  }
  btor_dump_exp (btor, file, result);
  btor_release_exp (btor, result);
}

void
btor_add_assumption_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *cur, *child;
  BtorExpPtrStack stack;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (btor->inc_enabled);
  assert (exp != NULL);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  mm = btor->mm;
  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_EXP (exp) && exp->kind == BTOR_AND_EXP)
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto BTOR_ADD_ASSUMPTION_EXP_ENTER_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    BTOR_ADD_ASSUMPTION_EXP_ENTER_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_EXP (cur));
      assert (cur->kind == BTOR_AND_EXP);
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_EXP (child) && child->kind == BTOR_AND_EXP)
          BTOR_PUSH_STACK (mm, stack, child);
        else
        {
          if (!btor_find_in_ptr_hash_table (btor->assumptions, child))
            (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                                  btor_copy_exp (btor, child));
        }
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_EXP (child) && child->kind == BTOR_AND_EXP)
          BTOR_PUSH_STACK (mm, stack, child);
        else
        {
          if (!btor_find_in_ptr_hash_table (btor->assumptions, child))
            (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                                  btor_copy_exp (btor, child));
        }
      }
    } while (!BTOR_EMPTY_STACK (stack));
    BTOR_RELEASE_STACK (mm, stack);
    btor_mark_exp (btor, exp, 0);
  }
  else
  {
    if (!btor_find_in_ptr_hash_table (btor->assumptions, exp))
      (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                            btor_copy_exp (btor, exp));
  }
}

/* synthesizes unsynthesized constraints and updates constraints tables.
 * returns 0 if a constraint has been synthesized into AIG_FALSE */
static int
process_unsynthesized_constraints (Btor *btor)
{
  BtorPtrHashTable *unsynthesized_constraints, *synthesized_constraints;
  BtorPtrHashBucket *bucket;
  BtorExp *cur;
  BtorAIG *aig;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  assert (btor != NULL);
  unsynthesized_constraints = btor->unsynthesized_constraints;
  synthesized_constraints   = btor->synthesized_constraints;
  amgr                      = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr                      = btor_get_sat_mgr_aig_mgr (amgr);
  while (unsynthesized_constraints->count > 0)
  {
    bucket = unsynthesized_constraints->first;
    assert (bucket != NULL);
    cur = (BtorExp *) bucket->key;

    if (btor_find_in_ptr_hash_table (synthesized_constraints, cur) == NULL)
    {
      aig = exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE) return 1;

      btor_add_toplevel_aig_to_sat (amgr, aig);
      btor_release_aig (amgr, aig);
      (void) btor_insert_in_ptr_hash_table (synthesized_constraints, cur);
      btor_remove_from_ptr_hash_table (unsynthesized_constraints, cur, 0, 0);

      btor->stats.constraints.synthesized++;
      report_constraint_stats (btor, 0);
    }
    else
    {
      /* constraint is already in synthesized_constraints */
      btor_remove_from_ptr_hash_table (
          unsynthesized_constraints, cur, NULL, NULL);
      btor_release_exp (btor, cur);
    }
  }
  return 0;
}

static void
update_assumptions (Btor *btor)
{
  BtorPtrHashBucket *bucket;
  BtorExp *cur, *simp;
  assert (btor != NULL);
  for (bucket = btor->assumptions->first; bucket != NULL; bucket = bucket->next)
  {
    cur = (BtorExp *) bucket->key;
    if (cur->simplified != NULL)
    {
      simp =
          btor_copy_exp (btor, btor_pointer_chase_simplified_exp (btor, cur));
      btor_release_exp (btor, cur);
      bucket->key = simp;
    }
  }
}

/* we perform all variable substitutions in one pass and rebuild the formula
 * cyclic substitutions must have been deleted before! */
static void
substitute_vars_and_rebuild_exps (Btor *btor, BtorPtrHashTable *substs)
{
  BtorExpPtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorExp *cur, *cur_parent, *rebuilt_exp, **temp, **top, *rhs, *simplified;
  BtorMemMgr *mm;
  BtorFullParentIterator it;
  int pushed, i;
  assert (btor != NULL);
  assert (substs != NULL);

  if (substs->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (root_stack);
  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  for (b = substs->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur));
    BTOR_PUSH_STACK (mm, stack, cur);
  }
  do
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      init_full_parent_iterator (&it, cur);
      /* are we at a root ? */
      pushed = 0;
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        pushed = 1;
        BTOR_PUSH_STACK (mm, stack, cur_parent);
      }
      if (!pushed) BTOR_PUSH_STACK (mm, root_stack, btor_copy_exp (btor, cur));
    }
  } while (!BTOR_EMPTY_STACK (stack));

  /* copy roots on substitution stack */
  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    BTOR_PUSH_STACK (mm, stack, *temp);

  /* substitute */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));

    if (cur->aux_mark == 0) continue;

    assert (!BTOR_IS_BV_CONST_EXP (cur));

    if (cur->aux_mark == 1)
    {
      BTOR_PUSH_STACK (mm, stack, cur);
      cur->aux_mark = 2;
      if (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur))
      {
        b = btor_find_in_ptr_hash_table (substs, cur);
        assert (b != NULL);
        assert (cur == (BtorExp *) b->key);
        rhs = (BtorExp *) b->data.asPtr;
        assert (rhs != NULL);
        BTOR_PUSH_STACK (mm, stack, rhs);
      }
      else
      {
        for (i = cur->arity - 1; i >= 0; i--)
          BTOR_PUSH_STACK (mm, stack, cur->e[i]);
      }
    }
    else
    {
      assert (cur->aux_mark == 2);
      cur->aux_mark = 0;
      if (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur))
      {
        b = btor_find_in_ptr_hash_table (substs, cur);
        assert (b != NULL);
        assert (cur == (BtorExp *) b->key);
        rhs = (BtorExp *) b->data.asPtr;
        assert (rhs != NULL);
        rebuilt_exp = btor_copy_exp (btor, rhs);
        if (BTOR_IS_BV_VAR_EXP (cur))
          btor->stats.var_substitutions++;
        else
          btor->stats.array_substitutions++;
      }
      else
        rebuilt_exp = rebuild_exp (btor, cur);
      assert (rebuilt_exp != NULL);
      assert (rebuilt_exp != cur);

      simplified = btor_pointer_chase_simplified_exp (btor, rebuilt_exp);
      set_simplified_exp (btor, cur, simplified, 1);
      btor_release_exp (btor, rebuilt_exp);
    }
  }

  BTOR_RELEASE_STACK (mm, stack);

  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    btor_release_exp (btor, *temp);
  BTOR_RELEASE_STACK (mm, root_stack);
}

static void
substitute_var_exps (Btor *btor, int check_cyclic)
{
  int order_num, val, max, i;
  BtorPtrHashTable *varsubst_constraints, *order, *substs;
  BtorPtrHashBucket *b, *b_temp;
  BtorExpPtrStack stack;
  BtorMemMgr *mm;
  BtorExp *cur, *constraint, *left, *right, *child;
  assert (btor != NULL);

  mm                   = btor->mm;
  varsubst_constraints = btor->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  if (!check_cyclic)
  {
    assert (varsubst_constraints->count > 0u);
    /* new equality constraints may be added during rebuild */
    do
    {
      /* we copy the current substitution constraints into a local hash table,
       * and empty the global substitution table */
      substs = btor_new_ptr_hash_table (mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);
      assert (varsubst_constraints->count > 0u);
      do
      {
        b   = varsubst_constraints->first;
        cur = (BtorExp *) b->key;
        assert (BTOR_IS_REGULAR_EXP (cur));
        assert (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur));
        btor_insert_in_ptr_hash_table (substs, cur)->data.asPtr = b->data.asPtr;
        btor_remove_from_ptr_hash_table (varsubst_constraints, cur, NULL, NULL);
      } while (varsubst_constraints->count > 0u);
      assert (varsubst_constraints->count == 0u);
      /* we rebuild and substiute variables in one pass */
      substitute_vars_and_rebuild_exps (btor, substs);
      /* cleanup, we delete all substitution constraints */
      for (b = substs->first; b != NULL; b = b->next)
      {
        left = (BtorExp *) b->key;
        assert (BTOR_IS_REGULAR_EXP (left));
        assert (left->kind == BTOR_PROXY_EXP);
        assert (left->simplified != NULL);
        right = (BtorExp *) b->data.asPtr;
        assert (right != NULL);
        btor_release_exp (btor, left);
        btor_release_exp (btor, right);
      }
      btor_delete_ptr_hash_table (substs);
    } while (varsubst_constraints->count > 0u);
    return;
  }

  BTOR_INIT_STACK (stack);

  /* new equality constraints may be added during rebuild */
  while (varsubst_constraints->count > 0u)
  {
    order_num = 1;
    order     = btor_new_ptr_hash_table (mm,
                                     (BtorHashPtr) btor_hash_exp_by_id,
                                     (BtorCmpPtr) btor_compare_exp_by_id);

    substs = btor_new_ptr_hash_table (mm,
                                      (BtorHashPtr) btor_hash_exp_by_id,
                                      (BtorCmpPtr) btor_compare_exp_by_id);

    /* we copy the current substitution constraints into a local hash table,
     * and empty the global substitution table */
    while (varsubst_constraints->count > 0u)
    {
      b   = varsubst_constraints->first;
      cur = (BtorExp *) b->key;
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur));
      btor_insert_in_ptr_hash_table (substs, cur)->data.asPtr = b->data.asPtr;
      btor_remove_from_ptr_hash_table (varsubst_constraints, cur, NULL, NULL);
    }
    assert (varsubst_constraints->count == 0u);

    /* we search for cyclic substitution dependencies
     * and map the substitutions to an ordering number */
    for (b = substs->first; b != NULL; b = b->next)
    {
      cur = (BtorExp *) b->key;
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur));
      BTOR_PUSH_STACK (mm, stack, (BtorExp *) cur);

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));

        if (cur == NULL)
        {
          cur = BTOR_POP_STACK (stack);
          assert (BTOR_IS_REGULAR_EXP (cur));
          assert (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur));
          assert (btor_find_in_ptr_hash_table (order, cur) == NULL);
          btor_insert_in_ptr_hash_table (order, cur)->data.asInt = order_num++;
          continue;
        }

        if (cur->mark == 1) continue;

        cur->mark = 1;

        if (BTOR_IS_BV_CONST_EXP (cur) || BTOR_IS_BV_VAR_EXP (cur)
            || BTOR_IS_ARRAY_VAR_EXP (cur))
        {
          b_temp = btor_find_in_ptr_hash_table (substs, cur);
          if (b_temp != NULL)
          {
            BTOR_PUSH_STACK (mm, stack, cur);
            BTOR_PUSH_STACK (mm, stack, NULL);
            BTOR_PUSH_STACK (mm, stack, (BtorExp *) b_temp->data.asPtr);
          }
          else
          {
            assert (btor_find_in_ptr_hash_table (order, cur) == NULL);
            btor_insert_in_ptr_hash_table (order, cur)->data.asInt = 0;
          }
        }
        else
        {
          assert (cur->arity >= 1);
          assert (cur->arity <= 3);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (mm, stack, cur->e[i]);
        }
      }
    }

    /* intermediate cleanup of mark flags */
    for (b = substs->first; b != NULL; b = b->next)
    {
      assert (BTOR_IS_REGULAR_EXP ((BtorExp *) b->key));
      assert (BTOR_IS_BV_VAR_EXP ((BtorExp *) b->key)
              || BTOR_IS_ARRAY_VAR_EXP ((BtorExp *) b->key));
      btor_mark_exp (btor, (BtorExp *) b->key, 0);
      btor_mark_exp (btor, (BtorExp *) b->data.asPtr, 0);
    }

    /* we look for cycles */
    for (b = substs->first; b != NULL; b = b->next)
    {
      cur = (BtorExp *) b->key;
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (BTOR_IS_BV_VAR_EXP (cur) || BTOR_IS_ARRAY_VAR_EXP (cur));
      BTOR_PUSH_STACK (mm, stack, (BtorExp *) b->data.asPtr);

      /* we assume that there are no direct loops
       * as a result of occurrence check */
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));

        if (cur->mark == 2) continue;

        if (BTOR_IS_BV_CONST_EXP (cur) || BTOR_IS_BV_VAR_EXP (cur)
            || BTOR_IS_ARRAY_VAR_EXP (cur))
        {
          assert (btor_find_in_ptr_hash_table (order, cur) != NULL);
          continue;
        }

        assert (cur->arity >= 1);
        assert (cur->arity <= 3);

        if (cur->mark == 0)
        {
          cur->mark = 1;
          BTOR_PUSH_STACK (mm, stack, cur);
          for (i = cur->arity - 1; i >= 0; i--)
            BTOR_PUSH_STACK (mm, stack, cur->e[i]);
        }
        else
        {
          /* compute maximum of children */
          assert (cur->mark == 1);
          cur->mark = 2;
          max       = 0;
          for (i = cur->arity - 1; i >= 0; i--)
          {
            child  = BTOR_REAL_ADDR_EXP (cur->e[i]);
            b_temp = btor_find_in_ptr_hash_table (order, child);
            assert (b_temp != NULL);
            val = b_temp->data.asInt;
            assert (val >= 0);
            max = BTOR_MAX_UTIL (max, val);
          }
          btor_insert_in_ptr_hash_table (order, cur)->data.asInt = max;
        }
      }
    }

    assert (BTOR_EMPTY_STACK (stack));
    /* we eliminate cyclic substitutions, and reset mark flags */
    for (b = substs->first; b != NULL; b = b->next)
    {
      left = (BtorExp *) b->key;
      assert (BTOR_IS_REGULAR_EXP (left));
      assert (BTOR_IS_BV_VAR_EXP (left) || BTOR_IS_ARRAY_VAR_EXP (left));
      right = (BtorExp *) b->data.asPtr;
      btor_mark_exp (btor, left, 0);
      btor_mark_exp (btor, right, 0);
      b_temp = btor_find_in_ptr_hash_table (order, left);
      assert (b_temp != NULL);
      order_num = b_temp->data.asInt;
      b_temp = btor_find_in_ptr_hash_table (order, BTOR_REAL_ADDR_EXP (right));
      assert (b_temp != NULL);
      max = b_temp->data.asInt;
      assert (order_num != max);
      /* found cycle */
      if (max > order_num) BTOR_PUSH_STACK (mm, stack, left);
    }

    /* we delete cyclic substitutions and synthesize them instead */
    while (!BTOR_EMPTY_STACK (stack))
    {
      left = BTOR_POP_STACK (stack);
      assert (BTOR_IS_REGULAR_EXP (left));
      assert (BTOR_IS_BV_VAR_EXP (left) || BTOR_IS_ARRAY_VAR_EXP (left));
      right =
          (BtorExp *) btor_find_in_ptr_hash_table (substs, left)->data.asPtr;
      assert (right != NULL);

      constraint = btor_eq_exp (btor, left, right);
      insert_unsynthesized_constraint (btor, constraint);
      btor_release_exp (btor, constraint);

      btor_remove_from_ptr_hash_table (substs, left, NULL, NULL);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    /* we rebuild and substiute variables in one pass */
    substitute_vars_and_rebuild_exps (btor, substs);

    /* cleanup, we delete all substitution constraints */
    for (b = substs->first; b != NULL; b = b->next)
    {
      left = (BtorExp *) b->key;
      assert (BTOR_IS_REGULAR_EXP (left));
      assert (left->kind == BTOR_PROXY_EXP);
      assert (left->simplified != NULL);
      right = (BtorExp *) b->data.asPtr;
      assert (right != NULL);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    btor_delete_ptr_hash_table (order);
    btor_delete_ptr_hash_table (substs);
  }

  BTOR_RELEASE_STACK (mm, stack);
}

/* Simple substitution by following simplified pointer.
 */
static void
substitute_and_rebuild (Btor *btor, BtorPtrHashTable *subst)
{
  BtorExpPtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorExp *cur, *cur_parent, *rebuilt_exp, **temp, **top, *simplified;
  BtorMemMgr *mm;
  BtorFullParentIterator it;
  int pushed, i;

  assert (btor != NULL);
  assert (subst != NULL);

  if (subst->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (root_stack);

  /* we push all expressions on the search stack */
  for (b = subst->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_EXP (cur));
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    /* search upwards for all reachable roots */
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      init_full_parent_iterator (&it, cur);
      /* are we at a root ? */
      pushed = 0;
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        pushed = 1;
        BTOR_PUSH_STACK (mm, stack, cur_parent);
      }
      if (!pushed) BTOR_PUSH_STACK (mm, root_stack, btor_copy_exp (btor, cur));
    }
  }

  /* copy roots on substitution stack */
  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    BTOR_PUSH_STACK (mm, stack, *temp);

  /* substitute */
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));

    if (cur->aux_mark == 0) continue;

    if (cur->aux_mark == 1)
    {
      cur->aux_mark = 2;
      BTOR_PUSH_STACK (mm, stack, cur);

      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
    else
    {
      assert (cur->aux_mark == 2);
      cur->aux_mark = 0;

      rebuilt_exp = rebuild_exp (btor, cur);
      assert (rebuilt_exp != NULL);
      /* base case: rebuilt_exp == cur */
      if (rebuilt_exp != cur)
      {
        simplified = btor_pointer_chase_simplified_exp (btor, rebuilt_exp);
        set_simplified_exp (btor, cur, simplified, 1);
      }

      btor_release_exp (btor, rebuilt_exp);
    }
  }

  BTOR_RELEASE_STACK (mm, stack);

  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    btor_release_exp (btor, *temp);
  BTOR_RELEASE_STACK (mm, root_stack);
}

static void
substitute_embedded_constraints (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorExp *cur;

  assert (btor != NULL);

  for (b = btor->embedded_constraints->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (BTOR_REAL_ADDR_EXP (cur)->constraint);
    /* embedded constraints have possibly lost their parents,
     * e.g. top conjunction of constraints that are released */
    if (has_parents_exp (btor, cur)) btor->stats.ec_substitutions++;
  }
  substitute_and_rebuild (btor, btor->embedded_constraints);
}

static void
process_embedded_constraints (Btor *btor)
{
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashBucket *b;
  BtorExp *cur;
  assert (btor != NULL);
  embedded_constraints = btor->embedded_constraints;
  if (embedded_constraints->count > 0u)
  {
    substitute_embedded_constraints (btor);

    while (embedded_constraints->count > 0u)
    {
      b   = embedded_constraints->first;
      cur = (BtorExp *) b->key;
      insert_unsynthesized_constraint (btor, cur);
      btor_remove_from_ptr_hash_table (embedded_constraints, cur, NULL, NULL);
      btor_release_exp (btor, cur);
    }
  }
}

static void
run_rewrite_engine (Btor *btor, int full)
{
  int rewrite_level, inc_enabled, model_gen, check_cyclic;

  assert (btor != NULL);

  if (btor->inconsistent) return;

  rewrite_level = btor->rewrite_level;
  inc_enabled   = btor->inc_enabled;
  model_gen     = btor->model_gen;
  check_cyclic  = 1;

  if (rewrite_level > 1)
  {
    do
    {
      do
      {
        do
        {
          do
          {
            assert (check_all_hash_tables_proxy_free_dbg (btor));
            substitute_var_exps (btor, check_cyclic);
            assert (check_all_hash_tables_proxy_free_dbg (btor));
            if (btor->inconsistent) return;
            check_cyclic = 1;

            process_embedded_constraints (btor);
            assert (check_all_hash_tables_proxy_free_dbg (btor));
            if (btor->inconsistent) return;
          } while (btor->varsubst_constraints->count > 0u
                   || btor->embedded_constraints->count > 0u);

          if (!full) return;

        } while (btor->varsubst_constraints->count > 0u
                 || btor->embedded_constraints->count > 0u);

        if (rewrite_level > 2 && !inc_enabled)
        {
          /* needs recursive rewrite bound > 0 */
          eliminate_slices_on_bv_vars (btor);
          if (btor->inconsistent) return;
          check_cyclic = 1;
        }

      } while (btor->varsubst_constraints->count > 0u
               || btor->embedded_constraints->count > 0u);

      if (rewrite_level > 2 && !inc_enabled && !model_gen)
      {
        abstract_domain_bv_variables (btor);
        if (btor->inconsistent) return;
        check_cyclic = 0;
      }

    } while (btor->varsubst_constraints->count > 0u
             || btor->embedded_constraints->count > 0u);
  }
}

static int
max_len_global_under_approx_vars (Btor *btor)
{
  BtorPtrHashBucket *b;
  int max;
  BtorExp *cur;

  assert (btor->ua.mode == BTOR_UA_GLOBAL_MODE);

  max = 0;

  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);
    if (cur->len > max) max = cur->len;
  }
  return max;
}

static void
update_local_under_approx_eff_width (Btor *btor, BtorExp *exp, BtorUAData *data)
{
  char *max_string;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (data != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  assert (BTOR_IS_BV_VAR_EXP (exp) || exp->kind == BTOR_READ_EXP);

  max_string = "";

  if (btor->ua.ref == BTOR_UA_REF_BY_INC_ONE)
    data->eff_width++;
  else
  {
    assert (btor->ua.ref == BTOR_UA_REF_BY_DOUBLING);
    data->eff_width *= 2;
  }

  /* check also for overflow */
  if (data->eff_width >= exp->len || data->eff_width <= 0)
  {
    max_string      = " (max)";
    data->eff_width = exp->len;
  }

  data->updated_eff_width = 1;
  data->refinements++;

  if (btor->verbosity >= 3)
  {
    if (BTOR_IS_BV_VAR_EXP (exp))
      btor_msg_exp (btor,
                    "UA: setting effective bit-width of %s to %d%s",
                    exp->symbol,
                    data->eff_width,
                    max_string);
    else
      btor_msg_exp (btor,
                    "UA: setting effective bit-width of read %d to %d%s",
                    exp->id,
                    data->eff_width,
                    max_string);
  }
}

static int
update_under_approx_eff_width (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorUARef ua_ref;
  BtorExp *cur, *min_exp;
  BtorUAData *data, *min_data;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  char *max_string;
  int update, e, verbosity, found_top;

  assert (btor != NULL);
  assert (btor->ua.enabled);

  ua_ref     = btor->ua.ref;
  verbosity  = btor->verbosity;
  update     = 0;
  found_top  = 0;
  min_data   = NULL;
  min_exp    = NULL;
  max_string = "";

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);

  if (btor->ua.mode == BTOR_UA_GLOBAL_MODE)
  {
    if (btor_failed_sat (smgr, btor->ua.global_last_e))
    {
      if (ua_ref == BTOR_UA_REF_BY_INC_ONE)
        btor->ua.global_eff_width++;
      else
      {
        assert (ua_ref == BTOR_UA_REF_BY_DOUBLING);
        btor->ua.global_eff_width *= 2;
      }

      /* check also for overflow */
      if (btor->ua.global_eff_width >= btor->ua.global_max_eff_width
          || btor->ua.global_eff_width <= 0)
      {
        max_string                = " (max)";
        btor->ua.global_eff_width = btor->ua.global_max_eff_width;
      }

      if (verbosity > 0)
        btor_msg_exp (btor,
                      "UA: setting global effective bit-width to %d%s",
                      btor->ua.global_eff_width,
                      max_string);
      update = 1;
    }
  }
  else if (btor->ua.mode == BTOR_UA_LOCAL_MODE)
  {
    for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
    {
      max_string = "";

      cur  = (BtorExp *) b->key;
      data = (BtorUAData *) b->data.asPtr;

      assert (!BTOR_IS_INVERTED_EXP (cur));
      assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

      e = data->last_e;

      if (e != 0 && btor_failed_sat (smgr, e))
      {
        update = 1;
        update_local_under_approx_eff_width (btor, cur, data);
      }
      else
        data->updated_eff_width = 0;
    }
  }
  else
  {
    assert (btor->ua.mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
    for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
    {
      max_string = "";

      cur                     = (BtorExp *) b->key;
      data                    = (BtorUAData *) b->data.asPtr;
      data->updated_eff_width = 0;

      assert (!BTOR_IS_INVERTED_EXP (cur));
      assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

      e = data->last_e;

      if (e == 0) continue;

      if (btor_fixed_sat (smgr, e) == -1)
      {
        found_top = 1;
        update    = 1;
        update_local_under_approx_eff_width (btor, cur, data);
      }
      else if (!found_top && btor_failed_sat (smgr, e))
      {
        if (min_data == NULL || data->eff_width < min_data->eff_width)
        {
          min_exp  = cur;
          min_data = data;
        }
      }
    }

    /* no assumption was top level assigned, so we refine the 'best fit' */
    if (!found_top)
    {
      if (min_data != NULL)
      {
        assert (min_exp != NULL);
        update = 1;
        update_local_under_approx_eff_width (btor, min_exp, min_data);
      }
      else
      {
        assert (min_exp == NULL);
        assert (update == 0);
      }
    }
  }

  return update;
}

static int
encode_under_approx_const_extend (Btor *btor, int phase)
{
  BtorSATMgr *smgr;
  BtorPtrHashBucket *b;
  BtorExp *cur;
  BtorAIG **aigs;
  int id, i, len, encoded, encoded_local;
  int eff_width      = 0;
  int under_approx_e = 0;
  BtorUAMode ua_mode;
  BtorUAData *data = NULL;

  assert (btor != NULL);
  assert (btor->ua.enabled);

  encoded = 0;
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  ua_mode = btor->ua.mode;

  if (ua_mode == BTOR_UA_GLOBAL_MODE) eff_width = btor->ua.global_eff_width;

  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

    if (!cur->reachable && !cur->vread && !cur->vread_index) continue;

    assert (cur->av != NULL);

    aigs = cur->av->aigs;
    assert (aigs != NULL);

    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      data = (BtorUAData *) b->data.asPtr;
      if (data->updated_eff_width == 0 && data->last_e != 0)
      {
        /* variable has not been refined, reassume e */
        btor_assume_sat (smgr, data->last_e);
        encoded = 1;
        continue;
      }

      eff_width = data->eff_width;

      /* disable previous clauses */
      if (data->last_e != 0)
      {
        btor_add_sat (smgr, -data->last_e);
        btor_add_sat (smgr, 0);
        data->last_e = 0;
      }
    }

    len = cur->len;
    if (eff_width >= len) continue;

    encoded_local = 0;
    for (i = len - eff_width - 1; i >= 0; i--)
    {
      if (BTOR_IS_CONST_AIG (aigs[i])) continue;

      id = aigs[i]->cnf_id;

      if (id == 0) continue;

      if (ua_mode == BTOR_UA_GLOBAL_MODE)
      {
        if (!encoded)
        {
          under_approx_e         = btor_next_cnf_id_sat_mgr (smgr);
          btor->ua.global_last_e = under_approx_e;
        }
      }
      else
      {
        assert (ua_mode == BTOR_UA_LOCAL_MODE
                || ua_mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
        if (!encoded_local)
        {
          under_approx_e = btor_next_cnf_id_sat_mgr (smgr);
          assert (data->last_e == 0);
          data->last_e  = under_approx_e;
          encoded_local = 1;
        }
      }

      encoded = 1;

      if (phase)
        btor_add_sat (smgr, id);
      else
        btor_add_sat (smgr, -id);

      btor_add_sat (smgr, -under_approx_e);
      btor_add_sat (smgr, 0);
    }

    if (encoded_local)
    {
      assert (ua_mode == BTOR_UA_LOCAL_MODE
              || ua_mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
      btor_assume_sat (smgr, under_approx_e);
    }
  }

  return encoded;
}

static int
encode_under_approx_zero_extend (Btor *btor)
{
  assert (btor != NULL);
  assert (btor->ua.enabled);
  return encode_under_approx_const_extend (btor, 0);
}

static int
encode_under_approx_one_extend (Btor *btor)
{
  assert (btor != NULL);
  assert (btor->ua.enabled);
  return encode_under_approx_const_extend (btor, 1);
}

static int
encode_under_approx_sign_extend (Btor *btor)
{
  BtorSATMgr *smgr;
  BtorPtrHashBucket *b;
  BtorExp *cur;
  BtorAIG **aigs;
  int encoded, encoded_local, len, i, id1, id2, first_pos;
  int eff_width      = 0;
  int under_approx_e = 0;
  BtorUAMode ua_mode;
  BtorUAData *data = NULL;

  assert (btor != NULL);
  assert (btor->ua.enabled);

  encoded = 0;
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  ua_mode = btor->ua.mode;

  if (ua_mode == BTOR_UA_GLOBAL_MODE) eff_width = btor->ua.global_eff_width;

  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

    if (!cur->reachable && !cur->vread && !cur->vread_index) continue;

    assert (cur->av != NULL);

    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      data = (BtorUAData *) b->data.asPtr;
      if (data->updated_eff_width == 0 && data->last_e != 0)
      {
        /* variable has not been refined, reassume e */
        btor_assume_sat (smgr, data->last_e);
        encoded = 1;
        continue;
      }

      eff_width = data->eff_width;

      /* disable previous clauses */
      if (data->last_e != 0)
      {
        btor_add_sat (smgr, -data->last_e);
        btor_add_sat (smgr, 0);
        data->last_e = 0;
      }
    }

    len = cur->len;
    if (eff_width >= len) continue;

    aigs = cur->av->aigs;
    assert (aigs != NULL);

    i = len - eff_width;
    while (i >= 0 && (BTOR_IS_CONST_AIG (aigs[i]) || aigs[i]->cnf_id == 0)) i--;

    if (i < 0) continue;

    first_pos = i;
    id1       = aigs[first_pos]->cnf_id;
    assert (id1 != 0);

    encoded_local = 0;
    for (i = first_pos - 1; i >= 0; i--)
    {
      if (BTOR_IS_CONST_AIG (aigs[i])) continue;

      id2 = aigs[i]->cnf_id;

      if (id2 == 0) continue;

      if (ua_mode == BTOR_UA_GLOBAL_MODE)
      {
        if (!encoded)
        {
          under_approx_e         = btor_next_cnf_id_sat_mgr (smgr);
          btor->ua.global_last_e = under_approx_e;
        }
      }
      else
      {
        assert (ua_mode == BTOR_UA_LOCAL_MODE
                || ua_mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
        if (!encoded_local)
        {
          under_approx_e = btor_next_cnf_id_sat_mgr (smgr);
          assert (data->last_e == 0);
          data->last_e  = under_approx_e;
          encoded_local = 1;
        }
      }

      encoded = 1;

      btor_add_sat (smgr, -id1);
      btor_add_sat (smgr, id2);
      btor_add_sat (smgr, -under_approx_e);
      btor_add_sat (smgr, 0);

      btor_add_sat (smgr, id1);
      btor_add_sat (smgr, -id2);
      btor_add_sat (smgr, -under_approx_e);
      btor_add_sat (smgr, 0);
    }

    if (encoded_local)
    {
      assert (ua_mode == BTOR_UA_LOCAL_MODE
              || ua_mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
      btor_assume_sat (smgr, under_approx_e);
    }
  }

  return encoded;
}

static void
encode_under_approx_eq_classes_aux (Btor *btor,
                                    BtorExp *cur,
                                    BtorUAData *data,
                                    int high,
                                    int low,
                                    int classes,
                                    int *under_approx_e,
                                    int *encoded)
{
  BtorSATMgr *smgr;
  BtorAIG **aigs;
  int i, id1, id2, first_pos, mid;
  BtorUAMode ua_mode;

  assert (btor != NULL);
  assert (cur != NULL);
  assert (btor->ua.mode == BTOR_UA_GLOBAL_MODE || data != NULL);
  assert (low >= 0);
  assert (high >= low);
  assert (encoded != NULL);

  if (classes <= 0) return;

  if (classes == 1)
  {
    smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
    ua_mode = btor->ua.mode;
    aigs    = cur->av->aigs;
    assert (aigs != NULL);

    i = high;
    while (i >= low && (BTOR_IS_CONST_AIG (aigs[i]) || aigs[i]->cnf_id == 0))
      i--;

    if (i < low) return;

    first_pos = i;
    id1       = aigs[first_pos]->cnf_id;
    assert (id1 != 0);

    for (i = first_pos - 1; i >= low; i--)
    {
      if (BTOR_IS_CONST_AIG (aigs[i])) continue;

      id2 = aigs[i]->cnf_id;

      if (id2 == 0) continue;

      if (ua_mode == BTOR_UA_GLOBAL_MODE)
      {
        if (!*under_approx_e)
        {
          *under_approx_e        = btor_next_cnf_id_sat_mgr (smgr);
          btor->ua.global_last_e = *under_approx_e;
        }
      }
      else
      {
        assert (ua_mode == BTOR_UA_LOCAL_MODE
                || ua_mode == BTOR_UA_LOCAL_INDIVIDUAL_MODE);
        if (!*under_approx_e)
        {
          *under_approx_e = btor_next_cnf_id_sat_mgr (smgr);
          assert (data->last_e == 0);
          data->last_e = *under_approx_e;
        }
      }

      *encoded = 1;

      btor_add_sat (smgr, -id1);
      btor_add_sat (smgr, id2);
      btor_add_sat (smgr, -*under_approx_e);
      btor_add_sat (smgr, 0);

      btor_add_sat (smgr, id1);
      btor_add_sat (smgr, -id2);
      btor_add_sat (smgr, -*under_approx_e);
      btor_add_sat (smgr, 0);
    }
  }
  else
  {
    mid = low + ((high - low) >> 1);
    classes >>= 1;
    encode_under_approx_eq_classes_aux (
        btor, cur, data, high, mid + 1, classes, under_approx_e, encoded);
    encode_under_approx_eq_classes_aux (
        btor, cur, data, mid, low, classes, under_approx_e, encoded);
  }
}

static int
encode_under_approx_eq_classes (Btor *btor)
{
  BtorSATMgr *smgr;
  BtorPtrHashBucket *b;
  BtorExp *cur;
  int encoded, len, under_approx_e;
  int eff_width = 0;
  BtorUAMode ua_mode;
  BtorUAData *data;

  assert (btor != NULL);
  assert (btor->ua.enabled);

  encoded = 0;
  data    = NULL;
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  ua_mode        = btor->ua.mode;
  under_approx_e = 0;

  if (ua_mode == BTOR_UA_GLOBAL_MODE) eff_width = btor->ua.global_eff_width;

  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

    if (!cur->reachable && !cur->vread && !cur->vread_index) continue;

    if (ua_mode != BTOR_UA_GLOBAL_MODE)
    {
      data = (BtorUAData *) b->data.asPtr;
      if (data->updated_eff_width == 0 && data->last_e != 0)
      {
        /* variable has not been refined, reassume e */
        btor_assume_sat (smgr, data->last_e);
        encoded = 1;
        continue;
      }

      eff_width = data->eff_width;

      /* disable previous clauses */
      if (data->last_e != 0)
      {
        btor_add_sat (smgr, -data->last_e);
        btor_add_sat (smgr, 0);
        data->last_e = 0;
      }
    }

    len = cur->len;
    if (eff_width >= len) continue;

    if (ua_mode != BTOR_UA_GLOBAL_MODE) under_approx_e = 0;

    encode_under_approx_eq_classes_aux (
        btor, cur, data, len - 1, 0, eff_width, &under_approx_e, &encoded);

    if (under_approx_e != 0 && ua_mode != BTOR_UA_GLOBAL_MODE)
      btor_assume_sat (smgr, under_approx_e);
  }

  return encoded;
}

static int
encode_under_approx (Btor *btor)
{
  int encoded;
  BtorSATMgr *smgr;

  assert (btor != NULL);
  assert (btor->ua.enabled);

  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));

  /* disable previous clauses */
  if (btor->ua.mode == BTOR_UA_GLOBAL_MODE && btor->ua.global_last_e != 0)
  {
    btor_add_sat (smgr, -btor->ua.global_last_e);
    btor_add_sat (smgr, 0);
  }

  switch (btor->ua.enc)
  {
    case BTOR_UA_ENC_ZERO_EXTEND:
      encoded = encode_under_approx_zero_extend (btor);
      break;
    case BTOR_UA_ENC_ONE_EXTEND:
      encoded = encode_under_approx_one_extend (btor);
      break;
    case BTOR_UA_ENC_SIGN_EXTEND:
      encoded = encode_under_approx_sign_extend (btor);
      break;
    default:
      assert (btor->ua.enc == BTOR_UA_ENC_EQ_CLASSES);
      encoded = encode_under_approx_eq_classes (btor);
      break;
  }

  if (encoded)
  {
    if (btor->ua.mode == BTOR_UA_GLOBAL_MODE)
      btor_assume_sat (smgr, btor->ua.global_last_e);
  }

  return encoded;
}

static void
synthesize_reads_and_writes_for_under_approx (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorExp *cur;

  assert (btor != NULL);

  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);

    if (cur->kind == BTOR_READ_EXP && (cur->reachable || cur->vread))
      lazy_synthesize_and_encode_acc_exp (btor, cur, 0);
  }

  for (b = btor->ua.writes_aconds->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_WRITE_EXP (cur) || BTOR_IS_ARRAY_COND_EXP (cur));

    if (cur->reachable)
    {
      if (BTOR_IS_WRITE_EXP (cur))
        lazy_synthesize_and_encode_acc_exp (btor, cur, 0);
      else
        lazy_synthesize_and_encode_acond_exp (btor, cur, 0);
    }
  }
}

void
btor_reset_effective_bit_widths (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorUAData *ua_data;
  BtorExp *cur;
  int count;

  assert (btor != NULL);

  if (!btor->ua.enabled) return;

  count = 0;
  for (b = btor->ua.vars_reads->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (!BTOR_IS_INVERTED_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur) || cur->kind == BTOR_READ_EXP);
    ua_data = b->data.asPtr;
    if (ua_data->eff_width > btor->ua.initial_eff_width)
    {
      ua_data->last_e    = 0;
      ua_data->eff_width = btor->ua.initial_eff_width;
      count++;
    }
  }
  btor_msg_exp (btor, "reset bit-width of %d reads and variables", count);
}

static void
synthesize_all_var_rhs (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorExp *cur, *real_cur;

  assert (btor != NULL);
  assert (btor->model_gen);

  for (b = btor->var_rhs->first; b != NULL; b = b->next)
  {
    cur      = (BtorExp *) b->key;
    cur      = btor_pointer_chase_simplified_exp (btor, cur);
    real_cur = BTOR_REAL_ADDR_EXP (cur);

    if (real_cur->vread) continue;

    synthesize_exp (btor, cur, NULL);

    if (!real_cur->sat_both_phases)
    {
      btor_aigvec_to_sat_both_phases (btor->avmgr, real_cur->av);
      real_cur->sat_both_phases = 1;
    }
  }
}

#if BTOR_ENABLE_PROBING_OPT

static int
probe_exps (Btor *btor)
{
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorPtrHashBucket *b;
  BtorExpPtrStack stack, new_constraints;
  BtorExp *cur;
  BtorMemMgr *mm;
  int ret_val, id, sat_result;

  assert (btor != NULL);

  mm      = btor->mm;
  ret_val = 0;
  amgr    = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr    = btor_get_sat_mgr_aig_mgr (amgr);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (new_constraints);

  for (b = btor->synthesized_constraints->first; b != NULL; b = b->next)
  {
    cur = BTOR_REAL_ADDR_EXP ((BtorExp *) b->key);
    goto PROBE_EXPS_ENTER_WITHOUT_POP;

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    PROBE_EXPS_ENTER_WITHOUT_POP:
      assert (cur->mark == 0 || cur->mark == 1);

      /* we only search through the boolean layer */
      if (cur->mark || cur->len != 1) continue;
      cur->mark = 1;

      if (cur->kind == BTOR_AND_EXP)
      {
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
        BTOR_PUSH_STACK (mm, stack, cur->e[1]);
      }
      else if (cur->kind == BTOR_BEQ_EXP)
      {
        /* we try to set bit-vector equality to false
         * if SAT solver can quickly decide
         * that this leads to unsat, then
         * the equality must be set to true
         * which may enable further substitutions
         * As our abstraction variables for reads
         * are over-approximating abstractions, this
         * also works for equalities between read values
         */
        assert (BTOR_IS_SYNTH_EXP (cur));
        assert (cur->len == 1);
        if (BTOR_IS_CONST_AIG (cur->av->aigs[0])) continue;

        id = BTOR_GET_CNF_ID_AIG (cur->av->aigs[0]);
        /* we do not want to introduce new clauses on the cnf layer,
         * so we skip probing here */
        if (!id) continue;

        btor_assume_sat (smgr, -id);
        sat_result = btor_sat_sat (smgr, BTOR_EXP_FAILED_EQ_LIMIT);
        assert (sat_result != BTOR_UNKNOWN);
        if (sat_result == BTOR_UNSAT)
        {
          BTOR_PUSH_STACK (mm, new_constraints, cur);
          btor->stats.probed_equalities++;
        }
      }
    }
  }

  /* reset mark flags */
  for (b = btor->synthesized_constraints->first; b != NULL; b = b->next)
    btor_mark_exp (btor, (BtorExp *) b->key, 0);

  ret_val = (int) BTOR_COUNT_STACK (new_constraints);
  while (!BTOR_EMPTY_STACK (new_constraints))
    btor_add_constraint_exp (btor, BTOR_POP_STACK (new_constraints));

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, new_constraints);
  return ret_val;
}

#endif

static void
eliminate_slices_on_bv_vars (Btor *btor)
{
  BtorExpPtrStack vars;
  BtorFullParentIterator it;
  BtorPtrHashBucket *b_var, *b1, *b2;
  BtorExp *var, *cur, *result, *lambda_var, *temp;
  BtorSlice *s1, *s2, *new_s1, *new_s2, *new_s3, **sorted_slices;
  BtorPtrHashTable *slices;
  BtorMemMgr *mm;
  int i, min, max;
  int vals[4];

  assert (btor != NULL);

  mm = btor->mm;
  BTOR_INIT_STACK (vars);
  for (b_var = btor->bv_vars->first; b_var != NULL; b_var = b_var->next)
  {
    var = (BtorExp *) b_var->key;
    BTOR_PUSH_STACK (mm, vars, var);
  }

  while (!BTOR_EMPTY_STACK (vars))
  {
    slices = btor_new_ptr_hash_table (
        mm, (BtorHashPtr) hash_slice, (BtorCmpPtr) compare_slices);
    var = BTOR_POP_STACK (vars);
    assert (BTOR_IS_REGULAR_EXP (var));
    assert (BTOR_IS_BV_VAR_EXP (var));
    init_full_parent_iterator (&it, var);
    /* find all slices on variable */
    while (has_next_parent_full_parent_iterator (&it))
    {
      cur = next_parent_full_parent_iterator (&it);
      assert (BTOR_IS_REGULAR_EXP (cur));
      if (cur->kind == BTOR_SLICE_EXP)
      {
        s1 = new_slice (btor, cur->upper, cur->lower);
        assert (!btor_find_in_ptr_hash_table (slices, s1));
        btor_insert_in_ptr_hash_table (slices, s1);
      }
    }

    /* no splitting necessary? */
    if (slices->count == 0u)
    {
      btor_delete_ptr_hash_table (slices);
      continue;
    }

    /* add full slice */
    s1 = new_slice (btor, var->len - 1, 0);
    assert (!btor_find_in_ptr_hash_table (slices, s1));
    btor_insert_in_ptr_hash_table (slices, s1);

  BTOR_SPLIT_SLICES_RESTART:
    for (b1 = slices->last; b1 != NULL; b1 = b1->prev)
    {
      s1 = (BtorSlice *) b1->key;
      for (b2 = b1->prev; b2 != NULL; b2 = b2->prev)
      {
        s2 = (BtorSlice *) b2->key;

        assert (compare_slices (s1, s2));

        /* not overlapping? */
        if ((s1->lower > s2->upper) || (s1->upper < s2->lower)
            || (s2->lower > s1->upper) || (s2->upper < s1->lower))
          continue;

        if (s1->upper == s2->upper)
        {
          assert (s1->lower != s2->lower);
          max    = BTOR_MAX_UTIL (s1->lower, s2->lower);
          min    = BTOR_MIN_UTIL (s1->lower, s2->lower);
          new_s1 = new_slice (btor, max - 1, min);
          if (!btor_find_in_ptr_hash_table (slices, new_s1))
            btor_insert_in_ptr_hash_table (slices, new_s1);
          else
            delete_slice (btor, new_s1);

          if (min == s1->lower)
          {
            btor_remove_from_ptr_hash_table (slices, s1, NULL, NULL);
            delete_slice (btor, s1);
          }
          else
          {
            btor_remove_from_ptr_hash_table (slices, s2, NULL, NULL);
            delete_slice (btor, s2);
          }
          goto BTOR_SPLIT_SLICES_RESTART;
        }

        if (s1->lower == s2->lower)
        {
          assert (s1->upper != s2->upper);
          max    = BTOR_MAX_UTIL (s1->upper, s2->upper);
          min    = BTOR_MIN_UTIL (s1->upper, s2->upper);
          new_s1 = new_slice (btor, max, min + 1);
          if (!btor_find_in_ptr_hash_table (slices, new_s1))
            btor_insert_in_ptr_hash_table (slices, new_s1);
          else
            delete_slice (btor, new_s1);
          if (max == s1->upper)
          {
            btor_remove_from_ptr_hash_table (slices, s1, NULL, NULL);
            delete_slice (btor, s1);
          }
          else
          {
            btor_remove_from_ptr_hash_table (slices, s2, NULL, NULL);
            delete_slice (btor, s2);
          }
          goto BTOR_SPLIT_SLICES_RESTART;
        }

        /* regular overlapping case (overlapping at both ends) */
        vals[0] = s1->upper;
        vals[1] = s1->lower;
        vals[2] = s2->upper;
        vals[3] = s2->lower;
        qsort (vals, 4, sizeof (int), compare_int_ptr);
        new_s1 = new_slice (btor, vals[3], vals[2] + 1);
        new_s2 = new_slice (btor, vals[2], vals[1]);
        new_s3 = new_slice (btor, vals[1] - 1, vals[0]);
        btor_remove_from_ptr_hash_table (slices, s1, NULL, NULL);
        btor_remove_from_ptr_hash_table (slices, s2, NULL, NULL);
        delete_slice (btor, s1);
        delete_slice (btor, s2);
        if (!btor_find_in_ptr_hash_table (slices, new_s1))
          btor_insert_in_ptr_hash_table (slices, new_s1);
        else
          delete_slice (btor, new_s1);
        if (!btor_find_in_ptr_hash_table (slices, new_s2))
          btor_insert_in_ptr_hash_table (slices, new_s2);
        else
          delete_slice (btor, new_s2);
        if (!btor_find_in_ptr_hash_table (slices, new_s3))
          btor_insert_in_ptr_hash_table (slices, new_s3);
        else
          delete_slice (btor, new_s3);
        goto BTOR_SPLIT_SLICES_RESTART;
      }
    }

    /* copy slices to sort them */
    assert (slices->count > 1u);
    BTOR_NEWN (mm, sorted_slices, slices->count);
    i = 0;
    for (b1 = slices->first; b1 != NULL; b1 = b1->next)
    {
      s1                 = (BtorSlice *) b1->key;
      sorted_slices[i++] = s1;
    }
    qsort (sorted_slices,
           slices->count,
           sizeof (BtorSlice *),
           compare_slices_qsort);

    s1 = sorted_slices[(int) slices->count - 1];
    /* printf ("[%d:%d]\n", s1->upper, s1->lower); */
    result = lambda_var_exp (btor, s1->upper - s1->lower + 1);
    delete_slice (btor, s1);
    for (i = (int) slices->count - 2; i >= 0; i--)
    {
      s1         = sorted_slices[i];
      lambda_var = lambda_var_exp (btor, s1->upper - s1->lower + 1);
      temp       = btor_concat_exp (btor, result, lambda_var);
      btor_release_exp (btor, result);
      result = temp;
      btor_release_exp (btor, lambda_var);
      /* printf ("[%d:%d]\n", s1->upper, s1->lower); */
      delete_slice (btor, s1);
    }
    BTOR_DELETEN (mm, sorted_slices, slices->count);
    btor_delete_ptr_hash_table (slices);
    /* printf ("\n"); */

    insert_varsubst_constraint (btor, var, result);
    btor_release_exp (btor, result);
  }

  BTOR_RELEASE_STACK (mm, vars);
}

static int
restrict_domain_of_eq_class (Btor *btor, BtorPtrHashTable *eq)
{
  BtorPtrHashBucket *b;
  BtorExp *cur, *lambda_var;
  int min_len;

  assert (btor != NULL);
  assert (eq != NULL);
  assert (btor->rewrite_level > 2);
  assert (!btor->inc_enabled);
  assert (!btor->model_gen);

  if (eq->count <= 1u) return 0;

  min_len = btor_log_2_util (btor_next_power_of_2_util ((int) eq->count));
  cur     = BTOR_REAL_ADDR_EXP ((BtorExp *) eq->first->key);
  if (min_len >= cur->len) return 0;

  /* perform uniform domain abstraction */
  for (b = eq->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (BTOR_REAL_ADDR_EXP (cur)->len > 1);
    if (!btor_find_in_ptr_hash_table (btor->varsubst_constraints,
                                      BTOR_REAL_ADDR_EXP (cur)))
    {
      lambda_var = lambda_var_exp (btor, min_len);
      insert_varsubst_constraint (btor, BTOR_REAL_ADDR_EXP (cur), lambda_var);
      btor_release_exp (btor, lambda_var);
      btor->stats.domain_abst++;
    }
  }
  return 1;
}

static void
abstract_domain_bv_variables (Btor *btor)
{
  BtorFullParentIterator it;
  BtorMemMgr *mm;
  BtorExpPtrStack stack, vars;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *eq, *marked;
  BtorExp *cur, *cur_parent, *next;
  int i;

  assert (btor != NULL);
  assert (btor->rewrite_level > 2);
  assert (!btor->inc_enabled);
  assert (!btor->model_gen);
  assert (btor->assumptions->count == 0u);
  assert (btor->varsubst_constraints->count == 0u);
  assert (btor->embedded_constraints->count == 0u);
  assert (btor->synthesized_constraints->count == 0u);

  mm = btor->mm;
  BTOR_INIT_STACK (vars);
  BTOR_INIT_STACK (stack);

  for (b = btor->bv_vars->first; b != NULL; b = b->next)
  {
    cur = (BtorExp *) b->key;
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur));
    BTOR_PUSH_STACK (mm, vars, cur);
  }

  marked = btor_new_ptr_hash_table (mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

  for (i = 0; i < BTOR_COUNT_STACK (vars); i++)
  {
    cur = vars.start[i];

    /* boolean variables cannot be abstracted further */
    if (cur->len == 1) continue;

    if (btor_find_in_ptr_hash_table (marked, cur)) continue;

    assert (BTOR_EMPTY_STACK (stack));
    eq = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
    btor_insert_in_ptr_hash_table (eq, cur);
    goto BTOR_ABSTRACT_DOMAIN_BV_VARS_ENTER_WITHOUT_POP;

    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_POP_STACK (stack);
      assert (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (cur)));

      if (btor_find_in_ptr_hash_table (marked, cur))
        goto BTOR_ABSTRACT_DOMAIN_BV_VARS_CLEANUP;

    BTOR_ABSTRACT_DOMAIN_BV_VARS_ENTER_WITHOUT_POP:
      assert (btor_find_in_ptr_hash_table (eq, cur));
      init_full_parent_iterator (&it, cur);
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        if (BTOR_IS_BV_EQ_EXP (cur_parent))
        {
          /* we assume that rewriting rules have already simplified
           * x = x, and x = ~x
           */
          if (BTOR_REAL_ADDR_EXP (cur_parent->e[0]) == BTOR_REAL_ADDR_EXP (cur))
          {
            next = cur_parent->e[1];
          }
          else
          {
            assert (BTOR_REAL_ADDR_EXP (cur_parent->e[1])
                    == BTOR_REAL_ADDR_EXP (cur));
            next = cur_parent->e[0];
          }

          if (BTOR_IS_BV_VAR_EXP (BTOR_REAL_ADDR_EXP (next)))
          {
            if (!btor_find_in_ptr_hash_table (eq, next))
            {
              btor_insert_in_ptr_hash_table (eq, next);
              BTOR_PUSH_STACK (mm, stack, next);
            }
          }
          else
            goto BTOR_ABSTRACT_DOMAIN_BV_VARS_CLEANUP;
        }
        else
          goto BTOR_ABSTRACT_DOMAIN_BV_VARS_CLEANUP;
      }
    }

    restrict_domain_of_eq_class (btor, eq);

  BTOR_ABSTRACT_DOMAIN_BV_VARS_CLEANUP:
    BTOR_RESET_STACK (stack);

    for (b = eq->first; b != NULL; b = b->next)
    {
      cur = (BtorExp *) b->key;
      if (!btor_find_in_ptr_hash_table (marked, cur))
        btor_insert_in_ptr_hash_table (marked, cur);
    }
    btor_delete_ptr_hash_table (eq);
  }

  /* cleanup */
  btor_delete_ptr_hash_table (marked);
  BTOR_RELEASE_STACK (mm, vars);
  BTOR_RELEASE_STACK (mm, stack);
}

int
btor_sat_btor (Btor *btor)
{
  int sat_result, found_conflict, found_constraint_false, verbosity;
  int found_assumption_false, under_approx_finished, ua;
  BtorExpPtrStack top_arrays;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (btor->btor_sat_btor_called >= 0);
  assert (btor->inc_enabled || btor->btor_sat_btor_called == 0);
  btor->btor_sat_btor_called++;

  verbosity             = btor->verbosity;
  ua                    = btor->ua.enabled;
  under_approx_finished = 0;

  if (btor->inconsistent) return BTOR_UNSAT;

  if (verbosity > 0) btor_msg_exp (btor, "calling SAT");

  run_rewrite_engine (btor, 1);

  if (btor->inconsistent) return BTOR_UNSAT;

  mm = btor->mm;

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  if (!btor_is_initialized_sat (smgr)) btor_init_sat (smgr, btor->inc_enabled);

  if (btor->valid_assignments == 1) btor_reset_incremental_usage (btor);
  btor->valid_assignments = 1;

  assert (check_all_hash_tables_proxy_free_dbg (btor));
  found_constraint_false = process_unsynthesized_constraints (btor);
  assert (check_all_hash_tables_proxy_free_dbg (btor));

  if (found_constraint_false) return BTOR_UNSAT;

  if (btor->model_gen) synthesize_all_var_rhs (btor);

  assert (btor->unsynthesized_constraints->count == 0u);

#if BTOR_ENABLE_PROBING_OPT
  if (!ua && !btor->inc_enabled && btor->rewrite_level > 2)
  {
    if (probe_exps (btor))
    {
      run_rewrite_engine (btor, 0);
      if (btor->inconsistent) return BTOR_UNSAT;
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      found_constraint_false = process_unsynthesized_constraints (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      if (found_constraint_false) return BTOR_UNSAT;
    }
  }
#endif

  /* pointer chase assumptions */
  update_assumptions (btor);

  found_assumption_false = add_again_assumptions (btor);
  if (found_assumption_false) return BTOR_UNSAT;

  if (ua)
  {
    synthesize_reads_and_writes_for_under_approx (btor);
    if (btor->ua.mode == BTOR_UA_GLOBAL_MODE)
      btor->ua.global_max_eff_width = max_len_global_under_approx_vars (btor);
    under_approx_finished = !encode_under_approx (btor);
  }

  sat_result = btor_sat_sat (smgr);
  assert (sat_result != BTOR_UNKNOWN);

  BTOR_INIT_STACK (top_arrays);
  search_top_arrays (btor, &top_arrays);

  while (sat_result == BTOR_SAT
         || (ua && !under_approx_finished && sat_result != BTOR_UNKNOWN))
  {
    if (sat_result == BTOR_SAT)
    {
      found_conflict = check_and_resolve_conflicts (btor, &top_arrays);

      if (!found_conflict) break;

      btor->stats.lod_refinements++;
      found_assumption_false = add_again_assumptions (btor);
      assert (!found_assumption_false);

      if (ua && !under_approx_finished) read_under_approx_assumptions (btor);
    }
    else
    {
      assert (sat_result == BTOR_UNSAT);
      assert (ua);
      assert (!under_approx_finished);

      if (btor_inconsistent_sat (smgr) || !update_under_approx_eff_width (btor))
      {
        if (verbosity >= 2)
        {
          btor_msg_exp (btor,
                        "early termination of under-approximation refinement "
                        "in UNSAT case");
          btor_msg_exp (btor,
                        "current under-approximation has not been used to "
                        "conclude UNSAT");
        }
        break;
      }

      under_approx_finished = !encode_under_approx (btor);
      btor->stats.ua_refinements++;
    }
    if (verbosity > 1)
    {
      if (verbosity > 2
          || !((btor->stats.lod_refinements + btor->stats.ua_refinements) % 10))
      {
        fprintf (stdout,
                 "[btorsat] refinement iteration %d\n",
                 btor->stats.lod_refinements + btor->stats.ua_refinements);
        fflush (stdout);
      }
    }
    found_assumption_false = add_again_assumptions (btor);
    if (found_assumption_false)
      sat_result = BTOR_UNSAT;
    else
    {
      sat_result = btor_sat_sat (smgr);
      assert (sat_result != BTOR_UNKNOWN);
    }
  }

  BTOR_RELEASE_STACK (mm, top_arrays);
  BTOR_ABORT_EXP (sat_result != BTOR_SAT && sat_result != BTOR_UNSAT,
                  "result must be sat or unsat");
  return sat_result;
}

char *
btor_bv_assignment_exp (Btor *btor, BtorExp *exp)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *av;
  BtorExp *real_exp;
  char *assignment;
  int invert_av, invert_bits;

  assert (btor != NULL);
  assert (exp != NULL);
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));

  real_exp = BTOR_REAL_ADDR_EXP (exp);

  if (BTOR_IS_BV_CONST_EXP (real_exp))
  {
    invert_bits = BTOR_IS_INVERTED_EXP (exp);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_EXP (exp)->bits);
    assignment = btor_copy_const (btor->mm, BTOR_REAL_ADDR_EXP (exp)->bits);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_EXP (exp)->bits);
  }
  else if ((!real_exp->reachable || !BTOR_IS_SYNTH_EXP (real_exp))
           && !real_exp->vread)
  {
    assignment = btor_x_const_3vl (btor->mm, real_exp->len);
  }
  else
  {
    avmgr     = btor->avmgr;
    invert_av = BTOR_IS_INVERTED_EXP (exp);
    av        = BTOR_REAL_ADDR_EXP (exp)->av;
    if (invert_av) btor_invert_aigvec (avmgr, av);
    assignment = btor_assignment_aigvec (avmgr, av);
    /* invert back if necessary */
    if (invert_av) btor_invert_aigvec (avmgr, av);
  }

  return assignment;
}

void
btor_array_assignment_exp (
    Btor *btor, BtorExp *exp, char ***indices, char ***values, int *size)
{
  BtorPtrHashBucket *b;
  BtorExp *index, *value;
  int i;

  assert (btor != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (BTOR_IS_ARRAY_EXP (exp));
  assert (indices != NULL);
  assert (values != NULL);
  assert (size != NULL);

  i = 0;

  if (exp->rho == NULL)
  {
    *size = 0;
    return;
  }

  *size = (int) exp->rho->count;
  if (*size > 0)
  {
    BTOR_NEWN (btor->mm, *indices, *size);
    BTOR_NEWN (btor->mm, *values, *size);

    for (b = exp->rho->first; b != NULL; b = b->next)
    {
      index         = (BtorExp *) b->key;
      value         = BTOR_GET_VALUE_ACC_EXP ((BtorExp *) b->data.asPtr);
      (*indices)[i] = btor_bv_assignment_exp (btor, index);
      (*values)[i]  = btor_bv_assignment_exp (btor, value);
      i++;
    }
  }
}

void
btor_free_bv_assignment_exp (Btor *btor, char *assignment)
{
  assert (btor != NULL);
  assert (assignment != NULL);
  btor_freestr (btor->mm, assignment);
}

const char *
btor_version (Btor *btor)
{
  assert (btor != NULL);
  (void) btor;
  return BTOR_VERSION;
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
