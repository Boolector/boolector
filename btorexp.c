/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorexp.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbeta.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btorlog.h"
#include "btormisc.h"
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

// #define BTOR_DO_NOT_ELIMINATE_SLICES

#ifndef BTOR_USE_LINGELING
#define BTOR_DO_NOT_PROCESS_SKELETON
#endif

/*------------------------------------------------------------------------*/

enum BtorSubstCompKind
{
  BTOR_SUBST_COMP_ULT_KIND,
  BTOR_SUBST_COMP_ULTE_KIND,
  BTOR_SUBST_COMP_UGT_KIND,
  BTOR_SUBST_COMP_UGTE_KIND
};

typedef enum BtorSubstCompKind BtorSubstCompKind;

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

#define BTOR_INIT_UNIQUE_TABLE(mm, table) \
  do                                      \
  {                                       \
    assert (mm);                          \
    (table).size         = 1;             \
    (table).num_elements = 0;             \
    BTOR_CNEW (mm, (table).chains);       \
  } while (0)

#define BTOR_RELEASE_UNIQUE_TABLE(mm, table)         \
  do                                                 \
  {                                                  \
    assert (mm);                                     \
    BTOR_DELETEN (mm, (table).chains, (table).size); \
  } while (0)

#define BTOR_UNIQUE_TABLE_LIMIT 30

#define BTOR_NODE_UNIQUE_TABLE_PRIME 2000000137u

#define BTOR_FULL_UNIQUE_TABLE(table)   \
  ((table).num_elements >= (table).size \
   && btor_log_2_util ((table).size) < BTOR_UNIQUE_TABLE_LIMIT)

#define BTOR_COND_INVERT_AIG_NODE(exp, aig) \
  ((BtorAIG *) (((unsigned long int) (exp) &1ul) ^ ((unsigned long int) (aig))))

#define MARK_PROP_UP(exp) ((BtorNode *) (1ul | (unsigned long int) (exp)))
#define PROPAGATED_UPWARDS(exp) (1ul & (unsigned long int) (exp)->parent)

/*------------------------------------------------------------------------*/

static void add_constraint (Btor *, BtorNode *);

static void run_rewrite_engine (Btor *);

static void rewrite_writes_to_lambda_exp (Btor *);
static BtorNode *rewrite_write_to_lambda_exp (Btor *, BtorNode *);

static int exp_to_cnf_lit (Btor *, BtorNode *);

#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
static void eliminate_slices_on_bv_vars (Btor *);
#endif

static void dump_node (FILE *file, BtorNode *node);
static void beta_reduce_reads_on_lambdas (Btor *);
static int bfs_lambda (
    Btor *, BtorNode *, BtorNode *, BtorNode *, BtorNode **, int);

static void init_cache (Btor *);
static void release_cache (Btor *);

/*------------------------------------------------------------------------*/

static const char *const g_op2string[] = {
    "invalid", "const",  "var",  "array", "slice", "and",   "beq",
    "aeq",     "add",    "mul",  "ult",   "sll",   "srl",   "udiv",
    "urem",    "concat", "read", "write", "bcond", "acond", "proxy"};

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

static int
check_unique_table_children_proxy_free_dbg (const Btor *btor)
{
  int i, j;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      for (j = 0; j < cur->arity; j++)
        if (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (cur->e[j]))) return 0;
  return 1;
}

static int
check_unique_table_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      if (cur->mark != 0) return 0;
  return 1;
}

static int
check_unique_table_aux_mark_unset_dbg (const Btor *btor)
{
  int i;
  BtorNode *cur;

  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (cur = btor->nodes_unique_table.chains[i]; cur; cur = cur->next)
      if (cur->aux_mark != 0) return 0;
  return 1;
}

static int
check_hash_table_proxy_free_dbg (const BtorPtrHashTable *table)
{
  BtorPtrHashBucket *b;
  for (b = table->first; b; b = b->next)
    if (BTOR_REAL_ADDR_NODE (b->key)->kind == BTOR_PROXY_NODE) return 0;
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

static int
check_hash_table_simp_free_dbg (const BtorPtrHashTable *table,
                                const char *table_name)
{
  BtorPtrHashBucket *b;
  (void) table_name;
  for (b = table->first; b; b = b->next)
    if (BTOR_REAL_ADDR_NODE (b->key)->simplified) return 0;
  return 1;
}

static int
check_all_hash_tables_simp_free_dbg (const Btor *btor)
{
  if (!check_hash_table_simp_free_dbg (btor->varsubst_constraints,
                                       "varsubst_constraints"))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->embedded_constraints,
                                       "embedded_constraints"))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->unsynthesized_constraints,
                                       "unsynthesized_constraints"))
    return 0;
  if (!check_hash_table_simp_free_dbg (btor->synthesized_constraints,
                                       "synthesized_constraints"))
    return 0;
  return 1;
}

int
btor_precond_slice_exp_dbg (const Btor *btor,
                            const BtorNode *exp,
                            int upper,
                            int lower)
{
  assert (btor);
  assert (exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->simplified);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_NODE (exp)->len);
  assert (BTOR_REAL_ADDR_NODE (exp)->len > 0);
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
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len > 0);
  return 1;
}

int
btor_precond_eq_exp_dbg (const Btor *btor,
                         const BtorNode *e0,
                         const BtorNode *e1)
{
  int is_array_e0, is_array_e1;
  BtorNode *real_e0, *real_e1;

  assert (btor);
  assert (e0);
  assert (e1);

  real_e0     = BTOR_REAL_ADDR_NODE (e0);
  real_e1     = BTOR_REAL_ADDR_NODE (e1);
  is_array_e0 = BTOR_IS_ARRAY_NODE (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_NODE (real_e1);

  assert (real_e0);
  assert (real_e1);
  assert (!real_e0->simplified);
  assert (!real_e1->simplified);
  assert (is_array_e0 == is_array_e1);
  assert (real_e0->len == real_e1->len);
  assert (real_e0->len > 0);
  assert (!is_array_e0 || real_e0->index_len == real_e1->index_len);
  assert (!is_array_e0 || real_e0->index_len > 0);
  assert (!is_array_e0
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
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (e1)->len > 0);
  assert (BTOR_REAL_ADDR_NODE (e0)->len
          <= INT_MAX - BTOR_REAL_ADDR_NODE (e1)->len);
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
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->len > 1);
  assert (BTOR_REAL_ADDR_NODE (e1)->len > 0);
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_NODE (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_NODE (e0)->len)
          == BTOR_REAL_ADDR_NODE (e1)->len);
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
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e0)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e1)));
  assert (BTOR_REAL_ADDR_NODE (e0)->len == BTOR_REAL_ADDR_NODE (e1)->len);
  assert (BTOR_REAL_ADDR_NODE (e0)->len > 0);
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
  assert (BTOR_IS_ARRAY_NODE (e_array));
  assert (!e_array->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_index)->simplified);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_index)));
  assert (BTOR_REAL_ADDR_NODE (e_index)->len > 0);
  assert (e_array->len > 0);
  assert (BTOR_IS_LAMBDA_NODE (e_array)
          || e_array->index_len == BTOR_REAL_ADDR_NODE (e_index)->len);
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
  assert (BTOR_IS_ARRAY_NODE (e_array));
  assert (!e_array->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_index)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e_value)->simplified);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_index)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_value)));
  assert (e_array->index_len == BTOR_REAL_ADDR_NODE (e_index)->len);
  assert (BTOR_REAL_ADDR_NODE (e_index)->len > 0);
  assert (e_array->len == BTOR_REAL_ADDR_NODE (e_value)->len);
  assert (BTOR_REAL_ADDR_NODE (e_value)->len > 0);
  return 1;
}

int
btor_precond_cond_exp_dbg (const Btor *btor,
                           const BtorNode *e_cond,
                           const BtorNode *e_if,
                           const BtorNode *e_else)
{
  BtorNode *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;

  assert (btor);
  assert (e_cond);
  assert (e_if);
  assert (e_else);
  assert (!BTOR_REAL_ADDR_NODE (e_cond)->simplified);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_cond)));
  assert (BTOR_REAL_ADDR_NODE (e_cond)->len == 1);

  real_e_if   = BTOR_REAL_ADDR_NODE (e_if);
  real_e_else = BTOR_REAL_ADDR_NODE (e_else);

  assert (!real_e_if->simplified);
  assert (!real_e_else->simplified);

  is_array_e_if   = BTOR_IS_ARRAY_NODE (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_NODE (real_e_else);

  assert (is_array_e_if == is_array_e_else);
  assert (real_e_if->len == real_e_else->len);
  assert (real_e_if->len > 0);
  assert (!is_array_e_if
          || (BTOR_IS_REGULAR_NODE (e_if) && BTOR_IS_REGULAR_NODE (e_else)));
  assert (!is_array_e_if || e_if->index_len == e_else->index_len);
  assert (!is_array_e_if || e_if->index_len > 0);
  return 1;
}

static int
has_num_parents_dbg (BtorNode *exp, int num)
{
  assert (exp);
  assert (num > 0);

  int num_parents = 0;
  BtorFullParentIterator it;

  init_full_parent_iterator (&it, exp);

  while (has_next_parent_full_parent_iterator (&it))
  {
    (void) next_parent_full_parent_iterator (&it);
    num_parents++;

    if (num_parents > num) break;
  }

  return num_parents == num;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
btor_msg_exp (Btor *btor, char *fmt, ...)
{
  va_list ap;
  fputs ("[btorexp] ", stdout);
  if (btor->inc_enabled && btor->msgtick >= 0)
    printf ("%d : ", (int) btor->msgtick);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/
static void
btor_init_substitutions (Btor *btor)
{
  assert (btor);
  assert (!btor->substitutions);

  btor->substitutions =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
btor_delete_substitutions (Btor *btor)
{
  assert (btor);

  BtorPtrHashBucket *b;

  for (b = btor->substitutions->first; b; b = b->next)
  {
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
    btor_release_exp (btor, (BtorNode *) b->key);
  }

  btor_delete_ptr_hash_table (btor->substitutions);
  btor->substitutions = 0;
}

static void
btor_insert_substitution (Btor *btor, BtorNode *exp, BtorNode *subst)
{
  assert (btor);
  assert (exp);
  assert (subst);
  assert (btor->substitutions);

  // TODO: maybe overwrite existing substitutions?
  assert (!btor_find_in_ptr_hash_table (btor->substitutions,
                                        BTOR_REAL_ADDR_NODE (exp)));

  btor_insert_in_ptr_hash_table (
      btor->substitutions, btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (exp)))
      ->data.asPtr = btor_copy_exp (btor, subst);
}

static BtorNode *
btor_find_substitution (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *result;
  BtorPtrHashBucket *bucket;

  if (!btor->substitutions) return 0;

  bucket = btor_find_in_ptr_hash_table (btor->substitutions,
                                        BTOR_REAL_ADDR_NODE (exp));

  if (!bucket) return 0;

  result = btor_simplify_exp (btor, (BtorNode *) bucket->data.asPtr);

  if (BTOR_IS_INVERTED_NODE (exp)) return BTOR_INVERT_NODE (result);
  return result;
}

static void
inc_sort_ref_counter (Btor *btor, BtorSort *sort)
{
  assert (btor);
  assert (sort);
  (void) btor;
  BTOR_ABORT_NODE (sort->refs == INT_MAX, "Sort reference counter overflow");
  sort->refs++;
}

BtorSort *
btor_copy_sort (Btor *btor, BtorSort *sort)
{
  inc_sort_ref_counter (btor, sort);
  return sort;
}

static unsigned
compute_hash_sort (BtorSort *sort, int table_size)
{
  unsigned res, tmp;

  assert (sort);
  assert (table_size);
  assert (btor_is_power_of_2_util (table_size));

  tmp = 0;

  switch (sort->kind)
  {
    default:
    case BTOR_BOOL_SORT:
      assert (sort->kind == BTOR_BOOL_SORT);
      res = 0;
      break;

    case BTOR_BITVEC_SORT: res = (unsigned int) sort->bitvec.len; break;

    case BTOR_ARRAY_SORT:
      res = (unsigned int) sort->array.index->id;
      tmp = (unsigned int) sort->array.element->id;
      break;

    case BTOR_LST_SORT:
      res = (unsigned int) sort->lst.head->id;
      tmp = (unsigned int) sort->lst.tail->id;
      break;

    case BTOR_FUN_SORT:
      res = (unsigned int) sort->fun.domain->id;
      tmp = (unsigned int) sort->fun.codomain->id;
      break;
  }

  res *= 444555667u;

  if (tmp)
  {
    res += tmp;
    res *= 123123137u;
  }

  res &= table_size - 1;

  return res;
}

static void
remove_from_sorts_unique_table_sort (Btor *btor, BtorSort *sort)
{
  unsigned int hash;
  BtorSort *prev, *cur;

  assert (btor);
  assert (sort);
  assert (!sort->refs);
  assert (btor->sorts_unique_table.num_elements > 0);

  hash = compute_hash_sort (sort, btor->sorts_unique_table.size);
  prev = 0;
  cur  = btor->sorts_unique_table.chains[hash];

  while (cur != sort)
  {
    assert (cur);
    prev = cur;
    cur  = cur->next;
  }

  assert (cur);
  if (!prev)
    btor->sorts_unique_table.chains[hash] = cur->next;
  else
    prev->next = cur->next;

  btor->sorts_unique_table.num_elements--;
}

static int
equal_sort (const BtorSort *a, const BtorSort *b)
{
  assert (a);
  assert (b);

  if (a->kind != b->kind) return 0;

  switch (a->kind)
  {
    case BTOR_BOOL_SORT:
    default: assert (a->kind == BTOR_BOOL_SORT); break;

    case BTOR_BITVEC_SORT:
      if (a->bitvec.len != b->bitvec.len) return 0;
      break;

    case BTOR_ARRAY_SORT:
      if (a->array.index != b->array.index) return 0;
      if (a->array.element != b->array.element) return 0;
      break;

    case BTOR_LST_SORT:
      if (a->lst.head != b->lst.head) return 0;
      if (a->lst.tail != b->lst.tail) return 0;
      break;

    case BTOR_FUN_SORT:
      if (a->fun.domain != b->fun.domain) return 0;
      if (a->fun.codomain != b->fun.codomain) return 0;
      break;
  }

  return 1;
}

static BtorSort **
find_sort (Btor *btor, BtorSort *pattern)
{
  BtorSort **res, *sort;
  unsigned int hash;
  assert (btor);
  assert (pattern);
  hash = compute_hash_sort (pattern, btor->sorts_unique_table.size);
  assert (hash < (unsigned) btor->sorts_unique_table.size);
  for (res = btor->sorts_unique_table.chains + hash;
       (sort = *res) && !equal_sort (sort, pattern);
       res = &sort->next)
    assert (sort->refs > 0);
  return res;
}

// static // TODO remove comment and add back 'static'
void
enlarge_sorts_unique_table (Btor *btor)
{
  BtorSort *cur, *temp, **new_chains;
  int size, new_size, i;
  unsigned int hash;
  BtorMemMgr *mm;
  assert (btor);
  if (BTOR_FULL_UNIQUE_TABLE (btor->sorts_unique_table))
    enlarge_sorts_unique_table (btor);
  mm       = btor->mm;
  size     = btor->sorts_unique_table.size;
  new_size = size << 1;
  assert (new_size / size == 2);
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = btor->sorts_unique_table.chains[i];
    while (cur)
    {
      temp             = cur->next;
      hash             = compute_hash_sort (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BTOR_DELETEN (mm, btor->sorts_unique_table.chains, size);
  btor->sorts_unique_table.size   = new_size;
  btor->sorts_unique_table.chains = new_chains;
}

static void
release_sort (Btor *btor, BtorSort *sort)
{
  assert (btor);
  assert (sort);
  assert (sort->refs > 0);

  if (--sort->refs > 0) return;

  switch (sort->kind)
  {
    default: break;

    case BTOR_LST_SORT:
      release_sort (btor, sort->lst.head);
      release_sort (btor, sort->lst.tail);
      break;

    case BTOR_ARRAY_SORT:
      release_sort (btor, sort->array.index);
      release_sort (btor, sort->array.element);
      break;

    case BTOR_FUN_SORT:
      release_sort (btor, sort->fun.domain);
      release_sort (btor, sort->fun.codomain);
      break;
  }

  remove_from_sorts_unique_table_sort (btor, sort);
  BTOR_DELETE (btor->mm, sort);
}

void
btor_release_sort (Btor *btor, BtorSort *sort)
{
  assert (btor);
  assert (sort);
  assert (sort->refs > 0);
  release_sort (btor, sort);
}

BtorSort *
btor_bool_sort (Btor *btor)
{
  BtorSort *res, **pos, pattern;
  assert (btor);
  BTOR_CLR (&pattern);
  pattern.kind = BTOR_BOOL_SORT;
  pos          = find_sort (btor, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    BTOR_NEW (btor->mm, res);
    BTOR_CLR (res);
    res->kind = BTOR_BOOL_SORT;
    *pos      = res;
  }
  inc_sort_ref_counter (btor, res);
  return res;
}

BtorSort *
btor_bitvec_sort (Btor *btor, int len)
{
  BtorSort *res, **pos, pattern;
  assert (btor);
  assert (len > 0);
  BTOR_CLR (&pattern);
  pattern.kind       = BTOR_BITVEC_SORT;
  pattern.bitvec.len = len;
  pos                = find_sort (btor, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    BTOR_NEW (btor->mm, res);
    BTOR_CLR (res);
    res->kind       = BTOR_BOOL_SORT;
    res->bitvec.len = len;
    *pos            = res;
  }
  inc_sort_ref_counter (btor, res);
  return res;
}

BtorSort *
btor_array_sort (Btor *btor, BtorSort *index, BtorSort *element)
{
  BtorSort *res, **pos, pattern;
  assert (btor);
  assert (index);
  assert (index->refs > 0);
  assert (element);
  assert (element->refs > 0);
  BTOR_CLR (&pattern);
  pattern.kind          = BTOR_ARRAY_SORT;
  pattern.array.index   = index;
  pattern.array.element = element;
  pos                   = find_sort (btor, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    BTOR_NEW (btor->mm, res);
    BTOR_CLR (res);
    res->kind          = BTOR_ARRAY_SORT;
    res->array.index   = index;
    res->array.element = element;
    inc_sort_ref_counter (btor, index);
    inc_sort_ref_counter (btor, element);
    *pos = res;
  }
  inc_sort_ref_counter (btor, res);
  return res;
}

BtorSort *
btor_lst_sort (Btor *btor, BtorSort *head, BtorSort *tail)
{
  BtorSort *res, **pos, pattern;
  assert (btor);
  assert (head);
  assert (head->refs > 0);
  assert (tail);
  assert (tail->refs > 0);
  BTOR_CLR (&pattern);
  pattern.kind     = BTOR_LST_SORT;
  pattern.lst.head = head;
  pattern.lst.tail = tail;
  pos              = find_sort (btor, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    BTOR_NEW (btor->mm, res);
    BTOR_CLR (res);
    res->kind     = BTOR_LST_SORT;
    res->lst.head = head;
    res->lst.tail = tail;
    inc_sort_ref_counter (btor, head);
    inc_sort_ref_counter (btor, tail);
    *pos = res;
  }
  inc_sort_ref_counter (btor, res);
  return res;
}

BtorSort *
btor_fun_sort (Btor *btor, BtorSort *domain, BtorSort *codomain)
{
  BtorSort *res, **pos, pattern;
  assert (btor);
  assert (domain);
  assert (domain->refs > 0);
  assert (codomain);
  assert (codomain->refs > 0);
  BTOR_CLR (&pattern);
  pattern.kind         = BTOR_FUN_SORT;
  pattern.fun.domain   = domain;
  pattern.fun.codomain = codomain;
  pos                  = find_sort (btor, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    BTOR_NEW (btor->mm, res);
    BTOR_CLR (res);
    res->kind         = BTOR_FUN_SORT;
    res->fun.domain   = domain;
    res->fun.codomain = codomain;
    inc_sort_ref_counter (btor, domain);
    inc_sort_ref_counter (btor, codomain);
    *pos = res;
  }
  inc_sort_ref_counter (btor, res);
  return res;
}

/*------------------------------------------------------------------------*/

static void
inc_exp_ref_counter (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;
  assert (btor);
  assert (exp);
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
  inc_exp_ref_counter (btor, exp);
  return exp;
}

/* Creates an expression pair which can be compared with
 * other expression pairs via the function
 * 'compare_exp_pair'
 */
BtorNodePair *
new_exp_pair (Btor *btor, BtorNode *exp1, BtorNode *exp2)
{
  int id1, id2;
  BtorNodePair *result;
  assert (btor);
  assert (exp1);
  assert (exp2);
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

/* Disconnects a child from its parent and updates its parent list */
static void
disconnect_child_exp (Btor *btor, BtorNode *parent, int pos)
{
  BtorNode *first_parent, *last_parent;
  BtorNode *child, *real_child, *tagged_parent;
  assert (btor);
  assert (parent);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (!BTOR_IS_BV_CONST_NODE (parent));
  assert (!BTOR_IS_BV_VAR_NODE (parent));
  assert (!BTOR_IS_ARRAY_VAR_NODE (parent));
  (void) btor;
  tagged_parent = BTOR_TAG_NODE (parent, pos);
  /* special treatment of array children of aeq and acond */
  if (BTOR_IS_ARRAY_EQ_NODE (parent)
      || (BTOR_IS_ARRAY_COND_NODE (parent) && pos != 0))
  {
    child = parent->e[pos];
    assert (BTOR_IS_REGULAR_NODE (child));
    assert (BTOR_IS_ARRAY_NODE (child) || BTOR_IS_PROXY_NODE (child));
    first_parent = child->first_aeq_acond_parent;
    last_parent  = child->last_aeq_acond_parent;
    assert (first_parent);
    assert (last_parent);
    /* only one parent? */
    if (first_parent == tagged_parent && first_parent == last_parent)
    {
      assert (!parent->next_aeq_acond_parent[pos]);
      assert (!parent->prev_aeq_acond_parent[pos]);
      child->first_aeq_acond_parent = 0;
      child->last_aeq_acond_parent  = 0;
    }
    /* is parent first parent in the list? */
    else if (first_parent == tagged_parent)
    {
      assert (parent->next_aeq_acond_parent[pos]);
      assert (!parent->prev_aeq_acond_parent[pos]);
      child->first_aeq_acond_parent = parent->next_aeq_acond_parent[pos];
      BTOR_PREV_AEQ_ACOND_PARENT (child->first_aeq_acond_parent) = 0;
    }
    /* is parent last parent in the list? */
    else if (last_parent == tagged_parent)
    {
      assert (!parent->next_aeq_acond_parent[pos]);
      assert (parent->prev_aeq_acond_parent[pos]);
      child->last_aeq_acond_parent = parent->prev_aeq_acond_parent[pos];
      BTOR_NEXT_AEQ_ACOND_PARENT (child->last_aeq_acond_parent) = 0;
    }
    /* detach parent from list */
    else
    {
      assert (parent->next_aeq_acond_parent[pos]);
      assert (parent->prev_aeq_acond_parent[pos]);
      BTOR_PREV_AEQ_ACOND_PARENT (parent->next_aeq_acond_parent[pos]) =
          parent->prev_aeq_acond_parent[pos];
      BTOR_NEXT_AEQ_ACOND_PARENT (parent->prev_aeq_acond_parent[pos]) =
          parent->next_aeq_acond_parent[pos];
    }
    parent->next_aeq_acond_parent[pos] = 0;
    parent->prev_aeq_acond_parent[pos] = 0;
  }
  else
  {
    real_child   = BTOR_REAL_ADDR_NODE (parent->e[pos]);
    first_parent = real_child->first_parent;
    last_parent  = real_child->last_parent;
    assert (first_parent);
    assert (last_parent);

    /* special treatment of array children of aeq and acond */
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
  }
  parent->e[pos] = 0;
}

/* Computes hash value of expresssion by children ids */
static unsigned int
compute_hash_exp (BtorNode *exp, int table_size)
{
  unsigned int hash;
  assert (exp);
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (!BTOR_IS_BV_VAR_NODE (exp));
  assert (!BTOR_IS_ARRAY_VAR_NODE (exp));
  if (BTOR_IS_BV_CONST_NODE (exp))
    hash = btor_hashstr ((void *) exp->bits);
  else if (exp)
  {
    switch (exp->arity)
    {
      case 1:
        assert (exp->kind == BTOR_SLICE_NODE);
        hash = (unsigned int) BTOR_REAL_ADDR_NODE (exp->e[0])->id
               + (unsigned int) exp->upper + (unsigned int) exp->lower;
        break;
      case 2:
        hash = (unsigned int) BTOR_REAL_ADDR_NODE (exp->e[0])->id
               + (unsigned int) BTOR_REAL_ADDR_NODE (exp->e[1])->id;
        break;
      default:
        assert (exp->arity == 3);
        hash = (unsigned int) BTOR_REAL_ADDR_NODE (exp->e[0])->id
               + (unsigned int) BTOR_REAL_ADDR_NODE (exp->e[1])->id
               + (unsigned int) BTOR_REAL_ADDR_NODE (exp->e[2])->id;
        break;
    }
  }
  else
    hash = 0;
  hash = (hash * BTOR_NODE_UNIQUE_TABLE_PRIME) & (table_size - 1);
  return hash;
}

static void
remove_from_nodes_unique_table_exp (Btor *btor, BtorNode *exp)
{
  unsigned int hash;
  BtorNode *cur, *prev;

  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

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
}

static void
remove_from_hash_tables (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (exp->kind != BTOR_INVALID_NODE);

  switch (exp->kind)
  {
    case BTOR_BV_VAR_NODE:
      btor_remove_from_ptr_hash_table (btor->bv_vars, exp, 0, 0);
      break;
    case BTOR_ARRAY_VAR_NODE:
      btor_remove_from_ptr_hash_table (btor->array_vars, exp, 0, 0);
      break;
    case BTOR_READ_NODE: break;
    case BTOR_WRITE_NODE: break;
    case BTOR_ACOND_NODE: break;
    case BTOR_LAMBDA_NODE:
      btor_remove_from_ptr_hash_table (btor->lambdas, exp, 0, 0);
      break;
    default: break;
  }
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
  int i;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_NODE (exp));

  assert (exp->kind != BTOR_INVALID_NODE);

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
erase_local_data_exp (Btor *btor, BtorNode *exp, int free_symbol)
{
  BtorMemMgr *mm;
  BtorPtrHashTable *synth_reads;
  BtorPtrHashBucket *bucket;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_NODE (exp));

  assert (!exp->unique);
  assert (!exp->erased);
  assert (!exp->disconnected);
  assert (exp->kind != BTOR_INVALID_NODE);

  mm = btor->mm;
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  switch (exp->kind)
  {
    case BTOR_BV_CONST_NODE:
      btor_freestr (mm, exp->bits);
      exp->bits = 0;
      break;
    case BTOR_LAMBDA_NODE:
      synth_reads = ((BtorLambdaNode *) exp)->synth_reads;
      if (synth_reads)
      {
        for (bucket = synth_reads->last; bucket; bucket = bucket->prev)
          btor_release_exp (btor, (BtorNode *) bucket->key);
        btor_delete_ptr_hash_table (synth_reads);
        ((BtorLambdaNode *) exp)->synth_reads = 0;
      }
      goto ERASE_LOCAL_ARRAY_RHO;
      /* fall through wanted */
    case BTOR_ARRAY_VAR_NODE:
      if (free_symbol)
      {
        btor_freestr (mm, exp->symbol);
        exp->symbol = 0;
      }
      /* fall through wanted */
    case BTOR_WRITE_NODE:
    case BTOR_ACOND_NODE:
    ERASE_LOCAL_ARRAY_RHO:
      if (exp->rho)
      {
        btor_delete_ptr_hash_table (exp->rho);
        exp->rho = 0;
      }
      break;
    case BTOR_PARAM_NODE:
      assert (BTOR_EMPTY_STACK (((BtorParamNode *) exp)->assigned_exp));
      BTOR_RELEASE_STACK (mm, ((BtorParamNode *) exp)->assigned_exp);
    case BTOR_BV_VAR_NODE:
      if (free_symbol)
      {
        btor_freestr (mm, exp->symbol);
        exp->symbol = 0;
      }
      break;
    case BTOR_PROXY_NODE:
      if (free_symbol && exp->symbol)
      {
        btor_freestr (mm, exp->symbol);
        exp->symbol = 0;
      }
      break;
    case BTOR_AEQ_NODE:
      if (exp->vreads)
      {
        BTOR_DELETE (mm, exp->vreads);
        exp->vreads = 0;
      }
      break;
    case BTOR_READ_NODE:
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
really_deallocate_exp (Btor *btor, BtorNode *exp)
{
  BtorMemMgr *mm;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_NODE (exp));

  assert (!exp->unique);
  assert (exp->disconnected);
  assert (exp->erased);

  assert (exp->id);
  assert (BTOR_PEEK_STACK (btor->nodes_id_table, exp->id) == exp);
  BTOR_POKE_STACK (btor->nodes_id_table, exp->id, 0);

  assert (exp->btor == btor);

  mm = btor->mm;

  exp->kind = BTOR_INVALID_NODE;

  if (exp->bits) btor_freestr (btor->mm, exp->bits);

  btor_free (mm, exp, exp->bytes);
}

static void
recursively_release_exp (Btor *btor, BtorNode *root)
{
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorNode *cur;
  int i;

  assert (btor);
  assert (root);
  assert (BTOR_IS_REGULAR_NODE (root));
  assert (root->refs == 1);

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

      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);

      if (cur->simplified)
      {
        assert (btor->rewrite_level > 1 || btor->rewrite_writes);
        BTOR_PUSH_STACK (mm, stack, cur->simplified);
        cur->simplified = 0;
      }

      if (BTOR_IS_ARRAY_EQ_NODE (cur) && cur->vreads)
      {
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp2);
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp1);
      }

      remove_from_nodes_unique_table_exp (btor, cur);
      erase_local_data_exp (btor, cur, 1);

      /* It is safe to access the children here, since they are pushed
       * on the stack and will be released later if necessary.
       */
      remove_from_hash_tables (btor, cur);
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

  root = BTOR_REAL_ADDR_NODE (root);

  assert (root->refs > 0);

  if (root->refs > 1)
    root->refs--;
  else
    recursively_release_exp (btor, root);
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
  int result;
  assert (pair1);
  assert (pair2);
  result = BTOR_GET_ID_NODE (pair1->exp1);
  result -= BTOR_GET_ID_NODE (pair2->exp1);
  if (result != 0) return result;
  result = BTOR_GET_ID_NODE (pair1->exp2);
  result -= BTOR_GET_ID_NODE (pair2->exp2);
  return result;
}

static int
has_parents_exp (Btor *btor, BtorNode *exp)
{
  BtorFullParentIterator it;

  assert (btor);
  assert (exp);
  (void) btor;

  init_full_parent_iterator (&it, exp);
  return has_next_parent_full_parent_iterator (&it);
}

static void
check_not_simplified_or_const (Btor *btor, BtorNode *exp)
{
#ifndef NDEBUG
  assert (btor);
  assert (exp);

  exp = BTOR_REAL_ADDR_NODE (exp);

  if (!exp->simplified) return;

  assert (exp->len == 1);
  while (exp->simplified) exp = BTOR_REAL_ADDR_NODE (exp->simplified);
  assert (BTOR_IS_BV_CONST_NODE (exp));
#else
  (void) btor;
  (void) exp;
#endif
}

static int
assignment_always_unequal (Btor *btor, BtorNodePair *pair)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int i, len, val1, val2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  BtorNode *exp1, *exp2;

  assert (btor);
  assert (pair);

  exp1 = pair->exp1;
  exp2 = pair->exp2;

  if (!BTOR_IS_SYNTH_NODE (exp1)) return 0;

  if (!BTOR_IS_SYNTH_NODE (exp2)) return 0;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  assert (BTOR_REAL_ADDR_NODE (exp1)->len == BTOR_REAL_ADDR_NODE (exp2)->len);

  av1 = BTOR_REAL_ADDR_NODE (exp1)->av;
  av2 = BTOR_REAL_ADDR_NODE (exp2)->av;

  if (!av1 || !av2) return 0;

  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_NODE (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_NODE (exp2, av2->aigs[i]);

    if (aig1 == BTOR_AIG_TRUE)
      val1 = 1;
    else if (aig1 == BTOR_AIG_FALSE)
      val1 = -1;
    else if (!BTOR_REAL_ADDR_AIG (aig1)->cnf_id)
      val1 = 0;
    else
      val1 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig1));

    if (val1 != 0) /* toplevel assigned or const */
    {
      if (aig2 == BTOR_AIG_TRUE)
        val2 = 1;
      else if (aig2 == BTOR_AIG_FALSE)
        val2 = -1;
      else if (!BTOR_REAL_ADDR_AIG (aig2)->cnf_id)
        val2 = 0;
      else
        val2 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig2));

      if (val2 != 0 && val1 != val2) return 1;
    }
  }
  return 0;
}

static int
assignment_always_equal (Btor *btor, BtorNodePair *pair)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int i, len, val1, val2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  BtorNode *exp1, *exp2;

  assert (btor);
  assert (pair);

  exp1 = pair->exp1;
  exp2 = pair->exp2;

  if (!BTOR_IS_SYNTH_NODE (exp1)) return 0;

  if (!BTOR_IS_SYNTH_NODE (exp2)) return 0;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  assert (BTOR_REAL_ADDR_NODE (exp1)->len == BTOR_REAL_ADDR_NODE (exp2)->len);

  av1 = BTOR_REAL_ADDR_NODE (exp1)->av;
  av2 = BTOR_REAL_ADDR_NODE (exp2)->av;
  if (!av1 || !av2) return 0;

  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_NODE (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_NODE (exp2, av2->aigs[i]);

    if (aig1 == BTOR_AIG_TRUE)
      val1 = 1;
    else if (aig1 == BTOR_AIG_FALSE)
      val1 = -1;
    else if (!BTOR_REAL_ADDR_AIG (aig1)->cnf_id)
      return 0;
    else
      val1 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig1));

    if (!val1) return 0;

    if (aig2 == BTOR_AIG_TRUE)
      val2 = 1;
    else if (aig2 == BTOR_AIG_FALSE)
      val2 = -1;
    else if (!BTOR_REAL_ADDR_AIG (aig2)->cnf_id)
      return 0;
    else
      val2 = btor_fixed_sat (smgr, BTOR_GET_CNF_ID_AIG (aig2));

    if (!val2) return 0;

    if (val1 != val2) return 0;
  }
  return 1;
}

static void
add_eq_or_neq_exp_to_clause (Btor *btor,
                             BtorNode *a,
                             BtorNode *b,
                             BtorIntStack *linking_clause,
                             int sign)
{
  BtorPtrHashTable *table = btor->exp_pair_eq_table;
  int lit, true_lit, false_lit, hashed_pair;
  BtorPtrHashBucket *bucket;
  BtorNodePair *pair;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorNode *eq;

  assert (sign == 1 || sign == -1);

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);

  true_lit  = smgr->true_lit;
  false_lit = -true_lit;

  a = btor_simplify_exp (btor, a);
  b = btor_simplify_exp (btor, b);

  if (a == b)
    lit = true_lit;
  else if (a == BTOR_INVERT_NODE (b))
    lit = false_lit;
  else
  {
    hashed_pair = 0;
    pair        = new_exp_pair (btor, a, b);
    if (assignment_always_unequal (btor, pair))
      lit = false_lit;
    else if (assignment_always_equal (btor, pair))
      lit = true_lit;
    else
    {
      bucket = btor_find_in_ptr_hash_table (table, pair);
      if (bucket)
      {
        eq = bucket->data.asPtr;
        eq = btor_simplify_exp (btor, eq);
      }
      else
      {
        eq                 = btor_eq_exp (btor, a, b);
        bucket             = btor_insert_in_ptr_hash_table (table, pair);
        bucket->data.asPtr = eq;
        hashed_pair        = 1;
      }
      lit = exp_to_cnf_lit (btor, eq);
    }
    if (!hashed_pair) delete_exp_pair (btor, pair);
  }
  lit *= sign;
  if (lit != false_lit) BTOR_PUSH_STACK (btor->mm, *linking_clause, lit);
}

static void
add_eq_exp_to_clause (Btor *btor,
                      BtorNode *a,
                      BtorNode *b,
                      BtorIntStack *linking_clause)
{
  add_eq_or_neq_exp_to_clause (btor, a, b, linking_clause, 1);
}

static void
add_neq_exp_to_clause (Btor *btor,
                       BtorNode *a,
                       BtorNode *b,
                       BtorIntStack *linking_clause)
{
  add_eq_or_neq_exp_to_clause (btor, a, b, linking_clause, -1);
}

// TODO: build more generic function for caching eq, and, etc?
static void
add_and_exp_to_clause (Btor *btor,
                       BtorNode *a,
                       BtorNode *b,
                       BtorIntStack *linking_clause,
                       int sign)
{
  BtorPtrHashTable *table = btor->exp_pair_and_table;
  int lit, true_lit, false_lit, hashed_pair;
  BtorPtrHashBucket *bucket;
  BtorNodePair *pair;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorNode *and;

  assert (sign == 1 || sign == -1);

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);

  true_lit  = smgr->true_lit;
  false_lit = -true_lit;

  a = btor_simplify_exp (btor, a);
  b = btor_simplify_exp (btor, b);

  hashed_pair = 0;
  pair        = new_exp_pair (btor, a, b);
  bucket      = btor_find_in_ptr_hash_table (table, pair);

  if (bucket)
  {
    and = bucket->data.asPtr;
    and = btor_simplify_exp (btor, and);
  }
  else
  {
    and                = btor_and_exp (btor, a, b);
    bucket             = btor_insert_in_ptr_hash_table (table, pair);
    bucket->data.asPtr = and;
    hashed_pair        = 1;
  }

  lit = exp_to_cnf_lit (btor, and);

  if (!hashed_pair) delete_exp_pair (btor, pair);

  lit *= sign;
  if (lit != false_lit) BTOR_PUSH_STACK (btor->mm, *linking_clause, lit);
}

/* This function is used to encode a lemma on demand.
 * The stack 'writes' contains intermediate writes.
 * The stack 'aeqs' contains intermediate array equalities (true).
 * The stacks 'aconds' constain intermediate array conditionals.
 */
static void
add_param_cond_to_clause (Btor *btor,
                          BtorNode *cond,
                          BtorIntStack *linking_clause,
                          int sign)
{
  assert (btor);
  assert (cond);
  assert (linking_clause);
  assert (sign == 1 || sign == -1);

  int lit, false_lit, true_lit;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorNode *beta_cond, *parameterized;

  mm   = btor->mm;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);

  BTORLOG ("add_param_cond_to_clause: %s", node2string (cond));
  beta_cond = btor_beta_reduce_cutoff (btor, cond, &parameterized);
  assert (!beta_cond->parameterized);

  // TODO: cache arbitrary conditions?
  if (BTOR_IS_BV_EQ_NODE (BTOR_REAL_ADDR_NODE (beta_cond)))
  {
    sign *= BTOR_IS_INVERTED_NODE (beta_cond) ? -1 : 1;
    add_eq_or_neq_exp_to_clause (btor,
                                 BTOR_REAL_ADDR_NODE (beta_cond)->e[0],
                                 BTOR_REAL_ADDR_NODE (beta_cond)->e[1],
                                 linking_clause,
                                 sign);
  }
  else if (BTOR_REAL_ADDR_NODE (beta_cond)->kind == BTOR_AND_NODE)
  {
    sign *= BTOR_IS_INVERTED_NODE (beta_cond) ? -1 : 1;
    add_and_exp_to_clause (btor,
                           BTOR_REAL_ADDR_NODE (beta_cond)->e[0],
                           BTOR_REAL_ADDR_NODE (beta_cond)->e[1],
                           linking_clause,
                           sign);
  }
  else
  {
    //      assert (BTOR_IS_PARAM_NODE (parameterized) || !parameterized);
    lit = exp_to_cnf_lit (btor, beta_cond);
    lit *= sign;
    true_lit  = smgr->true_lit;
    false_lit = -true_lit;

    if (lit != false_lit && lit != true_lit)
      BTOR_PUSH_STACK (mm, *linking_clause, lit);
  }

  btor_release_exp (btor, beta_cond);
}

static void
print_encoded_lemma_dbg (Btor *btor,
                         BtorPtrHashTable *writes,
                         BtorPtrHashTable *aeqs,
                         BtorPtrHashTable *aconds_sel1,
                         BtorPtrHashTable *aconds_sel2,
                         BtorPtrHashTable *bconds_sel1,
                         BtorPtrHashTable *bconds_sel2,
                         BtorNode *i,
                         BtorNode *j,
                         BtorNode *a,
                         BtorNode *b)
{
  BtorPtrHashBucket *bucket;
  BtorNode *cur;

  (void) i, (void) a, (void) b;

  BTORLOG ("\e[1;32m");
  BTORLOG ("ENCODED LEMMA");
  BTORLOG (
      "  index: %c%s", BTOR_IS_INVERTED_NODE (i) ? '-' : ' ', node2string (i));
  BTORLOG ("  premisses:");

  if (j)
  {
    BTORLOG ("    indices:");
    BTORLOG ("      eq:");
    BTORLOG (
        "        %c%s", BTOR_IS_INVERTED_NODE (i) ? '-' : ' ', node2string (i));
    BTORLOG (
        "        %c%s", BTOR_IS_INVERTED_NODE (j) ? '-' : ' ', node2string (j));
  }

  BTORLOG ("    writes:");
  for (bucket = writes->last; bucket; bucket = bucket->prev)
  {
    cur = (BtorNode *) bucket->key;
    cur = cur->e[1];
    BTORLOG ("      eq:");
    BTORLOG (
        "       %c%s", BTOR_IS_INVERTED_NODE (i) ? '-' : ' ', node2string (i));
    BTORLOG ("        %c%s",
             BTOR_IS_INVERTED_NODE (cur) ? '-' : ' ',
             node2string (cur));
  }

  BTORLOG ("    aeqs:");
  for (bucket = aeqs->last; bucket; bucket = bucket->prev)
  {
    cur = (BtorNode *) bucket->key;
    BTORLOG ("      %c%s",
             BTOR_IS_INVERTED_NODE (cur) ? '-' : ' ',
             node2string (cur));
  }

  BTORLOG ("    aconds_sel1 (then):");
  for (bucket = aconds_sel1->last; bucket; bucket = bucket->prev)
  {
    cur = (BtorNode *) bucket->key;
    cur = cur->e[0];
    BTORLOG ("      %c%s",
             BTOR_IS_INVERTED_NODE (cur) ? '-' : ' ',
             node2string (cur));
  }

  BTORLOG ("    aconds_sel2 (else):");
  for (bucket = aconds_sel2->last; bucket; bucket = bucket->prev)
  {
    cur = (BtorNode *) bucket->key;
    cur = cur->e[0];
    BTORLOG ("      %c%s",
             BTOR_IS_INVERTED_NODE (cur) ? ' ' : '-',
             node2string (cur));
  }

  BTORLOG ("    bconds_sel1 (then):");
  for (bucket = bconds_sel1->last; bucket; bucket = bucket->prev)
  {
    cur = (BtorNode *) bucket->key;
    cur = cur->e[0];
    BTORLOG ("      %c%s",
             BTOR_IS_INVERTED_NODE (cur) ? '-' : ' ',
             node2string (cur));
  }

  BTORLOG ("    bconds_sel2 (else):");
  for (bucket = bconds_sel2->last; bucket; bucket = bucket->prev)
  {
    cur = (BtorNode *) bucket->key;
    cur = cur->e[0];
    BTORLOG ("      %c%s",
             BTOR_IS_INVERTED_NODE (cur) ? ' ' : '-',
             node2string (cur));
  }

  BTORLOG ("  conclusion:");
  BTORLOG (
      "      %c%s", BTOR_IS_INVERTED_NODE (a) ? '-' : ' ', node2string (a));
  BTORLOG (
      "      %c%s", BTOR_IS_INVERTED_NODE (b) ? '-' : ' ', node2string (b));
  BTORLOG ("\e[0;39m");
}

static void
collect_premisses (Btor *btor,
                   BtorNode *array,
                   BtorNode *acc,
                   BtorNode *index,
                   BtorPtrHashTable *writes,
                   BtorPtrHashTable *aeqs,
                   BtorPtrHashTable *aconds_sel1,
                   BtorPtrHashTable *aconds_sel2,
                   BtorPtrHashTable *bconds_sel1,
                   BtorPtrHashTable *bconds_sel2)
{
  assert (btor);
  assert (array);
  assert (acc);
  assert (writes);
  assert (aeqs);
  assert (aconds_sel1);
  assert (aconds_sel2);
  assert (bconds_sel1);
  assert (bconds_sel2);

  const char *res;
  int assignment, propagated_upwards, prev_propagated_upwards;
  BtorNode *cur, *prev, *cond, *prev_lambda, *bcond, *lambda;
  BtorNodePtrStack bconds;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;

  mm   = btor->mm;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  BTOR_INIT_STACK (bconds);

  prev        = 0;
  prev_lambda = 0;
  cur         = array;
  while (1)
  {
    assert (cur);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_ARRAY_NODE (cur) || BTOR_IS_ARRAY_EQ_NODE (cur)
            || BTOR_IS_ARRAY_COND_NODE (cur) || BTOR_IS_ACC_NODE (cur)
            || BTOR_IS_BV_COND_NODE (cur) || BTOR_IS_LAMBDA_NODE (acc));

    /* set parent lambda expression for previous bv conds */
    if (BTOR_IS_LAMBDA_NODE (cur) || (cur == acc && !BTOR_EMPTY_STACK (bconds)))
    {
      assert (btor->lambdas->count > 0u);
      while (!BTOR_EMPTY_STACK (bconds))
      {
        bcond = BTOR_POP_STACK (bconds);
        assert (BTOR_IS_REGULAR_NODE (bcond));
        assert (BTOR_IS_BV_COND_NODE (bcond));
        cond = bcond->e[0];

        if (PROPAGATED_UPWARDS (bcond))
        {
          assert (prev_lambda);
          lambda = prev_lambda;
        }
        else
        {
          lambda = cur;
        }
        BTORLOG ("set lambda exp %d for bvcond: %d",
                 BTOR_REAL_ADDR_NODE (lambda)->id,
                 bcond->id);

        btor_assign_param (btor, lambda, index);
        res = btor_eval_exp (btor, cond);
        btor_unassign_param (btor, lambda);

        /* determine resp. branch that was taken in bfs */
        if (res[0] == '1')
        {
          if (!btor_find_in_ptr_hash_table (bconds_sel1, bcond))
            btor_insert_in_ptr_hash_table (bconds_sel1, bcond)->data.asPtr =
                lambda;
        }
        else
        {
          assert (res[0] == '0');
          if (!btor_find_in_ptr_hash_table (bconds_sel2, bcond))
            btor_insert_in_ptr_hash_table (bconds_sel2, bcond)->data.asPtr =
                lambda;
        }
        btor_freestr (mm, (char *) res);
      }

      if (BTOR_IS_LAMBDA_NODE (cur)) prev_lambda = cur;
    }

    if (cur == acc) break;

    propagated_upwards = PROPAGATED_UPWARDS (cur);

    /* skip 'cur' in case it does not influence propagation path:
     *
     * 1) (!prev && propagated_upwards)
     *    'acc' was propagated down to 'cur' (conflicting array if !prev).
     *    when we propagte 'acc' down to the conflicting array 'array',
     *    we do not need the info about 'array' as the down-propagation
     *    of 'acc' was not not influenced by 'array'.
     *
     * 2) (prev && !(prev_propagated_upwards && !propagated_upwards))
     *	'acc' was propagated down from 'prev' to 'cur' and afterwards
     *    propagated up from 'cur' to 'cur + 1'. in this case, we do not
     *    need 'cur' in the lemma, because the down- and up-propagation
     *    of 'acc' was not influenced by 'cur'.
     */
    if ((!prev && propagated_upwards)
        || (prev && !(prev_propagated_upwards && !propagated_upwards)))
    {
      if (BTOR_IS_WRITE_NODE (cur))
      {
        if (!btor_find_in_ptr_hash_table (writes, cur))
          btor_insert_in_ptr_hash_table (writes, cur);
      }
      else if (BTOR_IS_ARRAY_EQ_NODE (cur))
      {
        if (!btor_find_in_ptr_hash_table (aeqs, cur))
          btor_insert_in_ptr_hash_table (aeqs, cur);
      }
      else if (BTOR_IS_ARRAY_COND_NODE (cur))
      {
        cond = cur->e[0];
        assert (btor->rewrite_level == 0
                || !BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cond)));
        if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cond)))
        {
          assignment = btor_get_assignment_aig (
              amgr, BTOR_REAL_ADDR_NODE (cond)->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
          if (BTOR_IS_INVERTED_NODE (cond)) assignment = -assignment;
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
      /* we only need to collect parameterized bv conds */
      else if (BTOR_IS_BV_COND_NODE (cur) && cur->parameterized)
      {
        cond = cur->e[0];
        assert (btor->rewrite_level == 0
                || !BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cond)));
        if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (cond)))
          BTOR_PUSH_STACK (mm, bconds, cur);
      }
    }
    prev                    = cur;
    prev_propagated_upwards = propagated_upwards;
    cur                     = BTOR_REAL_ADDR_NODE (cur->parent);
  }

  BTOR_RELEASE_STACK (mm, bconds);
}

static void
encode_lemma (Btor *btor,
              BtorPtrHashTable *writes,
              BtorPtrHashTable *aeqs,
              BtorPtrHashTable *aconds_sel1,
              BtorPtrHashTable *aconds_sel2,
              BtorPtrHashTable *bconds_sel1,
              BtorPtrHashTable *bconds_sel2,
              BtorNode *acc1,
              BtorNode *acc2)
{
  assert (btor);
  assert (writes);
  assert (aeqs);
  assert (aconds_sel1);
  assert (aconds_sel2);
  assert (bconds_sel1);
  assert (bconds_sel2);
  assert (acc1);
  assert (acc2);
  assert (BTOR_IS_REGULAR_NODE (acc1));
  assert (BTOR_IS_REGULAR_NODE (acc2));

#ifndef NDEBUG
  int found;
#endif
  int k, val, false_lit, true_lit;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorNode *i, *j, *a, *b, *cur_write, *w_index, *aeq, *cond, *acond, *bcond;
  BtorNode *cur, *lambda_value, *parameterized;
  BtorIntStack linking_clause;
  BtorPtrHashBucket *bucket;

  mm    = btor->mm;
  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  true_lit  = smgr->true_lit;
  false_lit = -true_lit;

  i = BTOR_GET_INDEX_ACC_NODE (acc1);
  a = BTOR_GET_VALUE_ACC_NODE (acc1);

  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (i)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (a)));
  assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (i)));
  assert (BTOR_REAL_ADDR_NODE (i)->tseitin);

  BTOR_INIT_STACK (linking_clause);

  /* array axiom 2 conflict (acc2 is lambda expression) */
  if (BTOR_IS_LAMBDA_NODE (acc2))
  {
    /* get value at position i */
    btor_assign_param (btor, acc2, i);
    lambda_value = btor_beta_reduce_cutoff (btor, acc2, &parameterized);
    btor_unassign_param (btor, acc2);
    b            = lambda_value;
    lambda_value = BTOR_REAL_ADDR_NODE (lambda_value);

    BTORLOG (" encode_lemma: lambda_value %s", node2string (b));

    if (parameterized)
    {
#ifndef NDEBUG
      found =
#endif
          bfs_lambda (btor, acc2, acc1, parameterized, &cur, 0);
      cur = parameterized;
    }
    else
    {
#ifndef NDEBUG
      found =
#endif
          bfs_lambda (btor, acc2, acc1, lambda_value, &cur, 0);
      cur = lambda_value;
    }
    assert (found);
    assert (cur);

    collect_premisses (btor,
                       cur,
                       acc2,
                       i,
                       writes,
                       aeqs,
                       aconds_sel1,
                       aconds_sel2,
                       bconds_sel1,
                       bconds_sel2);

    print_encoded_lemma_dbg (btor,
                             writes,
                             aeqs,
                             aconds_sel1,
                             aconds_sel2,
                             bconds_sel1,
                             bconds_sel2,
                             i,
                             NULL,
                             a,
                             b);

    add_eq_exp_to_clause (btor, a, b, &linking_clause);
    btor_release_exp (btor, lambda_value);
  }
  else
  {
    j = BTOR_GET_INDEX_ACC_NODE (acc2);
    b = BTOR_GET_VALUE_ACC_NODE (acc2);

    assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (j)));
    assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (j)));
    assert (BTOR_REAL_ADDR_NODE (j)->tseitin);

    add_neq_exp_to_clause (btor, i, j, &linking_clause);
    btor->stats.lemmas_size_sum += 1; /* i != j */
    print_encoded_lemma_dbg (btor,
                             writes,
                             aeqs,
                             aconds_sel1,
                             aconds_sel2,
                             bconds_sel1,
                             bconds_sel2,
                             i,
                             j,
                             a,
                             b);
    add_eq_exp_to_clause (btor, a, b, &linking_clause);
  }

  btor->stats.lemmas_size_sum += writes->count;
  btor->stats.lemmas_size_sum += aeqs->count;
  btor->stats.lemmas_size_sum += aconds_sel1->count;
  btor->stats.lemmas_size_sum += aconds_sel2->count;
  btor->stats.lemmas_size_sum += bconds_sel1->count;
  btor->stats.lemmas_size_sum += bconds_sel2->count;
  btor->stats.lemmas_size_sum += 1; /* a == b */

  /* encode i = write index premisses */
  for (bucket = writes->last; bucket; bucket = bucket->prev)
  {
    cur_write = (BtorNode *) bucket->key;
    assert (BTOR_IS_REGULAR_NODE (cur_write));
    assert (BTOR_IS_WRITE_NODE (cur_write));
    w_index = cur_write->e[1];
    add_eq_exp_to_clause (btor, i, w_index, &linking_clause);
  }

  /* add array equalites in the premisse to linking clause */
  for (bucket = aeqs->last; bucket; bucket = bucket->prev)
  {
    // TODO replace by 'exp_to_cnf_lit'
    aeq = (BtorNode *) bucket->key;
    assert (BTOR_IS_REGULAR_NODE (aeq));
    assert (BTOR_IS_ARRAY_EQ_NODE (aeq));
    assert (BTOR_IS_SYNTH_NODE (aeq));
    assert (aeq->av->len == 1);
    assert (!BTOR_IS_INVERTED_AIG (aeq->av->aigs[0]));
    assert (!BTOR_IS_CONST_AIG (aeq->av->aigs[0]));
    assert (BTOR_IS_VAR_AIG (aeq->av->aigs[0]));
    k = -aeq->av->aigs[0]->cnf_id;
    BTOR_PUSH_STACK (mm, linking_clause, k);
  }

  for (bucket = aconds_sel1->last; bucket; bucket = bucket->prev)
  {
    acond = (BtorNode *) bucket->key;
    assert (BTOR_IS_REGULAR_NODE (acond));
    assert (BTOR_IS_ARRAY_COND_NODE (acond));
    cond = acond->e[0];
    assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cond)));
    assert (BTOR_REAL_ADDR_NODE (cond)->av->len == 1);
    k = exp_to_cnf_lit (btor, cond);

    if (k == true_lit || k == false_lit) continue;

    assert (k != 0);
    BTOR_PUSH_STACK (mm, linking_clause, -k);
  }

  for (bucket = aconds_sel2->last; bucket; bucket = bucket->prev)
  {
    acond = (BtorNode *) bucket->key;
    assert (BTOR_IS_REGULAR_NODE (acond));
    assert (BTOR_IS_ARRAY_COND_NODE (acond));
    cond = acond->e[0];
    assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cond)));
    assert (BTOR_REAL_ADDR_NODE (cond)->av->len == 1);
    k = exp_to_cnf_lit (btor, cond);

    if (k == true_lit || k == false_lit) continue;

    assert (k != 0);
    BTOR_PUSH_STACK (mm, linking_clause, k);
  }

  for (bucket = bconds_sel1->last; bucket; bucket = bucket->prev)
  {
    bcond = (BtorNode *) bucket->key;
    assert (BTOR_IS_REGULAR_NODE (bcond));
    assert (BTOR_IS_BV_COND_NODE (bcond));
    cond = bcond->e[0];
    assert (BTOR_IS_LAMBDA_NODE ((BtorNode *) bucket->data.asPtr));
    btor_assign_param (btor, (BtorNode *) bucket->data.asPtr, i);
    add_param_cond_to_clause (btor, cond, &linking_clause, -1);
    btor_unassign_param (btor, (BtorNode *) bucket->data.asPtr);
  }

  for (bucket = bconds_sel2->last; bucket; bucket = bucket->prev)
  {
    bcond = (BtorNode *) bucket->key;
    assert (BTOR_IS_REGULAR_NODE (bcond));
    assert (BTOR_IS_BV_COND_NODE (bcond));
    cond = bcond->e[0];
    assert (BTOR_IS_LAMBDA_NODE ((BtorNode *) bucket->data.asPtr));
    btor_assign_param (btor, (BtorNode *) bucket->data.asPtr, i);
    add_param_cond_to_clause (btor, cond, &linking_clause, 1);
    btor_unassign_param (btor, (BtorNode *) bucket->data.asPtr);
  }

  /* add linking clause */
  while (!BTOR_EMPTY_STACK (linking_clause))
  {
    k = BTOR_POP_STACK (linking_clause);
    assert (k != 0);
    val = btor_fixed_sat (smgr, k);
    if (val < 0) continue;
    assert (!val);
    btor_add_sat (smgr, k);
    btor->stats.lclause_size_sum++;
  }
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, linking_clause);
}

/* Encodes the following array inequality constraint:
 * array1 != array2 <=> EXISTS(i): read(array1, i) != read(array2, i)
 */
static void
encode_array_inequality_virtual_reads (Btor *btor, BtorNode *aeq)
{
  BtorNodePair *vreads;
  BtorNode *read1, *read2;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  BtorAIGVecMgr *avmgr;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  int len, k, d_k, r1_k, r2_k, e;
  BtorIntStack diffs;
  assert (btor);
  assert (aeq);
  assert (BTOR_IS_REGULAR_NODE (aeq));
  assert (BTOR_IS_ARRAY_EQ_NODE (aeq));
  assert (!aeq->tseitin);
  assert (aeq->vreads);
  mm     = btor->mm;
  avmgr  = btor->avmgr;
  amgr   = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr   = btor_get_sat_mgr_aig_mgr (amgr);
  vreads = aeq->vreads;

  read1 = vreads->exp1;
  assert (BTOR_IS_REGULAR_NODE (read1));
  assert (BTOR_IS_READ_NODE (read1));
  assert (BTOR_IS_SYNTH_NODE (read1));
  assert (!read1->tseitin);

  read2 = vreads->exp2;
  assert (BTOR_IS_REGULAR_NODE (read2));
  assert (BTOR_IS_READ_NODE (read2));
  assert (BTOR_IS_SYNTH_NODE (read2));
  assert (!read2->tseitin);

  assert (read1->e[1] == read2->e[1]);
  assert (BTOR_IS_REGULAR_NODE (read1->e[1]));
  assert (BTOR_IS_BV_VAR_NODE (read1->e[1]));
  assert (read1->len == read2->len);

  av1 = read1->av;
  assert (av1);
  av2 = read2->av;
  assert (av2);

  /* assign aig cnf indices as there are only variables,
   * no SAT constraints are generated */
  btor_aigvec_to_sat_tseitin (avmgr, aeq->av);
  aeq->tseitin = 1;
  btor_aigvec_to_sat_tseitin (avmgr, av1);
  read1->tseitin = 1;
  btor_aigvec_to_sat_tseitin (avmgr, av2);
  read2->tseitin = 1;

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

  assert (BTOR_IS_SYNTH_NODE (aeq));
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
connect_array_child_write_exp (Btor *btor, BtorNode *parent, BtorNode *child)
{
  BtorNode *last_parent;
  int tag;
  assert (btor);
  assert (parent);
  assert (child);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (BTOR_IS_WRITE_NODE (parent));
  assert (BTOR_IS_REGULAR_NODE (child));
  assert (BTOR_IS_ARRAY_NODE (child));
  (void) btor;
  parent->e[0] = child;
  /* no parent so far? */
  if (!child->first_parent)
  {
    assert (!child->last_parent);
    child->first_parent = parent;
    child->last_parent  = parent;
    assert (!parent->prev_parent[0]);
    assert (!parent->next_parent[0]);
  }
  /* append at the end of the list */
  else
  {
    last_parent = child->last_parent;
    assert (last_parent);
    parent->prev_parent[0] = last_parent;
    tag                    = BTOR_GET_TAG_NODE (last_parent);
    BTOR_REAL_ADDR_NODE (last_parent)->next_parent[tag] = parent;
    child->last_parent                                  = parent;
  }
}

/* Connects array child to array conditional parent.
 * Array conditionals are appended to the end of the
 * array equality and array conditional parent list.
 */
static void
connect_array_child_acond_exp (Btor *btor,
                               BtorNode *parent,
                               BtorNode *child,
                               int pos)
{
  BtorNode *last_parent, *tagged_parent;
  int tag;
  assert (btor);
  assert (parent);
  assert (child);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (BTOR_IS_ARRAY_COND_NODE (parent));
  assert (BTOR_IS_REGULAR_NODE (child));
  assert (BTOR_IS_ARRAY_NODE (child));
  assert (pos == 1 || pos == 2);
  (void) btor;
  parent->e[pos] = child;
  tagged_parent  = BTOR_TAG_NODE (parent, pos);
  /* no parent so far? */
  if (!child->first_aeq_acond_parent)
  {
    assert (!child->last_aeq_acond_parent);
    child->first_aeq_acond_parent = tagged_parent;
    child->last_aeq_acond_parent  = tagged_parent;
    assert (!parent->prev_aeq_acond_parent[pos]);
    assert (!parent->next_aeq_acond_parent[pos]);
  }
  /* append at the end of the list */
  else
  {
    assert (!parent->prev_aeq_acond_parent[pos]);
    assert (!parent->next_aeq_acond_parent[pos]);
    last_parent = child->last_aeq_acond_parent;
    assert (last_parent);
    parent->prev_aeq_acond_parent[pos] = last_parent;
    tag                                = BTOR_GET_TAG_NODE (last_parent);
    BTOR_REAL_ADDR_NODE (last_parent)->next_aeq_acond_parent[tag] =
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
                             BtorNode *parent,
                             BtorNode *child,
                             int pos)
{
  BtorNode *first_parent, *tagged_parent;
  int tag;
  assert (btor);
  assert (parent);
  assert (child);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (BTOR_IS_ARRAY_EQ_NODE (parent));
  assert (BTOR_IS_REGULAR_NODE (child));
  assert (BTOR_IS_ARRAY_NODE (child));
  assert (pos == 0 || pos == 1);
  (void) btor;
  parent->e[pos] = child;
  tagged_parent  = BTOR_TAG_NODE (parent, pos);
  /* no parent so far? */
  if (!child->first_aeq_acond_parent)
  {
    assert (!child->last_aeq_acond_parent);
    child->first_aeq_acond_parent = tagged_parent;
    child->last_aeq_acond_parent  = tagged_parent;
    assert (!parent->prev_aeq_acond_parent[pos]);
    assert (!parent->next_aeq_acond_parent[pos]);
  }
  /* add parent at the beginning of the list */
  else
  {
    assert (!parent->prev_aeq_acond_parent[pos]);
    assert (!parent->next_aeq_acond_parent[pos]);
    first_parent = child->first_aeq_acond_parent;
    assert (first_parent);
    parent->next_aeq_acond_parent[pos] = first_parent;
    tag                                = BTOR_GET_TAG_NODE (first_parent);
    BTOR_REAL_ADDR_NODE (first_parent)->prev_aeq_acond_parent[tag] =
        tagged_parent;
    child->first_aeq_acond_parent = tagged_parent;
  }
}

static void
update_constraints (Btor *btor, BtorNode *exp)
{
  BtorPtrHashTable *unsynthesized_constraints, *synthesized_constraints;
  BtorPtrHashTable *embedded_constraints, *pos, *neg;
  BtorNode *simplified, *not_simplified, *not_exp;
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (exp->simplified);
  assert (!BTOR_REAL_ADDR_NODE (exp->simplified)->simplified);
  assert (exp->constraint);
  assert (exp->refs > 1);

  not_exp                   = BTOR_INVERT_NODE (exp);
  simplified                = exp->simplified;
  not_simplified            = BTOR_INVERT_NODE (simplified);
  embedded_constraints      = btor->embedded_constraints;
  unsynthesized_constraints = btor->unsynthesized_constraints;
  synthesized_constraints   = btor->synthesized_constraints;
  pos = neg = 0;

  if (btor_find_in_ptr_hash_table (unsynthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = unsynthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (unsynthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = unsynthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (embedded_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = embedded_constraints;
  }

  if (btor_find_in_ptr_hash_table (embedded_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = embedded_constraints;
  }

  if (btor_find_in_ptr_hash_table (synthesized_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (!pos);
    pos = synthesized_constraints;
  }

  if (btor_find_in_ptr_hash_table (synthesized_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (!neg);
    neg = synthesized_constraints;
  }

  if (pos)
  {
    btor_remove_from_ptr_hash_table (pos, exp, 0, 0);
    btor_release_exp (btor, exp);
  }

  if (neg)
  {
    btor_remove_from_ptr_hash_table (neg, not_exp, 0, 0);
    btor_release_exp (btor, not_exp);
  }

  exp->constraint = 0;
}

static void
set_simplified_exp (Btor *btor, BtorNode *exp, BtorNode *simplified)
{
  BtorNode *e[3];
  int i;
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (simplified);
  assert (!BTOR_REAL_ADDR_NODE (simplified)->simplified);
  assert (btor->rewrite_level > 1 || btor->rewrite_writes);

  if (exp->simplified) btor_release_exp (btor, exp->simplified);

  exp->simplified = btor_copy_exp (btor, simplified);

  if (exp->constraint) update_constraints (btor, exp);

  if (exp->kind == BTOR_AEQ_NODE && exp->vreads)
  {
    btor_release_exp (btor, exp->vreads->exp2);
    btor_release_exp (btor, exp->vreads->exp1);
    BTOR_DELETE (btor->mm, exp->vreads);
    exp->vreads = 0;
  }

  remove_from_nodes_unique_table_exp (btor, exp);
  /* also updates op stats */
  erase_local_data_exp (btor, exp, 0);
  btor->ops[BTOR_PROXY_NODE]++;
  assert (exp->arity <= 3);
  memset (e, 0, sizeof e);
  for (i = 0; i < exp->arity; i++) e[i] = exp->e[i];
  remove_from_hash_tables (btor, exp);
  disconnect_children_exp (btor, exp);
  for (i = 0; i < exp->arity; i++) btor_release_exp (btor, e[i]);
  exp->kind         = BTOR_PROXY_NODE;
  exp->disconnected = 0;
  exp->erased       = 0;
  exp->arity        = 0;
}

/* Finds most simplified expression and shortens path to it */
static BtorNode *
recursively_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp, *cur, *simplified, *not_simplified, *next;
  int invert;

  assert (btor);
  assert (exp);

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  assert (real_exp->simplified);
  assert (BTOR_REAL_ADDR_NODE (real_exp->simplified)->simplified);

  /* shorten path to simplified expression */
  invert     = 0;
  simplified = real_exp->simplified;
  do
  {
    assert (BTOR_IS_PROXY_NODE (BTOR_REAL_ADDR_NODE (simplified)));
    if (BTOR_IS_INVERTED_NODE (simplified)) invert = !invert;
    simplified = BTOR_REAL_ADDR_NODE (simplified)->simplified;
  } while (BTOR_REAL_ADDR_NODE (simplified)->simplified);
  /* 'simplified' is representative element */
  assert (!BTOR_REAL_ADDR_NODE (simplified)->simplified);
  if (invert) simplified = BTOR_INVERT_NODE (simplified);

  invert         = 0;
  not_simplified = BTOR_INVERT_NODE (simplified);
  cur            = btor_copy_exp (btor, real_exp);
  do
  {
    if (BTOR_IS_INVERTED_NODE (cur)) invert = !invert;
    cur  = BTOR_REAL_ADDR_NODE (cur);
    next = btor_copy_exp (btor, cur->simplified);
    set_simplified_exp (btor, cur, invert ? not_simplified : simplified);
    btor_release_exp (btor, cur);
    cur = next;
  } while (BTOR_REAL_ADDR_NODE (cur)->simplified);
  btor_release_exp (btor, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (BTOR_IS_INVERTED_NODE (exp)) simplified = BTOR_INVERT_NODE (simplified);

  return simplified;
}

BtorNode *
btor_pointer_chase_simplified_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;

  assert (btor);
  assert (exp);
  (void) btor;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  /* no simplified expression ? */
  if (!real_exp->simplified) return exp;

  /* only one simplified expression ? */
  if (!BTOR_REAL_ADDR_NODE (real_exp->simplified)->simplified)
  {
    if (BTOR_IS_INVERTED_NODE (exp))
      return BTOR_INVERT_NODE (real_exp->simplified);
    return exp->simplified;
  }
  return recursively_pointer_chase_simplified_exp (btor, exp);
}

BtorNode *
btor_simplify_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *real_exp, *not_exp, *result;
  BtorPtrHashBucket *bucket;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  not_exp  = BTOR_INVERT_NODE (real_exp);

  if (real_exp->constraint)
  {
    assert (!real_exp->simplified);

    if (BTOR_IS_BV_CONST_NODE (real_exp)) return exp;

    if (btor_find_in_ptr_hash_table (btor->embedded_constraints, real_exp))
    {
      result = btor->true_exp;
    }
    else if (btor_find_in_ptr_hash_table (btor->embedded_constraints, not_exp))
    {
      result = BTOR_INVERT_NODE (btor->true_exp);
    }
    else if (btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                          real_exp))
    {
      result = btor->true_exp;
    }
    else if (btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                          not_exp))
    {
      result = BTOR_INVERT_NODE (btor->true_exp);
    }
    else if (btor_find_in_ptr_hash_table (btor->synthesized_constraints,
                                          real_exp))
    {
      result = btor->true_exp;
    }
    else
    {
      assert (
          btor_find_in_ptr_hash_table (btor->synthesized_constraints, not_exp));
      result = BTOR_INVERT_NODE (btor->true_exp);
    }

    if (BTOR_IS_INVERTED_NODE (exp)) return BTOR_INVERT_NODE (result);
    return result;
  }

  // TODO: substitution flag for BtorNode?
  if (btor->substitutions)
  {
    BtorNode *simp;
    simp = btor_pointer_chase_simplified_exp (btor, real_exp);

    bucket = btor_find_in_ptr_hash_table (btor->substitutions,
                                          BTOR_REAL_ADDR_NODE (simp));
    if (bucket)
      result = btor_pointer_chase_simplified_exp (btor, bucket->data.asPtr);
    else
      result = simp;

    if (BTOR_IS_INVERTED_NODE (exp)) return BTOR_INVERT_NODE (result);
    return result;
  }

  return btor_pointer_chase_simplified_exp (btor, exp);
}

static int
constraint_is_inconsistent (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (btor->rewrite_level > 1);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  BtorNode *rep;

  rep = btor_simplify_exp (btor, exp);

  return rep == BTOR_INVERT_NODE (rep);
}

/* Connects child to its parent and updates list of parent pointers.
 * Expressions are inserted at the beginning of the regular parent list
 */
static void
connect_child_exp (Btor *btor, BtorNode *parent, BtorNode *child, int pos)
{
  BtorNode *real_child, *first_parent, *tagged_parent;
  int tag;
  (void) btor;
  assert (btor);
  assert (parent);
  assert (child);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (BTOR_IS_REGULAR_NODE (parent));
  assert (btor_simplify_exp (btor, child) == child);

  /* set parent parameterized if child is parameterized */
  if (!BTOR_IS_LAMBDA_NODE (parent))
  {
    if (BTOR_REAL_ADDR_NODE (child)->parameterized) parent->parameterized = 1;
  }

  // FIXME: array conditionals are not rewritten in beta reduction. thus,
  //        lambdas below aconds are never reduced as they are not instantiated
  //        and can be skipped in beta reduction phase
  if (BTOR_REAL_ADDR_NODE (child)->lambda_below
      && !BTOR_IS_ARRAY_COND_NODE (parent))
    parent->lambda_below = 1;

  if (parent->kind == BTOR_WRITE_NODE && pos == 0)
    connect_array_child_write_exp (btor, parent, child);
  else if (BTOR_IS_ARRAY_EQ_NODE (parent))
    connect_array_child_aeq_exp (btor, parent, child, pos);
  else if (BTOR_IS_ARRAY_COND_NODE (parent) && pos != 0)
    connect_array_child_acond_exp (btor, parent, child, pos);
  else
  {
    real_child     = BTOR_REAL_ADDR_NODE (child);
    parent->e[pos] = child;
    tagged_parent  = BTOR_TAG_NODE (parent, pos);
    /* no parent so far? */
    if (!real_child->first_parent)
    {
      assert (!real_child->last_parent);
      real_child->first_parent = tagged_parent;
      real_child->last_parent  = tagged_parent;
      assert (!parent->prev_parent[pos]);
      assert (!parent->next_parent[pos]);
    }
    /* add parent at the beginning of the list */
    else
    {
      first_parent = real_child->first_parent;
      assert (first_parent);
      parent->next_parent[pos] = first_parent;
      tag                      = BTOR_GET_TAG_NODE (first_parent);
      BTOR_REAL_ADDR_NODE (first_parent)->prev_parent[tag] = tagged_parent;
      real_child->first_parent                             = tagged_parent;
    }
  }
}

static void
setup_node_and_add_to_id_table (Btor *btor, void *ptr)
{
  BtorNode *exp = ptr;
  int id;
  exp->refs = 1;
  exp->btor = btor;
  btor->stats.expressions++;
  assert (btor);
  assert (exp);
  assert (!BTOR_IS_INVERTED_NODE (exp));
  assert (!exp->id);
  id = BTOR_COUNT_STACK (btor->nodes_id_table);
  BTOR_ABORT_NODE (id == INT_MAX, "expression id overflow");
  exp->id = id;
  BTOR_PUSH_STACK (btor->mm, btor->nodes_id_table, exp);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == exp->id + 1);
  assert (BTOR_PEEK_STACK (btor->nodes_id_table, exp->id) == exp);
}

static BtorNode *
new_const_exp_node (Btor *btor, const char *bits, int len)
{
  BtorBVConstNode *exp;
  int i;
  assert (btor);
  assert (bits);
  assert (len > 0);
  assert ((int) strlen (bits) == len);
  assert (btor_is_const_2vl (btor->mm, bits));
  BTOR_CNEW (btor->mm, exp);
  btor->ops[BTOR_BV_CONST_NODE]++;
  exp->kind  = BTOR_BV_CONST_NODE;
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
  BtorBVNode *exp = 0;

  assert (btor);
  assert (e0);
  assert (upper < BTOR_REAL_ADDR_NODE (e0)->len);
  assert (upper >= lower);
  assert (lower >= 0);

  BTOR_CNEW (btor->mm, exp);
  btor->ops[BTOR_SLICE_NODE]++;
  exp->kind  = BTOR_SLICE_NODE;
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
new_binary_exp_node (
    Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, int len)
{
  BtorBVNode *exp;

  assert (btor);
  assert (BTOR_IS_BINARY_NODE_KIND (kind));
  assert (kind != BTOR_AEQ_NODE);
  assert (e0);
  assert (e1);
  assert (len > 0);

  BTOR_CNEW (btor->mm, exp);
  btor->ops[kind]++;
  exp->kind  = kind;
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = len;
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, (BtorNode *) exp, e0, 0);
  connect_child_exp (btor, (BtorNode *) exp, e1, 1);

  return (BtorNode *) exp;
}

static BtorNode *
new_aeq_exp_node (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  /* we need aeq and acond next and prev fields -> type is BtorNode */
  BtorNode *exp;
  assert (btor);
  assert (e0);
  assert (e1);
  BTOR_CNEW (btor->mm, exp);
  btor->ops[BTOR_AEQ_NODE]++;
  exp->kind  = BTOR_AEQ_NODE;
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = 1;
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, exp, e0, 0);
  connect_child_exp (btor, exp, e1, 1);
  return exp;
}

static BtorNode *
new_lambda_exp_node (Btor *btor, BtorNode *e_param, BtorNode *e_exp, int len)
{
  BtorLambdaNode *lambda_exp;

  assert (btor);
  assert (e_param);
  assert (BTOR_IS_PARAM_NODE (e_param));
  assert (e_exp);
  assert (len > 0);

  BTOR_CNEW (btor->mm, lambda_exp);
  btor->ops[BTOR_LAMBDA_NODE]++;
  lambda_exp->kind         = BTOR_LAMBDA_NODE;
  lambda_exp->bytes        = sizeof *lambda_exp;
  lambda_exp->arity        = 2;
  lambda_exp->len          = len;
  lambda_exp->lambda_below = 1;
  setup_node_and_add_to_id_table (btor, (BtorNode *) lambda_exp);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_param, 0);
  connect_child_exp (btor, (BtorNode *) lambda_exp, e_exp, 1);

  return (BtorNode *) lambda_exp;
}

#if 0
static int
is_nested_lambda_exp_node (BtorNode * exp)
{
  assert (exp);

  BtorFullParentIterator it;
  BtorNode *parent;

  if (BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp->e[0])))
    return 1;

  init_full_parent_iterator (&it, exp);
  while (has_next_parent_full_parent_iterator (&it))
    {
      parent = next_parent_full_parent_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (parent));
      if (BTOR_IS_LAMBDA_NODE (parent))
	return 1;
    }

  return 0;
}
#endif

static BtorNode *
new_ternary_exp_node (Btor *btor,
                      BtorNodeKind kind,
                      BtorNode *e0,
                      BtorNode *e1,
                      BtorNode *e2,
                      int len)
{
  BtorBVNode *exp;

  assert (btor);
  assert (BTOR_IS_TERNARY_NODE_KIND (kind));
  assert (kind == BTOR_BCOND_NODE);
  assert (e0);
  assert (e1);
  assert (e2);
  assert (len > 0);

  BTOR_CNEW (btor->mm, exp);
  btor->ops[kind]++;
  exp->kind  = kind;
  exp->bytes = sizeof *exp;
  exp->arity = 3;
  exp->len   = len;
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, (BtorNode *) exp, e0, 0);
  connect_child_exp (btor, (BtorNode *) exp, e1, 1);
  connect_child_exp (btor, (BtorNode *) exp, e2, 2);
  return (BtorNode *) exp;
}

static BtorNode *
new_write_exp_node (Btor *btor,
                    BtorNode *e_array,
                    BtorNode *e_index,
                    BtorNode *e_value)
{
  BtorMemMgr *mm;
  BtorNode *exp;
  assert (btor);
  assert (e_array);
  assert (e_index);
  assert (e_value);
  assert (BTOR_IS_REGULAR_NODE (e_array));
  assert (BTOR_IS_ARRAY_NODE (e_array));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_index)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_value)));
  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->ops[BTOR_WRITE_NODE]++;
  exp->kind      = BTOR_WRITE_NODE;
  exp->bytes     = sizeof *exp;
  exp->arity     = 3;
  exp->index_len = BTOR_REAL_ADDR_NODE (e_index)->len;
  exp->len       = BTOR_REAL_ADDR_NODE (e_value)->len;
  setup_node_and_add_to_id_table (btor, exp);
  /* append writes to the end of parent list */
  connect_child_exp (btor, exp, e_array, 0);
  connect_child_exp (btor, exp, e_index, 1);
  connect_child_exp (btor, exp, e_value, 2);

  return exp;
}

static BtorNode *
new_acond_exp_node (Btor *btor,
                    BtorNode *e_cond,
                    BtorNode *a_if,
                    BtorNode *a_else)
{
  BtorMemMgr *mm;
  BtorNode *exp;
  assert (btor);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_cond)));
  assert (BTOR_IS_REGULAR_NODE (a_if));
  assert (BTOR_IS_REGULAR_NODE (a_else));
  assert (BTOR_IS_ARRAY_NODE (a_if));
  assert (BTOR_IS_ARRAY_NODE (a_else));
  assert (a_if->index_len == a_else->index_len);
  assert (a_if->index_len > 0);
  assert (a_if->len == a_else->len);
  assert (a_if->len > 0);
  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->ops[BTOR_ACOND_NODE]++;
  exp->kind      = BTOR_ACOND_NODE;
  exp->bytes     = sizeof *exp;
  exp->arity     = 3;
  exp->index_len = a_if->index_len;
  exp->len       = a_if->len;
  setup_node_and_add_to_id_table (btor, exp);
  connect_child_exp (btor, exp, e_cond, 0);
  connect_child_exp (btor, exp, a_if, 1);
  connect_child_exp (btor, exp, a_else, 2);

  return exp;
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
  int id0, id1;
  assert (exp0);
  assert (exp1);
  id0 = BTOR_GET_ID_NODE (exp0);
  id1 = BTOR_GET_ID_NODE (exp1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

/* Search for constant expression in hash table. Returns 0 if not found. */
static BtorNode **
find_const_exp (Btor *btor, const char *bits, int len)
{
  BtorNode *cur, **result;
  unsigned int hash;
  assert (btor);
  assert (bits);
  assert (len > 0);
  assert ((int) strlen (bits) == len);
  hash = btor_hashstr ((void *) bits);
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
  BtorNode *cur, **result;
  unsigned int hash;
  assert (btor);
  assert (e0);
  assert (lower >= 0);
  assert (upper >= lower);
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

/* Search for binary expression in hash table. Returns 0 if not found. */
static BtorNode **
find_binary_exp (Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1)
{
  BtorNode *cur, **result;
  unsigned int hash;
  assert (btor);
  assert (BTOR_IS_BINARY_NODE_KIND (kind));
  assert (e0);
  assert (e1);
  assert (btor->rewrite_level == 0
          || !BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind)
          || BTOR_REAL_ADDR_NODE (e0)->id <= BTOR_REAL_ADDR_NODE (e1)->id);
  hash = (((unsigned int) BTOR_REAL_ADDR_NODE (e0)->id
           + (unsigned int) BTOR_REAL_ADDR_NODE (e1)->id)
          * BTOR_NODE_UNIQUE_TABLE_PRIME)
         & (btor->nodes_unique_table.size - 1);
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
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

/* Search for ternary expression in hash table. Returns 0 if not found. */
static BtorNode **
find_ternary_exp (
    Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  BtorNode *cur, **result;
  unsigned int hash;
  assert (btor);
  assert (BTOR_IS_TERNARY_NODE_KIND (kind));
  assert (e0);
  assert (e1);
  assert (e2);
  hash = (((unsigned) BTOR_REAL_ADDR_NODE (e0)->id
           + (unsigned) BTOR_REAL_ADDR_NODE (e1)->id
           + (unsigned) BTOR_REAL_ADDR_NODE (e2)->id)
          * BTOR_NODE_UNIQUE_TABLE_PRIME)
         & (btor->nodes_unique_table.size - 1);
  result = btor->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
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
enlarge_nodes_unique_table (Btor *btor)
{
  BtorMemMgr *mm;
  int size, new_size, i;
  unsigned int hash;
  BtorNode *cur, *temp, **new_chains;
  assert (btor);
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
      assert (!BTOR_IS_ARRAY_VAR_NODE (cur));
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

static void
mark_synth_mark_exp (Btor *btor, BtorNode *exp, int new_mark)
{
  BtorMemMgr *mm;
  BtorNodePtrStack stack;
  BtorNode *cur;
  int i;

  assert (btor);
  assert (exp);

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  cur = BTOR_REAL_ADDR_NODE (exp);
  goto MARK_SYNTH_MARK_NODE_ENTER_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
  MARK_SYNTH_MARK_NODE_ENTER_WITHOUT_POP:
    if (cur->synth_mark != new_mark)
    {
      cur->synth_mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

static void
btor_mark_exp (Btor *btor, BtorNode *exp, int new_mark)
{
  BtorMemMgr *mm;
  BtorNodePtrStack stack;
  BtorNode *cur;
  int i;

  assert (btor);
  assert (exp);

  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  cur = BTOR_REAL_ADDR_NODE (exp);
  goto BTOR_MARK_NODE_ENTER_WITHOUT_POP;

  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
  BTOR_MARK_NODE_ENTER_WITHOUT_POP:
    if (cur->mark != new_mark)
    {
      cur->mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

BtorNode *
btor_const_exp (Btor *btor, const char *bits)
{
  BtorNode **lookup;
  int inv, len;
  char *lookupbits;

  assert (btor);
  assert (bits);
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
  char *string;
  BtorNode *result;
  assert (btor);
  assert (len > 0);
  string    = btor_zero_const (btor->mm, len);
  string[0] = '1';
  result    = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_zero_exp (Btor *btor, int len)
{
  char *string;
  BtorNode *result;

  assert (btor);
  assert (len > 0);

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
  char *string;
  BtorNode *result;

  assert (btor);
  assert (len > 0);

  string = btor_ones_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_one_exp (Btor *btor, int len)
{
  char *string;
  BtorNode *result;

  assert (btor);
  assert (len > 0);

  string = btor_one_const (btor->mm, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_int_to_exp (Btor *btor, int i, int len)
{
  char *string;
  BtorNode *result;

  assert (btor);
  assert (len > 0);

  string = btor_int_to_const (btor->mm, i, len);
  result = btor_const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorNode *
btor_unsigned_to_exp (Btor *btor, unsigned int u, int len)
{
  char *string;
  BtorNode *result;

  assert (btor);
  assert (len > 0);

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
  BtorMemMgr *mm;
  BtorBVVarNode *exp;

  assert (btor);
  assert (len > 0);
  assert (symbol);

  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->ops[BTOR_BV_VAR_NODE]++;
  exp->kind   = BTOR_BV_VAR_NODE;
  exp->bytes  = sizeof *exp;
  exp->symbol = btor_strdup (mm, symbol);
  exp->len    = len;
  setup_node_and_add_to_id_table (btor, exp);
  exp->bits = btor_x_const_3vl (btor->mm, len);
  (void) btor_insert_in_ptr_hash_table (btor->bv_vars, exp);
  return (BtorNode *) exp;
}

BtorNode *
btor_param_exp (Btor *btor, int len, const char *symbol)
{
  BtorMemMgr *mm;
  BtorParamNode *exp;

  assert (btor);
  assert (len > 0);
  assert (symbol);

  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->ops[BTOR_PARAM_NODE]++;
  exp->kind          = BTOR_PARAM_NODE;
  exp->bytes         = sizeof *exp;
  exp->symbol        = btor_strdup (mm, symbol);
  exp->len           = len;
  exp->parameterized = 1;
  setup_node_and_add_to_id_table (btor, exp);
  return (BtorNode *) exp;
}

BtorNode *
btor_array_exp (Btor *btor, int elem_len, int index_len, const char *symbol)
{
  BtorMemMgr *mm;
  BtorArrayVarNode *exp;

  assert (btor);
  assert (elem_len > 0);
  assert (index_len > 0);
  assert (symbol);

  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->ops[BTOR_ARRAY_VAR_NODE]++;
  exp->kind      = BTOR_ARRAY_VAR_NODE;
  exp->bytes     = sizeof *exp;
  exp->symbol    = btor_strdup (mm, symbol);
  exp->index_len = index_len;
  exp->len       = elem_len;
  setup_node_and_add_to_id_table (btor, exp);
  (void) btor_insert_in_ptr_hash_table (btor->array_vars, exp);
  return (BtorNode *) exp;
}

static BtorNode *
unary_exp_slice_exp (Btor *btor, BtorNode *exp, int upper, int lower)
{
  BtorNode **lookup;
  assert (btor);
  assert (exp);
  int inv;

  exp = btor_simplify_exp (btor, exp);

  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_NODE (exp)->len);

  if (btor->rewrite_level > 0 && BTOR_IS_INVERTED_NODE (exp))
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
    inc_exp_ref_counter (btor, exp);
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
binary_exp (Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, int len)
{
  BtorNode **lookup, *temp;
  assert (btor);
  assert (BTOR_IS_BINARY_NODE_KIND (kind));
  assert (e0);
  assert (e1);
  assert (len > 0);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);

  if (btor->rewrite_level > 0 && BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind)
      && BTOR_REAL_ADDR_NODE (e1)->id < BTOR_REAL_ADDR_NODE (e0)->id)
  {
    temp = e0;
    e0   = e1;
    e1   = temp;
  }
  assert (btor->rewrite_level == 0
          || !BTOR_IS_BINARY_COMMUTATIVE_NODE_KIND (kind)
          || BTOR_REAL_ADDR_NODE (e0)->id <= BTOR_REAL_ADDR_NODE (e1)->id);
  lookup = find_binary_exp (btor, kind, e0, e1);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_binary_exp (btor, kind, e0, e1);
    }
    if (kind == BTOR_AEQ_NODE)
      *lookup = new_aeq_exp_node (btor, e0, e1);
    else if (kind == BTOR_LAMBDA_NODE)
      *lookup = new_lambda_exp_node (btor, e0, e1, len);
    else
      *lookup = new_binary_exp_node (btor, kind, e0, e1, len);
    inc_exp_ref_counter (btor, e0);
    inc_exp_ref_counter (btor, e1);
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_NODE (*lookup));
  return *lookup;
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

  if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e0)))
    kind = BTOR_AEQ_NODE;
  else
    kind = BTOR_BEQ_NODE;

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
btor_read_exp_node (Btor *btor, BtorNode *e_array, BtorNode *e_index)
{
  BtorNode *result;
  e_array = btor_simplify_exp (btor, e_array);
  // assert (btor->rewrite_level < 3 || !BTOR_IS_ARRAY_COND_NODE (e_array));
  // // TODO AB: remove
  e_index = btor_simplify_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));
  result = binary_exp (btor, BTOR_READ_NODE, e_array, e_index, e_array->len);
  if (!result->bits) result->bits = btor_x_const_3vl (btor->mm, e_array->len);
  return result;
}

BtorNode *
btor_lambda_exp (Btor *btor, BtorNode *e_param, BtorNode *e_exp)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (e_param));
  assert (BTOR_IS_PARAM_NODE (e_param));
  assert (BTOR_REAL_ADDR_NODE (e_param)->len > 0);
  assert (!BTOR_REAL_ADDR_NODE (e_param)->simplified);
  assert (e_exp);
  assert (BTOR_REAL_ADDR_NODE (e_exp)->len > 0);

  BtorNode *lambda_exp;
  int index_len = BTOR_REAL_ADDR_NODE (e_param)->len;
  int elem_len  = BTOR_REAL_ADDR_NODE (e_exp)->len;

  e_exp      = btor_simplify_exp (btor, e_exp);
  lambda_exp = binary_exp (btor, BTOR_LAMBDA_NODE, e_param, e_exp, elem_len);
  lambda_exp->index_len = index_len;

  /* set lambda expression of parameter */
  // assert (!((BtorParamNode *) e_param)->lambda_exp);
  assert (!((BtorParamNode *) e_param)->lambda_exp
          || ((BtorParamNode *) e_param)->lambda_exp == lambda_exp);
  if (!((BtorParamNode *) e_param)->lambda_exp)
    ((BtorParamNode *) e_param)->lambda_exp = lambda_exp;
  // else lambda_exp is an already existing one

  if (!btor_find_in_ptr_hash_table (btor->lambdas, lambda_exp))
    (void) btor_insert_in_ptr_hash_table (btor->lambdas, lambda_exp);

  return lambda_exp;
}

BtorNode *
btor_fun_exp (Btor *btor, int paramc, BtorNode **params, BtorNode *exp)
{
  assert (btor);
  assert (paramc > 0);
  assert (params);
  assert (exp);

  int i;
  BtorNode *fun      = btor_simplify_exp (btor, exp);
  BtorNode *prev_fun = 0;

  for (i = paramc - 1; i >= 0; i--)
  {
    assert (params[i]);
    assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (params[i])));
    fun = btor_lambda_exp (btor, params[i], fun);
    if (prev_fun) btor_release_exp (btor, prev_fun);
    prev_fun = fun;
  }

  return fun;
}

BtorNode *
btor_apply_exp (Btor *btor, int argc, BtorNode **args, BtorNode *lambda)
{
  assert (btor);
  assert (argc > 0);
  assert (args);
  assert (lambda);

  int i;
  BtorNode *next, *prev, *read;
#ifndef NDEBUG
  assert (args[argc - 1]);
  BtorNode *cur_lambda = BTOR_REAL_ADDR_NODE (lambda);
  assert (BTOR_REAL_ADDR_NODE (cur_lambda->e[0])->len
          == BTOR_REAL_ADDR_NODE (args[argc - 1])->len);
#endif

  next = prev = args[argc - 1];
  for (i = argc - 2; i >= 0; i--)
  {
#ifndef NDEBUG
    assert (args[i]);
    cur_lambda = BTOR_REAL_ADDR_NODE (cur_lambda->e[1]);
    assert (BTOR_REAL_ADDR_NODE (cur_lambda->e[0])->len
            == BTOR_REAL_ADDR_NODE (args[i])->len);
#endif
    next = btor_concat_exp (btor, args[i], prev);
    if (i < argc - 2) btor_release_exp (btor, prev);
    prev = next;
  }

  read = btor_read_exp (btor, lambda, next);
  btor_release_exp (btor, next);
  return read;
}

static BtorNode *
ternary_exp (Btor *btor,
             BtorNodeKind kind,
             BtorNode *e0,
             BtorNode *e1,
             BtorNode *e2,
             int len)
{
  BtorNode **lookup;
  assert (btor);
  assert (BTOR_IS_TERNARY_NODE_KIND (kind));
  assert (e0);
  assert (e1);
  assert (e2);

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  e2 = btor_simplify_exp (btor, e2);

  lookup = find_ternary_exp (btor, kind, e0, e1, e2);
  if (!*lookup)
  {
    if (BTOR_FULL_UNIQUE_TABLE (btor->nodes_unique_table))
    {
      enlarge_nodes_unique_table (btor);
      lookup = find_ternary_exp (btor, kind, e0, e1, e2);
    }
    switch (kind)
    {
      case BTOR_WRITE_NODE:
        *lookup = new_write_exp_node (btor, e0, e1, e2);
        break;
      case BTOR_ACOND_NODE:
        *lookup = new_acond_exp_node (btor, e0, e1, e2);
        break;
      default:
        assert (kind == BTOR_BCOND_NODE);
        *lookup = new_ternary_exp_node (btor, kind, e0, e1, e2, len);
        break;
    }
    inc_exp_ref_counter (btor, e0);
    inc_exp_ref_counter (btor, e1);
    inc_exp_ref_counter (btor, e2);
    assert (btor->nodes_unique_table.num_elements < INT_MAX);
    btor->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_NODE (*lookup));
  return *lookup;
}

BtorNode *
btor_write_exp_node (Btor *btor,
                     BtorNode *e_array,
                     BtorNode *e_index,
                     BtorNode *e_value)
{
  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));
  return ternary_exp (btor, BTOR_WRITE_NODE, e_array, e_index, e_value, 0);
}

BtorNode *
btor_cond_exp_node (Btor *btor,
                    BtorNode *e_cond,
                    BtorNode *e_if,
                    BtorNode *e_else)
{
  BtorNodeKind kind;

  e_cond = btor_simplify_exp (btor, e_cond);
  e_if   = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));

  if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_if)))
    kind = BTOR_ACOND_NODE;
  else
    kind = BTOR_BCOND_NODE;

  return ternary_exp (
      btor, kind, e_cond, e_if, e_else, BTOR_REAL_ADDR_NODE (e_if)->len);
}

BtorNode *
btor_not_exp (Btor *btor, BtorNode *exp)
{
  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  (void) btor;
  inc_exp_ref_counter (btor, exp);
  return BTOR_INVERT_NODE (exp);
}

BtorNode *
btor_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_add_exp (btor, e0, e1);
  else
    result = btor_add_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_neg_exp (Btor *btor, BtorNode *exp)
{
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
  BtorNode *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_slice_exp (btor, exp, upper, lower);
  else
    result = btor_slice_exp_node (btor, exp, upper, lower);

  assert (result);
  return result;
}

BtorNode *
btor_or_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (
      btor_and_exp (btor, BTOR_INVERT_NODE (e0), BTOR_INVERT_NODE (e1)));
}

BtorNode *
btor_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_eq_exp (btor, e0, e1);
  else
    result = btor_eq_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_and_exp (btor, e0, e1);
  else
    result = btor_and_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_xor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_xor_exp (btor, e0, e1));
}

BtorNode *
btor_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_concat_exp (btor, e0, e1);
  else
    result = btor_concat_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_cond_exp (Btor *btor, BtorNode *e_cond, BtorNode *e_if, BtorNode *e_else)
{
  BtorNode *result;

  e_cond = btor_simplify_exp (btor, e_cond);
  e_if   = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_cond_exp (btor, e_cond, e_if, e_else);
  else
    result = btor_cond_exp_node (btor, e_cond, e_if, e_else);

  assert (result);
  return result;
}

#if 0
BtorNode *
btor_cond_exp_no_rewrite (Btor * btor,
			  BtorNode * e_cond, BtorNode * e_if, BtorNode * e_else)
{
  BtorNode *result;

  e_cond = btor_simplify_exp (btor, e_cond);
  e_if = btor_simplify_exp (btor, e_if);
  e_else = btor_simplify_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));

  result = btor_cond_exp_node (btor, e_cond, e_if, e_else);
  assert (result);
  return result;
}
#endif

BtorNode *
btor_redor_exp (Btor *btor, BtorNode *exp)
{
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
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_and_exp (btor, e0, e1));
}

BtorNode *
btor_nor_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_or_exp (btor, e0, e1));
}

BtorNode *
btor_implies_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (BTOR_REAL_ADDR_NODE (e0)->len == 1);
  return BTOR_INVERT_NODE (btor_and_exp (btor, e0, BTOR_INVERT_NODE (e1)));
}

BtorNode *
btor_iff_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (BTOR_REAL_ADDR_NODE (e0)->len == 1);
  return btor_eq_exp (btor, e0, e1);
}

BtorNode *
btor_ne_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));
  return BTOR_INVERT_NODE (btor_eq_exp (btor, e0, e1));
}

BtorNode *
btor_uaddo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_mul_exp (btor, e0, e1);
  else
    result = btor_mul_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_umulo_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_ult_exp (btor, e0, e1);
  else
    result = btor_ult_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_slt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_ult_exp (btor, e1, e0);
}

BtorNode *
btor_sgt_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  return btor_slt_exp (btor, e1, e0);
}

BtorNode *
btor_ugte_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_sll_exp (btor, e0, e1);
  else
    result = btor_sll_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_srl_exp (btor, e0, e1);
  else
    result = btor_srl_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_sra_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_udiv_exp (btor, e0, e1);
  else
    result = btor_udiv_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_sdiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  BtorNode *result;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_urem_exp (btor, e0, e1);
  else
    result = btor_urem_exp_node (btor, e0, e1);

  assert (result);
  return result;
}

BtorNode *
btor_srem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
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
  BtorNode *result;

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_read_exp (btor, e_array, e_index);
  else
    result = btor_read_exp_node (btor, e_array, e_index);

  assert (result);
  return result;
}

BtorNode *
btor_write_exp (Btor *btor,
                BtorNode *e_array,
                BtorNode *e_index,
                BtorNode *e_value)
{
  BtorNode *result;

  e_array = btor_simplify_exp (btor, e_array);
  e_index = btor_simplify_exp (btor, e_index);
  e_value = btor_simplify_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));

  if (btor->rewrite_level > 0)
    result = btor_rewrite_write_exp (btor, e_array, e_index, e_value);
  else
    result = btor_write_exp_node (btor, e_array, e_index, e_value);

  assert (result);
  return result;
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
  BtorNode *one, *result;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_regular_unary_bv_exp_dbg (btor, exp));

  one    = btor_one_exp (btor, BTOR_REAL_ADDR_NODE (exp)->len);
  result = btor_sub_exp (btor, exp, one);
  btor_release_exp (btor, one);
  return result;
}

BtorNode *
btor_reduce (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  return btor_beta_reduce_full (btor, exp);
}

BtorNode *
btor_apply_and_reduce (Btor *btor, int argc, BtorNode **args, BtorNode *lambda)
{
  assert (btor);
  assert (argc >= 0);
  assert (argc < 1 || args);
  assert (lambda);

  int i;
  BtorNode *result, *cur;
  BtorNodePtrStack unassign;
  BtorMemMgr *mm;

  mm = btor->mm;

  BTOR_INIT_STACK (unassign);

  cur = lambda;
  for (i = 0; i < argc; i++)
  {
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_LAMBDA_NODE (cur));
    btor_assign_param (btor, cur, args[i]);
    BTOR_PUSH_STACK (mm, unassign, cur);
    cur = BTOR_REAL_ADDR_NODE (cur->e[1]);
  }

  result = btor_beta_reduce_full (btor, lambda);

  while (!BTOR_EMPTY_STACK (unassign))
  {
    cur = BTOR_POP_STACK (unassign);
    btor_unassign_param (btor, cur);
  }

  BTOR_RELEASE_STACK (mm, unassign);

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
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_get_index_exp_len (Btor *btor, BtorNode *e_array)
{
  assert (btor);
  assert (e_array);
  e_array = btor_simplify_exp (btor, e_array);
  assert (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (e_array)));
  assert (BTOR_IS_REGULAR_NODE (e_array));
  return e_array->index_len;
}

char *
btor_get_symbol_exp (Btor *btor, BtorNode *exp)
{
  /* do not pointer-chase! */
  assert (btor);
  assert (exp);
  (void) btor;
  return BTOR_REAL_ADDR_NODE (exp)->symbol;
}

int
btor_is_param_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (exp));
}

int
btor_is_bound_param (Btor *btor, BtorNode *param)
{
  assert (btor);
  assert (param);
  assert (BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (param)));
  param = btor_simplify_exp (btor, param);
  return ((BtorParamNode *) BTOR_REAL_ADDR_NODE (param))->lambda_exp != 0;
}

int
btor_is_lambda_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (exp));
}

#define BTOR_PUSH_NODE_IF_NOT_MARKED(e)          \
  do                                             \
  {                                              \
    BtorNode *child = BTOR_REAL_ADDR_NODE ((e)); \
    if (child->mark) break;                      \
    child->mark = 1;                             \
    BTOR_PUSH_STACK (mm, stack, child);          \
  } while (0)

static int
btor_cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return a->id - b->id;
}

static void
dump_node (FILE *file, BtorNode *node)
{
  int j;
  char idbuffer[20];
  const char *op;
  BtorNode *n;

  n = BTOR_REAL_ADDR_NODE (node);
  fprintf (file, "%d ", n->id);

  switch (n->kind)
  {
    case BTOR_ADD_NODE: op = "add"; goto PRINT;
    case BTOR_AND_NODE: op = "and"; goto PRINT;
    case BTOR_CONCAT_NODE: op = "concat"; goto PRINT;
    case BTOR_BCOND_NODE: op = "cond"; goto PRINT;
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: op = "eq"; goto PRINT;
    case BTOR_MUL_NODE: op = "mul"; goto PRINT;
    case BTOR_PROXY_NODE: op = "proxy"; goto PRINT;
    case BTOR_READ_NODE: op = "read"; goto PRINT;
    case BTOR_SLL_NODE: op = "sll"; goto PRINT;
    case BTOR_SRL_NODE: op = "srl"; goto PRINT;
    case BTOR_UDIV_NODE: op = "udiv"; goto PRINT;
    case BTOR_ULT_NODE: op = "ult"; goto PRINT;
    case BTOR_UREM_NODE:
      op = "urem";
    PRINT:
      fputs (op, file);
      fprintf (file, " %d", n->len);

      if (n->kind == BTOR_PROXY_NODE)
        fprintf (file, " %d", BTOR_GET_ID_NODE (n->simplified));
      else
        for (j = 0; j < n->arity; j++)
          fprintf (file, " %d", BTOR_GET_ID_NODE (n->e[j]));
      break;

    case BTOR_SLICE_NODE:
      fprintf (file,
               "slice %d %d %d %d",
               n->len,
               BTOR_GET_ID_NODE (n->e[0]),
               n->upper,
               n->lower);
      break;

    case BTOR_ARRAY_VAR_NODE:
      fprintf (file, "array %d %d", n->len, n->index_len);
      break;

    case BTOR_WRITE_NODE:
      fprintf (file,
               "write %d %d %d %d %d",
               n->len,
               n->index_len,
               BTOR_GET_ID_NODE (n->e[0]),
               BTOR_GET_ID_NODE (n->e[1]),
               BTOR_GET_ID_NODE (n->e[2]));
      break;

    case BTOR_ACOND_NODE:
      fprintf (file,
               "acond %d %d %d %d %d",
               n->len,
               n->index_len,
               BTOR_GET_ID_NODE (n->e[0]),
               BTOR_GET_ID_NODE (n->e[1]),
               BTOR_GET_ID_NODE (n->e[2]));
      break;

    case BTOR_BV_CONST_NODE:
      fprintf (file, "const %d %s", n->len, n->bits);
      break;

    case BTOR_PARAM_NODE: fprintf (file, "param %d", n->len); break;

    case BTOR_LAMBDA_NODE:
      fprintf (file,
               "lambda %d %d %d %d",
               n->len,
               n->index_len,
               BTOR_GET_ID_NODE (n->e[0]),
               BTOR_GET_ID_NODE (n->e[1]));
      break;

    default:
      assert (n->kind == BTOR_BV_VAR_NODE);
      fprintf (file, "var %d", n->len);
      sprintf (idbuffer, "%d", n->id);
      assert (n->symbol);
      if (strcmp (n->symbol, idbuffer)) fprintf (file, " %s", n->symbol);
      break;
  }

  fputc ('\n', file);
}

static void
dump_exps (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  BtorMemMgr *mm = btor->mm;
  int i, id = 0, maxid;
  BtorNodePtrStack work_stack, stack;
  BtorNodePtrStack const_stack, param_stack, bvvar_stack, avar_stack;
  BtorIntStack id_stack;
  BtorNode *root, *cur = 0;

  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);
  assert (mm);

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (stack);

  maxid = 0;

  if (btor->pprint)
  {
    BTOR_INIT_STACK (const_stack);
    BTOR_INIT_STACK (bvvar_stack);
    BTOR_INIT_STACK (avar_stack);
    BTOR_INIT_STACK (param_stack);
    BTOR_INIT_STACK (id_stack);
  }

  for (i = 0; i < nroots; i++)
  {
    root = roots[i];
    assert (root);
    BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (root));
  }

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_POP_STACK (work_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (cur->mark == 2) continue;

    if (cur->mark == 0)
    {
      cur->mark = 1;
      BTOR_PUSH_STACK (mm, work_stack, cur);
      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (cur->e[i]));
      // TODO: debug
      if (cur->simplified)
        BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (cur->simplified));
    }
    else
    {
      cur->mark = 2;
      if (btor->pprint)
      {
        switch (cur->kind)
        {
          case BTOR_BV_CONST_NODE:
            BTOR_PUSH_STACK (mm, const_stack, cur);
            break;
          case BTOR_BV_VAR_NODE: BTOR_PUSH_STACK (mm, bvvar_stack, cur); break;
          case BTOR_ARRAY_VAR_NODE:
            BTOR_PUSH_STACK (mm, avar_stack, cur);
            break;
          case BTOR_PARAM_NODE: BTOR_PUSH_STACK (mm, param_stack, cur); break;
          default: BTOR_PUSH_STACK (mm, stack, cur);
        }
      }
      else
        BTOR_PUSH_STACK (mm, stack, cur);
    }
  }

  BTOR_RELEASE_STACK (mm, work_stack);

  if (btor->pprint)
  {
    /* unmark and assign ids in order of DFS traversal - var, const and param
     * nodes are sorted by original id and dumped first */
    if (const_stack.start)
      qsort (const_stack.start,
             BTOR_COUNT_STACK (const_stack),
             sizeof cur,
             btor_cmp_node_id);
    if (bvvar_stack.start)
      qsort (bvvar_stack.start,
             BTOR_COUNT_STACK (bvvar_stack),
             sizeof cur,
             btor_cmp_node_id);
    if (avar_stack.start)
      qsort (avar_stack.start,
             BTOR_COUNT_STACK (avar_stack),
             sizeof cur,
             btor_cmp_node_id);
    if (param_stack.start)
      qsort (param_stack.start,
             BTOR_COUNT_STACK (param_stack),
             sizeof cur,
             btor_cmp_node_id);

    for (i = 0; i < BTOR_COUNT_STACK (const_stack); i++)
    {
      const_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, const_stack.start[i]->id);
      const_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (bvvar_stack); i++)
    {
      bvvar_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, bvvar_stack.start[i]->id);
      bvvar_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (avar_stack); i++)
    {
      avar_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, avar_stack.start[i]->id);
      avar_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (param_stack); i++)
    {
      param_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, param_stack.start[i]->id);
      param_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    {
      stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, stack.start[i]->id);
      stack.start[i]->id = ++id;
    }

    maxid = id;
  }
  else
  {
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;
    if (stack.start)
      qsort (
          stack.start, BTOR_COUNT_STACK (stack), sizeof cur, btor_cmp_node_id);
    if (BTOR_COUNT_STACK (stack))
      maxid = stack.start[BTOR_COUNT_STACK (stack) - 1]->id;
  }

  if (btor->pprint)
  {
    for (i = 0; i < BTOR_COUNT_STACK (const_stack); i++)
    {
      cur = const_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
    for (i = 0; i < BTOR_COUNT_STACK (bvvar_stack); i++)
    {
      cur = bvvar_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
    for (i = 0; i < BTOR_COUNT_STACK (avar_stack); i++)
    {
      cur = avar_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
    for (i = 0; i < BTOR_COUNT_STACK (param_stack); i++)
    {
      cur = param_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
  }
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur = stack.start[i];
    assert (BTOR_IS_REGULAR_NODE (cur));
    dump_node (file, cur);
  }

  for (i = 0; i < nroots; i++)
  {
    id = maxid + i;
    BTOR_ABORT_NODE (id == INT_MAX, "expression id overflow");
    fprintf (
        file, "%d root %d %d\n", id + 1, cur->len, BTOR_GET_ID_NODE (roots[i]));
  }

  if (btor->pprint)
  {
    /* reassign original ids */
    for (i = 0; i < BTOR_COUNT_STACK (const_stack); i++)
      const_stack.start[i]->id = id_stack.start[const_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (bvvar_stack); i++)
      bvvar_stack.start[i]->id = id_stack.start[bvvar_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (avar_stack); i++)
      avar_stack.start[i]->id = id_stack.start[avar_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (param_stack); i++)
      param_stack.start[i]->id = id_stack.start[param_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
      stack.start[i]->id = id_stack.start[stack.start[i]->id - 1];
  }

  BTOR_RELEASE_STACK (mm, stack);
  if (btor->pprint)
  {
    BTOR_RELEASE_STACK (mm, const_stack);
    BTOR_RELEASE_STACK (mm, bvvar_stack);
    BTOR_RELEASE_STACK (mm, avar_stack);
    BTOR_RELEASE_STACK (mm, param_stack);
    BTOR_RELEASE_STACK (mm, id_stack);
  }
}

void
btor_dump_exps (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
#ifndef NDEBUG
  int i;
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);
  for (i = 0; i < nroots; i++) assert (roots[i]);
#endif

  dump_exps (btor, file, roots, nroots);
}

void
btor_dump_exp (Btor *btor, FILE *file, BtorNode *root)
{
  assert (btor);
  assert (file);
  assert (root);
  dump_exps (btor, file, &root, 1);
}

void
btor_dump_exps_after_global_rewriting (Btor *btor, FILE *file)
{
  BtorNode *temp, **new_roots;
  BtorPtrHashBucket *b;
  int new_nroots, i;
  assert (!btor->inc_enabled);
  assert (!btor->model_gen);
  assert (btor->rewrite_level > 1);

  run_rewrite_engine (btor);

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
    for (b = btor->unsynthesized_constraints->first; b; b = b->next)
      new_roots[i++] = (BtorNode *) b->key;
    dump_exps (btor, file, new_roots, new_nroots);
    BTOR_DELETEN (btor->mm, new_roots, new_nroots);
  }
}

int
btor_vis_exp (Btor *btor, BtorNode *exp)
{
  char cmd[100], *path;
  FILE *file;
  int res;
  sprintf (cmd, "btorvis --ids ");
  path = cmd + strlen (cmd);
  sprintf (path, "/tmp/btorvisexp.%d.btor", btor->vis_idx++);
  file = fopen (path, "w");
  btor_dump_exp (btor, file, exp);
  fclose (file);
  strcat (cmd, "&");
  res = system (cmd);
  return res;
}

static void
btor_dump_smt_id (BtorNode *e, const char *symgenprefix, FILE *file)
{
  const char *type, *sym;
  BtorNode *u;

  u = BTOR_REAL_ADDR_NODE (e);

  if (u != e) fputs ("(bvnot ", file);

  if (BTOR_IS_BV_VAR_NODE (u))
  {
    sym = u->symbol;
    if (!isdigit (sym[0]))
    {
      fputs (sym, file);
      goto CLOSE;
    }

    type = "v";
  }
  else if (BTOR_IS_ARRAY_VAR_NODE (u))
    type = "a";
  else
    type = symgenprefix;

  fprintf (file, "%s%d", type, u ? u->id : -1);

CLOSE:
  if (u != e) fputc (')', file);
}

static void
btor_dump_bit_smt (int format, int bit, FILE *file)
{
  assert (bit == 0 || bit == 1);
  if (format < 2)
    fprintf (file, "bv%d[1]", bit);
  else
    fprintf (file, "#b%d", bit);
}

void
btor_dump_smt (Btor *btor, int format, FILE *file, BtorNode *root)
{
  const char *sgp = (format < 2) ? "?e" : "$e";
  int next, i, j, arrays, lets, pad;
  BtorMemMgr *mm = btor->mm;
  BtorNodePtrStack stack;
  const char *op;
  char *tmp;
  BtorNode *e;

  assert (btor);
  assert (file);
  assert (root);

  BTOR_INIT_STACK (stack);
  BTOR_PUSH_NODE_IF_NOT_MARKED (root);

  arrays = 0;
  next   = 0;

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_NODE (e));
    assert (e->mark);

    if (BTOR_IS_BV_CONST_NODE (e)) continue;

    if (BTOR_IS_BV_VAR_NODE (e)) continue;

    if (BTOR_IS_ARRAY_VAR_NODE (e))
    {
      arrays = 1;
      continue;
    }

    for (i = 0; i < e->arity; i++) BTOR_PUSH_NODE_IF_NOT_MARKED (e->e[i]);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;

  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof e, btor_cmp_node_id);

  if (format < 2)
  {
    fputs ("(benchmark ", file);
    if (BTOR_IS_INVERTED_NODE (root)) fputs ("not", file);
    fprintf (file, "root%d\n", BTOR_REAL_ADDR_NODE (root)->id);

    if (arrays)
      fputs (":logic QF_AUFBV\n", file);
    else
      fputs (":logic QF_BV\n", file);
  }
  else
  {
    if (arrays)
      fputs ("(set-logic QF_AUFBV)\n", file);
    else
      fputs ("(set-logic QF_BV)\n", file);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_NODE (e));

    if (!BTOR_IS_BV_VAR_NODE (e) && !BTOR_IS_ARRAY_VAR_NODE (e)) continue;

    if (format < 2)
    {
      fputs (":extrafuns ((", file);

      btor_dump_smt_id (e, sgp, file);

      if (BTOR_IS_BV_VAR_NODE (e))
        fprintf (file, " BitVec[%d]))\n", e->len);
      else
        fprintf (file, " Array[%d:%d]))\n", e->index_len, e->len);
    }
    else
    {
      fputs ("(declare-fun ", file);
      btor_dump_smt_id (e, sgp, file);
      fputs (" () (", file);

      if (BTOR_IS_BV_VAR_NODE (e))
        fprintf (file, "_ BitVec %d", e->len);
      else
        fprintf (
            file, "Array (_ BitVec %d) (_ BitVec %d)", e->index_len, e->len);

      fputs ("))\n", file);
    }
  }

  if (format < 2)
    fputs (":formula\n", file);
  else
    fputs ("(assert\n", file);

  lets = 0;

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_NODE (e));

    if (!e || BTOR_IS_BV_VAR_NODE (e) || BTOR_IS_ARRAY_VAR_NODE (e)) continue;

    lets++;

    fputs ("(let (", file);
    if (format >= 2) fputc ('(', file);
    btor_dump_smt_id (e, sgp, file);
    fputc (' ', file);

    if (e->kind == BTOR_BV_CONST_NODE)
    {
      tmp = btor_const_to_decimal (mm, e->bits);
      if (format < 2)
        fprintf (file, "bv%s[%d]", tmp, e->len);
      else
        fprintf (file, "(_ bv%s %d)", tmp, e->len);
      btor_freestr (mm, tmp);
    }
    else if (e->kind == BTOR_SLICE_NODE)
    {
      if (format < 2)
        fprintf (file, "(extract[%d:%d] ", e->upper, e->lower);
      else
        fprintf (file, "((_ extract %d %d) ", e->upper, e->lower);

      btor_dump_smt_id (e->e[0], sgp, file);
      fputc (')', file);
    }
    else if (e->kind == BTOR_SLL_NODE || e->kind == BTOR_SRL_NODE)
    {
      fputc ('(', file);

      if (e->kind == BTOR_SRL_NODE)
        fputs ("bvlshr", file);
      else
        fputs ("bvshl", file);

      fputc (' ', file);
      btor_dump_smt_id (e->e[0], sgp, file);
      fputc (' ', file);

      assert (e->len > 1);
      pad = e->len - BTOR_REAL_ADDR_NODE (e->e[1])->len;

      if (format < 2)
        fprintf (file, " (zero_extend[%d] ", pad);
      else
        fprintf (file, " ((_ zero_extend %d) ", pad);

      btor_dump_smt_id (e->e[1], sgp, file);

      fputs ("))", file);
    }
    else if (BTOR_IS_ARRAY_OR_BV_COND_NODE (e))
    {
      fputs ("(ite (= ", file);
      btor_dump_bit_smt (format, 1, file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[0], sgp, file);
      fputs (") ", file);
      btor_dump_smt_id (e->e[1], sgp, file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[2], sgp, file);
      fputc (')', file);
    }
    else if (BTOR_IS_ARRAY_OR_BV_EQ_NODE (e) || e->kind == BTOR_ULT_NODE)
    {
      fputs ("(ite (", file);
      if (e->kind == BTOR_ULT_NODE)
        fputs ("bvult", file);
      else
        fputc ('=', file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[0], sgp, file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[1], sgp, file);
      fputs (") ", file);
      btor_dump_bit_smt (format, 1, file);
      fputc (' ', file);
      btor_dump_bit_smt (format, 0, file);
      fputc (')', file);
    }
    else
    {
      fputc ('(', file);

      switch (e->kind)
      {
        case BTOR_AND_NODE: op = "bvand"; break;
        case BTOR_ADD_NODE: op = "bvadd"; break;
        case BTOR_MUL_NODE: op = "bvmul"; break;
        case BTOR_UDIV_NODE: op = "bvudiv"; break;
        case BTOR_UREM_NODE: op = "bvurem"; break;
        case BTOR_CONCAT_NODE: op = "concat"; break;
        case BTOR_READ_NODE: op = "select"; break;

        default:
        case BTOR_WRITE_NODE:
          assert (e->kind == BTOR_WRITE_NODE);
          op = "store";
          break;
      }

      fputs (op, file);

      for (j = 0; j < e->arity; j++)
      {
        fputc (' ', file);
        btor_dump_smt_id (e->e[j], sgp, file);
      }

      fputc (')', file);
    }

    if (format >= 2) fputc (')', file);
    fputs (")\n", file);
  }

  fputs ("(not (= ", file);
  btor_dump_smt_id (root, sgp, file);

  if (format < 2)
    fprintf (file, " bv0[%d]))\n", BTOR_REAL_ADDR_NODE (root)->len);
  else
    fprintf (file, " (_ bv0 %d)))\n", BTOR_REAL_ADDR_NODE (root)->len);

  for (i = 0; i < lets + 1; i++) fputc (')', file);

#if 0
  if (format >= 2)
    fputc (')', file);
#endif

  fputc ('\n', file);

  BTOR_RELEASE_STACK (mm, stack);

  if (format >= 2)
  {
    fputs ("(check-sat)\n", file);
    fputs ("(exit)\n", file);
  }

  fflush (file);
}

Btor *
btor_new_btor (void)
{
  BtorMemMgr *mm;
  Btor *btor;

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, btor);

  btor->mm = mm;

  BTOR_INIT_UNIQUE_TABLE (mm, btor->nodes_unique_table);

  btor->avmgr = btor_new_aigvec_mgr (mm);

  btor->bv_vars = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
  btor->array_vars =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->lambdas = btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);

  btor->bv_lambda_id      = 1;
  btor->array_lambda_id   = 1;
  btor->valid_assignments = 1;
  btor->rewrite_level     = 3;
  btor->vread_index_id    = 1;
  btor->msgtick           = -1;
  btor->pprint            = 1;

  BTOR_PUSH_STACK (btor->mm, btor->nodes_id_table, 0);

  btor->exp_pair_eq_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  btor->exp_pair_and_table = btor_new_ptr_hash_table (
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

  btor->true_exp = btor_true_exp (btor);

  return btor;
}

Btor *
btor_clone_btor (Btor *orig)
{
  BtorMemMgr *mm;
  Btor *btor;

  (void) orig;

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, btor);

  btor->mm = mm;

  return btor;
}

void
btor_set_rewrite_level_btor (Btor *btor, int rewrite_level)
{
  assert (btor);
  assert (btor->rewrite_level >= 0);
  assert (btor->rewrite_level <= 3);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == 2);
  btor->rewrite_level = rewrite_level;
}

void
btor_generate_model_for_all_reads (Btor *btor)
{
  assert (btor);
  btor->generate_model_for_all_reads = 1;
}

int
btor_set_sat_solver (Btor *btor, const char *solver)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;

  assert (btor);
  assert (solver);

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);

  if (!strcasecmp (solver, "lingeling"))
#ifdef BTOR_USE_LINGELING
  {
    btor_enable_lingeling_sat (smgr, 0, 0);
    return 1;
  }
#else
    return 0;
#endif

  if (!strcasecmp (solver, "minisat"))
#ifdef BTOR_USE_MINISAT
  {
    btor_enable_minisat_sat (smgr);
    return 1;
  }
#else
    return 0;
#endif

  if (!strcasecmp (solver, "picosat"))
#ifdef BTOR_USE_PICOSAT
  {
    btor_enable_picosat_sat (smgr);
    return 1;
  }
#else
    return 0;
#endif

  return 0;
}

void
btor_enable_rewrite_writes (Btor *btor)
{
  assert (btor);
  btor->rewrite_writes = 1;
}

void
btor_enable_rewrite_reads (Btor *btor)
{
  assert (btor);
  btor->rewrite_reads = 1;
}

void
btor_disable_pretty_print (Btor *btor)
{
  assert (btor);
  btor->pprint = 0;
}

void
btor_enable_model_gen (Btor *btor)
{
  assert (btor);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == 2);
  if (!btor->model_gen)
  {
    btor->model_gen = 1;

    btor->var_rhs =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

    btor->array_rhs =
        btor_new_ptr_hash_table (btor->mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);
  }
}

void
btor_enable_inc_usage (Btor *btor)
{
  assert (btor);
  assert (btor->btor_sat_btor_called == 0);
  btor->inc_enabled = 1;
}

void
btor_set_verbosity_btor (Btor *btor, int verbosity)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;

  assert (btor);
  assert (btor->verbosity >= -1);
  assert (BTOR_COUNT_STACK (btor->nodes_id_table) == 2);
  btor->verbosity = verbosity;

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);
  btor_set_verbosity_aigvec_mgr (avmgr, verbosity);
  btor_set_verbosity_aig_mgr (amgr, verbosity);
  btor_set_verbosity_sat_mgr (smgr, verbosity);
}

void
btor_set_loglevel_btor (Btor *btor, int loglevel)
{
  assert (btor);
  (void) btor;
  (void) loglevel;
#ifndef NBTORLOG
  btor->loglevel = loglevel;
#endif
}

void
btor_delete_btor (Btor *btor)
{
  BtorPtrHashTable *ht;
  BtorPtrHashBucket *b;
  BtorMemMgr *mm;
  BtorNode *exp;

  assert (btor);

  mm = btor->mm;

  btor_release_exp (btor, btor->true_exp);

  for (b = btor->lambdas->first; b; b = b->next)
  {
    ht = ((BtorLambdaNode *) b->key)->synth_reads;
    while (ht && ht->count > 0u)
    {
      exp = (BtorNode *) ht->first->key;
      btor_remove_from_ptr_hash_table (ht, exp, 0, 0);
      btor_release_exp (btor, exp);
    }
  }

  for (b = btor->exp_pair_eq_table->first; b; b = b->next)
  {
    delete_exp_pair (btor, (BtorNodePair *) b->key);
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
  }
  btor_delete_ptr_hash_table (btor->exp_pair_eq_table);

  for (b = btor->exp_pair_and_table->first; b; b = b->next)
  {
    delete_exp_pair (btor, (BtorNodePair *) b->key);
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
  }
  btor_delete_ptr_hash_table (btor->exp_pair_and_table);

  for (b = btor->varsubst_constraints->first; b; b = b->next)
  {
    btor_release_exp (btor, (BtorNode *) b->key);
    btor_release_exp (btor, (BtorNode *) b->data.asPtr);
  }
  btor_delete_ptr_hash_table (btor->varsubst_constraints);

  for (b = btor->embedded_constraints->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->embedded_constraints);

  for (b = btor->unsynthesized_constraints->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->unsynthesized_constraints);

  for (b = btor->synthesized_constraints->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->synthesized_constraints);

  for (b = btor->assumptions->first; b; b = b->next)
    btor_release_exp (btor, (BtorNode *) b->key);
  btor_delete_ptr_hash_table (btor->assumptions);

  if (btor->model_gen)
  {
    for (b = btor->var_rhs->first; b; b = b->next)
      btor_release_exp (btor, (BtorNode *) b->key);
    btor_delete_ptr_hash_table (btor->var_rhs);

    for (b = btor->array_rhs->first; b; b = b->next)
      btor_release_exp (btor, (BtorNode *) b->key);
    btor_delete_ptr_hash_table (btor->array_rhs);
  }

  BTOR_RELEASE_STACK (mm, btor->arrays_with_model);

#ifndef NDEBUG
  int k;
  if (btor->nodes_unique_table.num_elements)
    BTORLOG ("*** btor->nodes_unique_table.num_elements: %d",
             0,
             btor->nodes_unique_table.num_elements);
  for (k = 0; k < btor->nodes_unique_table.size; k++)
    if (btor->nodes_unique_table.chains[k])
      BTORLOG ("  unreleased node: %s",
               node2string (btor->nodes_unique_table.chains[k]));
#endif
  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKEXP")
          || btor->nodes_unique_table.num_elements == 0);
  BTOR_RELEASE_UNIQUE_TABLE (mm, btor->nodes_unique_table);
  BTOR_RELEASE_STACK (mm, btor->nodes_id_table);

  assert (getenv ("BTORLEAK") || getenv ("BTORLEAKSORT")
          || btor->sorts_unique_table.num_elements == 0);
  BTOR_RELEASE_UNIQUE_TABLE (mm, btor->sorts_unique_table);

  btor_delete_ptr_hash_table (btor->bv_vars);
  btor_delete_ptr_hash_table (btor->array_vars);
  btor_delete_ptr_hash_table (btor->lambdas);

  btor_delete_aigvec_mgr (btor->avmgr);

  assert (btor->rec_rw_calls == 0);
  BTOR_DELETE (mm, btor);
  btor_delete_mem_mgr (mm);
}

static int
constraints_stats_changes (Btor *btor)
{
  int res;

  if (btor->stats.oldconstraints.varsubst && !btor->varsubst_constraints->count)
    return INT_MAX;

  if (btor->stats.oldconstraints.embedded && !btor->embedded_constraints->count)
    return INT_MAX;

  if (btor->stats.oldconstraints.unsynthesized
      && !btor->unsynthesized_constraints->count)
    return INT_MAX;

  res = abs (btor->stats.oldconstraints.varsubst
             - btor->varsubst_constraints->count);

  res += abs (btor->stats.oldconstraints.embedded
              - btor->embedded_constraints->count);

  res += abs (btor->stats.oldconstraints.unsynthesized
              - btor->unsynthesized_constraints->count);

  res += abs (btor->stats.oldconstraints.synthesized
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

    if (btor->verbosity == 1 && changes < 100000) return;

    if (btor->verbosity == 2 && changes < 1000) return;

    if (btor->verbosity == 3 && changes < 10) return;

    if (!changes) return;
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

  btor->stats.oldconstraints.varsubst = btor->varsubst_constraints->count;
  btor->stats.oldconstraints.embedded = btor->embedded_constraints->count;
  btor->stats.oldconstraints.unsynthesized =
      btor->unsynthesized_constraints->count;
  btor->stats.oldconstraints.synthesized = btor->synthesized_constraints->count;
}

/* we do not count proxies */
static int
number_of_ops (Btor *btor)
{
  int i, result;
  assert (btor);

  result = 0;
  for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++) result += btor->ops[i];

  return result;
}

static double
percent (double a, double b)
{
  return b ? 100.0 * a / b : 0.0;
}

void
btor_print_stats_btor (Btor *btor)
{
  int num_final_ops, verbosity, i;

  assert (btor);

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
  if (btor->ops[BTOR_AEQ_NODE])
    btor_msg_exp (btor, "virtual reads: %d", btor->stats.vreads);

  if (verbosity > 2)
  {
    btor_msg_exp (btor, "max rec. RW: %d", btor->stats.max_rec_rw_calls);
    btor_msg_exp (btor,
                  "number of expressions ever created: %lld",
                  btor->stats.expressions);
    num_final_ops = number_of_ops (btor);
    assert (num_final_ops >= 0);
    btor_msg_exp (btor, "number of final expressions: %d", num_final_ops);
    if (num_final_ops > 0)
      for (i = 1; i < BTOR_NUM_OPS_NODE - 1; i++)
        if (btor->ops[i])
          btor_msg_exp (btor, " %s:%d", g_op2string[i], btor->ops[i]);
  }

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
  btor_msg_exp (btor,
                "gaussian elimination in linear equations: %d",
                btor->stats.gaussian_eliminations);
  btor_msg_exp (
      btor, "eliminated sliced variables: %d", btor->stats.eliminated_slices);
  btor_msg_exp (btor,
                "extracted skeleton constraints: %d",
                btor->stats.skeleton_constraints);
  btor_msg_exp (btor, "add normalizations: %d", btor->stats.adds_normalized);
  btor_msg_exp (btor, "mul normalizations: %d", btor->stats.muls_normalized);
  btor_msg_exp (btor,
                "read over write propagations during construction: %d",
                btor->stats.read_props_construct);
  btor_msg_exp (btor,
                "synthesis assignment inconsistencies: %d",
                btor->stats.synthesis_assignment_inconsistencies);
  btor_msg_exp (btor, "beta reductions: %d", btor->stats.beta_reduce_calls);
  btor_msg_exp (btor, "expression evaluations: %d", btor->stats.eval_exp_calls);
  btor_msg_exp (
      btor, "synthesized lambda reads: %d", btor->stats.lambda_synth_reads);
  btor_msg_exp (
      btor, "lambda chains merged: %d", btor->stats.lambda_chains_merged);
  btor_msg_exp (btor, "lambdas merged: %d", btor->stats.lambdas_merged);

  btor_msg_exp (btor, "");
  btor_msg_exp (btor, "%.2f seconds beta-reduction", btor->time.beta);
  btor_msg_exp (btor, "%.2f seconds expression evaluation", btor->time.eval);
  btor_msg_exp (btor, "");
  btor_msg_exp (btor, "%.2f seconds in rewriting engine", btor->time.rewrite);
  btor_msg_exp (btor, "%.2f seconds in pure SAT solving", btor->time.sat);
  btor_msg_exp (btor, "");
  btor_msg_exp (
      btor,
      "%.2f seconds in variable substitution during rewriting (%.0f%%)",
      btor->time.subst,
      percent (btor->time.subst, btor->time.rewrite));
  btor_msg_exp (
      btor,
      "%.2f seconds in embedded constraint replacing during rewriting (%.0f%%)",
      btor->time.slicing,
      percent (btor->time.slicing, btor->time.rewrite));
#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
  btor_msg_exp (btor,
                "%.2f seconds in slicing during rewriting (%.0f%%)",
                btor->time.slicing,
                percent (btor->time.slicing, btor->time.rewrite));
#endif
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  btor_msg_exp (btor,
                "%.2f seconds skeleton preprocessing during rewriting (%.0f%%)",
                btor->time.skel,
                percent (btor->time.skel, btor->time.rewrite));
#endif
}

/*------------------------------------------------------------------------*/

BtorMemMgr *
btor_get_mem_mgr_btor (const Btor *btor)
{
  assert (btor);
  return btor->mm;
}

BtorAIGVecMgr *
btor_get_aigvec_mgr_btor (const Btor *btor)
{
  assert (btor);
  return btor->avmgr;
}

static BtorNode *
vread_index_exp (Btor *btor, int len)
{
  char *symbol;
  size_t bytes;
  BtorNode *result;
  assert (btor);
  assert (len > 0);
  BTOR_ABORT_NODE (btor->vread_index_id == INT_MAX, "vread index id overflow");
  bytes = 6 + btor_num_digits_util (btor->vread_index_id) + 1;
  bytes *= sizeof (char);
  symbol = (char *) btor_malloc (btor->mm, bytes);
  sprintf (symbol, "vindex%d", btor->vread_index_id);
  btor->vread_index_id++;
  result = btor_var_exp (btor, len, symbol);
  btor_free (btor->mm, symbol, bytes);
  return result;
}

static void insert_unsynthesized_constraint (Btor *, BtorNode *);

static void
synthesize_array_equality (Btor *btor, BtorNode *aeq)
{
  BtorNode *index, *read1, *read2;
  BtorAIGVecMgr *avmgr;
  assert (btor);
  assert (aeq);
  assert (BTOR_IS_REGULAR_NODE (aeq));
  assert (BTOR_IS_ARRAY_EQ_NODE (aeq));
  assert (!BTOR_IS_SYNTH_NODE (aeq));
  avmgr   = btor->avmgr;
  aeq->av = btor_var_aigvec (avmgr, 1);
  /* generate virtual reads */
  index              = vread_index_exp (btor, aeq->e[0]->index_len);
  index->vread_index = 1;

  /* we do not want optimizations for the virtual reads
   * and the equality, e.g. rewriting of reads on array
   * conditionals, so we call 'btor_read_exp_node' directly.
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

static void
synthesize_exp (Btor *btor, BtorNode *exp, BtorPtrHashTable *backannotation)
{
  BtorNodePtrStack exp_stack;
  BtorNode *cur;
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

  assert (btor);
  assert (exp);

  mm    = btor->mm;
  avmgr = btor->avmgr;
  count = 0;

  BTOR_INIT_STACK (exp_stack);
  BTOR_PUSH_STACK (mm, exp_stack, exp);
  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (exp_stack));

    assert (cur->synth_mark >= 0);
    assert (cur->synth_mark <= 2);

    if (BTOR_IS_SYNTH_NODE (cur)) continue;

    if (cur->synth_mark >= 2) continue;

    count++;

    if (cur->synth_mark == 0)
    {
      cur->reachable = 1;
      if (BTOR_IS_BV_CONST_NODE (cur))
      {
        cur->av = btor_const_aigvec (avmgr, cur->bits);
        BTORLOG ("  synthesized: %s", node2string (cur));
      }
      else if (BTOR_IS_BV_VAR_NODE (cur))
      {
        cur->av = btor_var_aigvec (avmgr, cur->len);
        BTORLOG ("  synthesized: %s", node2string (cur));
        if (backannotation)
        {
          // TODO param handling?
          name = btor_get_symbol_exp (btor, cur);
          len  = (int) strlen (name) + 40;
          if (cur->len > 1)
          {
            indexed_name = btor_malloc (mm, len);
            for (i = 0; i < cur->av->len; i++)
            {
              b = btor_insert_in_ptr_hash_table (backannotation,
                                                 cur->av->aigs[i]);
              assert (b->key == cur->av->aigs[i]);
              sprintf (indexed_name, "%s[%d]", name, i);
              b->data.asStr = btor_strdup (mm, indexed_name);
            }
            btor_free (mm, indexed_name, len);
          }
          else
          {
            assert (cur->len == 1);
            b = btor_insert_in_ptr_hash_table (backannotation,
                                               cur->av->aigs[0]);
            assert (b->key == cur->av->aigs[0]);
            b->data.asStr = btor_strdup (mm, name);
          }
        }
      }
      else if (BTOR_IS_ARRAY_VAR_NODE (cur))
      {
        /* nothing to synthesize for array base case */
      }
      else if (BTOR_IS_WRITE_NODE (cur) || BTOR_IS_LAMBDA_NODE (cur)
               || BTOR_IS_ARRAY_COND_NODE (cur))
      {
        goto REGULAR_CASE;
      }
      else
      {
        /* Writes and Lambda expressions cannot be reached directly,
         * hence we stop the synthesis as soon as we reach reads or
         * array equalities.  If we synthesize writes later, we only
         * synthesize its index and value, but not the write itself.
         * If there are no reads or array equalities on a write, then
         * it is not reachable. (Lambdas are treated similarly.)
         */
        assert (!BTOR_IS_WRITE_NODE (cur));
        assert (!BTOR_IS_LAMBDA_NODE (cur));

        /* Atomic arrays and array conditionals should also not be
         * reached directly.
         */
        assert (!BTOR_IS_ARRAY_VAR_NODE (cur));
        assert (!BTOR_IS_ARRAY_COND_NODE (cur));

        /* special cases */
        if (BTOR_IS_READ_NODE (cur) && !cur->parameterized)
        {
          cur->av = btor_var_aigvec (avmgr, cur->len);
          BTORLOG ("  synthesized: %s", node2string (cur));
          assert (BTOR_IS_REGULAR_NODE (cur->e[0]));
          assert (BTOR_IS_ARRAY_NODE (cur->e[0]));
          goto REGULAR_CASE;
        }
        else if (BTOR_IS_ARRAY_EQ_NODE (cur) && !cur->parameterized)
        {
          /* Generate virtual reads and create AIG variable for
           * array equality.
           */
          synthesize_array_equality (btor, cur);
          BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
          BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
          goto REGULAR_CASE;
        }
        else
        {
        REGULAR_CASE:
          /* always skip lambda and parameterized nodes */
          if (BTOR_IS_LAMBDA_NODE (cur) || cur->parameterized)
            cur->synth_mark = 2;
          else
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
      assert (!BTOR_IS_READ_NODE (cur));
      assert (!BTOR_IS_LAMBDA_NODE (cur));

      if (cur->arity == 1)
      {
        assert (cur->kind == BTOR_SLICE_NODE);
        invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
        av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
        if (invert_av0) btor_invert_aigvec (avmgr, av0);
        cur->av = btor_slice_aigvec (avmgr, av0, cur->upper, cur->lower);
        BTORLOG ("  synthesized: %s", node2string (cur));
        if (invert_av0) btor_invert_aigvec (avmgr, av0);
      }
      else if (cur->arity == 2)
      {
        /* We have to check if the children are in the same memory
         * place if they are in the same memory place. Then we need to
         * allocate memory for the AIG vectors if they are not, then
         * we can invert them in place and invert them back afterwards
         * (only if necessary) .
         */
        same_children_mem =
            BTOR_REAL_ADDR_NODE (cur->e[0]) == BTOR_REAL_ADDR_NODE (cur->e[1]);
        if (same_children_mem)
        {
          av0 = BTOR_AIGVEC_NODE (btor, cur->e[0]);
          av1 = BTOR_AIGVEC_NODE (btor, cur->e[1]);
        }
        else
        {
          invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
          av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
          if (invert_av0) btor_invert_aigvec (avmgr, av0);
          invert_av1 = BTOR_IS_INVERTED_NODE (cur->e[1]);
          av1        = BTOR_REAL_ADDR_NODE (cur->e[1])->av;
          if (invert_av1) btor_invert_aigvec (avmgr, av1);
        }
        switch (cur->kind)
        {
          case BTOR_AND_NODE:
            cur->av = btor_and_aigvec (avmgr, av0, av1);
            break;
          case BTOR_BEQ_NODE: cur->av = btor_eq_aigvec (avmgr, av0, av1); break;
          case BTOR_ADD_NODE:
            cur->av = btor_add_aigvec (avmgr, av0, av1);
            break;
          case BTOR_MUL_NODE:
            cur->av = btor_mul_aigvec (avmgr, av0, av1);
            break;
          case BTOR_ULT_NODE:
            cur->av = btor_ult_aigvec (avmgr, av0, av1);
            break;
          case BTOR_SLL_NODE:
            cur->av = btor_sll_aigvec (avmgr, av0, av1);
            break;
          case BTOR_SRL_NODE:
            cur->av = btor_srl_aigvec (avmgr, av0, av1);
            break;
          case BTOR_UDIV_NODE:
            cur->av = btor_udiv_aigvec (avmgr, av0, av1);
            break;
          case BTOR_UREM_NODE:
            cur->av = btor_urem_aigvec (avmgr, av0, av1);
            break;
          default:
            assert (cur->kind == BTOR_CONCAT_NODE);
            cur->av = btor_concat_aigvec (avmgr, av0, av1);
            break;
        }
        BTORLOG ("  synthesized: %s", node2string (cur));

        if (same_children_mem)
        {
          btor_release_delete_aigvec (avmgr, av0);
          btor_release_delete_aigvec (avmgr, av1);
        }
        else
        {
          if (invert_av0) btor_invert_aigvec (avmgr, av0);
          if (invert_av1) btor_invert_aigvec (avmgr, av1);
        }
      }
      else
      {
        assert (cur->arity == 3);

        if (BTOR_IS_BV_COND_NODE (cur))
        {
          same_children_mem =
              BTOR_REAL_ADDR_NODE (cur->e[0]) == BTOR_REAL_ADDR_NODE (cur->e[1])
              || BTOR_REAL_ADDR_NODE (cur->e[0])
                     == BTOR_REAL_ADDR_NODE (cur->e[2])
              || BTOR_REAL_ADDR_NODE (cur->e[1])
                     == BTOR_REAL_ADDR_NODE (cur->e[2]);
          if (same_children_mem)
          {
            av0 = BTOR_AIGVEC_NODE (btor, cur->e[0]);
            av1 = BTOR_AIGVEC_NODE (btor, cur->e[1]);
            av2 = BTOR_AIGVEC_NODE (btor, cur->e[2]);
          }
          else
          {
            invert_av0 = BTOR_IS_INVERTED_NODE (cur->e[0]);
            av0        = BTOR_REAL_ADDR_NODE (cur->e[0])->av;
            if (invert_av0) btor_invert_aigvec (avmgr, av0);
            invert_av1 = BTOR_IS_INVERTED_NODE (cur->e[1]);
            av1        = BTOR_REAL_ADDR_NODE (cur->e[1])->av;
            if (invert_av1) btor_invert_aigvec (avmgr, av1);
            invert_av2 = BTOR_IS_INVERTED_NODE (cur->e[2]);
            av2        = BTOR_REAL_ADDR_NODE (cur->e[2])->av;
            if (invert_av2) btor_invert_aigvec (avmgr, av2);
          }
          cur->av = btor_cond_aigvec (avmgr, av0, av1, av2);
          BTORLOG ("  synthesized: %s", node2string (cur));
          if (same_children_mem)
          {
            btor_release_delete_aigvec (avmgr, av2);
            btor_release_delete_aigvec (avmgr, av1);
            btor_release_delete_aigvec (avmgr, av0);
          }
          else
          {
            if (invert_av0) btor_invert_aigvec (avmgr, av0);
            if (invert_av1) btor_invert_aigvec (avmgr, av1);
            if (invert_av2) btor_invert_aigvec (avmgr, av2);
          }
        }
      }
    }
  }

  BTOR_RELEASE_STACK (mm, exp_stack);
  mark_synth_mark_exp (btor, exp, 0);

  if (count > 0 && btor->verbosity > 3)
    btor_msg_exp (btor, "synthesized %u expressions into AIG vectors", count);
}

static BtorAIG *
exp_to_aig (Btor *btor, BtorNode *exp)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorAIGVec *av;
  BtorAIG *result;

  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);

  synthesize_exp (btor, exp, 0);
  av = BTOR_REAL_ADDR_NODE (exp)->av;

  assert (av);
  assert (av->len == 1);

  result = av->aigs[0];

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_not_aig (amgr, result);
  else
    result = btor_copy_aig (amgr, result);

  return result;
}

static int
exp_to_cnf_lit (Btor *btor, BtorNode *exp)
{
  int res, sign, val;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorAIG *aig;

  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  exp = btor_simplify_exp (btor, exp);

  sign = 1;

  if (BTOR_IS_INVERTED_NODE (exp))
  {
    exp = BTOR_INVERT_NODE (exp);
    sign *= -1;
  }

  aig = exp_to_aig (btor, exp);

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);

  if (BTOR_IS_CONST_AIG (aig))
  {
    res = smgr->true_lit;
    if (aig == BTOR_AIG_FALSE) sign *= -1;
  }
  else
  {
    if (BTOR_IS_INVERTED_AIG (aig))
    {
      aig = BTOR_INVERT_AIG (aig);
      sign *= -1;
    }

    if (!aig->cnf_id)
    {
      assert (!exp->tseitin);
      btor_aig_to_sat_tseitin (amgr, aig);
      exp->tseitin = 1;
    }

    res = aig->cnf_id;
    btor_release_aig (amgr, aig);

    if ((val = btor_fixed_sat (smgr, res)))
    {
      res = smgr->true_lit;
      if (val < 0) sign *= -1;
    }
  }
  res *= sign;

  return res;
}

BtorAIGVec *
btor_exp_to_aigvec (Btor *btor, BtorNode *exp, BtorPtrHashTable *backannotation)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *result;

  assert (exp);

  avmgr = btor->avmgr;

  synthesize_exp (btor, exp, backannotation);
  result = BTOR_REAL_ADDR_NODE (exp)->av;
  assert (result);

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_not_aigvec (avmgr, result);
  else
    result = btor_copy_aigvec (avmgr, result);

  return result;
}

/* Compares the assignments of two expressions. */
static int
compare_assignments (BtorNode *exp1, BtorNode *exp2)
{
  int return_val, val1, val2, i, len;
  Btor *btor;
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorAIGVec *av1, *av2;
  BtorAIG *aig1, *aig2;
  assert (exp1);
  assert (exp2);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  assert (BTOR_REAL_ADDR_NODE (exp1)->len == BTOR_REAL_ADDR_NODE (exp2)->len);
  assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (exp1)));
  assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (exp2)));
  btor = BTOR_REAL_ADDR_NODE (exp1)->btor;
  assert (btor);
  return_val = 0;
  avmgr      = btor->avmgr;
  amgr       = btor_get_aig_mgr_aigvec_mgr (avmgr);
  av1        = BTOR_REAL_ADDR_NODE (exp1)->av;
  av2        = BTOR_REAL_ADDR_NODE (exp2)->av;
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_NODE (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_NODE (exp2, av2->aigs[i]);

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
hash_assignment (BtorNode *exp)
{
  unsigned int hash;
  Btor *btor;
  BtorAIGVecMgr *avmgr;
  BtorNode *real_exp;
  BtorAIGVec *av;
  int invert_av;
  char *assignment;
  assert (exp);
  real_exp  = BTOR_REAL_ADDR_NODE (exp);
  btor      = real_exp->btor;
  avmgr     = btor->avmgr;
  av        = real_exp->av;
  invert_av = BTOR_IS_INVERTED_NODE (exp);
  if (invert_av) btor_invert_aigvec (avmgr, av);
  assignment = btor_assignment_aigvec (avmgr, av);
  hash       = btor_hashstr (assignment);
  btor_freestr (btor->mm, assignment);
  /* invert back if necessary */
  if (invert_av) btor_invert_aigvec (avmgr, av);
  return hash;
}

static int
bfs_lambda (Btor *btor,
            BtorNode *lambda_exp,
            BtorNode *acc,
            BtorNode *search,
            BtorNode **result,
            int propagate_upwards)
{
  assert (btor);
  assert (lambda_exp);
  assert (acc);
  assert (search);
  assert (BTOR_IS_LAMBDA_NODE (lambda_exp));
  assert (BTOR_IS_ACC_NODE (acc));
  assert (BTOR_IS_REGULAR_NODE (search));
  assert (propagate_upwards == 0 || propagate_upwards == 1);

  int found = 0;
  const char *res;
  BtorMemMgr *mm;
  BtorNode *cur, *next, *index, *cond;
  BtorNodePtrQueue queue;
  BtorNodePtrStack unmark_stack;

  BTORLOG ("bfs_lambda: looking for %s", node2string (search));

  mm    = btor->mm;
  index = BTOR_GET_INDEX_ACC_NODE (acc);

  cur = BTOR_REAL_ADDR_NODE (lambda_exp->e[1]);
  assert (BTOR_IS_REGULAR_NODE (cur));
  assert (cur->mark == 0);

  if (propagate_upwards)
  {
    lambda_exp->parent = MARK_PROP_UP (cur);
    BTORLOG ("bfs_lambda: up %d -> %d",
             lambda_exp->id,
             BTOR_REAL_ADDR_NODE (cur)->id);
  }
  else
  {
    cur->parent = lambda_exp;
    BTORLOG ("bfs_lambda: down %d -> %d",
             BTOR_REAL_ADDR_NODE (cur)->id,
             lambda_exp->id);
  }
  cur->mark = 1;

  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_QUEUE (queue);
  BTOR_ENQUEUE (mm, queue, BTOR_REAL_ADDR_NODE (cur));
  BTOR_PUSH_STACK (mm, unmark_stack, cur);

  btor_assign_param (btor, lambda_exp, index);

  // TODO: follow path as long it is parameterized? (for the more general case)
  do
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (cur == search)
    {
      found = 1;
      break;
    }

    /* reads on lambda expressions can only be propagated along bv-conds
     * with reads as leaves */
    if (BTOR_IS_BV_COND_NODE (cur))
    {
      cond = cur->e[0];
      res  = btor_eval_exp (btor, cond);
      next = res[0] == '1' ? cur->e[1] : cur->e[2];
      next = BTOR_REAL_ADDR_NODE (next);
      btor_freestr (mm, (char *) res);

      next->mark = 1;
      if (propagate_upwards)
      {
        cur->parent = MARK_PROP_UP (next);
        BTORLOG ("bfs_lambda: up %d -> %d",
                 BTOR_REAL_ADDR_NODE (cur)->id,
                 BTOR_REAL_ADDR_NODE (next)->id);
      }
      else
      {
        next->parent = cur;
        BTORLOG ("bfs_lambda: down %d -> %d",
                 BTOR_REAL_ADDR_NODE (next)->id,
                 BTOR_REAL_ADDR_NODE (cur)->id);
      }
      BTOR_ENQUEUE (mm, queue, next);
      BTOR_PUSH_STACK (mm, unmark_stack, next);
    }
    /* we leave the lambda expression with a parameterized read */
    else if (BTOR_IS_READ_NODE (cur) && cur->parameterized)
    {
      next = cur->e[0];
      assert (BTOR_IS_ARRAY_NODE (next));

      if (propagate_upwards)
      {
        cur->parent = MARK_PROP_UP (next);
        BTORLOG ("bfs_lambda: up %d -> %d",
                 BTOR_REAL_ADDR_NODE (cur)->id,
                 BTOR_REAL_ADDR_NODE (next)->id);
        *result = lambda_exp;
      }
      else
      {
        next->parent = cur;
        BTORLOG ("bfs_lambda: down %d -> %d",
                 BTOR_REAL_ADDR_NODE (next)->id,
                 BTOR_REAL_ADDR_NODE (cur)->id);
        *result = next;
      }
      break;
    }
    else
    {
      /* acc not propagated through lambda expression */
      *result = cur;
      break;
    }
  } while (!BTOR_EMPTY_QUEUE (queue));
  BTOR_RELEASE_QUEUE (mm, queue);

  btor_unassign_param (btor, lambda_exp);

  /* reset mark flags */
  assert (!BTOR_EMPTY_STACK (unmark_stack));
  do
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    cur->mark = 0;
  } while (!BTOR_EMPTY_STACK (unmark_stack));
  BTOR_RELEASE_STACK (mm, unmark_stack);

  BTORLOG (
      "bfs_lambda: %s %s", found ? "found" : "not found", node2string (search));

  return found;
}

/* This function breadth first searches the shortest path from a read to an
 * array After the function is completed the parent pointers can be followed
 * from the array to the read
 */
static void
bfs (Btor *btor, BtorNode *acc, BtorNode *array)
{
  BtorNode *cur, *next, *cur_aeq, *cond, *index;  //, *param_read, *lambda_exp;
  //  BtorNode *lambda_value, *parameterized;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorNodePtrQueue queue;
  BtorNodePtrStack unmark_stack;  // param_read_stack;
  BtorPartialParentIterator it;
  int assignment, propagate_writes_as_reads;
#ifndef NDEBUG
  int found = 0;
#endif
  assert (btor);
  assert (acc);
  assert (array);
  assert (BTOR_IS_REGULAR_NODE (acc));
  assert (BTOR_IS_ACC_NODE (acc)
          || (BTOR_IS_LAMBDA_NODE (acc) && acc == array));
  assert (BTOR_IS_REGULAR_NODE (array));
  assert (BTOR_IS_ARRAY_NODE (array));
  assert (btor->ops[BTOR_AEQ_NODE] >= 0);
  propagate_writes_as_reads = (btor->ops[BTOR_AEQ_NODE] > 0) || btor->model_gen;
  mm                        = btor->mm;
  index                     = BTOR_GET_INDEX_ACC_NODE (acc);
  amgr                      = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  cur                       = BTOR_ACC_TARGET_NODE (acc);
  assert (BTOR_IS_REGULAR_NODE (cur));
  assert (BTOR_IS_ARRAY_NODE (cur));
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
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_ARRAY_NODE (cur));

    if (cur == array)
    {
#ifndef NDEBUG
      found = 1;
#endif
      break;
    }

    /* lazy_synthesize_and_encode_acc_exp sets the 'tseitin' flag.
     * If this flag is not set, we have to find an other way
     * to the conflict. */
    if (BTOR_IS_WRITE_NODE (cur) && cur->e[0]->mark == 0
        && BTOR_REAL_ADDR_NODE (cur->e[1])->tseitin
        && compare_assignments (cur->e[1], index) != 0)
    {
      assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cur->e[1])));
      next         = cur->e[0];
      next->mark   = 1;
      next->parent = cur;
      BTOR_ENQUEUE (mm, queue, next);
      BTOR_PUSH_STACK (mm, unmark_stack, next);
      BTORLOG ("bfs: %d -> %d", next->id, cur->id);
    }
    /* lazy_synthesize_and_encode_acond_exp sets the 'tseitin' flag.
     * If this flag is not set, we have to find an other way
     * to the conflict. */
    else if (BTOR_IS_ARRAY_COND_NODE (cur)
             && BTOR_REAL_ADDR_NODE (cur->e[0])->tseitin)
    {
      assert (BTOR_IS_SYNTH_NODE (cur->e[0]));
      /* check assignment to determine which array to choose */
      cond       = cur->e[0];
      assignment = btor_get_assignment_aig (
          amgr, BTOR_REAL_ADDR_NODE (cond)->av->aigs[0]);
      assert (assignment == 1 || assignment == -1);
      if (BTOR_IS_INVERTED_NODE (cond)) assignment = -assignment;
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
        BTORLOG ("bfs: %d -> %d", next->id, cur->id);
      }
    }
    // NOTE: right now, we do not need this case as no reads are propagated
    //       through lambdas (we always synthesize and encode param reads)
    else if (BTOR_IS_LAMBDA_NODE (cur) && cur->tseitin
             && BTOR_REAL_ADDR_NODE (cur->e[1])->mark == 0)
    {
      if (bfs_lambda (btor, cur, acc, array, &next, 0))
      {
#ifndef NDEBUG
        found = 1;
#endif
        break;
      }

      if (next)
      {
        assert (BTOR_IS_ARRAY_NODE (next));
        assert (BTOR_IS_REGULAR_NODE (next));

        next->mark = 1;
        /* mark lambda expression as visited */
        BTOR_REAL_ADDR_NODE (cur->e[1])->mark = 1;

        BTOR_ENQUEUE (mm, queue, next);
        BTOR_PUSH_STACK (mm, unmark_stack, next);
        BTOR_PUSH_STACK (mm, unmark_stack, BTOR_REAL_ADDR_NODE (cur->e[1]));
      }
    }

    if (propagate_writes_as_reads)
    {
      /* enqueue all arrays which are reachable via equality
       * where equality is set to true by the SAT solver */
      init_aeq_parent_iterator (&it, cur);
      while (has_next_parent_aeq_parent_iterator (&it))
      {
        cur_aeq = next_parent_aeq_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_aeq));
        check_not_simplified_or_const (btor, cur_aeq);
        if (cur_aeq->reachable && cur_aeq->mark == 0)
        {
          /* array equalities are synthesized eagerly */
          assert (BTOR_IS_SYNTH_NODE (cur_aeq));
          assert (cur_aeq->tseitin);
          assert (cur_aeq->len == 1);
          if (btor_get_assignment_aig (amgr, cur_aeq->av->aigs[0]) == 1)
          {
            /* we need the other child */
            if (cur_aeq->e[0] == cur)
              next = cur_aeq->e[1];
            else
              next = cur_aeq->e[0];
            assert (BTOR_IS_REGULAR_NODE (next));
            assert (BTOR_IS_ARRAY_NODE (next));
            if (next->mark == 0)
            {
              /* set parent of array equality */
              cur_aeq->parent = MARK_PROP_UP (cur);
              next->parent    = cur_aeq;
              next->mark      = 1;
              BTOR_ENQUEUE (mm, queue, next);
              BTOR_PUSH_STACK (mm, unmark_stack, next);
              BTORLOG ("bfs: %d -> %d, %d -> %d",
                       cur_aeq->id,
                       cur->id,
                       next->id,
                       cur_aeq->id);
            }
          }
        }
      }
      /* search upwards */
      init_acond_parent_iterator (&it, cur);
      while (has_next_parent_acond_parent_iterator (&it))
      {
        next = next_parent_acond_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (next));
        assert (BTOR_IS_ARRAY_NODE (next));
        assert (!next->simplified);
        /* lazy_synthesize_and_encode_acc_exp sets the
         * 'tseitin' flag.
         * If this flag is not set, we have to find an other way
         * to the conflict. */
        if (next->reachable && next->mark == 0
            && BTOR_REAL_ADDR_NODE (next->e[0])->tseitin)
        {
          cond       = next->e[0];
          assignment = btor_get_assignment_aig (
              amgr, BTOR_REAL_ADDR_NODE (cond)->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
          if (BTOR_IS_INVERTED_NODE (cond)) assignment = -assignment;
          /* search upwards only if array has been selected */
          if ((assignment == 1 && cur == next->e[1])
              || (assignment == -1 && cur == next->e[2]))
          {
            next->mark   = 1;
            next->parent = MARK_PROP_UP (cur);
            BTOR_ENQUEUE (mm, queue, next);
            BTOR_PUSH_STACK (mm, unmark_stack, next);
            BTORLOG ("bfs: %d -> %d", next->id, cur->id);
          }
        }
      }
      init_write_parent_iterator (&it, cur);
      while (has_next_parent_write_parent_iterator (&it))
      {
        next = next_parent_write_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (next));
        assert (BTOR_IS_ARRAY_NODE (next));
        assert (!next->simplified);
        if (next->reachable && next->mark == 0)
        {
          /* search upwards only if write has been synthesized and
           * assignments to the indices are unequal
           */
          if (BTOR_REAL_ADDR_NODE (next->e[1])->tseitin
              && compare_assignments (next->e[1], index) != 0)
          {
            next->mark   = 1;
            next->parent = MARK_PROP_UP (cur);
            BTOR_ENQUEUE (mm, queue, next);
            BTOR_PUSH_STACK (mm, unmark_stack, next);
            BTORLOG ("bfs: %d -> %d", next->id, cur->id);
          }
        }
      }
// NOTE: right now this code is not working with general lambdas. it is
//       disabled as we do not rewrite writes to lambdas in case of
//       extensionality
//
#if 0
	  /* search upwards lambda expressions */
	  BTOR_INIT_STACK (param_read_stack);
	  init_read_parent_iterator (&it, cur);
	  /* get all parameterized reads on cur */
	  while (has_next_parent_read_parent_iterator (&it))
	    {
	      next = next_parent_read_parent_iterator (&it);
	      assert (BTOR_IS_REGULAR_NODE (next));
	      assert (BTOR_IS_READ_NODE (next));
  //            assert (!next->simplified);
  //          // TODO: is only valid for write case
	      // TODO: do we need special handling of simplified reads?
	      if (next->reachable && BTOR_IS_PARAM_NODE (next->e[1]))
  //                && !next->simplified)
		  BTOR_PUSH_STACK (mm, param_read_stack, next);
	    }

	  while (!BTOR_EMPTY_STACK (param_read_stack))
	    {
	      param_read = BTOR_POP_STACK (param_read_stack);
	      assert (BTOR_IS_REGULAR_NODE (param_read));
	      assert (BTOR_IS_PARAM_NODE (param_read->e[1]));
	      lambda_exp = ((BtorParamNode *) param_read->e[1])->lambda_exp;

	      /* already processed */
	      if (BTOR_REAL_ADDR_NODE (lambda_exp->e[1])->mark == 1)
		continue;

	      /* instantiate lambda expressions with read index of acc */
	      btor_assign_param (btor, lambda_exp, index);
	      lambda_value = 
		btor_beta_reduce (btor, lambda_exp, BETA_RED_CUTOFF, &parameterized);
	      btor_unassign_param (btor, lambda_exp);

	      lambda_value = BTOR_REAL_ADDR_NODE (lambda_value);

	      // FIXME: more general approach: e[1] does not have to be index,
	      // may also be index + 2 etc.  in that case we have to propagate
	      // lambda_value, instead of acc, but we require a reference from
	      // lambda_value to acc (for lemma generation).
	      if (BTOR_IS_READ_NODE (lambda_value) && parameterized)
		{
		  assert (lambda_value->e[0] == param_read->e[0]);
		  assert (lambda_value->e[1] == index);
		  /* we search from lambda_exp down to param_read since acc was
		   * propagated upwards from param_read to lambda_exp */
		  bfs_lambda (btor, lambda_exp, acc, param_read->e[0], &next,
			      1);
		  assert (next == lambda_exp);
		  assert (BTOR_IS_REGULAR_NODE (next));
		  assert (cur->mark);

		  next->mark = 1;
		  /* mark lambda expression as visited */
		  BTOR_REAL_ADDR_NODE (next->e[1])->mark = 1;

		  BTOR_ENQUEUE (mm, queue, next);
		  BTOR_PUSH_STACK (mm, unmark_stack, next);
		  BTOR_PUSH_STACK (mm, unmark_stack,
				   BTOR_REAL_ADDR_NODE (lambda_exp->e[1]));
		}
	      btor_release_exp (btor, lambda_value);
	    }
	  BTOR_RELEASE_STACK (mm, param_read_stack);
#endif
    }
  } while (!BTOR_EMPTY_QUEUE (queue));
  assert (found);
  BTOR_RELEASE_QUEUE (mm, queue);
  /* reset mark flags */
  assert (!BTOR_EMPTY_STACK (unmark_stack));
  do
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_ARRAY_NODE (cur) || BTOR_IS_ARRAY_EQ_NODE (cur)
            || BTOR_IS_ARRAY_COND_NODE (cur) || BTOR_IS_BV_COND_NODE (cur));
    cur->mark = 0;
  } while (!BTOR_EMPTY_STACK (unmark_stack));
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static void
print_bfs_path_dbg (Btor *btor, BtorNode *from, BtorNode *to)
{
  assert (from);
  assert (from->parent);
  assert (to);

  int hops = 0;
  BtorNode *cur;

  cur = BTOR_REAL_ADDR_NODE (from);
  (void) hops;

  while (cur != to)
  {
    assert (BTOR_REAL_ADDR_NODE (cur->parent));
    BTORLOG ("bfs path: %d, %c, id: %d ",
             hops++,
             PROPAGATED_UPWARDS (cur) ? 'u' : 'd',
             BTOR_REAL_ADDR_NODE (cur)->id);
    cur = BTOR_REAL_ADDR_NODE (cur->parent);
  }
}

/* Adds lemma on demand
 * 'array' is the array where the conflict has been detected
 */
static void
add_lemma (Btor *btor, BtorNode *array, BtorNode *acc1, BtorNode *acc2)
{
  BtorPtrHashTable *writes, *aeqs, *aconds_sel1, *aconds_sel2, *bconds_sel1;
  BtorPtrHashTable *bconds_sel2;
  BtorNode *acc, *index;
  BtorMemMgr *mm;

  assert (btor);
  assert (array);
  assert (acc1);
  assert (acc2);
  assert (BTOR_IS_REGULAR_NODE (array));
  assert (BTOR_IS_REGULAR_NODE (acc1));
  assert (BTOR_IS_REGULAR_NODE (acc2));
  assert (BTOR_IS_ARRAY_NODE (array));
  assert (BTOR_IS_ACC_NODE (acc1));
  assert (BTOR_IS_ACC_NODE (acc2) || BTOR_IS_LAMBDA_NODE (acc2));
  assert (!BTOR_IS_LAMBDA_NODE (acc2) || array == acc2);

  mm = btor->mm;

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
  bconds_sel1 = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  bconds_sel2 = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  index = BTOR_GET_INDEX_ACC_NODE (acc1);

  for (acc = acc1; acc; acc = acc == acc1 ? acc2 : 0)
  {
    BTORLOG ("bfs:");
    BTORLOG ("  acc: %d", acc->id);
    BTORLOG ("  arr: %d", array->id);
    bfs (btor, acc, array);
    print_bfs_path_dbg (btor, array, acc);
    collect_premisses (btor,
                       array,
                       acc,
                       index,
                       writes,
                       aeqs,
                       aconds_sel1,
                       aconds_sel2,
                       bconds_sel1,
                       bconds_sel2);
  }

  encode_lemma (btor,
                writes,
                aeqs,
                aconds_sel1,
                aconds_sel2,
                bconds_sel1,
                bconds_sel2,
                acc1,
                acc2);

  btor_delete_ptr_hash_table (writes);
  btor_delete_ptr_hash_table (aeqs);
  btor_delete_ptr_hash_table (aconds_sel1);
  btor_delete_ptr_hash_table (aconds_sel2);
  btor_delete_ptr_hash_table (bconds_sel1);
  btor_delete_ptr_hash_table (bconds_sel2);
}

/* checks array axiom 2 */
static int
find_array_axiom_2_conflict (Btor *btor,
                             BtorNode *acc,
                             BtorNode *write,
                             int *indices_equal)
{
  assert (btor);
  assert (acc);
  assert (write);
  assert (indices_equal);
  assert (BTOR_IS_REGULAR_NODE (acc));
  assert (BTOR_IS_REGULAR_NODE (write));
  assert (BTOR_IS_ACC_NODE (acc));
  assert (BTOR_IS_WRITE_NODE (write));
  (void) btor;
  if ((*indices_equal =
           compare_assignments (BTOR_GET_INDEX_ACC_NODE (acc), write->e[1])
           == 0)
      && compare_assignments (BTOR_GET_VALUE_ACC_NODE (acc), write->e[2]) != 0)
    return 1;
  return 0;
}

/* makes assumptions to the SAT solver */
static int
add_again_assumptions (Btor *btor)
{
  BtorNode *exp;
  BtorPtrHashBucket *b;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  assert (btor);
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  for (b = btor->assumptions->first; b; b = b->next)
  {
    assert (BTOR_REAL_ADDR_NODE ((BtorNode *) b->key)->len == 1);
    exp = (BtorNode *) b->key;
    exp = btor_simplify_exp (btor, exp);
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

static int
btor_timed_sat_sat (Btor *btor, int limit)
{
  double start, delta;
  BtorSATMgr *smgr;
  int res;
  smgr  = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  start = btor_time_stamp ();
  res   = btor_sat_sat (smgr, limit);
  delta = btor_time_stamp () - start;
  btor->time.sat += delta;
  if (btor->verbosity)
    btor_msg_exp (btor, "SAT solver returns %d after %.1f seconds", res, delta);
  return res;
}

/* updates SAT assignments, reads assumptions and
 * returns if an assignment has changed
 */
static int
update_sat_assignments (Btor *btor)
{
  int result, found_assumption_false;
  BtorSATMgr *smgr = 0;
  assert (btor);
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  found_assumption_false = add_again_assumptions (btor);
  assert (!found_assumption_false);
  result = btor_timed_sat_sat (btor, -1);
  assert (result == BTOR_SAT);
  return found_assumption_false || (result != BTOR_SAT)
         || btor_changed_sat (smgr);
}

/* synthesizes and fully encodes index and value of access expression into SAT
 * (if necessary)
 * it returns if encoding changed assignments made so far
 */
static int
lazy_synthesize_and_encode_acc_exp (Btor *btor, BtorNode *acc, int force_update)
{
  BtorNode *index, *value;
  int changed_assignments, update;
  BtorAIGVecMgr *avmgr = 0;

  assert (btor);
  assert (acc);
  assert (BTOR_IS_REGULAR_NODE (acc));
  assert (BTOR_IS_ACC_NODE (acc));
  changed_assignments = 0;
  update              = 0;
  avmgr               = btor->avmgr;
  index               = BTOR_GET_INDEX_ACC_NODE (acc);
  value               = BTOR_GET_VALUE_ACC_NODE (acc);

  BTORLOG ("%s: %s", __FUNCTION__, node2string (acc));

  if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (index)))
  {
    synthesize_exp (btor, index, 0);
  }
  if (!BTOR_REAL_ADDR_NODE (index)->tseitin)
  {
    update = 1;
    btor_aigvec_to_sat_tseitin (avmgr, BTOR_REAL_ADDR_NODE (index)->av);
    BTOR_REAL_ADDR_NODE (index)->tseitin = 1;
    BTORLOG ("  encode: %s", node2string (index));
  }
  if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (value)))
  {
    synthesize_exp (btor, value, 0);
  }
  if (!BTOR_REAL_ADDR_NODE (value)->tseitin)
  {
    update = 1;
    btor_aigvec_to_sat_tseitin (avmgr, BTOR_REAL_ADDR_NODE (value)->av);
    BTOR_REAL_ADDR_NODE (value)->tseitin = 1;
    BTORLOG ("  encode: %s", node2string (value));
  }
  /* update assignments if necessary */
  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);
  return changed_assignments;
}

static int
lazy_synthesize_and_encode_acond_exp (Btor *btor,
                                      BtorNode *acond,
                                      int force_update)
{
  BtorNode *cond;
  int changed_assignments, update;
  BtorAIGVecMgr *avmgr;

  avmgr = btor->avmgr;
  assert (btor);
  assert (acond);
  assert (BTOR_IS_REGULAR_NODE (acond));
  assert (BTOR_IS_ARRAY_COND_NODE (acond));
  changed_assignments = 0;
  update              = 0;
  cond                = acond->e[0];
  assert (cond);
  BTORLOG ("%s: %s", __FUNCTION__, node2string (acond));
  if (!BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cond)))
    synthesize_exp (btor, cond, 0);
  if (!BTOR_REAL_ADDR_NODE (cond)->tseitin)
  {
    update = 1;
    btor_aigvec_to_sat_tseitin (avmgr, BTOR_REAL_ADDR_NODE (cond)->av);
    BTOR_REAL_ADDR_NODE (cond)->tseitin = 1;
    BTORLOG ("  encode: %s", node2string (cond));
  }
  /* update assignments if necessary */
  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);
  return changed_assignments;
}

static int
lazy_synthesize_and_encode_lambda_exp (Btor *btor,
                                       BtorNode *lambda_exp,
                                       int force_update)
{
  assert (btor);
  assert (lambda_exp);
  assert (BTOR_IS_REGULAR_NODE (lambda_exp));
  assert (BTOR_IS_LAMBDA_NODE (lambda_exp));

  int changed_assignments, update, i;
  BtorNodePtrStack work_stack, unmark_stack;
  BtorNode *cur;
  BtorMemMgr *mm;
  BtorAIGVecMgr *avmgr;

  mm                  = btor->mm;
  avmgr               = btor->avmgr;
  changed_assignments = 0;
  update              = 0;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  BTORLOG ("%s: %s", __FUNCTION__, node2string (lambda_exp));

  BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (lambda_exp->e[1]));

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_POP_STACK (work_stack);
    assert (cur);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!BTOR_IS_WRITE_NODE (cur));

    if (cur->mark == 2) continue;

    /* do not encode array vars */
    if (BTOR_IS_ARRAY_VAR_NODE (cur)) continue;

    if (cur->mark == 0)
    {
      cur->mark = 1;
      BTOR_PUSH_STACK (mm, work_stack, cur);
      BTOR_PUSH_STACK (mm, unmark_stack, cur);

      if (BTOR_IS_READ_NODE (cur)) continue;

      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (cur->e[i]));
    }
    else
    {
      /* lambdas, writes and array conditionals are only reachable over
       * array equalities, we do not need to synthesize array nodes */
      if (BTOR_IS_LAMBDA_NODE (cur) || BTOR_IS_WRITE_NODE (cur)
          || BTOR_IS_ARRAY_COND_NODE (cur))
        continue;

      assert (cur->mark == 1);
      cur->mark = 2;

      if (!cur->parameterized)
      {
        if (!BTOR_IS_SYNTH_NODE (cur)) synthesize_exp (btor, cur, 0);

        if (!cur->tseitin)
        {
          BTORLOG ("  encode: %s", node2string (cur));
          update = 1;
          btor_aigvec_to_sat_tseitin (avmgr, cur->av);
          cur->tseitin = 1;
        }
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->mark);
    cur->mark = 0;
  }

  BTOR_RELEASE_STACK (mm, unmark_stack);
  BTOR_RELEASE_STACK (mm, work_stack);

  /* set tseitin flag of lambda expression to indicate that it has been
   * lazily synthesized already */
  lambda_exp->tseitin = 1;

  if (update && force_update)
    changed_assignments = update_sat_assignments (btor);

  return changed_assignments;
}
#if 0
static void
btor_assign_param (Btor *btor, BtorNode *lambda, BtorNode *arg)
{
  assert (lambda);
  assert (arg);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (BTOR_IS_PARAM_NODE (lambda->e[0]));

  BTORLOG ("btor_assign_param: %s", node2string (lambda));
  BTORLOG ("  assigned exp: %s", node2string (arg));

  int upper, lower;
  BtorNode *cur_lambda, *cur_arg;
  BtorParamNode *param;

  param = (BtorParamNode *) BTOR_REAL_ADDR_NODE (lambda->e[0]);

  /* apply multiple arguments */
  if (param->len < BTOR_REAL_ADDR_NODE (arg)->len)
    {
      assert (BTOR_REAL_ADDR_NODE (arg)->kind == BTOR_CONCAT_NODE);

      cur_lambda = lambda;
      lower = 0;
      do
	{
	  param = (BtorParamNode *) BTOR_REAL_ADDR_NODE (cur_lambda->e[0]);
	  upper = lower + param->len - 1;
	  cur_arg = btor_rewrite_slice_exp (btor, arg, upper, lower);
	  btor_release_exp (btor, cur_arg);  /* still referenced afterwards */

	  assert (BTOR_REAL_ADDR_NODE (cur_arg)->kind != BTOR_SLICE_NODE);
	  assert (param->len == cur_arg->len);

	  BTOR_PUSH_STACK (btor->mm, param->assigned_exp, cur_arg);
	  cur_lambda = cur_lambda->e[1];
	  lower = upper + 1; 
	}
      while (BTOR_IS_LAMBDA_NODE (cur_lambda));
      // TODO: handle in with type safe functions
      assert (lower == BTOR_REAL_ADDR_NODE (arg)->len);
    }
  else
    {
      BTOR_PUSH_STACK (btor->mm, param->assigned_exp, arg);
    }
}

static void
btor_unassign_param (Btor *btor, BtorNode *lambda)
{
  assert (lambda);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));
  assert (BTOR_IS_PARAM_NODE (lambda->e[0]));

  BtorParamNode *param;

  do 
    {
      BTORLOG ("btor_unassign_param: %s", node2string (lambda));
      param = (BtorParamNode *) lambda->e[0];

      if (BTOR_EMPTY_STACK (param->assigned_exp))
	break;

      (void) BTOR_POP_STACK (param->assigned_exp);
      lambda = BTOR_REAL_ADDR_NODE (lambda->e[1]);
    }
  while (BTOR_IS_LAMBDA_NODE (lambda));
}
#endif

#if 0
static BtorNode *
param_cur_assignment (BtorNode *param)
{
  assert (param);
  assert (BTOR_IS_REGULAR_NODE (param));
  assert (BTOR_IS_PARAM_NODE (param));

  if (BTOR_EMPTY_STACK (((BtorParamNode *) param)->assigned_exp))
    return 0;

  return BTOR_TOP_STACK (((BtorParamNode *) param)->assigned_exp);
}
#endif

const char *
btor_eval_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  const char *result = 0, *inv_result, *e[3];
  double start;
  BtorMemMgr *mm;
  BtorNodePtrStack work_stack, unmark_stack;
  BtorCharPtrStack arg_stack;
  BtorNode *cur, *real_cur, *assigned_exp;

  mm    = btor->mm;
  start = btor_time_stamp ();
  btor->stats.eval_exp_calls++;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (arg_stack);
  BTOR_INIT_STACK (unmark_stack);

  BTOR_PUSH_STACK (mm, work_stack, exp);
  assert (!BTOR_REAL_ADDR_NODE (exp)->eval_mark);
  BTORLOG ("eval_exp: %s", node2string (exp));

  while (!BTOR_EMPTY_STACK (work_stack))
  {
#if 0
      // debug
      for (i = 0; i < BTOR_COUNT_STACK (work_stack); i++)
	{
	  fprintf (stderr, "    work_stack[%d]: (%d) ", i, 
	           (BTOR_REAL_ADDR_NODE (work_stack.start[i]))->eval_mark);
	  dump_node (stderr, work_stack.start[i]);
	}
      for (i = 0; i < BTOR_COUNT_STACK (arg_stack); i++)
	  fprintf (stderr, "    arg_stack[%d]: %s ", i, arg_stack.start[i]);
      // end debug
#endif

    cur      = BTOR_POP_STACK (work_stack);
    cur      = btor_simplify_exp (btor, cur);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    //      BTORLOG ("  real_cur: %s %d", node2string (cur), real_cur->tseitin);

    if (real_cur->eval_mark == 0 || real_cur->eval_mark == 2)
    {
      if (real_cur->eval_mark == 0) /* don't push twice */
        BTOR_PUSH_STACK (mm, unmark_stack, real_cur);

      real_cur->eval_mark = 1;

      if (BTOR_IS_PARAM_NODE (real_cur))
      {
        assert (!BTOR_EMPTY_STACK (((BtorParamNode *) real_cur)->assigned_exp));
        assigned_exp = btor_param_cur_assignment (real_cur);

        if (BTOR_IS_INVERTED_NODE (cur))
          assigned_exp = BTOR_INVERT_NODE (assigned_exp);

        BTOR_PUSH_STACK (mm, work_stack, assigned_exp);
        real_cur->eval_mark = 2;
      }
      else
      {
        BTOR_PUSH_STACK (mm, work_stack, cur);

        /* if current node already has an assignment, skip children */
        if (real_cur->tseitin)
        {
          //		BTORLOG ("  skip (tseitin): %s", node2string
          //(real_cur));
          continue;
        }

        for (i = 0; i < real_cur->arity; i++)
        {
          //		BTORLOG ("  push %s", node2string (real_cur->e[i]));
          BTOR_PUSH_STACK (mm, work_stack, real_cur->e[i]);
        }
      }
    }
    else
    {
      assert (!BTOR_IS_PARAM_NODE (real_cur));
      assert (!BTOR_IS_LAMBDA_NODE (real_cur));
      assert (!BTOR_IS_PROXY_NODE (real_cur));
      real_cur->eval_mark = 2;

      if (BTOR_IS_BV_CONST_NODE (real_cur))
      {
        result = btor_copy_const (mm, real_cur->bits);
      }
      else if (real_cur->tseitin)
      {
        assert (real_cur->av);
        result = btor_assignment_aigvec (btor->avmgr, real_cur->av);
      }
      else
      {
        assert (!BTOR_IS_ARRAY_EQ_NODE (real_cur));
        assert (!BTOR_IS_ARRAY_COND_NODE (real_cur));
        assert (!BTOR_IS_ARRAY_NODE (real_cur));
        assert (!BTOR_IS_PROXY_NODE (real_cur));
        assert (!BTOR_IS_UNARY_NODE (real_cur)
                || BTOR_COUNT_STACK (arg_stack) >= 1);
        assert (!BTOR_IS_BINARY_NODE (real_cur)
                || BTOR_COUNT_STACK (arg_stack) >= 2);
        assert (!BTOR_IS_TERNARY_NODE (real_cur)
                || BTOR_COUNT_STACK (arg_stack) >= 3);

        for (i = 0; i < real_cur->arity; i++) e[i] = BTOR_POP_STACK (arg_stack);

        switch (real_cur->kind)
        {
          case BTOR_SLICE_NODE:
            result =
                btor_slice_const (mm, e[0], real_cur->upper, real_cur->lower);
            break;
          case BTOR_AND_NODE: result = btor_and_const (mm, e[0], e[1]); break;
          case BTOR_BEQ_NODE: result = btor_eq_const (mm, e[0], e[1]); break;
          case BTOR_ADD_NODE: result = btor_add_const (mm, e[0], e[1]); break;
          case BTOR_MUL_NODE: result = btor_mul_const (mm, e[0], e[1]); break;
          case BTOR_ULT_NODE: result = btor_ult_const (mm, e[0], e[1]); break;
          case BTOR_SLL_NODE: result = btor_sll_const (mm, e[0], e[1]); break;
          case BTOR_SRL_NODE: result = btor_srl_const (mm, e[0], e[1]); break;
          case BTOR_UDIV_NODE: result = btor_udiv_const (mm, e[0], e[1]); break;
          case BTOR_UREM_NODE: result = btor_urem_const (mm, e[0], e[1]); break;
          case BTOR_CONCAT_NODE:
            result = btor_concat_const (mm, e[0], e[1]);
            break;
          case BTOR_BCOND_NODE:
            if (e[0][0] == '1')
              result = btor_copy_const (mm, e[1]);
            else
              result = btor_copy_const (mm, e[2]);
            break;
          default:
            BTORLOG ("  *** %s", node2string (real_cur));
            /* should be unreachable */
            assert (0);
        }

        for (i = 0; i < real_cur->arity; i++) btor_freestr (mm, (char *) e[i]);
      }

      if (BTOR_IS_INVERTED_NODE (cur))
      {
        inv_result = btor_not_const (mm, result);
        btor_freestr (mm, (char *) result);
        result = inv_result;
      }

      //	  BTORLOG ("  result: %s, %s", result, node2string (real_cur));
      BTOR_PUSH_STACK (mm, arg_stack, (char *) result);
    }
  }
  assert (BTOR_COUNT_STACK (arg_stack) == 1);
  result = BTOR_POP_STACK (arg_stack);
  assert (result);

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->eval_mark);
    cur->eval_mark = 0;
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, arg_stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);

  BTORLOG ("eval_exp: %s '%s'", node2string (exp), result);
  btor->time.eval += btor_time_stamp () - start;
  return result;
}

static void
find_nodes_dfs (Btor *btor,
                BtorNode *exp,
                BtorNodePtrStack *results,
                int (*findfun) (BtorNode *),
                int (*skipfun) (BtorNode *))
{
  assert (btor);
  assert (exp);
  assert (results);
  assert (findfun);

  int i;
  BtorNode *cur;
  BtorNodePtrStack work_stack, unmark_stack;
  BtorMemMgr *mm;

  BTORLOG ("%s: %s", __FUNCTION__, node2string (exp));

  mm = btor->mm;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_PUSH_STACK (mm, work_stack, exp);

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));

    if (cur->mark || (skipfun && skipfun (cur))) continue;

    cur->mark = 1;
    BTOR_PUSH_STACK (mm, unmark_stack, cur);

    if (findfun (cur))
    {
      BTOR_PUSH_STACK (mm, *results, cur);
      BTORLOG ("  found: %s", node2string (cur));
      continue;
    }

    for (i = 0; i < cur->arity; i++)
      BTOR_PUSH_STACK (mm, work_stack, cur->e[i]);
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    cur->mark = 0;
  }

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static int
findfun_param (BtorNode *exp)
{
  assert (exp);
  return BTOR_IS_PARAM_NODE (BTOR_REAL_ADDR_NODE (exp));
}

static int
findfun_param_read (BtorNode *exp)
{
  assert (exp);
  exp = BTOR_REAL_ADDR_NODE (exp);
  return BTOR_IS_READ_NODE (exp) && exp->parameterized;
}

static int
skipfun_param (BtorNode *exp)
{
  assert (exp);
  return !BTOR_REAL_ADDR_NODE (exp)->parameterized;
}

static int
findfun_read (BtorNode *exp)
{
  assert (exp);
  return BTOR_IS_READ_NODE (BTOR_REAL_ADDR_NODE (exp));
}

static int
skipfun_tseitin (BtorNode *exp)
{
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->tseitin;
}

static int
process_working_stack (Btor *btor,
                       BtorNodePtrStack *stack,
                       BtorNodePtrStack *cleanup_stack,
                       int *assignments_changed)
{
  BtorPartialParentIterator it;
  BtorLambdaNode *lambda;
  BtorNode *acc, *index, *value, *array, *hashed_acc, *hashed_value;
  BtorNode *cur_aeq, *cond, *next, *lambda_value, *param_read;  // *lambda_exp
  BtorNode *parameterized;
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorNodePtrStack param_reads;
  int i, assignment, indices_equal, propagate_writes_as_reads;
  int values_equal;
  char *value_assignment, *lambda_value_assignment;
  assert (btor);
  assert (stack);
  assert (assignments_changed);
  assert (btor->ops[BTOR_AEQ_NODE] >= 0);
  propagate_writes_as_reads = (btor->ops[BTOR_AEQ_NODE] > 0) || btor->model_gen;
  amgr                      = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  mm                        = btor->mm;

  while (!BTOR_EMPTY_STACK (*stack))
  {
    array = BTOR_POP_STACK (*stack);
    assert (BTOR_IS_REGULAR_NODE (array));
    assert (BTOR_IS_ARRAY_NODE (array));
    assert (!array->simplified);
    assert (!BTOR_EMPTY_STACK (*stack));
    acc = BTOR_POP_STACK (*stack);
    assert (BTOR_IS_REGULAR_NODE (acc));
    assert (BTOR_IS_ACC_NODE (acc));
    check_not_simplified_or_const (btor, acc);
// NOTE: code not used right now, as we do not rewrite writes in case of
//       extensionality
#if 0
      /* synthesize index and value if necessary */
      if (BTOR_IS_LAMBDA_NODE (acc))
	*assignments_changed =
	  lazy_synthesize_and_encode_lambda_exp (btor, acc, 1);
      else
#else
    assert (!propagate_writes_as_reads || !BTOR_IS_LAMBDA_NODE (acc));
#endif
    *assignments_changed = lazy_synthesize_and_encode_acc_exp (btor, acc, 1);
    index                = BTOR_GET_INDEX_ACC_NODE (acc);
    value                = BTOR_GET_VALUE_ACC_NODE (acc);
    check_not_simplified_or_const (btor, index);
    check_not_simplified_or_const (btor, value);
    if (*assignments_changed) return 0;
    // debug
    BTORLOG ("");
    BTORLOG ("*** %s", __FUNCTION__);
    BTORLOG ("array: %s", node2string (array));
    BTORLOG ("access: %s", node2string (acc));
    char *a = btor_bv_assignment_exp (btor, value);
    BTORLOG ("   value: %s, %s", a, node2string (value));
    btor_free_bv_assignment_exp (btor, a);
    a = btor_bv_assignment_exp (btor, index);
    BTORLOG ("   index: %s, %s", a, node2string (index));
    btor_free_bv_assignment_exp (btor, a);
    // debug
    /* hash table lookup */
    if (!array->rho)
    {
      array->rho = btor_new_ptr_hash_table (
          mm, (BtorHashPtr) hash_assignment, (BtorCmpPtr) compare_assignments);
      BTOR_PUSH_STACK (mm, *cleanup_stack, array);
    }
    else
    {
      /* check array axiom 1 */
      bucket = btor_find_in_ptr_hash_table (array->rho, index);
      if (bucket)
      {
        hashed_acc = (BtorNode *) bucket->data.asPtr;
        assert (BTOR_IS_REGULAR_NODE (hashed_acc));
        assert (BTOR_IS_ACC_NODE (hashed_acc));
        hashed_value = BTOR_GET_VALUE_ACC_NODE (hashed_acc);
        /* we have to check if values are equal */
        if (compare_assignments (hashed_value, value) != 0)
        {
          BTORLOG ("\e[1;31m");
          BTORLOG ("A1 conflict in array expression: %s", node2string (array));
          BTORLOG ("add_lemma:");
          BTORLOG ("  array: %s", node2string (array));
          BTORLOG ("  acc1: %s", node2string (hashed_acc));
          BTORLOG ("  acc2: %s", node2string (acc));
          BTORLOG ("\e[0;39m");
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
    if (BTOR_IS_WRITE_NODE (array))
    {
      *assignments_changed =
          lazy_synthesize_and_encode_acc_exp (btor, array, 1);
      if (*assignments_changed) return 0;
      /* check array axiom 2 */
      if (find_array_axiom_2_conflict (btor, acc, array, &indices_equal))
      {
        BTORLOG ("\e[1;31m");
        BTORLOG ("A2 conflict in array expression: %s", node2string (array));
        BTORLOG ("add_lemma:");
        BTORLOG ("  array: %s", node2string (array));
        BTORLOG ("  acc1: %s", node2string (acc));
        BTORLOG ("  acc2: %s", node2string (array));
        BTORLOG ("\e[0;39m");
        btor->stats.array_axiom_2_conflicts++;
        add_lemma (btor, array, acc, array);
        return 1;
      }
      else if (!indices_equal)
      {
        /* propagate down */
        assert (BTOR_IS_REGULAR_NODE (array->e[0]));
        assert (BTOR_IS_ARRAY_NODE (array->e[0]));
        assert (!array->e[0]->simplified);
        BTOR_PUSH_STACK (mm, *stack, acc);
        BTOR_PUSH_STACK (mm, *stack, array->e[0]);
        BTORLOG ("write exp prop. down:");
        BTORLOG ("  acc: %s", node2string (acc));
        BTORLOG ("  array: %s", node2string (array->e[0]));
      }
    }
    else if (BTOR_IS_ARRAY_COND_NODE (array))
    {
      *assignments_changed =
          lazy_synthesize_and_encode_acond_exp (btor, array, 1);
      if (*assignments_changed) return 0;
      cond = array->e[0];
      check_not_simplified_or_const (btor, index);
      assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cond)));
      assignment = btor_get_assignment_aig (
          amgr, BTOR_REAL_ADDR_NODE (cond)->av->aigs[0]);
      assert (assignment == 1 || assignment == -1);
      if (BTOR_IS_INVERTED_NODE (cond)) assignment = -assignment;
      /* propagate down */
      BTOR_PUSH_STACK (mm, *stack, acc);
      BTORLOG ("array cond prop. down:");
      BTORLOG ("  acc: %s", node2string (acc));
      if (assignment == 1)
      {
        assert (BTOR_IS_REGULAR_NODE (array->e[1]));
        assert (BTOR_IS_ARRAY_NODE (array->e[1]));
        assert (!array->e[1]->simplified);
        BTOR_PUSH_STACK (mm, *stack, array->e[1]);
        BTORLOG ("  array: %s", node2string (array->e[1]));
      }
      else
      {
        assert (BTOR_IS_REGULAR_NODE (array->e[2]));
        assert (BTOR_IS_ARRAY_NODE (array->e[2]));
        assert (!array->e[2]->simplified);
        BTOR_PUSH_STACK (mm, *stack, array->e[2]);
        BTORLOG ("  array: %s", node2string (array->e[2]));
      }
    }
    else if (BTOR_IS_LAMBDA_NODE (array))
    {
      *assignments_changed =
          lazy_synthesize_and_encode_lambda_exp (btor, array, 1);
      if (*assignments_changed) return 0;

      btor_assign_param (btor, array, index);
      lambda_value = btor_beta_reduce_cutoff (btor, array, &parameterized);
      btor_unassign_param (btor, array);

      // debug
      char *a = btor_bv_assignment_exp (btor, value);
      BTORLOG ("   value:  %s, %s", a, node2string (value));
      btor_free_bv_assignment_exp (btor, a);
      a = btor_bv_assignment_exp (btor, index);
      BTORLOG ("   index:  %s, %s", a, node2string (index));
      btor_free_bv_assignment_exp (btor, a);
      a = btor_bv_assignment_exp (btor, lambda_value);
      BTORLOG ("   lambda: %s, %s", a, node2string (lambda_value));
      btor_free_bv_assignment_exp (btor, a);
      BTORLOG ("   lambda parameterized: %s", node2string (parameterized));
      // end debug

      /* check if we have an assignment for 'lambda_value' */
      if (parameterized)
      {
        assert (BTOR_IS_REGULAR_NODE (parameterized));
        assert (!BTOR_IS_READ_NODE (parameterized)
                || BTOR_IS_READ_NODE (BTOR_REAL_ADDR_NODE (lambda_value)));

        /* we can propagate 'acc' down to lamba_value->e[0] if
         * 'lamba_value' was a parameterized read and instantiated with
         * 'index'.
         */
        if (BTOR_IS_READ_NODE (BTOR_REAL_ADDR_NODE (lambda_value))
            && BTOR_REAL_ADDR_NODE (lambda_value)->e[1] == index)
        {
          assert (BTOR_IS_READ_NODE (parameterized));
          assert (parameterized->e[0]
                  == BTOR_REAL_ADDR_NODE (lambda_value)->e[0]);

          BTOR_PUSH_STACK (mm, *stack, acc);
          BTOR_PUSH_STACK (mm, *stack, parameterized->e[0]);
          BTORLOG ("lambda exp prop. down:");
          BTORLOG ("  acc: %s", node2string (acc));
          BTORLOG ("  array: %s", node2string (parameterized->e[0]));
        }
        /* no assignment for 'lambda_value', synthesize and encode
         * parameterized reads in 'lamba_value' if necessary. */
        else
        {
          BTOR_INIT_STACK (param_reads);
          find_nodes_dfs (
              btor, lambda_value, &param_reads, findfun_read, skipfun_tseitin);

          if (BTOR_COUNT_STACK (param_reads) > 0)
          {
            lambda = (BtorLambdaNode *) array;

            if (!lambda->synth_reads)
            {
              lambda->synth_reads =
                  btor_new_ptr_hash_table (mm,
                                           (BtorHashPtr) btor_hash_exp_by_id,
                                           (BtorCmpPtr) btor_compare_exp_by_id);
            }

            for (i = 0; i < BTOR_COUNT_STACK (param_reads); i++)
            {
              param_read = param_reads.start[i];
              assert (BTOR_IS_REGULAR_NODE (param_read));
              assert (BTOR_IS_READ_NODE (param_read));
              assert (!btor_find_in_ptr_hash_table (lambda->synth_reads,
                                                    param_read));

              btor->stats.lambda_synth_reads++;
              inc_exp_ref_counter (btor, param_read);
              btor_insert_in_ptr_hash_table (lambda->synth_reads, param_read);

              *assignments_changed =
                  lazy_synthesize_and_encode_acc_exp (btor, param_read, 1);

              if (*assignments_changed)
              {
                btor_release_exp (btor, lambda_value);
                BTOR_RELEASE_STACK (mm, param_reads);
                return 0;
              }
            }
          }

          value_assignment        = btor_bv_assignment_exp (btor, value);
          lambda_value_assignment = (char *) btor_eval_exp (btor, lambda_value);

          BTORLOG ("value_assignment: %s", value_assignment);
          BTORLOG ("lambda_value_assignment: %s", lambda_value_assignment);

          values_equal =
              strcmp (value_assignment, lambda_value_assignment) == 0;
          btor_freestr (mm, lambda_value_assignment);
          btor_free_bv_assignment_exp (btor, value_assignment);

          if (!values_equal)
          {
          LAMBDA_AXIOM_2_CONFLICT:
            BTORLOG ("\e[1;31m");
            BTORLOG ("A2 conflict in lambda expression: %s",
                     node2string (array));
            BTORLOG (" add_lemma:");
            BTORLOG ("   array: %s", node2string (array));
            BTORLOG ("   acc1: %s", node2string (acc));
            BTORLOG ("   acc2: %s", node2string (array));
            BTORLOG ("\e[0;39m");

            btor->stats.array_axiom_2_conflicts++;
            add_lemma (btor, array, acc, array);
            btor_release_exp (btor, lambda_value);
            if (parameterized) BTOR_RELEASE_STACK (mm, param_reads);
            return 1;
          }
          else if (BTOR_COUNT_STACK (param_reads) > 0)
          {
            for (i = 0; i < BTOR_COUNT_STACK (param_reads); i++)
            {
              param_read = BTOR_REAL_ADDR_NODE (param_reads.start[i]);
              BTOR_PUSH_STACK (mm, *stack, param_read);
              BTOR_PUSH_STACK (mm, *stack, param_read->e[0]);
              BTORLOG ("lambda exp prop. down:");
              BTORLOG ("  acc: %s", node2string (param_read));
              BTORLOG ("  array: %s", node2string (param_read->e[0]));
            }
          }
          BTOR_RELEASE_STACK (mm, param_reads);
        }
      }
      else
      {
        /* we have an assignment for 'lambda_value' */
        if (compare_assignments (value, lambda_value) != 0)
          goto LAMBDA_AXIOM_2_CONFLICT;
      }
      btor_release_exp (btor, lambda_value);
    }

    assert (array->rho);
    /* insert into hash table */
    btor_insert_in_ptr_hash_table (array->rho, index)->data.asPtr = acc;

    if (propagate_writes_as_reads)
    {
      /* propagate pairs wich are reachable via array equality */
      init_aeq_parent_iterator (&it, array);
      while (has_next_parent_aeq_parent_iterator (&it))
      {
        cur_aeq = next_parent_aeq_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_aeq));
        check_not_simplified_or_const (btor, cur_aeq);
        if (cur_aeq->reachable)
        {
          assert (BTOR_IS_SYNTH_NODE (cur_aeq));
          assert (cur_aeq->tseitin);
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
            assert (BTOR_IS_REGULAR_NODE (next));
            assert (BTOR_IS_ARRAY_NODE (next));
            assert (!next->simplified);
            BTOR_PUSH_STACK (mm, *stack, acc);
            BTOR_PUSH_STACK (mm, *stack, next);
            BTORLOG ("aeq exp prop.:");
            BTORLOG ("  acc: %s", node2string (acc));
            BTORLOG ("  array: %s", node2string (next));
          }
        }
      }
      /* propagate upwards */
      init_acond_parent_iterator (&it, array);
      while (has_next_parent_acond_parent_iterator (&it))
      {
        next = next_parent_acond_parent_iterator (&it);
        assert (!next->simplified);
        if (next->reachable)
        {
          assert (BTOR_IS_REGULAR_NODE (next));
          assert (BTOR_IS_ARRAY_NODE (next));
          *assignments_changed =
              lazy_synthesize_and_encode_acond_exp (btor, next, 1);
          if (*assignments_changed) return 0;
          cond       = next->e[0];
          assignment = btor_get_assignment_aig (
              amgr, BTOR_REAL_ADDR_NODE (cond)->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
          if (BTOR_IS_INVERTED_NODE (cond)) assignment = -assignment;
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
        assert (!next->simplified);
        if (next->reachable)
        {
          assert (BTOR_IS_REGULAR_NODE (next));
          assert (BTOR_IS_ARRAY_NODE (next));
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
// NOTE: code not used right now, as we do not rewrite writes in case of
//       extensionality
#if 0
	  /* propagate upwards lambda expressions */
	  BTOR_INIT_STACK (param_read_stack);
	  init_read_parent_iterator (&it, array);
	  /* get all parameterized reads on array */
	  while (has_next_parent_read_parent_iterator (&it))
	    {
	      next = next_parent_read_parent_iterator (&it);
	      assert (BTOR_IS_REGULAR_NODE (next));
	      assert (BTOR_IS_READ_NODE (next));
  //            assert (!next->simplified);
	      if (next->reachable && BTOR_IS_PARAM_NODE (next->e[1]))
		  BTOR_PUSH_STACK (mm, param_read_stack, next);
	    }

	  while (!BTOR_EMPTY_STACK (param_read_stack))
	    {
	      next = BTOR_POP_STACK (param_read_stack);
	      assert (BTOR_IS_REGULAR_NODE (next));
	      assert (BTOR_IS_PARAM_NODE (next->e[1]));

	      lambda_exp = ((BtorParamNode *) next->e[1])->lambda_exp;

	      /* ensure that given lambda expression is synthesized and encoded
	       */
	      if (!lambda_exp->tseitin)
		{
		  *assignments_changed =
		    lazy_synthesize_and_encode_lambda_exp (btor, lambda_exp, 1);

		  if (*assignments_changed)
		    {
		      BTOR_RELEASE_STACK (mm, param_read_stack);
		      return 0;
		    }
		}

	      /* instantiate lambda expressions with read index of acc */
	      btor_assign_param (btor, lambda_exp, index);
	      lambda_value = btor_beta_reduce (btor, lambda_exp, -1, &parameterized);
	      btor_unassign_param (btor, lambda_exp);
		
	      lambda_value = BTOR_REAL_ADDR_NODE (lambda_value);

	      if (BTOR_IS_READ_NODE (lambda_value) && parameterized)
		{
		  assert (lambda_value->e[0] == next->e[0]);
		  assert (lambda_value->e[1] == index);
		  BTORLOG ("lambda prop. upwards:");
		  BTORLOG ("  access: %s", node2string (acc));
		  BTORLOG ("  array: %s", node2string (lambda_exp));
		  BTOR_PUSH_STACK (mm, *stack, acc);
		  BTOR_PUSH_STACK (mm, *stack, lambda_exp);
		}
	      btor_release_exp (btor, lambda_value);
	    }
	  BTOR_RELEASE_STACK (mm, param_read_stack);
#endif
    }
  }
  return 0;
}

#if 0
static int
process_working_stack (Btor * btor, BtorNodePtrStack * stack,
		       BtorNodePtrStack * cleanup_stack,
		       int *assignments_changed)
{
  BtorPartialParentIterator it;
  BtorNode *acc, *index, *value, *array, *hashed_acc, *hashed_value;
  BtorNode *cur_aeq, *cond, *next, *lambda_value, *lambda_exp, *parameterized;
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  BtorNodePtrStack param_read_stack;
  int assignment, indices_equal, propagate_writes_as_reads;//, parameterized;
  assert (btor);
  assert (stack);
  assert (assignments_changed);
  assert (btor->ops[BTOR_AEQ_NODE] >= 0);
  propagate_writes_as_reads =
    (btor->ops[BTOR_AEQ_NODE] > 0) || btor->model_gen;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  mm = btor->mm;

  while (!BTOR_EMPTY_STACK (*stack))
    {
      array = BTOR_POP_STACK (*stack);
      assert (BTOR_IS_REGULAR_NODE (array));
      assert (BTOR_IS_ARRAY_NODE (array));
      assert (!array->simplified);
      assert (!BTOR_EMPTY_STACK (*stack));
      acc = BTOR_POP_STACK (*stack);
      assert (BTOR_IS_REGULAR_NODE (acc));
      assert (BTOR_IS_ACC_NODE (acc));
      check_not_simplified_or_const (btor, acc);
      /* synthesize index and value if necessary */
      if (BTOR_IS_LAMBDA_NODE (acc))
	*assignments_changed =
	  lazy_synthesize_and_encode_lambda_exp (btor, acc, 1);
      else
	*assignments_changed =
	  lazy_synthesize_and_encode_acc_exp (btor, acc, 1);
      index = BTOR_GET_INDEX_ACC_NODE (acc);
      value = BTOR_GET_VALUE_ACC_NODE (acc);
      check_not_simplified_or_const (btor, index);
      check_not_simplified_or_const (btor, value);
      if (*assignments_changed)
	return 0;
      //debug
      BTORLOG ("");
      BTORLOG ("*** process_working_stack");
      BTORLOG ("array: %s", node2string (array));
      BTORLOG ("access: %s", node2string (acc));
      char *a = btor_bv_assignment_exp (btor, value);
      BTORLOG ("   value: %s, %s", a, node2string (value));
      btor_free_bv_assignment_exp (btor, a);
      a = btor_bv_assignment_exp (btor, index);
      BTORLOG ("   index: %s, %s", a, node2string (index));
      btor_free_bv_assignment_exp (btor, a);
      //debug
      /* hash table lookup */
      if (!array->rho)
	{
	  array->rho =
	    btor_new_ptr_hash_table (mm,
	      (BtorHashPtr) hash_assignment, (BtorCmpPtr) compare_assignments);
	  BTOR_PUSH_STACK (mm, *cleanup_stack, array);
	}
      else
	{
	  /* check array axiom 1 */
	  bucket = btor_find_in_ptr_hash_table (array->rho, index);
	  if (bucket)
	    {
	      hashed_acc = (BtorNode *) bucket->data.asPtr;
	      assert (BTOR_IS_REGULAR_NODE (hashed_acc));
	      assert (BTOR_IS_ACC_NODE (hashed_acc));
	      hashed_value = BTOR_GET_VALUE_ACC_NODE (hashed_acc);
	      /* we have to check if values are equal */
	      if (compare_assignments (hashed_value, value) != 0)
		{
		  BTORLOG ("\e[1;31m");
		  BTORLOG ("A1 conflict in array expression: %s",
			   node2string (array));
		  BTORLOG ("add_lemma:");
		  BTORLOG ("  array: %s", node2string (array));
		  BTORLOG ("  acc1: %s", node2string (hashed_acc));
		  BTORLOG ("  acc2: %s", node2string (acc));
		  BTORLOG ("\e[0;39m");
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
      if (BTOR_IS_WRITE_NODE (array))
	{
	  *assignments_changed =
	    lazy_synthesize_and_encode_acc_exp (btor, array, 1);
	  if (*assignments_changed)
	    return 0;
	  /* check array axiom 2 */
	  if (find_array_axiom_2_conflict (btor, acc, array, &indices_equal))
	    {
	      BTORLOG ("\e[1;31m");
	      BTORLOG ("A2 conflict in array expression: %s",
		       node2string (array));
	      BTORLOG ("add_lemma:");
	      BTORLOG ("  array: %s", node2string (array));
	      BTORLOG ("  acc1: %s", node2string (acc));
	      BTORLOG ("  acc2: %s", node2string (array));
	      BTORLOG ("\e[0;39m");
	      btor->stats.array_axiom_2_conflicts++;
	      add_lemma (btor, array, acc, array);
	      return 1;
	    }
	  else if (!indices_equal)
	    {
	      /* propagate down */
	      assert (BTOR_IS_REGULAR_NODE (array->e[0]));
	      assert (BTOR_IS_ARRAY_NODE (array->e[0]));
	      assert (!array->e[0]->simplified);
	      BTOR_PUSH_STACK (mm, *stack, acc);
	      BTOR_PUSH_STACK (mm, *stack, array->e[0]);
	      BTORLOG ("write exp prop. down:");
	      BTORLOG ("  acc: %s", node2string (acc));
	      BTORLOG ("  array: %s", node2string (array->e[0]));
	    }
	}
      else if (BTOR_IS_ARRAY_COND_NODE (array))
	{
	  *assignments_changed =
	    lazy_synthesize_and_encode_acond_exp (btor, array, 1);
	  if (*assignments_changed)
	    return 0;
	  cond = array->e[0];
	  check_not_simplified_or_const (btor, index);
	  assert (BTOR_IS_SYNTH_NODE (BTOR_REAL_ADDR_NODE (cond)));
	  assignment =
	    btor_get_assignment_aig (amgr,
				     BTOR_REAL_ADDR_NODE (cond)->av->aigs[0]);
	  assert (assignment == 1 || assignment == -1);
	  if (BTOR_IS_INVERTED_NODE (cond))
	    assignment = -assignment;
	  /* propagate down */
	  BTOR_PUSH_STACK (mm, *stack, acc);
	  BTORLOG ("array cond prop. down:");
	  BTORLOG ("  acc: %s", node2string (acc));
	  if (assignment == 1)
	    {
	      assert (BTOR_IS_REGULAR_NODE (array->e[1]));
	      assert (BTOR_IS_ARRAY_NODE (array->e[1]));
	      assert (!array->e[1]->simplified);
	      BTOR_PUSH_STACK (mm, *stack, array->e[1]);
	      BTORLOG ("  array: %s", node2string (array->e[1]));
	    }
	  else
	    {
	      assert (BTOR_IS_REGULAR_NODE (array->e[2]));
	      assert (BTOR_IS_ARRAY_NODE (array->e[2]));
	      assert (!array->e[2]->simplified);
	      BTOR_PUSH_STACK (mm, *stack, array->e[2]);
	      BTORLOG ("  array: %s", node2string (array->e[2]));
	    }
	}
      else if (BTOR_IS_LAMBDA_NODE (array))
	{
	  *assignments_changed =
	    lazy_synthesize_and_encode_lambda_exp (btor, array, 1);
	  if (*assignments_changed)
	    return 0;

	  btor_assign_param (btor, array, index);
	  lambda_value = btor_beta_reduce_cutoff (btor, array, &parameterized);
	  btor_unassign_param (btor, array);

	  // debug
	  char *a = btor_bv_assignment_exp (btor, value);
	  BTORLOG ("   value:  %s, %s", a, node2string (value));
	  btor_free_bv_assignment_exp (btor, a);
	  a = btor_bv_assignment_exp (btor, index);
	  BTORLOG ("   index:  %s, %s", a, node2string (index));
	  btor_free_bv_assignment_exp (btor, a);
	  a = btor_bv_assignment_exp (btor, lambda_value);
	  BTORLOG ("   lambda: %s, %s", a, node2string (lambda_value));
	  btor_free_bv_assignment_exp (btor, a);
	  BTORLOG ("   lambda parameterized: %d", parameterized);
	  // end debug
	  
	  /* propagate down  */

	  /* as soon as we encounter a parameterized read, we propagate acc
	   * down */
	  if (BTOR_IS_READ_NODE (BTOR_REAL_ADDR_NODE (lambda_value))
	      && parameterized)
	    {
	      lambda_value = BTOR_REAL_ADDR_NODE (lambda_value);

	      BTOR_PUSH_STACK (mm, *stack, acc);
	      BTOR_PUSH_STACK (mm, *stack, lambda_value->e[0]);
	      BTORLOG ("lambda exp prop. down:");
	      BTORLOG ("  acc: %s", node2string (acc));
	      BTORLOG ("  array: %s", node2string (lambda_value->e[0]));
	    }
	  else
	    {
	      /* check for array axiom 2 conflict */
	      if (compare_assignments (value, lambda_value) != 0)
		{
		  BTORLOG ("\e[1;31m");
		  BTORLOG ("A2 conflict in lambda expression: %s",
			   node2string (array));
		  BTORLOG (" add_lemma:");
		  BTORLOG ("   array: %s", node2string (array));
		  BTORLOG ("   acc1: %s", node2string (acc));
		  BTORLOG ("   acc2: %s", node2string (array));
		  BTORLOG ("\e[0;39m");

		  btor->stats.array_axiom_2_conflicts++;
		  add_lemma (btor, array, acc, array);
		  btor_release_exp (btor, lambda_value);
		  return 1;
		}
	    }
	  btor_release_exp (btor, lambda_value);
	}
      assert (array->rho);
      /* insert into hash table */
      btor_insert_in_ptr_hash_table (array->rho, index)->data.asPtr = acc;
      if (propagate_writes_as_reads)
	{
	  /* propagate pairs wich are reachable via array equality */
	  init_aeq_parent_iterator (&it, array);
	  while (has_next_parent_aeq_parent_iterator (&it))
	    {
	      cur_aeq = next_parent_aeq_parent_iterator (&it);
	      assert (BTOR_IS_REGULAR_NODE (cur_aeq));
	      check_not_simplified_or_const (btor, cur_aeq);
	      if (cur_aeq->reachable)
		{
		  assert (BTOR_IS_SYNTH_NODE (cur_aeq));
		  assert (cur_aeq->tseitin);
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
		      assert (BTOR_IS_REGULAR_NODE (next));
		      assert (BTOR_IS_ARRAY_NODE (next));
		      assert (!next->simplified);
		      BTOR_PUSH_STACK (mm, *stack, acc);
		      BTOR_PUSH_STACK (mm, *stack, next);
		      BTORLOG ("aeq exp prop.:");
		      BTORLOG ("  acc: %s", node2string (acc));
		      BTORLOG ("  array: %s", node2string (next));
		    }
		}
	    }
	  /* propagate upwards */
	  init_acond_parent_iterator (&it, array);
	  while (has_next_parent_acond_parent_iterator (&it))
	    {
	      next = next_parent_acond_parent_iterator (&it);
	      assert (!next->simplified);
	      if (next->reachable)
		{
		  assert (BTOR_IS_REGULAR_NODE (next));
		  assert (BTOR_IS_ARRAY_NODE (next));
		  *assignments_changed =
		    lazy_synthesize_and_encode_acond_exp (btor, next, 1);
		  if (*assignments_changed)
		    return 0;
		  cond = next->e[0];
		  assignment =
		    btor_get_assignment_aig (amgr,
					     BTOR_REAL_ADDR_NODE (cond)->av->
					     aigs[0]);
		  assert (assignment == 1 || assignment == -1);
		  if (BTOR_IS_INVERTED_NODE (cond))
		    assignment = -assignment;
		  /* propagate upwards only if array has been selected
		   * by the condition */
		  if ((assignment == 1 && array == next->e[1]) ||
		      (assignment == -1 && array == next->e[2]))
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
	      assert (!next->simplified);
	      if (next->reachable)
		{
		  assert (BTOR_IS_REGULAR_NODE (next));
		  assert (BTOR_IS_ARRAY_NODE (next));
		  *assignments_changed =
		    lazy_synthesize_and_encode_acc_exp (btor, next, 1);
		  if (*assignments_changed)
		    return 0;
		  /* propagate upwards only if assignments to the
		   * indices are unequal */
		  if (compare_assignments (next->e[1], index) != 0)
		    {
		      BTOR_PUSH_STACK (mm, *stack, acc);
		      BTOR_PUSH_STACK (mm, *stack, next);
		    }
		}
	    }
	  /* propagate upwards lambda expressions */
	  BTOR_INIT_STACK (param_read_stack);
	  init_read_parent_iterator (&it, array);
	  /* get all parameterized reads on array */
	  while (has_next_parent_read_parent_iterator (&it))
	    {
	      next = next_parent_read_parent_iterator (&it);
	      assert (BTOR_IS_REGULAR_NODE (next));
	      assert (BTOR_IS_READ_NODE (next));
  //            assert (!next->simplified);
	      if (next->reachable && BTOR_IS_PARAM_NODE (next->e[1]))
		  BTOR_PUSH_STACK (mm, param_read_stack, next);
	    }

	  while (!BTOR_EMPTY_STACK (param_read_stack))
	    {
	      next = BTOR_POP_STACK (param_read_stack);
	      assert (BTOR_IS_REGULAR_NODE (next));
	      assert (BTOR_IS_PARAM_NODE (next->e[1]));

	      lambda_exp = ((BtorParamNode *) next->e[1])->lambda_exp;

	      /* ensure that given lambda expression is synthesized and encoded
	       */
	      if (!lambda_exp->tseitin)
		{
		  *assignments_changed =
		    lazy_synthesize_and_encode_lambda_exp (btor, lambda_exp, 1);

		  if (*assignments_changed)
		    {
		      BTOR_RELEASE_STACK (mm, param_read_stack);
		      return 0;
		    }
		}

	      /* instantiate lambda expressions with read index of acc */
	      btor_assign_param (btor, lambda_exp, index);
	      lambda_value = 
		btor_beta_reduce_cutoff (btor, lambda_exp, &parameterized);
	      btor_unassign_param (btor, lambda_exp);
		
	      lambda_value = BTOR_REAL_ADDR_NODE (lambda_value);

	      if (BTOR_IS_READ_NODE (lambda_value) && parameterized)
		{
		  assert (lambda_value->e[0] == next->e[0]);
		  assert (lambda_value->e[1] == index);
		  BTORLOG ("lambda prop. upwards:");
		  BTORLOG ("  access: %s", node2string (acc));
		  BTORLOG ("  array: %s", node2string (lambda_exp));
		  BTOR_PUSH_STACK (mm, *stack, acc);
		  BTOR_PUSH_STACK (mm, *stack, lambda_exp);
		}
	      btor_release_exp (btor, lambda_value);
	    }
	  BTOR_RELEASE_STACK (mm, param_read_stack);
	}
    }
  return 0;
}
#endif

/* searches the top arrays where the conflict check begins
 * and pushes them on the stack
 */
static void
search_top_arrays (Btor *btor, BtorNodePtrStack *top_arrays)
{
  BtorPartialParentIterator it;
  BtorNode *cur_array, *cur_parent, *param;
  BtorNodePtrStack stack, unmark_stack, params;
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  int found_top;
  assert (btor);
  assert (top_arrays);
  assert (BTOR_COUNT_STACK (*top_arrays) == 0);
  mm = btor->mm;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (params);
  for (bucket = btor->array_vars->first; bucket; bucket = bucket->next)
  {
    cur_array = (BtorNode *) bucket->key;
    assert (BTOR_IS_ARRAY_VAR_NODE (cur_array));
    assert (!cur_array->simplified);
    if (cur_array->reachable) BTOR_PUSH_STACK (mm, stack, cur_array);
  }
  /* add lambda expressions  */
  for (bucket = btor->lambdas->first; bucket; bucket = bucket->next)
  {
    cur_array = (BtorNode *) bucket->key;
    assert (BTOR_IS_LAMBDA_NODE (cur_array));
    assert (!cur_array->simplified);
    if (cur_array->reachable) BTOR_PUSH_STACK (mm, stack, cur_array);
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_array = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur_array));
    assert (BTOR_IS_ARRAY_NODE (cur_array));
    assert (cur_array->reachable);
    assert (!cur_array->simplified);
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
      // TODO: use full parent iterator instead of three different ones
      /* push writes on stack */
      init_write_parent_iterator (&it, cur_array);
      while (has_next_parent_write_parent_iterator (&it))
      {
        cur_parent = next_parent_write_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
        assert (!cur_parent->simplified);
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
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
        assert (!cur_parent->simplified);
        if (cur_parent->reachable)
        {
          found_top = 0;
          BTOR_PUSH_STACK (mm, stack, cur_parent);
        }
      }
      /* push lambda expressions on stack */
      init_read_parent_iterator (&it, cur_array);
      while (has_next_parent_read_parent_iterator (&it))
      {
        cur_parent = next_parent_read_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
        if (cur_parent->reachable && cur_parent->parameterized)
        {
          assert (!cur_parent->simplified);
          assert (BTOR_EMPTY_STACK (params));
          find_nodes_dfs (
              btor, cur_parent, &params, findfun_param, skipfun_param);
          found_top = 0;
          assert (cur_parent->array_mark == 0);
          assert (BTOR_COUNT_STACK (params) > 0);

          while (!BTOR_EMPTY_STACK (params))
          {
            param = BTOR_POP_STACK (params);
            assert (BTOR_IS_REGULAR_NODE (param));
            assert (BTOR_IS_PARAM_NODE (param));
            BTOR_PUSH_STACK (mm, stack, ((BtorParamNode *) param)->lambda_exp);
          }
        }
      }
      // TODO: nested lambdas: if parent of lambda is another lambda, then
      //       push lambda above
      if (found_top) BTOR_PUSH_STACK (mm, *top_arrays, cur_array);
    }
  }
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, stack);

  /* reset array marks of arrays */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur_array = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur_array));
    assert (BTOR_IS_ARRAY_NODE (cur_array));
    assert (cur_array->array_mark == 1);
    cur_array->array_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static int
check_and_resolve_conflicts (Btor *btor, BtorNodePtrStack *top_arrays)
{
  BtorNodePtrStack array_stack, cleanup_stack, working_stack, unmark_stack;
  BtorNodePtrStack param_reads;
  BtorPartialParentIterator it;
  BtorMemMgr *mm;
  BtorNode *cur_array, *cur_parent, **top, **temp, *param_read;
  int found_conflict, changed_assignments, propagate_writes_as_reads;
  assert (btor);
  assert (top_arrays);
  found_conflict = 0;
  mm             = btor->mm;
  assert (btor->ops[BTOR_AEQ_NODE] >= 0);
  propagate_writes_as_reads = (btor->ops[BTOR_AEQ_NODE] > 0) || btor->model_gen;
BTOR_READ_WRITE_ARRAY_CONFLICT_CHECK:
  assert (!found_conflict);
  changed_assignments = 0;
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (working_stack);
  BTOR_INIT_STACK (cleanup_stack);
  BTOR_INIT_STACK (array_stack);
  BTOR_INIT_STACK (param_reads);

  /* push all top arrays on the stack */
  top = top_arrays->top;
  for (temp = top_arrays->start; temp != top; temp++)
  {
    cur_array = *temp;
    assert (BTOR_IS_REGULAR_NODE (cur_array));
    assert (BTOR_IS_ARRAY_NODE (cur_array));
    assert (cur_array->reachable);
    assert (!cur_array->simplified);
    BTOR_PUSH_STACK (mm, array_stack, cur_array);
  }

  while (!BTOR_EMPTY_STACK (array_stack))
  {
    cur_array = BTOR_POP_STACK (array_stack);
    assert (BTOR_IS_REGULAR_NODE (cur_array));
    assert (BTOR_IS_ARRAY_NODE (cur_array));
    assert (cur_array->reachable);
    assert (!cur_array->simplified);
    assert (cur_array->array_mark == 0 || cur_array->array_mark == 1);
    if (cur_array->array_mark == 0)
    {
      cur_array->array_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur_array);
      if (BTOR_IS_WRITE_NODE (cur_array))
      {
        BTOR_PUSH_STACK (mm, array_stack, cur_array->e[0]);
        if (propagate_writes_as_reads)
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
      else if (BTOR_IS_ARRAY_COND_NODE (cur_array))
      {
        BTOR_PUSH_STACK (mm, array_stack, cur_array->e[2]);
        BTOR_PUSH_STACK (mm, array_stack, cur_array->e[1]);
      }
      else if (BTOR_IS_LAMBDA_NODE (cur_array))
      {
        assert (BTOR_IS_PARAM_NODE (cur_array->e[0]));
        assert (BTOR_EMPTY_STACK (param_reads));
        find_nodes_dfs (btor,
                        cur_array->e[1],
                        &param_reads,
                        findfun_param_read,
                        skipfun_param);

        /* push all arrays onto stack that are overwritten by lambda exp
         */
        while (!BTOR_EMPTY_STACK (param_reads))
        {
          param_read = BTOR_POP_STACK (param_reads);
          assert (BTOR_IS_REGULAR_NODE (param_read));
          assert (BTOR_IS_READ_NODE (param_read));
          assert (param_read->parameterized);
          BTOR_PUSH_STACK (mm, array_stack, param_read->e[0]);
        }
// NOTE: code not used right now, as we do not rewrite writes in case of
//       extensionality
#if 0
	      // FIXME this is a temporary measure in order to make
	      // extensionality for writes rewritten as lambdas work again
	      // -> will have to do this properly for the general case
	      if (propagate_writes_as_reads)
		{
		  /* propagate lambdas which are writes as reads if there are
		   * array equalities */
		  BTOR_PUSH_STACK (mm, working_stack, cur_array);
		  BTOR_PUSH_STACK (mm, working_stack, cur_array);
		  found_conflict =
		    process_working_stack (btor, &working_stack, &cleanup_stack,
					   &changed_assignments);
		  if (found_conflict || changed_assignments)
		    goto BTOR_READ_WRITE_ARRAY_CONFLICT_CLEANUP;
		}
#endif
      }
      init_read_parent_iterator (&it, cur_array);
      while (has_next_parent_read_parent_iterator (&it))
      {
        cur_parent = next_parent_read_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));

        /* skip parameterized reads */
        if (cur_parent->parameterized) continue;

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
    assert (BTOR_IS_REGULAR_NODE (cur_array));
    assert (BTOR_IS_ARRAY_NODE (cur_array));
    assert (cur_array->rho);

    if (found_conflict || changed_assignments)
    {
      btor_delete_ptr_hash_table (cur_array->rho);
      cur_array->rho = 0;
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
  BTOR_RELEASE_STACK (mm, param_reads);

  /* reset array marks of arrays */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur_array = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (cur_array));
    assert (BTOR_IS_ARRAY_NODE (cur_array));
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
  assert (btor);
  for (bucket = btor->assumptions->first; bucket; bucket = bucket->next)
    btor_release_exp (btor, (BtorNode *) bucket->key);
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static void
btor_reset_array_models (Btor *btor)
{
  BtorNode *cur;
  int i;

  assert (btor);

  for (i = 0; i < BTOR_COUNT_STACK (btor->arrays_with_model); i++)
  {
    cur = btor->arrays_with_model.start[i];
    assert (!BTOR_IS_INVERTED_NODE (cur));
    assert (BTOR_IS_ARRAY_NODE (cur));
    assert (cur->rho);
    btor_delete_ptr_hash_table (cur->rho);
    cur->rho = 0;
  }
  BTOR_RESET_STACK (btor->arrays_with_model);
}

static void
btor_reset_incremental_usage (Btor *btor)
{
  assert (btor);

  btor_reset_assumptions (btor);
  btor_reset_array_models (btor);
  btor->valid_assignments = 0;
}

/* check if left does not occur on the right side */
static int
occurrence_check (Btor *btor, BtorNode *left, BtorNode *right)
{
  BtorNode *cur, *real_left;
  BtorNodePtrStack stack, unmark_stack;
  int is_cyclic, i;
  BtorMemMgr *mm;
  assert (btor);
  assert (left);
  assert (right);

  is_cyclic = 0;
  mm        = btor->mm;
  real_left = BTOR_REAL_ADDR_NODE (left);
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark_stack);

  cur = BTOR_REAL_ADDR_NODE (right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));
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
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (cur->aux_mark == 1);
    cur->aux_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);

  return is_cyclic;
}

static BtorNode *
rebuild_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  switch (exp->kind)
  {
    case BTOR_PROXY_NODE:
    case BTOR_BV_CONST_NODE:
    case BTOR_BV_VAR_NODE:
    case BTOR_ARRAY_VAR_NODE:
    case BTOR_PARAM_NODE:
      return btor_copy_exp (btor,
                            btor_pointer_chase_simplified_exp (btor, exp));
    case BTOR_SLICE_NODE:
      return btor_slice_exp (btor, exp->e[0], exp->upper, exp->lower);
    case BTOR_AND_NODE: return btor_and_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: return btor_eq_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ADD_NODE: return btor_add_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_MUL_NODE: return btor_mul_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ULT_NODE: return btor_ult_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SLL_NODE: return btor_sll_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SRL_NODE: return btor_srl_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UDIV_NODE: return btor_udiv_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UREM_NODE: return btor_urem_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_CONCAT_NODE: return btor_concat_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_READ_NODE: return btor_read_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_WRITE_NODE:
      return btor_write_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
    case BTOR_LAMBDA_NODE:
      assert (BTOR_EMPTY_STACK (
          ((BtorParamNode *) BTOR_REAL_ADDR_NODE (exp->e[0]))->assigned_exp));
      ((BtorParamNode *) BTOR_REAL_ADDR_NODE (exp->e[0]))->lambda_exp = 0;
      return btor_lambda_exp (btor, exp->e[0], exp->e[1]);
    default:
      assert (BTOR_IS_ARRAY_OR_BV_COND_NODE (exp));
      return btor_cond_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
  }
}

static int
is_embedded_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return BTOR_REAL_ADDR_NODE (exp)->len == 1 && has_parents_exp (btor, exp);
}

static BtorNode *
lambda_var_exp (Btor *btor, int len)
{
  BtorNode *result;
  char *name;
  int string_len;
  BtorMemMgr *mm;

  assert (btor);
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

static BtorSubstCompKind
reverse_subst_comp_kind (Btor *btor, BtorSubstCompKind comp)
{
  assert (btor);
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
insert_unsynthesized_constraint (Btor *btor, BtorNode *exp)
{
  BtorPtrHashTable *uc;
  assert (btor);
  assert (exp);
  uc = btor->unsynthesized_constraints;
  if (!btor_find_in_ptr_hash_table (uc, exp))
  {
    assert (!btor_find_in_ptr_hash_table (btor->embedded_constraints, exp));
    inc_exp_ref_counter (btor, exp);
    (void) btor_insert_in_ptr_hash_table (uc, exp);
    BTOR_REAL_ADDR_NODE (exp)->constraint = 1;
    btor->stats.constraints.unsynthesized++;
  }
}

static void
insert_embedded_constraint (Btor *btor, BtorNode *exp)
{
  BtorPtrHashTable *embedded_constraints;
  assert (btor);
  assert (exp);
  embedded_constraints = btor->embedded_constraints;
  if (!btor_find_in_ptr_hash_table (embedded_constraints, exp))
  {
    assert (
        !btor_find_in_ptr_hash_table (btor->unsynthesized_constraints, exp));
    inc_exp_ref_counter (btor, exp);
    (void) btor_insert_in_ptr_hash_table (embedded_constraints, exp);
    BTOR_REAL_ADDR_NODE (exp)->constraint = 1;
    btor->stats.constraints.embedded++;
  }
}

static void
insert_varsubst_constraint (Btor *btor, BtorNode *left, BtorNode *right)
{
  BtorNode *eq;
  BtorPtrHashTable *vsc;
  BtorPtrHashBucket *bucket;

  assert (btor);
  assert (left);
  assert (right);

  vsc    = btor->varsubst_constraints;
  bucket = btor_find_in_ptr_hash_table (vsc, left);

  if (!bucket)
  {
    if (btor->model_gen && !BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (right))
        && !btor_find_in_ptr_hash_table (btor->var_rhs, left))
    {
      btor_insert_in_ptr_hash_table (btor->var_rhs, left);
      inc_exp_ref_counter (btor, left);
    }

    if (btor->model_gen && BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (right))
        && !btor_find_in_ptr_hash_table (btor->array_rhs, left))
    {
      btor_insert_in_ptr_hash_table (btor->array_rhs, left);
      inc_exp_ref_counter (btor, left);
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
  else if (right != (BtorNode *) bucket->data.asPtr)
  {
    eq = btor_eq_exp (btor, left, right);
    insert_unsynthesized_constraint (btor, eq);
    btor_release_exp (btor, eq);
  }
}

/* checks if we can substitute and normalizes arguments to substitution,
 * substitute left_result with right_result, exp is child of AND_NODE */
static int
normalize_substitution (Btor *btor,
                        BtorNode *exp,
                        BtorNode **left_result,
                        BtorNode **right_result)
{
  BtorNode *left, *right, *real_left, *real_right, *tmp, *inv, *var, *lambda;
  BtorNode *const_exp, *real_exp;
  int leadings;
  char *ic, *fc, *bits;
  BtorMemMgr *mm;
  BtorSubstCompKind comp;

  assert (btor);
  assert (exp);
  assert (left_result);
  assert (right_result);
  assert (btor->rewrite_level > 1);
  assert (btor_simplify_exp (btor, exp) == exp);

  mm = btor->mm;

  /* boolean BV_NODE, force assignment (right_result) w.r.t. phase */
  if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (exp)))
  {
    assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
    if (BTOR_IS_INVERTED_NODE (exp))
    {
      *left_result  = BTOR_REAL_ADDR_NODE (exp);
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

  if (BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_ULT_NODE
      && (BTOR_IS_BV_VAR_NODE (
              BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->e[0]))
          || BTOR_IS_BV_VAR_NODE (
                 BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->e[1]))))
  {
    real_exp = BTOR_REAL_ADDR_NODE (exp);

    if (BTOR_IS_INVERTED_NODE (exp))
      comp = BTOR_SUBST_COMP_UGTE_KIND;
    else
      comp = BTOR_SUBST_COMP_ULT_KIND;

    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_exp->e[0])))
    {
      var   = real_exp->e[0];
      right = real_exp->e[1];
    }
    else
    {
      assert (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (real_exp->e[1])));
      var   = real_exp->e[1];
      right = real_exp->e[0];
      comp  = reverse_subst_comp_kind (btor, comp);
    }

    /* ~a comp b is equal to a reverse_comp ~b,
     * where comp in ult, ulte, ugt, ugte
     * (e.g. reverse_comp of ult is ugt) */
    if (BTOR_IS_INVERTED_NODE (var))
    {
      var   = BTOR_REAL_ADDR_NODE (var);
      right = BTOR_INVERT_NODE (right);
      comp  = reverse_subst_comp_kind (btor, comp);
    }

    /* we do not create a lambda (index) if variable is already in
     * substitution table */
    assert (!BTOR_IS_INVERTED_NODE (var));
    if (btor_find_in_ptr_hash_table (btor->varsubst_constraints, var)) return 0;

    if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (right))) return 0;

    if (BTOR_IS_INVERTED_NODE (right))
      bits = btor_not_const_3vl (mm, BTOR_REAL_ADDR_NODE (right)->bits);
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
  if (BTOR_IS_INVERTED_NODE (exp)
      && BTOR_REAL_ADDR_NODE (exp)->kind == BTOR_BEQ_NODE
      && BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->e[0])->len == 1)
  {
    left  = BTOR_REAL_ADDR_NODE (exp)->e[0];
    right = BTOR_REAL_ADDR_NODE (exp)->e[1];

    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (left)))
    {
      *left_result  = btor_copy_exp (btor, left);
      *right_result = BTOR_INVERT_NODE (btor_copy_exp (btor, right));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }

    if (BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (right)))
    {
      *left_result  = btor_copy_exp (btor, right);
      *right_result = BTOR_INVERT_NODE (btor_copy_exp (btor, left));
      goto BTOR_NORMALIZE_SUBST_RESULT;
    }
  }

  if (BTOR_IS_INVERTED_NODE (exp) || !BTOR_IS_ARRAY_OR_BV_EQ_NODE (exp))
    return 0;

  left       = exp->e[0];
  right      = exp->e[1];
  real_left  = BTOR_REAL_ADDR_NODE (left);
  real_right = BTOR_REAL_ADDR_NODE (right);

  if (!BTOR_IS_BV_VAR_NODE (real_left) && !BTOR_IS_BV_VAR_NODE (real_right)
      && !BTOR_IS_ARRAY_VAR_NODE (real_left)
      && !BTOR_IS_ARRAY_VAR_NODE (real_right))
  {
    if (btor_rewrite_linear_term (btor, left, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, right, tmp);
    else if (btor_rewrite_linear_term (btor, right, &fc, left_result, &tmp))
      *right_result = btor_sub_exp (btor, left, tmp);
    else
      return 0;

    btor->stats.gaussian_eliminations++;

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
    if ((!BTOR_IS_BV_VAR_NODE (real_left) && BTOR_IS_BV_VAR_NODE (real_right))
        || (!BTOR_IS_ARRAY_VAR_NODE (real_left)
            && BTOR_IS_ARRAY_VAR_NODE (real_right)))
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
  if (BTOR_IS_INVERTED_NODE (*left_result))
  {
    *left_result  = BTOR_INVERT_NODE (*left_result);
    *right_result = BTOR_INVERT_NODE (*right_result);
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
insert_new_constraint (Btor *btor, BtorNode *exp)
{
  BtorNode *left, *right, *real_exp;
  assert (btor);
  assert (exp);
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  if (btor->inconsistent) return;

  exp      = btor_simplify_exp (btor, exp);
  real_exp = BTOR_REAL_ADDR_NODE (exp);

  if (BTOR_IS_BV_CONST_NODE (real_exp))
  {
    if ((BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '1')
        || (!BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '0'))
    {
      btor->inconsistent = 1;
      return;
    }
    else
    {
      /* we do not add true */
      assert ((BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '0')
              || (!BTOR_IS_INVERTED_NODE (exp) && real_exp->bits[0] == '1'));
      return;
    }
  }

  if (!btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp))
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
        if (constraint_is_inconsistent (btor, exp))
          btor->inconsistent = 1;
        else
        {
          if (!real_exp->constraint)
          {
            if (is_embedded_constraint_exp (btor, exp))
              insert_embedded_constraint (btor, exp);
            else
              insert_unsynthesized_constraint (btor, exp);
          }
          else
          {
            assert (btor_find_in_ptr_hash_table (
                        btor->unsynthesized_constraints, exp)
                    || btor_find_in_ptr_hash_table (btor->embedded_constraints,
                                                    exp));
          }
        }
      }
    }
    else
      insert_unsynthesized_constraint (btor, exp);

    report_constraint_stats (btor, 0);
  }
}

static void
add_constraint (Btor *btor, BtorNode *exp)
{
  BtorNode *cur, *child;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;

  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  mm = btor->mm;
  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_NODE (exp) && exp->kind == BTOR_AND_NODE)
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (cur->kind == BTOR_AND_NODE);
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
          BTOR_PUSH_STACK (mm, stack, child);
        else
          insert_new_constraint (btor, child);
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
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
btor_add_constraint_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  add_constraint (btor, exp);
}

void
btor_add_assumption_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *cur, *child;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;

  assert (btor);
  assert (btor->inc_enabled);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));
  assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);

  mm = btor->mm;
  if (btor->valid_assignments) btor_reset_incremental_usage (btor);

  if (!BTOR_IS_INVERTED_NODE (exp) && exp->kind == BTOR_AND_NODE)
  {
    BTOR_INIT_STACK (stack);
    cur = exp;
    goto BTOR_ADD_ASSUMPTION_NODE_ENTER_WITHOUT_POP;

    do
    {
      cur = BTOR_POP_STACK (stack);
    BTOR_ADD_ASSUMPTION_NODE_ENTER_WITHOUT_POP:
      assert (!BTOR_IS_INVERTED_NODE (cur));
      assert (cur->kind == BTOR_AND_NODE);
      assert (cur->mark == 0 || cur->mark == 1);
      if (!cur->mark)
      {
        cur->mark = 1;
        child     = cur->e[1];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
        {
          BTOR_PUSH_STACK (mm, stack, child);
        }
        else
        {
          if (!btor_find_in_ptr_hash_table (btor->assumptions, child))
            (void) btor_insert_in_ptr_hash_table (btor->assumptions,
                                                  btor_copy_exp (btor, child));
        }
        child = cur->e[0];
        if (!BTOR_IS_INVERTED_NODE (child) && child->kind == BTOR_AND_NODE)
        {
          BTOR_PUSH_STACK (mm, stack, child);
        }
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
  assert (btor);

  BtorPtrHashTable *uc, *sc;
  BtorPtrHashBucket *bucket;
  BtorNode *cur;
  BtorAIG *aig;
  BtorAIGMgr *amgr;

  uc   = btor->unsynthesized_constraints;
  sc   = btor->synthesized_constraints;
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);

  while (uc->count > 0)
  {
    bucket = uc->first;
    assert (bucket);
    cur = (BtorNode *) bucket->key;

#ifndef NDEBUG
    if (btor->rewrite_level > 2)
    {
      BtorNode *real_cur = BTOR_REAL_ADDR_NODE (cur);
      if (real_cur->kind == BTOR_BEQ_NODE)
      {
        BtorNode *left  = real_cur->e[0];
        BtorNode *right = real_cur->e[1];
        BtorNode *other;

        if (BTOR_REAL_ADDR_NODE (left)->kind == BTOR_BV_CONST_NODE)
          other = right;
        else if (BTOR_REAL_ADDR_NODE (right)->kind == BTOR_BV_CONST_NODE)
          other = left;
        else
          other = 0;

        if (other && !BTOR_IS_INVERTED_NODE (other)
            && other->kind == BTOR_ADD_NODE)
        {
          assert (BTOR_REAL_ADDR_NODE (other->e[0])->kind
                  != BTOR_BV_CONST_NODE);
          assert (BTOR_REAL_ADDR_NODE (other->e[1])->kind
                  != BTOR_BV_CONST_NODE);
        }
      }
    }
#endif

    if (!btor_find_in_ptr_hash_table (sc, cur))
    {
      aig = exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE) return 1;

      btor_add_toplevel_aig_to_sat (amgr, aig);
      btor_release_aig (amgr, aig);
      (void) btor_insert_in_ptr_hash_table (sc, cur);
      btor_remove_from_ptr_hash_table (uc, cur, 0, 0);

      btor->stats.constraints.synthesized++;
      report_constraint_stats (btor, 0);
    }
    else
    {
      /* constraint is already in sc */
      btor_remove_from_ptr_hash_table (uc, cur, 0, 0);
      btor_release_exp (btor, cur);
    }
  }
  return 0;
}

static void
update_assumptions (Btor *btor)
{
  BtorPtrHashBucket *bucket;
  BtorNode *cur, *simp;
  assert (btor);
  for (bucket = btor->assumptions->first; bucket; bucket = bucket->next)
  {
    cur = (BtorNode *) bucket->key;
    if (cur->simplified)
    {
      simp = btor_copy_exp (btor, btor_simplify_exp (btor, cur));
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
  BtorNodePtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorNode *cur, *cur_parent, *rebuilt_exp, **temp, **top, *rhs, *simplified;
  BtorMemMgr *mm;
  BtorFullParentIterator it;
  int pushed, i;
  assert (btor);
  assert (substs);

  if (substs->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (root_stack);
  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  for (b = substs->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
    BTOR_PUSH_STACK (mm, stack, cur);
  }

  do
  {
    assert (!BTOR_EMPTY_STACK (stack));
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_NODE (cur));
    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      init_full_parent_iterator (&it, cur);
      /* are we at a root ? */
      pushed = 0;
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_NODE (cur_parent));
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
    cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

    if (cur->aux_mark == 0) continue;

    assert (!BTOR_IS_BV_CONST_NODE (cur));

    if (cur->aux_mark == 1)
    {
      BTOR_PUSH_STACK (mm, stack, cur);
      cur->aux_mark = 2;
      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur))
      {
        b = btor_find_in_ptr_hash_table (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.asPtr;
        assert (rhs);
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
      if (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur))
      {
        b = btor_find_in_ptr_hash_table (substs, cur);
        assert (b);
        assert (cur == (BtorNode *) b->key);
        rhs = (BtorNode *) b->data.asPtr;
        assert (rhs);
        rebuilt_exp = btor_copy_exp (btor, rhs);
        if (BTOR_IS_BV_VAR_NODE (cur))
          btor->stats.var_substitutions++;
        else
          btor->stats.array_substitutions++;
      }
      else
        rebuilt_exp = rebuild_exp (btor, cur);
      assert (rebuilt_exp);
      assert (rebuilt_exp != cur);

      simplified = btor_simplify_exp (btor, rebuilt_exp);
      set_simplified_exp (btor, cur, simplified);
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
substitute_var_exps (Btor *btor)
{
  BtorPtrHashTable *varsubst_constraints, *order, *substs;
  BtorNode *cur, *constraint, *left, *right, *child;
  BtorPtrHashBucket *b, *b_temp;
  int order_num, val, max, i;
  BtorNodePtrStack stack;
  double start, delta;
  unsigned count;
  BtorMemMgr *mm;

  assert (btor);
  mm                   = btor->mm;
  varsubst_constraints = btor->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  start = btor_time_stamp ();

  BTOR_INIT_STACK (stack);

  /* new equality constraints may be added during rebuild */
  count = 0;
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
      count++;
      b   = varsubst_constraints->first;
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
      btor_insert_in_ptr_hash_table (substs, cur)->data.asPtr = b->data.asPtr;
      btor_remove_from_ptr_hash_table (varsubst_constraints, cur, 0, 0);
    }
    assert (varsubst_constraints->count == 0u);

    /* we search for cyclic substitution dependencies
     * and map the substitutions to an ordering number */
    for (b = substs->first; b; b = b->next)
    {
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
      BTOR_PUSH_STACK (mm, stack, (BtorNode *) cur);

      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (!cur)
        {
          cur = BTOR_POP_STACK (stack); /* left */
          assert (BTOR_IS_REGULAR_NODE (cur));
          assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
          assert (!btor_find_in_ptr_hash_table (order, cur));
          btor_insert_in_ptr_hash_table (order, cur)->data.asInt = order_num++;
          continue;
        }

        if (cur->mark == 1) /* visited (DFS) */
          continue;

        cur->mark = 1;

        if (BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
            || BTOR_IS_ARRAY_VAR_NODE (cur) || BTOR_IS_PARAM_NODE (cur))
        {
          b_temp = btor_find_in_ptr_hash_table (substs, cur);
          if (b_temp)
          {
            BTOR_PUSH_STACK (mm, stack, cur); /* left  */
            BTOR_PUSH_STACK (mm, stack, 0);
            BTOR_PUSH_STACK (mm,
                             stack, /* right */
                             (BtorNode *) b_temp->data.asPtr);
          }
          else
          {
            assert (!btor_find_in_ptr_hash_table (order, cur));
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
    for (b = substs->first; b; b = b->next)
    {
      assert (BTOR_IS_REGULAR_NODE ((BtorNode *) b->key));
      assert (BTOR_IS_BV_VAR_NODE ((BtorNode *) b->key)
              || BTOR_IS_ARRAY_VAR_NODE ((BtorNode *) b->key));
      btor_mark_exp (btor, (BtorNode *) b->key, 0);
      btor_mark_exp (btor, (BtorNode *) b->data.asPtr, 0);
    }

    /* we look for cycles */
    for (b = substs->first; b; b = b->next)
    {
#ifndef NDEBUG
      cur = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (cur));
      assert (BTOR_IS_BV_VAR_NODE (cur) || BTOR_IS_ARRAY_VAR_NODE (cur));
#endif
      BTOR_PUSH_STACK (mm, stack, (BtorNode *) b->data.asPtr);

      /* we assume that there are no direct loops
       * as a result of occurrence check */
      while (!BTOR_EMPTY_STACK (stack))
      {
        cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

        if (cur->mark == 2) /* cur has max order of its children */
          continue;

        if (BTOR_IS_BV_CONST_NODE (cur) || BTOR_IS_BV_VAR_NODE (cur)
            || BTOR_IS_ARRAY_VAR_NODE (cur) || BTOR_IS_PARAM_NODE (cur))
        {
          assert (btor_find_in_ptr_hash_table (order, cur));
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
        else /* cur is visited, its children are visited */
        {
          /* compute maximum of children */
          assert (cur->mark == 1);
          cur->mark = 2;
          max       = 0;
          for (i = cur->arity - 1; i >= 0; i--)
          {
            child  = BTOR_REAL_ADDR_NODE (cur->e[i]);
            b_temp = btor_find_in_ptr_hash_table (order, child);
            assert (b_temp);
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
    for (b = substs->first; b; b = b->next)
    {
      left = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (BTOR_IS_BV_VAR_NODE (left) || BTOR_IS_ARRAY_VAR_NODE (left));
      right = (BtorNode *) b->data.asPtr;
      btor_mark_exp (btor, left, 0);
      btor_mark_exp (btor, right, 0);
      b_temp = btor_find_in_ptr_hash_table (order, left);
      assert (b_temp);
      order_num = b_temp->data.asInt;
      b_temp = btor_find_in_ptr_hash_table (order, BTOR_REAL_ADDR_NODE (right));
      assert (b_temp);
      max = b_temp->data.asInt;
      assert (order_num != max);
      /* found cycle */
      if (max > order_num) BTOR_PUSH_STACK (mm, stack, left);
    }

    /* we delete cyclic substitutions and synthesize them instead */
    while (!BTOR_EMPTY_STACK (stack))
    {
      left = BTOR_POP_STACK (stack);
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (BTOR_IS_BV_VAR_NODE (left) || BTOR_IS_ARRAY_VAR_NODE (left));
      right =
          (BtorNode *) btor_find_in_ptr_hash_table (substs, left)->data.asPtr;
      assert (right);

      constraint = btor_eq_exp (btor, left, right);
      insert_unsynthesized_constraint (btor, constraint);
      btor_release_exp (btor, constraint);

      btor_remove_from_ptr_hash_table (substs, left, 0, 0);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    /* we rebuild and substiute variables in one pass */
    substitute_vars_and_rebuild_exps (btor, substs);

    /* cleanup, we delete all substitution constraints */
    for (b = substs->first; b; b = b->next)
    {
      left = (BtorNode *) b->key;
      assert (BTOR_IS_REGULAR_NODE (left));
      assert (left->kind == BTOR_PROXY_NODE);
      assert (left->simplified);
      right = (BtorNode *) b->data.asPtr;
      assert (right);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
    }

    btor_delete_ptr_hash_table (order);
    btor_delete_ptr_hash_table (substs);
  }

  BTOR_RELEASE_STACK (mm, stack);
  delta = btor_time_stamp () - start;
  btor->time.subst += delta;
  if (btor->verbosity)
    btor_msg_exp (
        btor, "%d variables substituted in %.1f seconds", count, delta);
}

static int
all_exps_below_rebuilt (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int i;
  BtorNode *subst;

  if (btor->substitutions)
  {
    subst = btor_find_substitution (btor, exp);
    if (subst && BTOR_REAL_ADDR_NODE (subst)->aux_mark != 0) return 0;
  }

  exp = BTOR_REAL_ADDR_NODE (exp);
  for (i = 0; i < exp->arity; i++)
    if (BTOR_REAL_ADDR_NODE (exp->e[i])->aux_mark > 0) return 0;

  return 1;
}

static void
substitute_and_rebuild (Btor *btor, BtorPtrHashTable *subst, int rww, int rwr)
{
  assert (btor);
  assert (subst);
  assert (rww == 0 || rww == 1);
  assert (rwr == 0 || rwr == 1);

  int i, pushed;
  BtorMemMgr *mm;
  BtorNode *cur, *cur_parent, *rebuilt_exp, *simplified;
  BtorNodePtrStack roots;
  BtorNodePtrQueue queue;
  BtorPtrHashBucket *b;
  BtorFullParentIterator it;

  if (subst->count == 0u) return;

  mm = btor->mm;

  BTOR_INIT_STACK (roots);
  BTOR_INIT_QUEUE (queue);

  //  printf ("%s\n", __FUNCTION__);
  assert (check_unique_table_mark_unset_dbg (btor));
  assert (check_unique_table_aux_mark_unset_dbg (btor));
  for (b = subst->first; b; b = b->next)
  {
    cur = BTOR_REAL_ADDR_NODE ((BtorNode *) b->key);
    assert (!BTOR_IS_PROXY_NODE (cur));
    if (rww || rwr) cur->mark = 1;
    BTOR_ENQUEUE (mm, queue, cur);
  }

  /* mark cone and copy roots */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!BTOR_IS_PROXY_NODE (cur));

    if (cur->aux_mark == 0)
    {
      cur->aux_mark = 1;
      //	  printf ("cone: %s\n", node2string (cur));

      pushed = 0;
      init_full_parent_iterator (&it, cur);
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        BTOR_ENQUEUE (mm, queue, cur_parent);
        pushed = 1;
      }
      if (!pushed) BTOR_PUSH_STACK (mm, roots, btor_copy_exp (btor, cur));
    }
  }

  for (b = subst->first; b; b = b->next)
  {
    cur = BTOR_REAL_ADDR_NODE ((BtorNode *) b->key);
    assert (cur->aux_mark == 1);
    BTOR_ENQUEUE (mm, queue, cur);
    cur->aux_mark = 2;
    //      printf ("enqueue: %s\n", node2string (cur));
  }

  /* rebuild bottom-up */
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_NODE (cur));
    assert (!BTOR_IS_PROXY_NODE (cur));
    assert (cur->aux_mark == 2);
    cur->aux_mark = 1;

    //      if (cur->aux_mark == 0)
    //	continue;

    if (all_exps_below_rebuilt (btor, cur))
    {
      cur->aux_mark = 0;

      init_full_parent_iterator (&it, cur);
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        //	      printf ("  enqueue: %s (%d)\n", node2string (cur_parent),
        //		      cur_parent->aux_mark);

        /* cur might get a new parent while rebuilding due to
         * simplification */
        if (cur_parent->aux_mark == 0 || cur_parent->aux_mark == 1)
        {
          BTOR_ENQUEUE (mm, queue, cur_parent);
          cur_parent->aux_mark = 2;
        }
      }

      simplified = btor_find_substitution (btor, cur);

      if (simplified)
      {
        assert (BTOR_REAL_ADDR_NODE (simplified) != cur);
        assert (!BTOR_REAL_ADDR_NODE (simplified)->simplified);
        //	      printf ("  set simplified: %s -> %s\n",
        //		      node2string (cur), node2string (simplified));
        set_simplified_exp (btor, cur, simplified);
        continue;
      }

      /* we only have to rewrite reads/writes if cur is in subst */
      if (rww && BTOR_IS_WRITE_NODE (cur) && cur->mark)
      {
        cur->mark   = 0;
        rebuilt_exp = rewrite_write_to_lambda_exp (btor, cur);
      }
      else if (rwr && BTOR_IS_READ_NODE (cur) && cur->mark)
      {
        cur->mark   = 0;
        rebuilt_exp = btor_beta_reduce_full (btor, cur);
      }
      else
      {
        assert (!cur->mark);
        rebuilt_exp = rebuild_exp (btor, cur);
      }

      //	      printf ("rebuild: %s, rebuilt: %s\n",
      //		      node2string (cur),
      //		      node2string (rebuilt_exp));

      assert (rebuilt_exp);
      /* base case: rebuilt_exp == cur */
      if (rebuilt_exp != cur)
      {
        simplified = btor_simplify_exp (btor, rebuilt_exp);
        //	      printf ("  set simplified: %s -> %s\n",
        //		      node2string (cur), node2string (simplified));
        set_simplified_exp (btor, cur, simplified);
      }

      btor_release_exp (btor, rebuilt_exp);
    }
    else
    {
      cur->aux_mark = 2;
      BTOR_ENQUEUE (mm, queue, cur);
    }
  }

  BTOR_RELEASE_QUEUE (mm, queue);

  for (i = 0; i < BTOR_COUNT_STACK (roots); i++)
    btor_release_exp (btor, roots.start[i]);

  BTOR_RELEASE_STACK (mm, roots);

  assert (check_unique_table_mark_unset_dbg (btor));
  assert (check_unique_table_aux_mark_unset_dbg (btor));
}

#if 0
/* Simple substitution by following simplified pointer.
 */
static void
substitute_and_rebuild_old (Btor * btor, BtorPtrHashTable *subst, int rww, int rwr)
{
  BtorNodePtrStack stack, root_stack;
  BtorPtrHashBucket *b;
  BtorNode *cur, *cur_parent, *rebuilt_exp, *simplified;
  BtorMemMgr *mm;
  BtorFullParentIterator it;
  int pushed, i;

  assert (btor);
  assert (subst);

  if (subst->count == 0u)
    return;

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (root_stack);

  /* we push all expressions on the search stack */
  for (b = subst->first; b; b = b->next)
    {
      cur = (BtorNode *) b->key;
      assert (!BTOR_REAL_ADDR_NODE (cur)->mark);
      if (rww || rwr)
	BTOR_REAL_ADDR_NODE (cur)->mark = 1;  /* mark as node in subst */
      BTOR_PUSH_STACK (mm, stack, BTOR_REAL_ADDR_NODE (cur));
    }
  while (!BTOR_EMPTY_STACK (stack))
    {
      /* search upwards for all reachable roots */
      cur = BTOR_POP_STACK (stack);
      assert (BTOR_IS_REGULAR_NODE (cur));
      if (cur->aux_mark == 0)
	{
	  cur->aux_mark = 1;
	  init_full_parent_iterator (&it, cur);
	  /* are we at a root ? */
	  pushed = 0;
	  while (has_next_parent_full_parent_iterator (&it))
	    {
	      cur_parent = next_parent_full_parent_iterator (&it);
	      assert (BTOR_IS_REGULAR_NODE (cur_parent));
	      pushed = 1;
	      BTOR_PUSH_STACK (mm, stack, cur_parent);
	    }
	  if (!pushed)
	    BTOR_PUSH_STACK (mm, root_stack, btor_copy_exp (btor, cur));
	}
    }

  /* copy roots on substitution stack */
  for (i = 0; i < BTOR_COUNT_STACK (root_stack); i++)
    BTOR_PUSH_STACK (mm, stack, root_stack.start[i]);

  /* substitute */
  while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (stack));

      if (cur->aux_mark == 0)
	continue;

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

	  /* we only have to rewrite reads/writes if cur is in subst */
	  if (rww && BTOR_IS_WRITE_NODE (cur) && cur->mark)
	    {
	      cur->mark = 0;
	      rebuilt_exp = rewrite_write_to_lambda_exp (btor, cur);
	    }
	  else if (rwr && BTOR_IS_READ_NODE (cur) && cur->mark)
	    {
	      cur->mark = 0;
	      rebuilt_exp = btor_beta_reduce (btor, cur, BETA_RED_FULL, 0);
	    }
	  else
	    {
	      assert (!cur->mark);
	      rebuilt_exp = rebuild_exp (btor, cur);
	    }

	  assert (rebuilt_exp);
	  /* base case: rebuilt_exp == cur */
	  if (rebuilt_exp != cur)
	    {
	      simplified = btor_simplify_exp (btor, rebuilt_exp);
	      set_simplified_exp (btor, cur, simplified);
	    }

	  btor_release_exp (btor, rebuilt_exp);
	}
    }

  BTOR_RELEASE_STACK (mm, stack);

  for (i = 0; i < BTOR_COUNT_STACK (root_stack); i++)
    btor_release_exp (btor, root_stack.start[i]);
  BTOR_RELEASE_STACK (mm, root_stack);
}
#endif

static void
substitute_embedded_constraints (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorNode *cur;

  assert (btor);

  for (b = btor->embedded_constraints->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    assert (BTOR_REAL_ADDR_NODE (cur)->constraint);
    /* embedded constraints have possibly lost their parents,
     * e.g. top conjunction of constraints that are released */
    if (has_parents_exp (btor, cur)) btor->stats.ec_substitutions++;
  }
  substitute_and_rebuild (btor, btor->embedded_constraints, 0, 0);
}

static void
process_embedded_constraints (Btor *btor)
{
  BtorPtrHashTable *embedded_constraints;
  BtorPtrHashBucket *b;
  double start, delta;
  BtorNode *cur;
  int count;
  assert (btor);
  embedded_constraints = btor->embedded_constraints;
  if (embedded_constraints->count > 0u)
  {
    start = btor_time_stamp ();
    count = 0;
    substitute_embedded_constraints (btor);

    while (embedded_constraints->count > 0u)
    {
      count++;
      b   = embedded_constraints->first;
      cur = (BtorNode *) b->key;
      btor_remove_from_ptr_hash_table (embedded_constraints, cur, 0, 0);
      insert_unsynthesized_constraint (btor, cur);
      btor_release_exp (btor, cur);
    }
    delta = btor_time_stamp () - start;
    btor->time.embedded += delta;
    if (btor->verbosity)
      btor_msg_exp (btor,
                    "replaced %d embedded constraints in %1.f seconds",
                    count,
                    delta);
  }
}

/*------------------------------------------------------------------------*/
#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
/*------------------------------------------------------------------------*/

struct BtorSlice
{
  int upper;
  int lower;
};

typedef struct BtorSlice BtorSlice;

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
eliminate_slices_on_bv_vars (Btor *btor)
{
  BtorNode *var, *cur, *result, *lambda_var, *temp;
  BtorSlice *s1, *s2, *new_s1, *new_s2, *new_s3, **sorted_slices;
  BtorPtrHashBucket *b_var, *b1, *b2;
  BtorFullParentIterator it;
  BtorPtrHashTable *slices;
  int i, min, max, count;
  BtorNodePtrStack vars;
  double start, delta;
  BtorMemMgr *mm;
  int vals[4];

  assert (btor != NULL);

  start = btor_time_stamp ();
  count = 0;

  mm = btor->mm;
  BTOR_INIT_STACK (vars);
  for (b_var = btor->bv_vars->first; b_var != NULL; b_var = b_var->next)
  {
    var = (BtorNode *) b_var->key;
    BTOR_PUSH_STACK (mm, vars, var);
  }

  while (!BTOR_EMPTY_STACK (vars))
  {
    slices = btor_new_ptr_hash_table (
        mm, (BtorHashPtr) hash_slice, (BtorCmpPtr) compare_slices);
    var = BTOR_POP_STACK (vars);
    assert (BTOR_IS_REGULAR_NODE (var));
    assert (BTOR_IS_BV_VAR_NODE (var));
    init_full_parent_iterator (&it, var);
    /* find all slices on variable */
    while (has_next_parent_full_parent_iterator (&it))
    {
      cur = next_parent_full_parent_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (cur));
      if (cur->kind == BTOR_SLICE_NODE)
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

    s1     = sorted_slices[(int) slices->count - 1];
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
      delete_slice (btor, s1);
    }
    BTOR_DELETEN (mm, sorted_slices, slices->count);
    btor_delete_ptr_hash_table (slices);

    count++;
    btor->stats.eliminated_slices++;
    insert_varsubst_constraint (btor, var, result);
    btor_release_exp (btor, result);
  }

  BTOR_RELEASE_STACK (mm, vars);

  delta = btor_time_stamp () - start;
  btor->time.embedded += delta;
  if (btor->verbosity)
    btor_msg_exp (btor, "sliced %d variables in %1.f seconds", count, delta);
}

/*------------------------------------------------------------------------*/
#endif /* BTOR_DO_NOT_ELIMINATE_SLICES */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
/*------------------------------------------------------------------------*/

#include "../lingeling/lglib.h"

static int
btor_fixed_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *real_exp;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  BtorAIG *aig;
  int res, id;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (real_exp->len == 1);
  if (!BTOR_IS_SYNTH_NODE (real_exp)) return 0;
  assert (real_exp->av);
  assert (real_exp->av->len == 1);
  assert (real_exp->av->aigs);
  aig = real_exp->av->aigs[0];
  if (aig == BTOR_AIG_TRUE)
    res = 1;
  else if (aig == BTOR_AIG_FALSE)
    res = -1;
  else
  {
    id = BTOR_GET_CNF_ID_AIG (aig);
    if (!id) return 0;
    amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
    smgr = btor_get_sat_mgr_aig_mgr (amgr);
    res  = btor_fixed_sat (smgr, id);
  }
  if (BTOR_IS_INVERTED_NODE (exp)) res = -res;
  return res;
}

static int
process_skeleton_tseitin_lit (BtorPtrHashTable *ids, BtorNode *exp)
{
  BtorPtrHashBucket *b;
  BtorNode *real_exp;
  int res;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (real_exp->len == 1);
  b = btor_find_in_ptr_hash_table (ids, real_exp);
  if (!b)
  {
    b             = btor_insert_in_ptr_hash_table (ids, real_exp);
    b->data.asInt = (int) ids->count;
  }

  res = b->data.asInt;
  assert (res > 0);

  if (BTOR_IS_INVERTED_NODE (exp)) res = -res;

  return res;
}

static void
process_skeleton_tseitin (Btor *btor,
                          LGL *lgl,
                          BtorNodePtrStack *work_stack,
                          BtorNodePtrStack *unmark_stack,
                          BtorPtrHashTable *ids,
                          BtorNode *root)
{
  int i, lhs, rhs[3], fixed;
  BtorNode *exp;

  BTOR_PUSH_STACK (btor->mm, *work_stack, root);

  do
  {
    exp = BTOR_POP_STACK (*work_stack);
    assert (exp);
    exp = BTOR_REAL_ADDR_NODE (exp);
    if (!exp->mark)
    {
      exp->mark = 1;
      BTOR_PUSH_STACK (btor->mm, *unmark_stack, exp);

      BTOR_PUSH_STACK (btor->mm, *work_stack, exp);
      for (i = exp->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (btor->mm, *work_stack, exp->e[i]);
    }
    else if (exp->mark == 1)
    {
      exp->mark = 2;
      if (exp->len != 1) continue;

#ifndef NDEBUG
      for (i = 0; i < exp->arity; i++)
      {
        BtorNode *child = exp->e[i];
        child           = BTOR_REAL_ADDR_NODE (child);
        assert (child->mark == 2);
        if (child->len == 1) assert (btor_find_in_ptr_hash_table (ids, child));
      }
#endif
      lhs   = process_skeleton_tseitin_lit (ids, exp);
      fixed = btor_fixed_exp (btor, exp);
      if (fixed)
      {
        lgladd (lgl, (fixed > 0) ? lhs : -lhs);
        lgladd (lgl, 0);
      }

      switch (exp->kind)
      {
        case BTOR_AND_NODE:
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);
          break;

        case BTOR_BEQ_NODE:
          if (BTOR_REAL_ADDR_NODE (exp->e[0])->len != 1) break;
          assert (BTOR_REAL_ADDR_NODE (exp->e[1])->len == 1);
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);

          lgladd (lgl, -lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          break;

        case BTOR_BCOND_NODE:
          assert (BTOR_REAL_ADDR_NODE (exp->e[0])->len == 1);
          if (BTOR_REAL_ADDR_NODE (exp->e[1])->len != 1) break;
          assert (BTOR_REAL_ADDR_NODE (exp->e[2])->len == 1);
          rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);
          rhs[2] = process_skeleton_tseitin_lit (ids, exp->e[2]);

          lgladd (lgl, -lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, -lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, rhs[2]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, -rhs[0]);
          lgladd (lgl, -rhs[1]);
          lgladd (lgl, 0);

          lgladd (lgl, lhs);
          lgladd (lgl, rhs[0]);
          lgladd (lgl, -rhs[2]);
          lgladd (lgl, 0);
          break;

        default: assert (exp->kind != BTOR_PROXY_NODE); break;
      }
    }
  } while (!BTOR_EMPTY_STACK (*work_stack));
}

static void
process_skeleton (Btor *btor)
{
  BtorPtrHashTable *ids, *table;
  BtorNodePtrStack unmark_stack;
  int constraints, count, fixed;
  BtorNodePtrStack work_stack;
  BtorMemMgr *mm = btor->mm;
  BtorPtrHashBucket *b;
  double start, delta;
  int res, lit, val;
  BtorNode *exp;
  LGL *lgl;

  start = btor_time_stamp ();

  ids = btor_new_ptr_hash_table (mm,
                                 (BtorHashPtr) btor_hash_exp_by_id,
                                 (BtorCmpPtr) btor_compare_exp_by_id);

  lgl = lglinit ();
  lglsetprefix (lgl, "[lglskel] ");
  if (btor->verbosity)
  {
    lglsetopt (lgl, "verbose", 1);
    lglbnr ("Lingeling", "[lglskel] ", stdout);
    fflush (stdout);
  }

  count = 0;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  for (constraints = 0; constraints <= 1; constraints++)
  {
    table = constraints ? btor->synthesized_constraints
                        : btor->unsynthesized_constraints;
    for (b = table->first; b; b = b->next)
    {
      count++;
      exp = b->key;
      assert (BTOR_REAL_ADDR_NODE (exp)->len == 1);
      process_skeleton_tseitin (
          btor, lgl, &work_stack, &unmark_stack, ids, exp);
      lgladd (lgl, process_skeleton_tseitin_lit (ids, exp));
      lgladd (lgl, 0);
    }
  }

  BTOR_RELEASE_STACK (mm, work_stack);

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    exp = BTOR_POP_STACK (unmark_stack);
    assert (!BTOR_IS_INVERTED_NODE (exp));
    assert (exp->mark);
    exp->mark = 0;
  }

  BTOR_RELEASE_STACK (mm, unmark_stack);

  if (btor->verbosity)
    btor_msg_exp (btor,
                  "found %u skeleton literals in %d constraints",
                  ids->count,
                  count);

#if 0
  lglsetopt (lgl, "clim", 10000);
  res = lglsat (lgl);
#else
  res = lglsimp (lgl, 0);
#endif

  if (btor->verbosity)
  {
    btor_msg_exp (btor, "skeleton preprocessing result %d", res);
    lglstats (lgl);
  }

  fixed = 0;

  if (res == 20)
  {
    if (btor->verbosity) btor_msg_exp (btor, "skeleton inconsistent");
    btor->inconsistent = 1;
  }
  else
  {
    assert (res == 0 || res == 10);
    for (b = ids->first; b; b = b->next)
    {
      exp = b->key;
      assert (!BTOR_IS_INVERTED_NODE (exp));
      lit = process_skeleton_tseitin_lit (ids, exp);
      val = lglfixed (lgl, lit);
      if (val)
      {
        if (!btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp)
            && !btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                             exp))
        {
          if (val < 0) exp = BTOR_INVERT_NODE (exp);
          add_constraint (btor, exp);
          btor->stats.skeleton_constraints++;
          fixed++;
        }
      }
      else
      {
        assert (
            !btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp));
        assert (!btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                              exp));
      }
    }
  }

  btor_delete_ptr_hash_table (ids);
  lglrelease (lgl);

  delta = btor_time_stamp () - start;
  btor->time.skel += delta;
  if (btor->verbosity)
    btor_msg_exp (
        btor,
        "skeleton preprocessing produced %d new constraints in %.1f seconds",
        fixed,
        delta);
}

/*------------------------------------------------------------------------*/
#endif /* BTOR_DO_NOT_PROCESS_SKELETON */
/*------------------------------------------------------------------------*/

static BtorNode *
rewrite_write_to_lambda_exp (Btor *btor, BtorNode *write)
{
  assert (btor);
  assert (BTOR_IS_REGULAR_NODE (write));
  assert (BTOR_IS_WRITE_NODE (write));

  int i, chain_depth = 0, has_write_parent;
  BtorNode *bvcond, *e_cond, *e_then, *e_else;
  BtorNode *lambda, *param, *e[3];
  BtorPartialParentIterator it;

  BTORLOG ("rewrite write: %s", node2string (write));

  for (i = 0; i < 3; i++) e[i] = btor_simplify_exp (btor, write->e[i]);

  /* write (e0, e1, e2) -> lambda p. p == e1 ? e2 : read (e0, p) */
  param  = btor_param_exp (btor, BTOR_REAL_ADDR_NODE (e[1])->len, "");
  e_then = btor_copy_exp (btor, e[2]);

  assert (BTOR_IS_REGULAR_NODE (e[0]));
  assert (!BTOR_IS_WRITE_NODE (e[0]));
  assert (BTOR_IS_REGULAR_NODE (write->e[0]));

  init_write_parent_iterator (&it, write);
  has_write_parent = has_next_parent_write_parent_iterator (&it);

  if ((has_write_parent && write->refs == 1)
      || (!has_write_parent && BTOR_IS_LAMBDA_NODE (e[0])
          && ((BtorLambdaNode *) e[0])->chain_depth > 0))
  {
    assert (!has_write_parent || has_num_parents_dbg (write, 1));
    if (BTOR_IS_LAMBDA_NODE (e[0]))
      chain_depth = ((BtorLambdaNode *) e[0])->chain_depth;
    chain_depth += 1;
  }

  assert (chain_depth >= 0);
  assert (chain_depth <= INT_MAX);

  /* end of lambda chain */
  if ((!has_write_parent || write->refs > 1) && chain_depth > 0)
  {
    assert (BTOR_IS_LAMBDA_NODE (e[0]));
    assert (!has_write_parent || !has_num_parents_dbg (write, 1));
    BTORLOG ("merge lambda: %s (merged %d)", node2string (e[0]), chain_depth);
    btor_assign_param (btor, e[0], param);
    e_else = btor_beta_reduce_chains (btor, e[0]);
    btor_unassign_param (btor, e[0]);

    if (write->e[0]->simplified) write->e[0]->simplified = 0;
    btor_release_exp (btor, e[0]);

    btor->stats.lambda_chains_merged++;
    btor->stats.lambdas_merged += chain_depth;
  }
  else
    e_else = btor_read_exp (btor, e[0], param);

  e_cond = btor_eq_exp (btor, param, e[1]);
  bvcond = btor_cond_exp (btor, e_cond, e_then, e_else);
  lambda = btor_lambda_exp (btor, param, bvcond);

  ((BtorLambdaNode *) lambda)->chain_depth = chain_depth;

  btor_release_exp (btor, e_then);
  btor_release_exp (btor, e_else);
  btor_release_exp (btor, e_cond);
  btor_release_exp (btor, bvcond);
  btor_release_exp (btor, param);

  BTORLOG ("rewrite write result: %s", node2string (lambda));

  return lambda;
}

static void
rewrite_writes_to_lambda_exp (Btor *btor)
{
  assert (btor);

  int i;
  BtorPtrHashTable *writes, *roots = NULL;
  BtorPtrHashBucket *b;
  BtorNode *exp;
  BtorNodePtrStack work_stack, unmark_stack;
  BtorMemMgr *mm;

  if (btor->ops[BTOR_WRITE_NODE] == 0) return;

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  mm     = btor->mm;
  writes = btor_new_ptr_hash_table (mm,
                                    (BtorHashPtr) btor_hash_exp_by_id,
                                    (BtorCmpPtr) btor_compare_exp_by_id);

  for (;;)
  {
    if (roots == NULL)
      roots = btor->unsynthesized_constraints;
    else if (roots == btor->unsynthesized_constraints)
      roots = btor->synthesized_constraints;
    else
      break;

    for (b = roots->first; b; b = b->next)
    {
      exp = b->key;
      BTOR_PUSH_STACK (mm, work_stack, exp);

      /* collect writes */
      while (!BTOR_EMPTY_STACK (work_stack))
      {
        exp = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));
        assert (exp);

        if (exp->mark) continue;

        assert (exp->mark == 0);
        exp->mark = 1;
        BTOR_PUSH_STACK (mm, unmark_stack, exp);
        for (i = exp->arity - 1; i >= 0; i--)
          BTOR_PUSH_STACK (mm, work_stack, exp->e[i]);

        if (BTOR_IS_WRITE_NODE (exp))
        {
          assert (!btor_find_in_ptr_hash_table (writes, exp));
          btor_insert_in_ptr_hash_table (writes, exp);
        }
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    exp = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_NODE (exp));
    assert (exp->mark);
    exp->mark = 0;
  }

  substitute_and_rebuild (btor, writes, 1, 0);

  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);

  btor_delete_ptr_hash_table (writes);
}

static void
init_cache (Btor *btor)
{
  assert (btor);
  assert (!btor->cache);

  btor->cache = btor_new_ptr_hash_table (
      btor->mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
}

#if 0
static void
cache_beta_result (Btor * btor, BtorNode * lambda, BtorNode * exp, 
		   BtorNode * result)
{
  assert (btor);
  assert (lambda);
  assert (exp);
  assert (result);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair = new_exp_pair (btor, lambda, exp);

  bucket = btor_find_in_ptr_hash_table (btor->cache, pair);
  if (bucket)
    {
      delete_exp_pair (btor, pair);
      assert ((BtorNode *) bucket->data.asPtr == result);
    }
  else
    btor_insert_in_ptr_hash_table (btor->cache, pair)->data.asPtr =
      btor_copy_exp (btor, result);
}

static BtorNode *
cached_beta_result (Btor * btor, BtorNode * lambda, BtorNode * exp)
{
  assert (btor);
  assert (lambda);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (lambda));
  assert (BTOR_IS_LAMBDA_NODE (lambda));

  BtorNodePair *pair;
  BtorPtrHashBucket *bucket;

  pair = new_exp_pair (btor, lambda, exp);
  bucket = btor_find_in_ptr_hash_table (btor->cache, pair);
  delete_exp_pair (btor, pair);

  if (bucket)
    return (BtorNode *) bucket->data.asPtr;

  return 0;
}
#endif

static void
release_cache (Btor *btor)
{
  assert (btor);
  assert (btor->cache);

  BtorPtrHashBucket *bucket;
  BtorNodePair *pair;

  for (bucket = btor->cache->first; bucket; bucket = bucket->next)
  {
    pair = (BtorNodePair *) bucket->key;
    btor_release_exp (btor, (BtorNode *) bucket->data.asPtr);
    delete_exp_pair (btor, pair);
  }
  btor_delete_ptr_hash_table (btor->cache);
  btor->cache = 0;
}

static void
beta_reduce_reads_on_lambdas (Btor *btor)
{
  assert (btor);

  BtorPtrHashTable *reads;
  BtorPtrHashBucket *b;
  BtorNode *read, *lambda;
  BtorPartialParentIterator it;
  BtorMemMgr *mm;

  if (btor->lambdas->count == 0) return;

  mm    = btor->mm;
  reads = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);

  /* collect reads */
  for (b = btor->lambdas->first; b; b = b->next)
  {
    lambda = BTOR_REAL_ADDR_NODE ((BtorNode *) b->key);
    init_read_parent_iterator (&it, lambda);
    while (has_next_parent_read_parent_iterator (&it))
    {
      read = next_parent_read_parent_iterator (&it);

      if (btor_find_in_ptr_hash_table (reads, read)) continue;

      if (!read->parameterized || BTOR_REAL_ADDR_NODE (read->e[0])->refs == 1)
      {
        assert (!read->parameterized || has_num_parents_dbg (read->e[0], 1));
        btor_insert_in_ptr_hash_table (reads, read);
      }
    }
  }

  substitute_and_rebuild (btor, reads, 0, 1);
  btor_delete_ptr_hash_table (reads);
}

static void
rewrite_reads_on_aconds (Btor *btor)
{
  assert (btor);

  int i, j, visited;
  BtorPtrHashTable *param_reads, *roots = 0;
  BtorPtrHashBucket *b;
  BtorNodePtrStack aconds, root_exps, work_stack, unmark_stack;
  BtorNode *exp, *read, *read_simp, *acond, *e[3], *read_then, *read_else;
  BtorPartialParentIterator it;
  BtorMemMgr *mm;

  if (btor->ops[BTOR_ACOND_NODE] == 0) return;

  mm = btor->mm;
  BTOR_INIT_STACK (aconds);
  BTOR_INIT_STACK (root_exps);
  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (unmark_stack);

  param_reads = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);

  btor_init_substitutions (btor);

  /* collect aconds */
  for (;;)
  {
    if (!roots)
      roots = btor->unsynthesized_constraints;
    else if (roots == btor->unsynthesized_constraints)
      roots = btor->synthesized_constraints;
    else
      break;

    for (b = roots->first; b; b = b->next)
    {
      exp = (BtorNode *) b->key;
      BTOR_PUSH_STACK (mm, root_exps, btor_copy_exp (btor, exp));
      BTOR_PUSH_STACK (mm, work_stack, exp);

      while (!BTOR_EMPTY_STACK (work_stack))
      {
        exp = BTOR_REAL_ADDR_NODE (BTOR_POP_STACK (work_stack));
        assert (exp);

        if (exp->mark) continue;

        /* ensure that all parent aconds of an acond are visited before
         * collecting the acond itself */
        if (BTOR_IS_ARRAY_COND_NODE (exp))
        {
          visited = 1;
          init_acond_parent_iterator (&it, exp);
          while (has_next_parent_acond_parent_iterator (&it))
          {
            acond = next_parent_acond_parent_iterator (&it);
            if (!acond->mark)
            {
              visited = 0;
              break;
            }
          }
          if (!visited) continue;

          //		  printf ("push: %s\n", node2string (exp));
          BTOR_PUSH_STACK (mm, aconds, exp);
        }

        exp->mark = 1;
        BTOR_PUSH_STACK (mm, unmark_stack, exp);

        for (i = 0; i < exp->arity; i++)
          BTOR_PUSH_STACK (mm, work_stack, exp->e[i]);
      }
    }
  }

  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    exp = BTOR_POP_STACK (unmark_stack);
    assert (exp);
    assert (exp->mark);
    exp->mark = 0;
  }

  /* rewrite aconds */
  for (i = 0; i < BTOR_COUNT_STACK (aconds); i++)
  {
    acond = aconds.start[i];
    assert (BTOR_IS_REGULAR_NODE (acond));
    assert (BTOR_IS_ARRAY_COND_NODE (acond));

    for (j = 0; j < acond->arity; j++) e[j] = acond->e[j];

    //      if (acond->refs > 2)
    //	continue;

    init_read_parent_iterator (&it, acond);
    while (has_next_parent_read_parent_iterator (&it))
    {
      /* we do not want the simplification from constraints here */
      read = btor_pointer_chase_simplified_exp (
          btor, next_parent_read_parent_iterator (&it));

      if (!BTOR_IS_READ_NODE (BTOR_REAL_ADDR_NODE (read))) continue;

      assert (read->e[0] == acond);

      read_then = btor_read_exp (btor, e[1], read->e[1]);
      read_else = btor_read_exp (btor, e[2], read->e[1]);
      read_simp = btor_cond_exp (btor, e[0], read_then, read_else);

      assert (!read->simplified);
      btor_insert_substitution (btor, read, read_simp);

      if (BTOR_REAL_ADDR_NODE (read_then)->parameterized
          && BTOR_IS_LAMBDA_NODE (e[1]))
      {
        assert (!btor_find_in_ptr_hash_table (param_reads, read_then));
        btor_insert_in_ptr_hash_table (param_reads, read_then);
      }

      if (BTOR_REAL_ADDR_NODE (read_else)->parameterized
          && BTOR_IS_LAMBDA_NODE (e[2]))
      {
        assert (!btor_find_in_ptr_hash_table (param_reads, read_else));
        btor_insert_in_ptr_hash_table (param_reads, read_else);
      }

      btor_release_exp (btor, read_then);
      btor_release_exp (btor, read_else);
      btor_release_exp (btor, read_simp);
    }
  }

  /* merge lambdas */
  substitute_and_rebuild (btor, param_reads, 0, 1);

  substitute_and_rebuild (btor, btor->substitutions, 0, 0);

#ifndef NDEBUG
  for (b = btor->substitutions->first; b; b = b->next)
    assert (BTOR_IS_PROXY_NODE ((BtorNode *) b->key));
#endif

  btor_delete_substitutions (btor);
  btor_delete_ptr_hash_table (param_reads);

  while (!BTOR_EMPTY_STACK (root_exps))
  {
    exp = BTOR_POP_STACK (root_exps);
    assert (exp);
    btor_release_exp (btor, exp);
  }

  BTOR_RELEASE_STACK (mm, aconds);
  BTOR_RELEASE_STACK (mm, root_exps);
  BTOR_RELEASE_STACK (mm, work_stack);
  BTOR_RELEASE_STACK (mm, unmark_stack);
}

static void
run_rewrite_engine (Btor *btor)
{
  int rounds;
  double start, delta;
#ifndef BTOR_DO_NOT_PROCESS_SKELETON
  int skelrounds = 0;
#endif

  assert (btor);
  if (btor->inconsistent) return;

  if (btor->rewrite_level <= 1 && !btor->rewrite_writes) return;

  rounds = 0;
  start  = btor_time_stamp ();

  init_cache (btor);

  do
  {
    rounds++;
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));
    assert (check_unique_table_children_proxy_free_dbg (btor));
    if (btor->rewrite_level > 1)
    {
      substitute_var_exps (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) break;

      process_embedded_constraints (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));

      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;
    }

#ifndef BTOR_DO_NOT_ELIMINATE_SLICES
    if (btor->rewrite_level > 2 && !btor->inc_enabled)
    {
      eliminate_slices_on_bv_vars (btor);
      if (btor->inconsistent) break;

      if (btor->varsubst_constraints->count) continue;

      if (btor->embedded_constraints->count) continue;
    }
#endif

#ifndef BTOR_DO_NOT_PROCESS_SKELETON
    if (btor->rewrite_level > 2)
    {
      skelrounds++;
      if (skelrounds <= 1)  // TODO only one?
      {
        process_skeleton (btor);
        assert (check_all_hash_tables_proxy_free_dbg (btor));
        assert (check_all_hash_tables_simp_free_dbg (btor));
        assert (check_unique_table_children_proxy_free_dbg (btor));
        if (btor->inconsistent) break;
      }

      if (btor->varsubst_constraints->count) continue;

      if (btor->embedded_constraints->count) continue;
    }
#endif

    /* rewrite writes to lambdas (skip in case of extensionality) */
    if ((btor->rewrite_writes && btor->ops[BTOR_AEQ_NODE] == 0))
    {
      rewrite_writes_to_lambda_exp (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));
      assert (btor->ops[BTOR_WRITE_NODE] == 0);

      //	  TODO: function for finding lambda chains, after aconds
      // rewrite, merge lambda chains ?
      rewrite_reads_on_aconds (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));
      // TODO: for debug purpose only
      assert (btor->ops[BTOR_ACOND_NODE] == 0);
    }

    if (btor->varsubst_constraints->count) continue;

    if (btor->embedded_constraints->count) continue;

    /* rewrite/beta-reduce reads on lambdas */
    if (btor->rewrite_reads)
    {
      beta_reduce_reads_on_lambdas (btor);
      assert (check_all_hash_tables_proxy_free_dbg (btor));
      assert (check_all_hash_tables_simp_free_dbg (btor));
      assert (check_unique_table_children_proxy_free_dbg (btor));
      //	  assert (btor->ops[BTOR_ACOND_NODE] > 0 || btor->lambdas->count
      //== 0);
    }
  } while (btor->varsubst_constraints->count
           || btor->embedded_constraints->count);

  release_cache (btor);

  delta = btor_time_stamp () - start;
  btor->time.rewrite += delta;
  if (btor->verbosity)
    btor_msg_exp (btor, "%d rewriting rounds in %.1f seconds", rounds, delta);
}

static void
synthesize_all_var_rhs (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorNode *cur, *real_cur;

  assert (btor);
  assert (btor->model_gen);

  for (b = btor->var_rhs->first; b; b = b->next)
  {
    cur      = (BtorNode *) b->key;
    cur      = btor_simplify_exp (btor, cur);
    real_cur = BTOR_REAL_ADDR_NODE (cur);
    assert (!BTOR_IS_ARRAY_NODE (real_cur));
    if (real_cur->vread) continue;

    synthesize_exp (btor, cur, 0);

    if (!real_cur->tseitin)
    {
      btor_aigvec_to_sat_tseitin (btor->avmgr, real_cur->av);
      real_cur->tseitin = 1;
    }
  }
}

static void
synthesize_all_array_rhs (Btor *btor)
{
  BtorPtrHashBucket *b;
  BtorNode *cur;

  assert (btor);
  assert (btor->model_gen);

  for (b = btor->array_rhs->first; b; b = b->next)
  {
    cur = (BtorNode *) b->key;
    cur = btor_simplify_exp (btor, cur);
    assert (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (cur)));
    synthesize_exp (btor, cur, 0);
  }
}

static void
synthesize_all_reads (Btor *btor)
{
  BtorNode *n;
  int i;
  for (i = 0; i < btor->nodes_unique_table.size; i++)
    for (n = btor->nodes_unique_table.chains[i]; n; n = n->next)
      if (BTOR_IS_READ_NODE (n)) synthesize_exp (btor, n, 0);
}

static int
btor_sat_aux_btor (Btor *btor)
{
  int sat_result, found_conflict, found_constraint_false, verbosity;
  int found_assumption_false, refinements;
  BtorNodePtrStack top_arrays;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorMemMgr *mm;

  assert (btor);
  verbosity = btor->verbosity;

  if (btor->inconsistent) return BTOR_UNSAT;

  if (verbosity > 0) btor_msg_exp (btor, "calling SAT");

  run_rewrite_engine (btor);

  if (btor->inconsistent) return BTOR_UNSAT;

  mm = btor->mm;

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  if (!btor_is_initialized_sat (smgr)) btor_init_sat (smgr);

  if (btor->valid_assignments == 1) btor_reset_incremental_usage (btor);

  do
  {
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));
    found_constraint_false = process_unsynthesized_constraints (btor);
    assert (check_all_hash_tables_proxy_free_dbg (btor));
    assert (check_all_hash_tables_simp_free_dbg (btor));

    if (found_constraint_false)
    {
    UNSAT:
      sat_result = BTOR_UNSAT;
      goto DONE;
    }

    if (btor->model_gen)
    {
      synthesize_all_var_rhs (btor);
      synthesize_all_array_rhs (btor);
      if (btor->generate_model_for_all_reads) synthesize_all_reads (btor);
    }

  } while (btor->unsynthesized_constraints->count > 0);

  update_assumptions (btor);

  found_assumption_false = add_again_assumptions (btor);
  if (found_assumption_false) goto UNSAT;

  BTOR_INIT_STACK (top_arrays);
  sat_result = btor_timed_sat_sat (btor, -1);

  while (sat_result == BTOR_SAT)
  {
    assert (BTOR_EMPTY_STACK (top_arrays));
    search_top_arrays (btor, &top_arrays);

    found_conflict = check_and_resolve_conflicts (btor, &top_arrays);

    if (found_conflict)
    {
      btor->stats.lod_refinements++;
      found_assumption_false = add_again_assumptions (btor);
      assert (!found_assumption_false);
    }

    BTOR_RELEASE_STACK (mm, top_arrays);

    if (!found_conflict) break;

    if (verbosity > 1)
    {
      refinements = btor->stats.lod_refinements;
      if (verbosity > 2 || !(refinements % 10))
      {
        fprintf (stdout, "[btorsat] refinement iteration %d\n", refinements);
        fflush (stdout);
      }
    }

    found_assumption_false = add_again_assumptions (btor);
    if (found_assumption_false)
      sat_result = BTOR_UNSAT;
    else
      sat_result = btor_timed_sat_sat (btor, -1);
  }

DONE:

  btor->valid_assignments = 1;
  BTOR_ABORT_NODE (sat_result != BTOR_SAT && sat_result != BTOR_UNSAT,
                   "result must be sat or unsat");
  return sat_result;
}

int
btor_sat_btor (Btor *btor)
{
  int res;
  assert (btor);
  assert (btor->btor_sat_btor_called >= 0);
  assert (btor->inc_enabled || btor->btor_sat_btor_called == 0);
  res = btor_sat_aux_btor (btor);
  btor->btor_sat_btor_called++;
  return res;
}

char *
btor_bv_assignment_exp (Btor *btor, BtorNode *exp)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *av;
  BtorNode *real_exp;
  char *assignment;
  int invert_av, invert_bits;

  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)));

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  assert (real_exp);

  if (BTOR_IS_BV_CONST_NODE (real_exp))
  {
    invert_bits = BTOR_IS_INVERTED_NODE (exp);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_NODE (exp)->bits);
    assignment = btor_copy_const (btor->mm, BTOR_REAL_ADDR_NODE (exp)->bits);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_NODE (exp)->bits);
  }
  else if ((!real_exp->reachable || !BTOR_IS_SYNTH_NODE (real_exp))
           && !real_exp->vread)
  {
    assignment = btor_x_const_3vl (btor->mm, real_exp->len);
  }
  else
  {
    avmgr     = btor->avmgr;
    invert_av = BTOR_IS_INVERTED_NODE (exp);
    av        = BTOR_REAL_ADDR_NODE (exp)->av;
    if (invert_av) btor_invert_aigvec (avmgr, av);
    assignment = btor_assignment_aigvec (avmgr, av);
    /* invert back if necessary */
    if (invert_av) btor_invert_aigvec (avmgr, av);
  }

  return assignment;
}

void
btor_array_assignment_exp (
    Btor *btor, BtorNode *exp, char ***indices, char ***values, int *size)
{
  BtorPtrHashBucket *b;
  BtorNode *index, *value;
  int i;

  assert (btor);
  assert (exp);
  assert (!BTOR_IS_INVERTED_NODE (exp));
  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_ARRAY_NODE (exp));
  assert (indices);
  assert (values);
  assert (size);

  i = 0;

  if (!exp->rho)
  {
    *size = 0;
    return;
  }

  *size = (int) exp->rho->count;
  if (*size > 0)
  {
    BTOR_NEWN (btor->mm, *indices, *size);
    BTOR_NEWN (btor->mm, *values, *size);

    for (b = exp->rho->first; b; b = b->next)
    {
      index         = (BtorNode *) b->key;
      value         = BTOR_GET_VALUE_ACC_NODE ((BtorNode *) b->data.asPtr);
      (*indices)[i] = btor_bv_assignment_exp (btor, index);
      (*values)[i]  = btor_bv_assignment_exp (btor, value);
      i++;
    }
  }
}

void
btor_free_bv_assignment_exp (Btor *btor, char *assignment)
{
  assert (btor);
  assert (assignment);
  btor_freestr (btor->mm, assignment);
}

const char *
btor_version (Btor *btor)
{
  assert (btor);
  (void) btor;
  return BTOR_VERSION;
}
