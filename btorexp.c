#include "btorexp.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorhash.h"
#include "btorsat.h"
#include "btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Pointer chasing is a must for most incremental applications.  We keep
 * this switch to turn off pointer chasing around, for debugging purposes.
 *
#define NPROXY
 */

/*------------------------------------------------------------------------*/

#define BTOR_AVERAGE_EXP(a, b) ((b) ? ((double) (a)) / ((double) (b)) : 0.0)

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

#define BTOR_ABORT_EXP(cond, msg)            \
  do                                         \
  {                                          \
    if (cond)                                \
    {                                        \
      fputs ("[btorexp] " msg "\n", stdout); \
      exit (BTOR_ERR_EXIT);                  \
    }                                        \
  } while (0)

struct BtorExpUniqueTable
{
  int size;
  int num_elements;
  struct BtorExp **chains;
};

typedef struct BtorExpUniqueTable BtorExpUniqueTable;

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

struct ConstraintStats
{
  int added;
  int processed;
  int synthesized;
};

struct Btor
{
  BtorMemMgr *mm;
  BtorExpUniqueTable table;
  BtorAIGVecMgr *avmgr;
  BtorPtrHashTable *arrays;
  int id; /* global expression id counter */
  int valid_assignments;
  int rewrite_level;
  int verbosity;
  int has_array_equalities;
  int replay;
  int vread_index_id;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table; /* hash table for CNF ids */
  BtorPtrHashTable *exp_pair_cnf_eq_id_table;   /* hash table for CNF ids */
  BtorPtrHashTable *new_constraints;
  BtorPtrHashTable *processed_constraints;
  BtorPtrHashTable *synthesized_constraints;
  BtorPtrHashTable *assumptions;
  BtorExpPtrStack replay_constraints;
  /* statistics */
  struct
  {
    /* number of iterative refinements */
    int refinements;
    /* number of restarts as a result of lazy synthesis */
    int synthesis_assignment_inconsistencies;
    /* number of read-read conflicts */
    int read_read_conflicts;
    /* number of read-write conflicts */
    int read_write_conflicts;
    /* number of variables that have been substituted */
    int var_substitutions;
    /* number of array variables that have been substituted */
    int array_substitutions;
    /* number of virtual reads */
    int vreads;
    /* number of linear equations */
    int linear_equations;
    /* sum of the size of all added lemmas */
    long long int lemmas_size_sum;
    /* sum of the size of all linking clauses */
    long long int lclause_size_sum;
    /* constraint statistics */
    struct ConstraintStats constraints;
    struct
    {
      struct ConstraintStats constraints;
    } old;
    long long expressions;
  } stats;
};

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

#define BTOR_READ_OVER_WRITE_DOWN_PROPAGATION_LIMIT 128

static BtorExp *rewrite_binary_exp (Btor *, BtorExpKind, BtorExp *, BtorExp *);
static void add_constraint (Btor *, BtorExp *);
static void process_new_constraints (Btor *);
static BtorExp *slice_exp_aux (Btor *, BtorExp *, int, int, int);
static BtorExp *mul_exp (Btor *, BtorExp *, BtorExp *);
static BtorExp *rewrite_slice_exp (Btor *, BtorExp *, int, int, int);

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

static void
print_verbose_msg (char *fmt, ...)
{
  va_list ap;
  fputs ("[btorexp] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static char *
zero_string (Btor *btor, int len)
{
  int i;
  char *string;
  assert (btor != NULL);
  assert (len > 0);
  BTOR_NEWN (btor->mm, string, len + 1);
  for (i = 0; i < len; i++) string[i] = '0';
  string[len] = '\0';
  return string;
}

static char *
ones_string (Btor *btor, int len)
{
  int i;
  char *string;
  assert (btor != NULL);
  assert (len > 0);
  BTOR_NEWN (btor->mm, string, len + 1);
  for (i = 0; i < len; i++) string[i] = '1';
  string[len] = '\0';
  return string;
}

static int
is_zero_string (Btor *btor, const char *string, int len)
{
  int i;
  assert (btor != NULL);
  assert (string != NULL);
  assert (len > 0);
  (void) btor;
  for (i = 0; i < len; i++)
    if (string[i] != '0') return 0;
  return 1;
}

static int
is_one_string (Btor *btor, const char *string, int len)
{
  int i;
  assert (btor != NULL);
  assert (string != NULL);
  assert (len > 0);
  (void) btor;
  if (string[len - 1] != '1') return 0;
  for (i = 0; i < len - 1; i++)
    if (string[i] != '0') return 0;
  return 1;
}

static int
is_ones_string (Btor *btor, const char *string, int len)
{
  int i;
  assert (btor != NULL);
  assert (string != NULL);
  assert (len > 0);
  (void) btor;
  if (string[len - 1] != '1') return 0;
  for (i = 0; i < len - 1; i++)
    if (string[i] != '1') return 0;
  return 1;
}

static void
inc_exp_ref_counter (Btor *btor, BtorExp *exp)
{
  BtorExp *real_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  (void) btor;
  real_exp = BTOR_REAL_ADDR_EXP (exp);
  BTOR_ABORT_EXP (real_exp->refs == UINT_MAX, "Reference counter overflow");
  real_exp->refs++;
}

static BtorExp *
copy_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  inc_exp_ref_counter (btor, exp);
  return exp;
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
    result->exp1 = copy_exp (btor, exp2);
    result->exp2 = copy_exp (btor, exp1);
  }
  else
  {
    result->exp1 = copy_exp (btor, exp1);
    result->exp2 = copy_exp (btor, exp2);
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
  assert (!BTOR_IS_CONST_EXP (parent));
  assert (!BTOR_IS_VAR_EXP (parent));
  assert (!BTOR_IS_ATOMIC_ARRAY_EXP (parent));
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
    /* hang out parent from list */
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
  assert (!BTOR_IS_VAR_EXP (exp));
  assert (!BTOR_IS_ATOMIC_ARRAY_EXP (exp));
  if (BTOR_IS_CONST_EXP (exp))
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
  BtorMemMgr *mm;
  int i;

  assert (btor);
  assert (exp);

  assert (BTOR_IS_REGULAR_EXP (exp));

  assert (exp->kind != BTOR_INVALID_EXP);

  assert (!exp->unique);
  assert (exp->erased);
  assert (!exp->disconnected);

  mm = btor->mm;

  if (BTOR_IS_PROXY_EXP (exp))
  {
    /* do nothing */
  }
  else if (BTOR_IS_VAR_EXP (exp))
  {
    /* do nothing */
  }
  else if (BTOR_IS_ATOMIC_ARRAY_EXP (exp))
  {
    btor_remove_from_ptr_hash_table (btor->arrays, exp, 0, 0);
  }
  else
  {
    for (i = 0; i < exp->arity; i++) disconnect_child_exp (btor, exp, i);
  }
  exp->disconnected = 1;
}

/* Delete local data of expression.
 *
 * Virtual reads and simplified expressions have to be handled by the
 * calling function, e.g. 'release_exp', to avoid recursion.
 */
static void
erase_local_data_exp (Btor *btor, BtorExp *exp)
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

  if (BTOR_IS_VAR_EXP (exp))
  {
    btor_freestr (mm, exp->symbol);
    exp->symbol = 0;
  }

  if (BTOR_IS_CONST_EXP (exp))
  {
    btor_freestr (mm, exp->bits);
    exp->bits = 0;
  }

  if (exp->av)
  {
    btor_release_delete_aigvec (btor->avmgr, exp->av);
    exp->av = 0;
  }
  exp->erased = 1;
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
  assert (root->refs == 1u);

  mm = btor->mm;

  BTOR_INIT_STACK (stack);
  cur = root;
  goto ENTER_WITHOUT_PUSH_AND_POP;

  do
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (cur->refs > 1u)
      cur->refs--;
    else
    {
    ENTER_WITHOUT_PUSH_AND_POP:
      assert (cur->refs == 1u);

      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);

      if (cur->simplified)
      {
        BTOR_PUSH_STACK (mm, stack, cur->simplified);
        cur->simplified = NULL;
      }

      if (BTOR_IS_ARRAY_EQ_EXP (cur) && cur->vreads)
      {
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp2);
        BTOR_PUSH_STACK (mm, stack, cur->vreads->exp1);
        BTOR_DELETE (mm, cur->vreads);
        cur->vreads = 0;
      }

      remove_from_unique_table_exp (btor, cur);
      erase_local_data_exp (btor, cur);

      /* It is safe to access the children here, since they are pushed
       * on the stack and will be release later if necessary.
       */
      disconnect_children_exp (btor, cur);
      really_deallocate_exp (btor, cur);
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
}

static void
release_exp (Btor *btor, BtorExp *root)
{
  assert (btor);
  assert (root);

  root = BTOR_REAL_ADDR_EXP (root);

  assert (root->refs > 0u);

  if (root->refs > 1u)
    root->refs--;
  else
    recursively_release_exp (btor, root);
}

static void
delete_exp_pair (Btor *btor, BtorExpPair *pair)
{
  assert (btor != NULL);
  assert (pair != NULL);
  release_exp (btor, pair->exp1);
  release_exp (btor, pair->exp2);
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

/* This function is used to encode a lemma on demand.
 * The stack 'writes' contains intermediate writes.
 * The stack 'aeqs' contains intermediate array equalities (true).
 * The stacks 'aconds' constain intermediate array conditionals.
 */
static void
encode_lemma (Btor *btor,
              BtorExpPtrStack *writes,
              BtorExpPtrStack *aeqs,
              BtorExpPtrStack *aconds_sel1,
              BtorExpPtrStack *aconds_sel2,
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
  BtorExp *w_index, *cur_write, *aeq, *acond, *cond, **temp, **top;
  BtorExpPair *pair;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table, *exp_pair_cnf_eq_id_table;
  BtorPtrHashBucket *bucket;
  BtorIntStack clauses;
  BtorIntStack linking_clause;
  int len_a_b, len_i_j_w, e;
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
      BTOR_COUNT_STACK (*writes) + BTOR_COUNT_STACK (*aeqs)
      + BTOR_COUNT_STACK (*aconds_sel1) + BTOR_COUNT_STACK (*aconds_sel2) + 2;

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
  if (i != j)
  {
    pair = new_exp_pair (btor, i, j);
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
      delete_exp_pair (btor, pair);
      for (k = 0; k < len_i_j_w; k++)
      {
        d_k++;
        BTOR_PUSH_STACK (mm, linking_clause, d_k);
      }
    }
  }

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
  top = writes->top;
  for (temp = writes->start; temp != top; temp++)
  {
    cur_write = *temp;
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_EXP (cur_write));
    w_index = cur_write->e[1];
    av_w    = BTOR_REAL_ADDR_EXP (w_index)->av;
    assert (av_w->len == len_i_j_w);

    /* write index has to be synthesized and translated to SAT before */
    assert (BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (w_index)));
    assert (BTOR_REAL_ADDR_EXP (w_index)->sat_both_phases);

    pair = new_exp_pair (btor, i, w_index);
    /* already encoded i != w_index into SAT ? */
    bucket = btor_find_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair);
    /* no ? */
    if (bucket == NULL)
    {
      e = btor_next_cnf_id_sat_mgr (smgr);
      btor_insert_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair)
          ->data.asInt = e;
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
            if (!BTOR_IS_CONST_AIG (aig2)) BTOR_PUSH_STACK (mm, clauses, -w_k);
            BTOR_PUSH_STACK (mm, clauses, 0);
          }
          if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_TRUE)
          {
            BTOR_PUSH_STACK (mm, clauses, -e);
            if (!BTOR_IS_CONST_AIG (aig1)) BTOR_PUSH_STACK (mm, clauses, -i_k);
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
      e = bucket->data.asInt;
      delete_exp_pair (btor, pair);
    }
    assert (e != 0);
    BTOR_PUSH_STACK (mm, linking_clause, e);
  }
  /* add array equalites in the premisse to linking clause */
  top = aeqs->top;
  for (temp = aeqs->start; temp != top; temp++)
  {
    aeq = *temp;
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
  top = aconds_sel1->top;
  for (temp = aconds_sel1->start; temp != top; temp++)
  {
    acond = *temp;
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
  top = aconds_sel2->top;
  for (temp = aconds_sel2->start; temp != top; temp++)
  {
    acond = *temp;
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
    btor_add_sat (smgr, k);
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
  assert (BTOR_IS_VAR_EXP (read1->e[1]));
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
  BtorPtrHashTable *new_constraints, *processed_constraints,
      *synthesized_constraints, *pos, *neg;
  BtorExp *simplified, *not_simplified, *not_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (exp->simplified != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp->simplified)->simplified == NULL);
  assert (exp->constraint);
  not_exp                 = BTOR_INVERT_EXP (exp);
  simplified              = exp->simplified;
  not_simplified          = BTOR_INVERT_EXP (simplified);
  new_constraints         = btor->new_constraints;
  processed_constraints   = btor->processed_constraints;
  synthesized_constraints = btor->synthesized_constraints;
  pos = neg = NULL;

  if (btor_find_in_ptr_hash_table (new_constraints, exp))
  {
    add_constraint (btor, simplified);
    pos = new_constraints;
  }
  if (btor_find_in_ptr_hash_table (new_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    neg = new_constraints;
  }

  if (btor_find_in_ptr_hash_table (processed_constraints, exp))
  {
    add_constraint (btor, simplified);
    assert (pos == NULL);
    pos = processed_constraints;
  }
  if (btor_find_in_ptr_hash_table (processed_constraints, not_exp))
  {
    add_constraint (btor, not_simplified);
    assert (neg == NULL);
    neg = processed_constraints;
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
    release_exp (btor, exp);
  }
  if (neg != NULL)
  {
    btor_remove_from_ptr_hash_table (neg, not_exp, NULL, NULL);
    release_exp (btor, not_exp);
  }
  exp->constraint = 0;
}

static void
overwrite_exp (Btor *btor, BtorExp *exp, BtorExp *simplified)
{
#ifndef NPROXY
  BtorExp *e[3];
  int i;
#endif
  assert (btor);
  assert (exp);
  assert (simplified);
  assert (BTOR_IS_REGULAR_EXP (exp));

  if (exp->simplified) release_exp (btor, exp->simplified);

  exp->simplified = copy_exp (btor, simplified);

  /* do we have to update a constraint ? */
  if (exp->constraint) update_constraints (btor, exp);

    /* TODO: PROXY CODE WORKING? */
#ifndef NPROXY
  remove_from_unique_table_exp (btor, exp);
  erase_local_data_exp (btor, exp);
  for (i = 0; i < exp->arity; i++) e[i] = exp->e[i];
  disconnect_children_exp (btor, exp);
  for (i = 0; i < exp->arity; i++) release_exp (btor, e[i]);
  exp->kind         = BTOR_PROXY_EXP;
  exp->disconnected = 0;
  exp->erased       = 0;
  exp->arity        = 0; /* defensive */
#endif
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
  cur            = copy_exp (btor, real_exp);
  do
  {
    if (BTOR_IS_INVERTED_EXP (cur)) invert = !invert;
    cur  = BTOR_REAL_ADDR_EXP (cur);
    next = copy_exp (btor, cur->simplified);
    overwrite_exp (btor, cur, invert ? not_simplified : simplified);
    release_exp (btor, cur);
    cur = next;
  } while (BTOR_REAL_ADDR_EXP (cur)->simplified != NULL);
  release_exp (btor, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (BTOR_IS_INVERTED_EXP (exp)) simplified = BTOR_INVERT_EXP (simplified);

  return simplified;
}

/* Finds most simplified expression and shortens path to it */
static BtorExp *
pointer_chase_simplified_exp (Btor *btor, BtorExp *exp)
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
  assert (pointer_chase_simplified_exp (btor, child) == child);
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
new_const_exp_node (Btor *btor, const char *bits)
{
  BtorBVConstExp *exp;
  int i, len;
  assert (btor != NULL);
  assert (bits != NULL);
  len = (int) strlen (bits);
  assert (len > 0);
  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  exp->kind  = BTOR_CONST_EXP;
  exp->bytes = sizeof *exp;
  BTOR_NEWN (btor->mm, exp->bits, len + 1);
  for (i = 0; i < len; i++) exp->bits[i] = bits[i] == '1' ? '1' : '0';
  exp->bits[len] = '\0';
  exp->len       = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  return (BtorExp *) exp;
}

static BtorExp *
new_slice_exp_node (Btor *btor, BtorExp *e0, int upper, int lower)
{
  BtorBVExp *exp = NULL;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (upper >= lower);
  BTOR_CNEW (btor->mm, exp);
  btor->stats.expressions++;
  exp->kind  = BTOR_SLICE_EXP;
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  exp->upper = upper;
  exp->lower = lower;
  exp->len   = upper - lower + 1;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  connect_child_exp (btor, (BtorExp *) exp, e0, 0);
  return (BtorExp *) exp;
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
  exp->kind  = kind;
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  connect_child_exp (btor, (BtorExp *) exp, e0, 0);
  connect_child_exp (btor, (BtorExp *) exp, e1, 1);
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
  exp->kind  = BTOR_AEQ_EXP;
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  exp->len   = 1;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
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
  exp->kind  = kind;
  exp->bytes = sizeof *exp;
  exp->arity = 3;
  exp->len   = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
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
  exp->kind      = BTOR_WRITE_EXP;
  exp->bytes     = sizeof *exp;
  exp->arity     = 3;
  exp->index_len = BTOR_REAL_ADDR_EXP (e_index)->len;
  exp->len       = BTOR_REAL_ADDR_EXP (e_value)->len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  /* append writes to the end of parrent list */
  connect_child_exp (btor, exp, e_array, 0);
  connect_child_exp (btor, exp, e_index, 1);
  connect_child_exp (btor, exp, e_value, 2);
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
  exp->kind      = BTOR_ACOND_EXP;
  exp->bytes     = sizeof *exp;
  exp->arity     = 3;
  exp->index_len = a_if->index_len;
  exp->len       = a_if->len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  connect_child_exp (btor, exp, e_cond, 0);
  connect_child_exp (btor, exp, a_if, 1);
  connect_child_exp (btor, exp, a_else, 2);
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
btor_compare_exp_by_id (BtorExp *exp1, BtorExp *exp2)
{
  int id1, id2;
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  id1 = BTOR_GET_ID_EXP (exp1);
  id2 = BTOR_GET_ID_EXP (exp2);
  if (id1 < id2) return -1;
  if (id1 > id2) return 1;
  return 0;
}

/* Finds constant expression in hash table. Returns NULL if it could not be
 * found. */
static BtorExp **
find_const_exp (Btor *btor, const char *bits)
{
  BtorExp *cur, **result;
  unsigned int hash;
  int len;
  assert (btor != NULL);
  assert (bits != NULL);
  len    = (int) strlen (bits);
  hash   = btor_hashstr ((void *) bits);
  hash   = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (btor->table.size - 1);
  result = btor->table.chains + hash;
  cur    = *result;
  while (cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (BTOR_IS_CONST_EXP (cur) && cur->len == len
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
  assert (!BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
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
      assert (!BTOR_IS_VAR_EXP (cur));
      assert (!BTOR_IS_ATOMIC_ARRAY_EXP (cur));
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

BtorExp *
btor_copy_exp (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_copy_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_copy_exp'");
  (void) btor;
  return copy_exp (btor, exp);
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
  BTOR_PUSH_STACK (mm, stack, exp);
  do
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (cur->mark != new_mark)
    {
      cur->mark = new_mark;
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, stack, cur->e[i]);
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
}

void
btor_release_exp (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_release_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_release_exp'");
  release_exp (btor, exp);
}

static BtorExp *
const_exp (Btor *btor, const char *bits)
{
  BtorExp **lookup;
  assert (btor != NULL);
  assert (bits != NULL);
  assert ((int) strlen (bits) > 0);
  lookup = find_const_exp (btor, bits);
  if (*lookup == NULL)
  {
    if (btor->table.num_elements == btor->table.size
        && btor_log_2_util (btor->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (btor);
      lookup = find_const_exp (btor, bits);
    }
    *lookup = new_const_exp_node (btor, bits);
    assert (btor->table.num_elements < INT_MAX);
    btor->table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
    inc_exp_ref_counter (btor, *lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  ;
  return *lookup;
}

BtorExp *
btor_const_exp (Btor *btor, const char *bits)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_const_exp'");
  BTOR_ABORT_EXP (bits == NULL, "'bits' must not be NULL in 'btor_const_exp'");
  BTOR_ABORT_EXP (*bits == '\0',
                  "'bits' must not be empty in 'btor_const_exp'");
  return const_exp (btor, bits);
}

static BtorExp *
int_min_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  string    = zero_string (btor, len);
  string[0] = '1';
  result    = const_exp (btor, string);
  btor_freestr (btor->mm, string);
  return result;
}

static BtorExp *
zero_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  string = zero_string (btor, len);
  result = const_exp (btor, string);
  btor_freestr (btor->mm, string);
  return result;
}

BtorExp *
btor_zero_exp (Btor *btor, int len)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_zero_exp'");
  BTOR_ABORT_EXP (len < 1, "'len' must not be < 1 in 'btor_zero_exp'");
  return zero_exp (btor, len);
}

static BtorExp *
false_exp (Btor *btor)
{
  assert (btor != NULL);
  return zero_exp (btor, 1);
}

BtorExp *
btor_false_exp (Btor *btor)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_false_exp'");
  return false_exp (btor);
}

static BtorExp *
ones_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  string = ones_string (btor, len);
  result = const_exp (btor, string);
  btor_freestr (btor->mm, string);
  return result;
}

BtorExp *
btor_ones_exp (Btor *btor, int len)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ones_exp'");
  BTOR_ABORT_EXP (len < 1, "'len' must not be < 1 in 'btor_ones_exp'");
  return ones_exp (btor, len);
}

static BtorExp *
one_exp (Btor *btor, int len)
{
  char *string;
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  string                            = zero_string (btor, len);
  string[(int) strlen (string) - 1] = '1';
  result                            = const_exp (btor, string);
  btor_freestr (btor->mm, string);
  return result;
}

BtorExp *
btor_one_exp (Btor *btor, int len)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_one_exp'");
  BTOR_ABORT_EXP (len < 1, "'len' must not be < 1 in 'btor_one_exp'");
  return one_exp (btor, len);
}

BtorExp *
btor_int_to_exp (Btor *btor, int i, int len)
{
  char *string;
  BtorExp *result;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_int_to_exp'");
  BTOR_ABORT_EXP (len < 1, "'len' must not be < 1 in 'btor_int_to_exp'");
  string = btor_int_to_const (btor->mm, i, len);
  result = const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

BtorExp *
btor_unsigned_to_exp (Btor *btor, unsigned int u, int len)
{
  char *string;
  BtorExp *result;
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_unsigned_to_exp'");
  BTOR_ABORT_EXP (len < 1, "'len' must not be < 1 in 'btor_unsigned_to_exp'");
  string = btor_unsigned_to_const (btor->mm, u, len);
  result = const_exp (btor, string);
  btor_delete_const (btor->mm, string);
  return result;
}

static BtorExp *
true_exp (Btor *btor)
{
  assert (btor != NULL);
  return one_exp (btor, 1);
}

BtorExp *
btor_true_exp (Btor *btor)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_true_exp'");
  return true_exp (btor);
}

static BtorExp *
var_exp (Btor *btor, int len, const char *symbol)
{
  BtorMemMgr *mm;
  BtorBVVarExp *exp;
  assert (btor != NULL);
  assert (len > 0);
  assert (symbol != NULL);
  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->stats.expressions++;
  exp->kind   = BTOR_VAR_EXP;
  exp->bytes  = sizeof *exp;
  exp->symbol = btor_strdup (mm, symbol);
  exp->len    = len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  return (BtorExp *) exp;
}

BtorExp *
btor_var_exp (Btor *btor, int len, const char *symbol)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_var_exp'");
  BTOR_ABORT_EXP (len < 1, "'len' must not be < 1 in 'btor_var_exp'");
  BTOR_ABORT_EXP (symbol == NULL,
                  "'symbol' must not be NULL in 'btor_var_exp'");
  return var_exp (btor, len, symbol);
}

static BtorExp *
array_exp (Btor *btor, int elem_len, int index_len)
{
  BtorMemMgr *mm;
  BtorArrayVarExp *exp;
  assert (btor != NULL);
  assert (elem_len >= 1);
  assert (index_len >= 1);
  mm = btor->mm;
  BTOR_CNEW (mm, exp);
  btor->stats.expressions++;
  exp->kind      = BTOR_ARRAY_EXP;
  exp->bytes     = sizeof *exp;
  exp->index_len = index_len;
  exp->len       = elem_len;
  BTOR_ABORT_EXP (btor->id == INT_MAX, "expression id overflow");
  exp->id   = btor->id++;
  exp->refs = 1u;
  exp->btor = btor;
  (void) btor_insert_in_ptr_hash_table (btor->arrays, exp);
  return (BtorExp *) exp;
}

BtorExp *
btor_array_exp (Btor *btor, int elem_len, int index_len)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_array_exp'");
  BTOR_ABORT_EXP (elem_len < 1,
                  "'elem_len' must not be < 1 in 'btor_array_exp'");
  BTOR_ABORT_EXP (index_len < 1,
                  "'index_len' must not be < 1 in 'btor_array_exp'");
  return array_exp (btor, elem_len, index_len);
}

static BtorExp *
unary_exp_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BtorExp **lookup;
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  exp    = pointer_chase_simplified_exp (btor, exp);
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
  return *lookup;
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
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  if (BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
      && BTOR_REAL_ADDR_EXP (e1)->id < BTOR_REAL_ADDR_EXP (e0)->id)
  {
    temp = e0;
    e0   = e1;
    e1   = temp;
  }
  assert (!BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
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
  e0     = pointer_chase_simplified_exp (btor, e0);
  e1     = pointer_chase_simplified_exp (btor, e1);
  e2     = pointer_chase_simplified_exp (btor, e2);
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

static BtorExp *
not_exp (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  (void) btor;
  inc_exp_ref_counter (btor, exp);
  return BTOR_INVERT_EXP (exp);
}

BtorExp *
btor_not_exp (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_not_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_not_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_not_exp'");
  return not_exp (btor, exp);
}

static BtorExp *
add_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_ADD_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_ADD_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_add_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_add_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_add_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_add_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_add_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_add_exp'");
  return add_exp (btor, e0, e1);
}

static BtorExp *
neg_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *one;
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  one    = one_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = add_exp (btor, BTOR_INVERT_EXP (exp), one);
  release_exp (btor, one);
  return result;
}

BtorExp *
btor_neg_exp (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_neg_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_neg_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_neg_exp'");
  return neg_exp (btor, exp);
}

static BtorExp *
slice_exp_aux (Btor *btor, BtorExp *exp, int upper, int lower, int calls)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_slice_exp (btor, exp, upper, lower, calls);
  if (result == NULL) result = unary_exp_slice_exp (btor, exp, upper, lower);
  return result;
}

#define BTOR_REWRITE_SLICE_EXP_REC_LIMIT 5

static BtorExp *
rewrite_slice_exp (Btor *btor, BtorExp *e0, int upper, int lower, int calls)
{
  BtorMemMgr *mm;
  BtorExp *real_e0, *result, *temp_left, *temp_right, *temp;
  char *bresult;
  int len;
  assert (btor != NULL);
  assert (btor->rewrite_level > 0);
  assert (btor->rewrite_level <= 2);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (lower <= upper);
  assert (calls >= 0);

  /* stop recursion */
  if (calls == BTOR_REWRITE_SLICE_EXP_REC_LIMIT) return NULL;

  mm      = btor->mm;
  result  = NULL;
  e0      = pointer_chase_simplified_exp (btor, e0);
  real_e0 = BTOR_REAL_ADDR_EXP (e0);
  len     = real_e0->len;
  if (upper - lower + 1 == len) /* handles result->len == 1 */
    result = copy_exp (btor, e0);
  else if (BTOR_IS_CONST_EXP (real_e0))
  {
    bresult = btor_slice_const (mm, real_e0->bits, upper, lower);
    result  = const_exp (btor, bresult);
    result  = BTOR_COND_INVERT_EXP (e0, result);
    btor_delete_const (mm, bresult);
  }
  /* push slice into ADD if we slice from the LSB and do not slice
   * the whole bit-vector */
  else if (lower == 0 && upper < len - 1
           && (real_e0->kind == BTOR_ADD_EXP || real_e0->kind == BTOR_MUL_EXP))
  {
    /* ATTENTION: 2 recursive calls */
    temp_left  = slice_exp_aux (btor, real_e0->e[0], upper, lower, calls + 1);
    temp_right = slice_exp_aux (btor, real_e0->e[1], upper, lower, calls + 1);
    if (real_e0->kind == BTOR_ADD_EXP)
      temp = add_exp (btor, temp_left, temp_right);
    else
    {
      assert (real_e0->kind == BTOR_MUL_EXP);
      temp = mul_exp (btor, temp_left, temp_right);
    }
    result = BTOR_COND_INVERT_EXP (e0, temp);
    release_exp (btor, temp_left);
    release_exp (btor, temp_right);
  }
  /* TODO: {a,b}[1,0] == b[1,0] etc., e.g. push slice into concat */
  return result;
}

static BtorExp *
slice_exp (Btor *btor, BtorExp *exp, int upper, int lower)
{
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  return slice_exp_aux (btor, exp, upper, lower, 0);
}

BtorExp *
btor_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_slice_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_slice_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_slice_exp'");
  BTOR_ABORT_EXP (lower < 0,
                  "'lower' must not be negative in 'btor_slice_exp'");
  BTOR_ABORT_EXP (upper < lower,
                  "'upper' must not be < 'lower' in 'btor_slice_exp'");
  BTOR_ABORT_EXP (upper >= BTOR_REAL_ADDR_EXP (exp)->len,
                  "'upper' must not be >= length of 'exp' in 'btor_slice_exp'");
  return slice_exp (btor, exp, upper, lower);
}

static BtorExp *
eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  BtorExpKind kind;
#ifndef NDEBUG
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
#endif
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
#ifndef NDEBUG
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  assert (is_array_e0 == is_array_e1);
  assert (real_e0->len == real_e1->len);
  assert (real_e0->len > 0);
  assert (!is_array_e0 || real_e0->index_len == real_e1->index_len);
  assert (!is_array_e0 || real_e0->index_len > 0);
  assert (!is_array_e0
          || (BTOR_IS_REGULAR_EXP (e0) && BTOR_IS_REGULAR_EXP (e1)));
#endif
  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (btor->rewrite_level > 0 && BTOR_IS_INVERTED_EXP (e0)
      && BTOR_IS_INVERTED_EXP (e1))
  {
    e0 = BTOR_REAL_ADDR_EXP (e0);
    e1 = BTOR_REAL_ADDR_EXP (e1);
  }
  result = NULL;
  kind   = BTOR_BEQ_EXP;
  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)))
  {
    assert (BTOR_IS_REGULAR_EXP (e0));
    assert (BTOR_IS_REGULAR_EXP (e1));
    assert (BTOR_IS_ARRAY_EXP (e0));
    assert (BTOR_IS_ARRAY_EXP (e1));
    kind = BTOR_AEQ_EXP;
  }
  if (btor->rewrite_level > 0) result = rewrite_binary_exp (btor, kind, e0, e1);
  if (result == NULL) result = binary_exp (btor, kind, e0, e1, 1);
  return result;
}

BtorExp *
btor_eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_eq_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_eq_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_eq_exp'");
  e0          = pointer_chase_simplified_exp (btor, e0);
  e1          = pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_EXP (
      is_array_e0 != is_array_e1,
      "array must not be compared with bit vector in 'btor_eq_exp'");
  BTOR_ABORT_EXP (!is_array_e0 && real_e0->len != real_e1->len,
                  "bit vectors must not have unequal length in 'btor_eq_exp'");
  BTOR_ABORT_EXP (
      is_array_e0 && real_e0->len != real_e1->len,
      "arrays must not have unequal element length in 'btor_eq_exp'");
  BTOR_ABORT_EXP (is_array_e0 && real_e0->index_len != real_e1->index_len,
                  "arrays must not have unequal index length in 'btor_eq_exp'");
  return eq_exp (btor, e0, e1);
}

static BtorExp *
and_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1, *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  real_e0 = BTOR_REAL_ADDR_EXP (e0);
  real_e1 = BTOR_REAL_ADDR_EXP (e1);
  result  = NULL;
  /* inline rewriting code as operands can change, e.g.
   * symtmetric rule of idempotency */
  if (btor->rewrite_level > 0)
  /* two level optimization [MEMICS] for BTOR_AND_EXP */
  {
  BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN:
    if (e0 == e1) /* x & x == x */
      return copy_exp (btor, e0);
    if (BTOR_INVERT_EXP (e0) == e1) /* x & ~x == 0 */
      return zero_exp (btor, real_e0->len);
    if (real_e0->kind == BTOR_AND_EXP && real_e1->kind == BTOR_AND_EXP)
    {
      if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1))
      {
        /* second rule of contradiction */
        if (real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[0])
            || real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[1])
            || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0])
            || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
          return zero_exp (btor, real_e0->len);
        /* symmetric rule of idempotency */
        if (real_e0->e[0] == real_e1->e[0] || real_e0->e[1] == real_e1->e[0])
        {
          e1      = real_e1->e[1];
          real_e1 = BTOR_REAL_ADDR_EXP (e1);
          assert (!BTOR_IS_CONST_EXP (real_e1));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
        /* use commutativity */
        if (real_e0->e[0] == real_e1->e[1] || real_e0->e[1] == real_e1->e[1])
        {
          e1      = real_e1->e[0];
          real_e1 = BTOR_REAL_ADDR_EXP (e1);
          assert (!BTOR_IS_CONST_EXP (real_e1));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
      }
      else if (!BTOR_IS_INVERTED_EXP (e0) && BTOR_IS_INVERTED_EXP (e1))
      {
        /* second rule of subsumption */
        if (real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[0])
            || real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[1])
            || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0])
            || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
          return copy_exp (btor, e0);
        /* symmetric rule of substitution */
        if ((real_e1->e[0] == real_e0->e[1])
            || (real_e1->e[0] == real_e0->e[0]))
        {
          e1      = BTOR_INVERT_EXP (real_e1->e[1]);
          real_e1 = BTOR_REAL_ADDR_EXP (e1);
          assert (!BTOR_IS_CONST_EXP (real_e1));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
        /* symmetric rule of substitution */
        if ((real_e1->e[1] == real_e0->e[1])
            || (real_e1->e[1] == real_e0->e[0]))
        {
          e1      = BTOR_INVERT_EXP (real_e1->e[0]);
          real_e1 = BTOR_REAL_ADDR_EXP (e1);
          assert (!BTOR_IS_CONST_EXP (real_e1));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
      }
      else if (BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1))
      {
        /* second rule of subsumption */
        if (real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[0])
            || real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[1])
            || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0])
            || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
          return copy_exp (btor, e1);
        /* symmetric rule of substitution */
        if ((real_e0->e[1] == real_e1->e[0])
            || (real_e0->e[1] == real_e1->e[1]))
        {
          e0      = BTOR_INVERT_EXP (real_e0->e[0]);
          real_e0 = BTOR_REAL_ADDR_EXP (e0);
          assert (!BTOR_IS_CONST_EXP (real_e0));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
        /* symmetric rule of substitution */
        if ((real_e0->e[0] == real_e1->e[0])
            || (real_e0->e[0] == real_e1->e[1]))
        {
          e0      = BTOR_INVERT_EXP (real_e0->e[1]);
          real_e0 = BTOR_REAL_ADDR_EXP (e0);
          assert (!BTOR_IS_CONST_EXP (real_e0));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
      }
      else
      {
        assert (BTOR_IS_INVERTED_EXP (e0));
        assert (BTOR_IS_INVERTED_EXP (e1));
        /* a XNOR b simplifies to a == b for the boolean case */
        if (real_e0->len == 1
            && BTOR_IS_INVERTED_EXP (real_e0->e[0])
                   != BTOR_IS_INVERTED_EXP (real_e0->e[1])
            && BTOR_IS_INVERTED_EXP (real_e1->e[0])
                   != BTOR_IS_INVERTED_EXP (real_e1->e[1])
            && ((real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[0])
                 && real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
                || (real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[1])
                    && real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0]))))
          return eq_exp (btor,
                         BTOR_REAL_ADDR_EXP (real_e0->e[0]),
                         BTOR_REAL_ADDR_EXP (real_e0->e[1]));
        /* rule of resolution */
        if ((real_e0->e[0] == real_e1->e[0]
             && real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
            || (real_e0->e[0] == real_e1->e[1]
                && real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0])))
          return BTOR_INVERT_EXP (copy_exp (btor, real_e0->e[0]));
        /* rule of resolution */
        if ((real_e1->e[1] == real_e0->e[1]
             && real_e1->e[0] == BTOR_INVERT_EXP (real_e0->e[0]))
            || (real_e1->e[1] == real_e0->e[0]
                && real_e1->e[0] == BTOR_INVERT_EXP (real_e0->e[1])))
          return BTOR_INVERT_EXP (copy_exp (btor, real_e1->e[1]));
      }
    }
    else if (real_e0->kind == BTOR_AND_EXP)
    {
      if (BTOR_IS_INVERTED_EXP (e0))
      {
        /* first rule of subsumption */
        if (real_e0->e[0] == BTOR_INVERT_EXP (e1)
            || real_e0->e[1] == BTOR_INVERT_EXP (e1))
          return copy_exp (btor, e1);
        /* asymmetric rule of substitution */
        if (real_e0->e[1] == e1)
        {
          e0      = BTOR_INVERT_EXP (real_e0->e[0]);
          real_e0 = BTOR_REAL_ADDR_EXP (e0);
          assert (!BTOR_IS_CONST_EXP (real_e0));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
        /* asymmetric rule of substitution */
        if (real_e0->e[0] == e1)
        {
          e0      = BTOR_INVERT_EXP (real_e0->e[1]);
          real_e0 = BTOR_REAL_ADDR_EXP (e0);
          assert (!BTOR_IS_CONST_EXP (real_e0));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
      }
      else
      {
        assert (!BTOR_IS_INVERTED_EXP (e0));
        /* first rule of contradiction */
        if (real_e0->e[0] == BTOR_INVERT_EXP (e1)
            || real_e0->e[1] == BTOR_INVERT_EXP (e1))
          return zero_exp (btor, real_e0->len);
        /* asymmetric rule of idempotency */
        if (real_e0->e[0] == e1 || real_e0->e[1] == e1)
          return copy_exp (btor, e0);
      }
    }
    else if (real_e1->kind == BTOR_AND_EXP)
    {
      if (BTOR_IS_INVERTED_EXP (e1))
      {
        /* first rule of subsumption */
        if (real_e1->e[0] == BTOR_INVERT_EXP (e0)
            || real_e1->e[1] == BTOR_INVERT_EXP (e0))
          return copy_exp (btor, e0);
        /* asymmetric rule of substitution */
        if (real_e1->e[0] == e0)
        {
          e1      = BTOR_INVERT_EXP (real_e1->e[1]);
          real_e1 = BTOR_REAL_ADDR_EXP (e1);
          assert (!BTOR_IS_CONST_EXP (real_e1));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
        /* asymmetric rule of substitution */
        if (real_e1->e[1] == e0)
        {
          e1      = BTOR_INVERT_EXP (real_e1->e[0]);
          real_e1 = BTOR_REAL_ADDR_EXP (e1);
          assert (!BTOR_IS_CONST_EXP (real_e1));
          goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
        }
      }
      else
      {
        assert (!BTOR_IS_INVERTED_EXP (e1));
        /* first rule of contradiction */
        if (real_e1->e[0] == BTOR_INVERT_EXP (e0)
            || real_e1->e[1] == BTOR_INVERT_EXP (e0))
          return zero_exp (btor, real_e0->len);
        /* asymmetric rule of idempotency */
        if (real_e1->e[0] == e0 || real_e1->e[1] == e0)
          return copy_exp (btor, e1);
      }
    }
    else
    {
      assert (real_e0->kind != BTOR_AND_EXP);
      assert (real_e1->kind != BTOR_AND_EXP);
      if (real_e0->kind == BTOR_ULT_EXP && real_e1->kind == BTOR_ULT_EXP)
      {
        /* a < b && b < a simplifies to FALSE */
        if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1)
            && e0->e[0] == e1->e[1] && e0->e[1] == e1->e[0])
          return false_exp (btor);
        /* NOT (a < b) && NOT (b < a) simplifies to a == b */
        if (BTOR_IS_INVERTED_EXP (e0) && BTOR_IS_INVERTED_EXP (e1)
            && real_e0->e[0] == real_e1->e[1] && real_e0->e[1] == real_e1->e[0])
          return eq_exp (btor,
                         BTOR_REAL_ADDR_EXP (real_e0->e[0]),
                         BTOR_REAL_ADDR_EXP (real_e0->e[1]));
      }
    }
  }
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_AND_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_AND_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_and_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_and_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_and_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_and_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_and_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_and_exp'");
  return and_exp (btor, e0, e1);
}

static BtorExp *
or_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (
      and_exp (btor, BTOR_INVERT_EXP (e0), BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_or_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_or_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_or_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_or_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_or_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_or_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_or_exp'");
  return or_exp (btor, e0, e1);
}

static BtorExp *
xor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, * or, *and;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);

  /* XOR (e0, e1) can be rewritten to e0 != e1 in the boolean case
   * this can lead to more substitutions */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1)
    return BTOR_INVERT_EXP (eq_exp (btor, e0, e1));

  or     = or_exp (btor, e0, e1);
  and    = and_exp (btor, e0, e1);
  result = and_exp (btor, or, BTOR_INVERT_EXP (and));
  release_exp (btor, or);
  release_exp (btor, and);
  return result;
}

BtorExp *
btor_xor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_xor_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_xor_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_xor_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_xor_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_xor_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_xor_exp'");
  return xor_exp (btor, e0, e1);
}

static BtorExp *
concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->len
          <= INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_CONCAT_EXP, e0, e1);
  if (result == NULL)
    result = binary_exp (
        btor,
        BTOR_CONCAT_EXP,
        e0,
        e1,
        BTOR_REAL_ADDR_EXP (e0)->len + BTOR_REAL_ADDR_EXP (e1)->len);
  return result;
}

BtorExp *
btor_concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_concat_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_concat_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_concat_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_concat_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_concat_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len > INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len,
      "length of result is too large in 'btor_concat_exp'");
  return concat_exp (btor, e0, e1);
}

static BtorExp *
rewrite_ternary_exp (
    Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1, BtorExp *e2)
{
  BtorExp *result, *real_e0, *real_e1, *real_e2, *temp_left, *temp_right;
  BtorMemMgr *mm;
  assert (btor != NULL);
  assert (btor->rewrite_level > 0);
  assert (btor->rewrite_level <= 2);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (kind == BTOR_BCOND_EXP || kind == BTOR_ACOND_EXP);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  e0      = pointer_chase_simplified_exp (btor, e0);
  e1      = pointer_chase_simplified_exp (btor, e1);
  e2      = pointer_chase_simplified_exp (btor, e2);
  mm      = btor->mm;
  result  = NULL;
  real_e0 = BTOR_REAL_ADDR_EXP (e0);
  real_e1 = BTOR_REAL_ADDR_EXP (e1);
  real_e2 = BTOR_REAL_ADDR_EXP (e2);
  if (BTOR_IS_CONST_EXP (real_e0))
  {
    if ((!BTOR_IS_INVERTED_EXP (e0) && e0->bits[0] == '1')
        || (BTOR_IS_INVERTED_EXP (e0) && real_e0->bits[0] == '0'))
      result = copy_exp (btor, e1);
    else
      result = copy_exp (btor, e2);
  }
  else if (e1 == e2)
    result = copy_exp (btor, e1);
  else if (kind == BTOR_BCOND_EXP && real_e1->len == 1)
  {
    temp_left  = and_exp (btor, e0, BTOR_INVERT_EXP (e1));
    temp_right = and_exp (btor, BTOR_INVERT_EXP (e0), BTOR_INVERT_EXP (e2));
    result     = and_exp (
        btor, BTOR_INVERT_EXP (temp_left), BTOR_INVERT_EXP (temp_right));
    release_exp (btor, temp_right);
    release_exp (btor, temp_left);
  }
  return result;
}

static BtorExp *
cond_exp (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExp *result, *temp;
  BtorExpKind kind;
#ifndef NDEBUG
  BtorExp *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;
#endif
  e_cond = pointer_chase_simplified_exp (btor, e_cond);
  e_if   = pointer_chase_simplified_exp (btor, e_if);
  e_else = pointer_chase_simplified_exp (btor, e_else);
#ifndef NDEBUG
  assert (btor != NULL);
  assert (e_cond != NULL);
  assert (e_if != NULL);
  assert (e_else != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (BTOR_REAL_ADDR_EXP (e_cond)->len == 1);
  real_e_if       = BTOR_REAL_ADDR_EXP (e_if);
  real_e_else     = BTOR_REAL_ADDR_EXP (e_else);
  is_array_e_if   = BTOR_IS_ARRAY_EXP (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_EXP (real_e_else);
  assert (is_array_e_if == is_array_e_else);
  assert (real_e_if->len == real_e_else->len);
  assert (real_e_if->len > 0);
  assert (!is_array_e_if
          || (BTOR_IS_REGULAR_EXP (e_if) && BTOR_IS_REGULAR_EXP (e_else)));
  assert (!is_array_e_if || e_if->index_len == e_else->index_len);
  assert (!is_array_e_if || e_if->index_len > 0);
#endif
  /* normalization: condition must not be inverted
   * we need this normalization also in rewrite level 0 */
  if (BTOR_IS_INVERTED_EXP (e_cond))
  {
    e_cond = BTOR_INVERT_EXP (e_cond);
    temp   = e_if;
    e_if   = e_else;
    e_else = temp;
  }
  result = NULL;
  kind   = BTOR_BCOND_EXP;
  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if))) kind = BTOR_ACOND_EXP;
  if (btor->rewrite_level > 0)
    result = rewrite_ternary_exp (btor, kind, e_cond, e_if, e_else);
  if (result == NULL)
    result = ternary_exp (
        btor, kind, e_cond, e_if, e_else, BTOR_REAL_ADDR_EXP (e_if)->len);
  return result;
}

BtorExp *
btor_cond_exp (Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else)
{
  BtorExp *real_e_if, *real_e_else;
  int is_array_e_if, is_array_e_else;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_cond_exp'");
  BTOR_ABORT_EXP (e_cond == NULL,
                  "'e_cond' must not be NULL in 'btor_cond_exp'");
  BTOR_ABORT_EXP (e_if == NULL, "'e_if' must not be NULL in 'btor_cond_exp'");
  BTOR_ABORT_EXP (e_else == NULL,
                  "'e_else' must not be NULL in 'btor_cond_exp'");
  e_cond = pointer_chase_simplified_exp (btor, e_cond);
  e_if   = pointer_chase_simplified_exp (btor, e_if);
  e_else = pointer_chase_simplified_exp (btor, e_else);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)),
                  "'e_cond' must not be an array in 'btor_cond_exp'");
  BTOR_ABORT_EXP (BTOR_REAL_ADDR_EXP (e_cond)->len != 1,
                  "length of 'e_cond' must be equal to 1 in 'btor_cond_exp'");
  real_e_if       = BTOR_REAL_ADDR_EXP (e_if);
  real_e_else     = BTOR_REAL_ADDR_EXP (e_else);
  is_array_e_if   = BTOR_IS_ARRAY_EXP (real_e_if);
  is_array_e_else = BTOR_IS_ARRAY_EXP (real_e_else);
  BTOR_ABORT_EXP (
      is_array_e_if != is_array_e_else,
      "array must not be combined with bit vector in 'btor_cond_exp'");
  BTOR_ABORT_EXP (
      !is_array_e_if && real_e_if->len != real_e_else->len,
      "bit vectors must not have unequal length in 'btor_cond_exp'");
  BTOR_ABORT_EXP (
      is_array_e_if && real_e_if->len != real_e_else->len,
      "arrays must not have unequal element length in 'btor_cond_exp'");
  BTOR_ABORT_EXP (
      is_array_e_if && real_e_if->index_len != real_e_else->index_len,
      "arrays must not have unequal index length in 'btor_cond_exp'");
  return cond_exp (btor, e_cond, e_if, e_else);
}

BtorExp *
btor_nego_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *sign_exp, *rest, *zero, *eq;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_nego_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_nego_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_nego_exp'");
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  len = BTOR_REAL_ADDR_EXP (exp)->len;
  if (len == 1) return copy_exp (btor, exp);
  sign_exp = slice_exp (btor, exp, len - 1, len - 1);
  rest     = slice_exp (btor, exp, len - 2, 0);
  zero     = zero_exp (btor, len - 1);
  eq       = eq_exp (btor, rest, zero);
  result   = and_exp (btor, sign_exp, eq);
  release_exp (btor, sign_exp);
  release_exp (btor, rest);
  release_exp (btor, zero);
  release_exp (btor, eq);
  return result;
}

BtorExp *
btor_redor_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *zero;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_redor_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_redor_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_redor_exp'");
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  zero   = zero_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = BTOR_INVERT_EXP (eq_exp (btor, exp, zero));
  release_exp (btor, zero);
  return result;
}

BtorExp *
btor_redxor_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *slice, *xor;
  int i, len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_redxor_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_redxor_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_redxor_exp'");
  len = BTOR_REAL_ADDR_EXP (exp)->len;
  assert (len > 0);
  result = slice_exp (btor, exp, 0, 0);
  for (i = 1; i < len; i++)
  {
    slice = slice_exp (btor, exp, i, i);
    xor   = xor_exp (btor, result, slice);
    release_exp (btor, slice);
    release_exp (btor, result);
    result = xor;
  }
  return result;
}

BtorExp *
btor_redand_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *result, *ones;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_redand_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_redand_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_redand_exp'");
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  ones   = ones_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = eq_exp (btor, exp, ones);
  release_exp (btor, ones);
  return result;
}

static BtorExp *
uext_exp (Btor *btor, BtorExp *exp, int len)
{
  BtorExp *result, *zero;
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (len >= 0);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  if (len == 0)
    result = copy_exp (btor, exp);
  else
  {
    assert (len > 0);
    zero   = zero_exp (btor, len);
    result = concat_exp (btor, zero, exp);
    release_exp (btor, zero);
  }
  return result;
}

BtorExp *
btor_uext_exp (Btor *btor, BtorExp *exp, int len)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_uext_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_uext_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_uext_exp'");
  BTOR_ABORT_EXP (len < 0, "'len' must not be negative in 'btor_uext_exp'");
  return uext_exp (btor, exp, len);
}

static BtorExp *
sext_exp (Btor *btor, BtorExp *exp, int len)
{
  BtorExp *result, *zero, *ones, *neg, *cond;
  int exp_len;
  assert (btor != NULL);
  assert (exp != NULL);
  exp = pointer_chase_simplified_exp (btor, exp);
  assert (len >= 0);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  if (len == 0)
    result = copy_exp (btor, exp);
  else
  {
    assert (len > 0);
    zero    = zero_exp (btor, len);
    ones    = ones_exp (btor, len);
    exp_len = BTOR_REAL_ADDR_EXP (exp)->len;
    neg     = slice_exp (btor, exp, exp_len - 1, exp_len - 1);
    cond    = cond_exp (btor, neg, ones, zero);
    result  = concat_exp (btor, cond, exp);
    release_exp (btor, zero);
    release_exp (btor, ones);
    release_exp (btor, neg);
    release_exp (btor, cond);
  }
  return result;
}

BtorExp *
btor_sext_exp (Btor *btor, BtorExp *exp, int len)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sext_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_sext_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_sext_exp'");
  BTOR_ABORT_EXP (len < 0, "'len' must not be negative in 'btor_sext_exp'");
  return sext_exp (btor, exp, len);
}

BtorExp *
btor_nand_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_nand_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_nand_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_nand_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_nand_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_nand_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_nand_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (and_exp (btor, e0, e1));
}

BtorExp *
btor_nor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_nor_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_nor_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_nor_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_nor_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_nor_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_nor_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (or_exp (btor, e0, e1));
}

BtorExp *
btor_implies_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_implies_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_implies_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_implies_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_implies_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_implies_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "length of 'e0' and 'e1' must not be unequal to 1 'btor_implies_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (and_exp (btor, e0, BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_iff_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_iff_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_iff_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_iff_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_iff_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_iff_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != 1 || BTOR_REAL_ADDR_EXP (e1)->len != 1,
      "length of 'e0' and 'e1' must not be unequal to 1 in 'btor_iff_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return eq_exp (btor, e0, e1);
}

BtorExp *
btor_xnor_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_xnor_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_xnor_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_xnor_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_xnor_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_xnor_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_xnor_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);

  /* XNOR (e0, e1) can be rewritten to e0 == e1 in the boolean case
   * this can lead to more substitutions */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1) return eq_exp (btor, e0, e1);

  return BTOR_INVERT_EXP (xor_exp (btor, e0, e1));
}

BtorExp *
btor_ne_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int is_array_e0, is_array_e1;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ne_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ne_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ne_exp'");
  e0          = pointer_chase_simplified_exp (btor, e0);
  e1          = pointer_chase_simplified_exp (btor, e1);
  real_e0     = BTOR_REAL_ADDR_EXP (e0);
  real_e1     = BTOR_REAL_ADDR_EXP (e1);
  is_array_e0 = BTOR_IS_ARRAY_EXP (real_e0);
  is_array_e1 = BTOR_IS_ARRAY_EXP (real_e1);
  BTOR_ABORT_EXP (
      is_array_e0 != is_array_e1,
      "array must not be compared with bit vector in 'btor_ne_exp'");
  BTOR_ABORT_EXP (
      is_array_e0 && real_e0->len != real_e1->len,
      "arrays must not have unequal element length in 'btor_ne_exp'");
  BTOR_ABORT_EXP (is_array_e0 && real_e0->index_len != real_e1->index_len,
                  "arrays must not have unequal index length in 'btor_ne_exp'");
  assert (!is_array_e0 || real_e0->index_len > 0);
  assert (!is_array_e0
          || (BTOR_IS_REGULAR_EXP (e0) && BTOR_IS_REGULAR_EXP (e1)));
  assert (real_e0->len > 0);
  return BTOR_INVERT_EXP (eq_exp (btor, e0, e1));
}

BtorExp *
btor_uaddo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *uext_e1, *uext_e2, *add;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_uaddo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_uaddo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_uaddo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_uaddo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_uaddo_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_uaddo_exp'");
  assert (len > 0);
  uext_e1 = uext_exp (btor, e0, 1);
  uext_e2 = uext_exp (btor, e1, 1);
  add     = add_exp (btor, uext_e1, uext_e2);
  result  = slice_exp (btor, add, len, len);
  release_exp (btor, uext_e1);
  release_exp (btor, uext_e2);
  release_exp (btor, add);
  return result;
}

BtorExp *
btor_saddo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *sign_result;
  BtorExp *add, *and1, *and2, *or1, *or2;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_saddo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_saddo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_saddo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_saddo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_saddo_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_saddo_exp'");
  assert (len > 0);
  sign_e1     = slice_exp (btor, e0, len - 1, len - 1);
  sign_e2     = slice_exp (btor, e1, len - 1, len - 1);
  add         = add_exp (btor, e0, e1);
  sign_result = slice_exp (btor, add, len - 1, len - 1);
  and1        = and_exp (btor, sign_e1, sign_e2);
  or1         = and_exp (btor, and1, BTOR_INVERT_EXP (sign_result));
  and2   = and_exp (btor, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  or2    = and_exp (btor, and2, sign_result);
  result = or_exp (btor, or1, or2);
  release_exp (btor, and1);
  release_exp (btor, and2);
  release_exp (btor, or1);
  release_exp (btor, or2);
  release_exp (btor, add);
  release_exp (btor, sign_e1);
  release_exp (btor, sign_e2);
  release_exp (btor, sign_result);
  return result;
}

static BtorExp *
mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_MUL_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_MUL_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_mul_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_mul_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_mul_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_mul_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_mul_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_mul_exp'");
  return mul_exp (btor, e0, e1);
}

BtorExp *
btor_umulo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *uext_e1, *uext_e2, *mul, *slice, *and, * or, **temps_e2;
  int i, len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_umulo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_umulo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_umulo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_umulo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_umulo_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_umulo_exp'");
  assert (len > 0);
  if (len == 1) return zero_exp (btor, 1);
  BTOR_NEWN (btor->mm, temps_e2, len - 1);
  temps_e2[0] = slice_exp (btor, e1, len - 1, len - 1);
  for (i = 1; i < len - 1; i++)
  {
    slice       = slice_exp (btor, e1, len - 1 - i, len - 1 - i);
    temps_e2[i] = or_exp (btor, temps_e2[i - 1], slice);
    release_exp (btor, slice);
  }
  slice  = slice_exp (btor, e0, 1, 1);
  result = and_exp (btor, slice, temps_e2[0]);
  release_exp (btor, slice);
  for (i = 1; i < len - 1; i++)
  {
    slice = slice_exp (btor, e0, i + 1, i + 1);
    and   = and_exp (btor, slice, temps_e2[i]);
    or    = or_exp (btor, result, and);
    release_exp (btor, slice);
    release_exp (btor, and);
    release_exp (btor, result);
    result = or ;
  }
  uext_e1 = uext_exp (btor, e0, 1);
  uext_e2 = uext_exp (btor, e1, 1);
  mul     = mul_exp (btor, uext_e1, uext_e2);
  slice   = slice_exp (btor, mul, len, len);
  or      = or_exp (btor, result, slice);
  release_exp (btor, uext_e1);
  release_exp (btor, uext_e2);
  release_exp (btor, mul);
  release_exp (btor, slice);
  release_exp (btor, result);
  result = or ;
  for (i = 0; i < len - 1; i++) release_exp (btor, temps_e2[i]);
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
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_smulo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_smulo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_smulo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_smulo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_smulo_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_smulo_exp'");
  assert (len > 0);
  if (len == 1) return and_exp (btor, e0, e1);
  if (len == 2)
  {
    sext_e1         = sext_exp (btor, e0, 1);
    sext_e2         = sext_exp (btor, e1, 1);
    mul             = mul_exp (btor, sext_e1, sext_e2);
    slice_n         = slice_exp (btor, mul, len, len);
    slice_n_minus_1 = slice_exp (btor, mul, len - 1, len - 1);
    result          = xor_exp (btor, slice_n, slice_n_minus_1);
    release_exp (btor, sext_e1);
    release_exp (btor, sext_e2);
    release_exp (btor, mul);
    release_exp (btor, slice_n);
    release_exp (btor, slice_n_minus_1);
  }
  else
  {
    sign_e1      = slice_exp (btor, e0, len - 1, len - 1);
    sign_e2      = slice_exp (btor, e1, len - 1, len - 1);
    sext_sign_e1 = sext_exp (btor, sign_e1, len - 1);
    sext_sign_e2 = sext_exp (btor, sign_e2, len - 1);
    xor_sign_e1  = xor_exp (btor, e0, sext_sign_e1);
    xor_sign_e2  = xor_exp (btor, e1, sext_sign_e2);
    BTOR_NEWN (btor->mm, temps_e2, len - 2);
    temps_e2[0] = slice_exp (btor, xor_sign_e2, len - 2, len - 2);
    for (i = 1; i < len - 2; i++)
    {
      slice       = slice_exp (btor, xor_sign_e2, len - 2 - i, len - 2 - i);
      temps_e2[i] = or_exp (btor, temps_e2[i - 1], slice);
      release_exp (btor, slice);
    }
    slice  = slice_exp (btor, xor_sign_e1, 1, 1);
    result = and_exp (btor, slice, temps_e2[0]);
    release_exp (btor, slice);
    for (i = 1; i < len - 2; i++)
    {
      slice = slice_exp (btor, xor_sign_e1, i + 1, i + 1);
      and   = and_exp (btor, slice, temps_e2[i]);
      or    = or_exp (btor, result, and);
      release_exp (btor, slice);
      release_exp (btor, and);
      release_exp (btor, result);
      result = or ;
    }
    sext_e1         = sext_exp (btor, e0, 1);
    sext_e2         = sext_exp (btor, e1, 1);
    mul             = mul_exp (btor, sext_e1, sext_e2);
    slice_n         = slice_exp (btor, mul, len, len);
    slice_n_minus_1 = slice_exp (btor, mul, len - 1, len - 1);
    xor             = xor_exp (btor, slice_n, slice_n_minus_1);
    or              = or_exp (btor, result, xor);
    release_exp (btor, sext_e1);
    release_exp (btor, sext_e2);
    release_exp (btor, sign_e1);
    release_exp (btor, sign_e2);
    release_exp (btor, sext_sign_e1);
    release_exp (btor, sext_sign_e2);
    release_exp (btor, xor_sign_e1);
    release_exp (btor, xor_sign_e2);
    release_exp (btor, mul);
    release_exp (btor, slice_n);
    release_exp (btor, slice_n_minus_1);
    release_exp (btor, xor);
    release_exp (btor, result);
    result = or ;
    for (i = 0; i < len - 2; i++) release_exp (btor, temps_e2[i]);
    BTOR_DELETEN (btor->mm, temps_e2, len - 2);
  }
  return result;
}

static BtorExp *
ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *temp;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  /* ~a < ~b  is the same as  b < a */
  if (btor->rewrite_level > 0 && BTOR_IS_INVERTED_EXP (e0)
      && BTOR_IS_INVERTED_EXP (e1))
  {
    temp = BTOR_REAL_ADDR_EXP (e1);
    e1   = BTOR_REAL_ADDR_EXP (e0);
    e0   = temp;
  }
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_ULT_EXP, e0, e1);
  if (result == NULL) result = binary_exp (btor, BTOR_ULT_EXP, e0, e1, 1);
  return result;
}

BtorExp *
btor_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ult_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ult_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ult_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_ult_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_ult_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ult_exp'");
  return ult_exp (btor, e0, e1);
}

static BtorExp *
slt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *rest_e1, *rest_e2, *ult;
  BtorExp *e1_signed_only, *e1_e2_pos, *e1_e2_signed, *and1, *and2, * or ;
  int len;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return and_exp (btor, e0, BTOR_INVERT_EXP (e1));
  sign_e1 = slice_exp (btor, e0, len - 1, len - 1);
  sign_e2 = slice_exp (btor, e1, len - 1, len - 1);
  /* rest_e1: e0 without sign bit */
  rest_e1 = slice_exp (btor, e0, len - 2, 0);
  /* rest_e2: e1 without sign bit */
  rest_e2 = slice_exp (btor, e1, len - 2, 0);
  /* ult: is rest of e0 < rest of e1 ? */
  ult = ult_exp (btor, rest_e1, rest_e2);
  /* e1_signed_only: only e0 is negative */
  e1_signed_only = and_exp (btor, sign_e1, BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_pos: e0 and e1 are positive */
  e1_e2_pos =
      and_exp (btor, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_signed: e0 and e1 are negative */
  e1_e2_signed = and_exp (btor, sign_e1, sign_e2);
  and1         = and_exp (btor, e1_e2_pos, ult);
  and2         = and_exp (btor, e1_e2_signed, ult);
  or           = or_exp (btor, and1, and2);
  result       = or_exp (btor, e1_signed_only, or);
  release_exp (btor, sign_e1);
  release_exp (btor, sign_e2);
  release_exp (btor, rest_e1);
  release_exp (btor, rest_e2);
  release_exp (btor, ult);
  release_exp (btor, e1_signed_only);
  release_exp (btor, e1_e2_pos);
  release_exp (btor, e1_e2_signed);
  release_exp (btor, and1);
  release_exp (btor, and2);
  release_exp (btor, or);
  return result;
}

BtorExp *
btor_slt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_slt_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_slt_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_slt_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_slt_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_slt_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_slt_exp'");
  return slt_exp (btor, e0, e1);
}

BtorExp *
btor_ulte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *ugt;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ulte_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ulte_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ulte_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_ulte_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_ulte_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ulte_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  ugt    = ult_exp (btor, e1, e0);
  result = not_exp (btor, ugt);
  release_exp (btor, ugt);
  return result;
}

BtorExp *
btor_slte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sgt;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_slte_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_slte_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_slte_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_slte_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_slte_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_slte_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  sgt    = slt_exp (btor, e1, e0);
  result = not_exp (btor, sgt);
  release_exp (btor, sgt);
  return result;
}

BtorExp *
btor_ugt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ugt_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ugt_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ugt_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_ugt_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_ugt_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ugt_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return ult_exp (btor, e1, e0);
}

BtorExp *
btor_sgt_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sgt_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sgt_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sgt_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sgt_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sgt_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sgt_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return slt_exp (btor, e1, e0);
}

BtorExp *
btor_ugte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *ult;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ugte_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ugte_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ugte_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_ugte_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_ugte_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ugte_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  ult    = ult_exp (btor, e0, e1);
  result = not_exp (btor, ult);
  release_exp (btor, ult);
  return result;
}

BtorExp *
btor_sgte_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *slt;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sgte_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sgte_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sgte_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sgte_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sgte_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sgte_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  slt    = slt_exp (btor, e0, e1);
  result = not_exp (btor, slt);
  release_exp (btor, slt);
  return result;
}

static BtorExp *
sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_SLL_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_SLL_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sll_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sll_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sll_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sll_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sll_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (!btor_is_power_of_2_util (len),
                  "length of 'e0' must be a power of 2 in 'btor_sll_exp'");
  BTOR_ABORT_EXP (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_sll_exp'");
  return sll_exp (btor, e0, e1);
}

static BtorExp *
srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_SRL_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_SRL_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_srl_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_srl_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_srl_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_srl_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_srl_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (!btor_is_power_of_2_util (len),
                  "length of 'e0' must be a power of 2 in 'btor_srl_exp'");
  BTOR_ABORT_EXP (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_srl_exp'");
  return srl_exp (btor, e0, e1);
}

BtorExp *
btor_sra_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *srl1, *srl2;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sra_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sra_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sra_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sra_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sra_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (!btor_is_power_of_2_util (len),
                  "length of 'e0' must be a power of 2 in 'btor_sra_exp'");
  BTOR_ABORT_EXP (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_sra_exp'");
  assert (len > 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  sign_e1 = slice_exp (btor, e0, len - 1, len - 1);
  srl1    = srl_exp (btor, e0, e1);
  srl2    = srl_exp (btor, BTOR_INVERT_EXP (e0), e1);
  result  = cond_exp (btor, sign_e1, BTOR_INVERT_EXP (srl2), srl1);
  release_exp (btor, sign_e1);
  release_exp (btor, srl1);
  release_exp (btor, srl2);
  return result;
}

BtorExp *
btor_rol_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sll, *neg_e2, *srl;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_rol_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_rol_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_rol_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_rol_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_rol_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (!btor_is_power_of_2_util (len),
                  "length of 'e0' must be a power of 2 in 'btor_rol_exp'");
  BTOR_ABORT_EXP (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_rol_exp'");
  assert (len > 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  sll    = sll_exp (btor, e0, e1);
  neg_e2 = neg_exp (btor, e1);
  srl    = srl_exp (btor, e0, neg_e2);
  result = or_exp (btor, sll, srl);
  release_exp (btor, sll);
  release_exp (btor, neg_e2);
  release_exp (btor, srl);
  return result;
}

BtorExp *
btor_ror_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *srl, *neg_e2, *sll;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ror_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ror_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ror_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_ror_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_ror_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (!btor_is_power_of_2_util (len),
                  "length of 'e0' must be a power of 2 in 'btor_ror_exp'");
  BTOR_ABORT_EXP (
      btor_log_2_util (len) != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e1' must be equal to log2(length of 'e0') in 'btor_ror_exp'");
  assert (len > 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  srl    = srl_exp (btor, e0, e1);
  neg_e2 = neg_exp (btor, e1);
  sll    = sll_exp (btor, e0, neg_e2);
  result = or_exp (btor, srl, sll);
  release_exp (btor, srl);
  release_exp (btor, neg_e2);
  release_exp (btor, sll);
  return result;
}

static BtorExp *
sub_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *neg_e2;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  neg_e2 = neg_exp (btor, e1);
  result = add_exp (btor, e0, neg_e2);
  release_exp (btor, neg_e2);
  return result;
}

BtorExp *
btor_sub_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sub_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sub_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sub_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sub_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sub_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sub_exp'");
  return sub_exp (btor, e0, e1);
}

BtorExp *
btor_usubo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *uext_e1, *uext_e2, *add1, *add2, *one;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_usubo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_usubo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_usubo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_usubo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_usubo_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_usubo_exp'");
  assert (len > 0);
  uext_e1 = uext_exp (btor, e0, 1);
  uext_e2 = uext_exp (btor, BTOR_INVERT_EXP (e1), 1);
  assert (len < INT_MAX);
  one    = one_exp (btor, len + 1);
  add1   = add_exp (btor, uext_e2, one);
  add2   = add_exp (btor, uext_e1, add1);
  result = BTOR_INVERT_EXP (slice_exp (btor, add2, len, len));
  release_exp (btor, uext_e1);
  release_exp (btor, uext_e2);
  release_exp (btor, add1);
  release_exp (btor, add2);
  release_exp (btor, one);
  return result;
}

BtorExp *
btor_ssubo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *sign_result;
  BtorExp *sub, *and1, *and2, *or1, *or2;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_ssubo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_ssubo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_ssubo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_ssubo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_ssubo_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_ssubo_exp'");
  assert (len > 0);
  sign_e1     = slice_exp (btor, e0, len - 1, len - 1);
  sign_e2     = slice_exp (btor, e1, len - 1, len - 1);
  sub         = sub_exp (btor, e0, e1);
  sign_result = slice_exp (btor, sub, len - 1, len - 1);
  and1        = and_exp (btor, BTOR_INVERT_EXP (sign_e1), sign_e2);
  or1         = and_exp (btor, and1, sign_result);
  and2        = and_exp (btor, sign_e1, BTOR_INVERT_EXP (sign_e2));
  or2         = and_exp (btor, and2, BTOR_INVERT_EXP (sign_result));
  result      = or_exp (btor, or1, or2);
  release_exp (btor, and1);
  release_exp (btor, and2);
  release_exp (btor, or1);
  release_exp (btor, or2);
  release_exp (btor, sub);
  release_exp (btor, sign_e1);
  release_exp (btor, sign_e2);
  release_exp (btor, sign_result);
  return result;
}

static BtorExp *
udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_UDIV_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_UDIV_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_udiv_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_udiv_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_udiv_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_udiv_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_udiv_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_udiv_exp'");
  return udiv_exp (btor, e0, e1);
}

BtorExp *
btor_sdiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e1, *sign_e2, *xor, *neg_e1, *neg_e2;
  BtorExp *cond_e1, *cond_e2, *udiv, *neg_udiv;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sdiv_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sdiv_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sdiv_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sdiv_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sdiv_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sdiv_exp'");
  assert (len > 0);
  if (len == 1)
    return BTOR_INVERT_EXP (and_exp (btor, BTOR_INVERT_EXP (e0), e1));
  sign_e1 = slice_exp (btor, e0, len - 1, len - 1);
  sign_e2 = slice_exp (btor, e1, len - 1, len - 1);
  /* xor: must result be signed? */
  xor    = xor_exp (btor, sign_e1, sign_e2);
  neg_e1 = neg_exp (btor, e0);
  neg_e2 = neg_exp (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = cond_exp (btor, sign_e1, neg_e1, e0);
  cond_e2  = cond_exp (btor, sign_e2, neg_e2, e1);
  udiv     = udiv_exp (btor, cond_e1, cond_e2);
  neg_udiv = neg_exp (btor, udiv);
  /* sign result if necessary */
  result = cond_exp (btor, xor, neg_udiv, udiv);
  release_exp (btor, sign_e1);
  release_exp (btor, sign_e2);
  release_exp (btor, xor);
  release_exp (btor, neg_e1);
  release_exp (btor, neg_e2);
  release_exp (btor, cond_e1);
  release_exp (btor, cond_e2);
  release_exp (btor, udiv);
  release_exp (btor, neg_udiv);
  return result;
}

BtorExp *
btor_sdivo_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *int_min, *ones, *eq1, *eq2;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sdivo_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_sdivo_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_sdivo_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_sdivo_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_sdivo_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_sdivo_exp'");
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  int_min = int_min_exp (btor, BTOR_REAL_ADDR_EXP (e0)->len);
  ones    = ones_exp (btor, BTOR_REAL_ADDR_EXP (e1)->len);
  eq1     = eq_exp (btor, e0, int_min);
  eq2     = eq_exp (btor, e1, ones);
  result  = and_exp (btor, eq1, eq2);
  release_exp (btor, int_min);
  release_exp (btor, ones);
  release_exp (btor, eq1);
  release_exp (btor, eq2);
  return result;
}

static BtorExp *
urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  result = NULL;
  if (btor->rewrite_level > 0)
    result = rewrite_binary_exp (btor, BTOR_UREM_EXP, e0, e1);
  if (result == NULL)
    result =
        binary_exp (btor, BTOR_UREM_EXP, e0, e1, BTOR_REAL_ADDR_EXP (e0)->len);
  return result;
}

BtorExp *
btor_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_urem_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_urem_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_urem_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_urem_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_urem_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (e0)->len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_urem_exp'");
  return urem_exp (btor, e0, e1);
}

BtorExp *
btor_srem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1;
  BtorExp *cond_e0, *cond_e1, *urem, *neg_urem;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_srem_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_srem_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_srem_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_srem_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_srem_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_srem_exp'");
  assert (len > 0);
  if (len == 1) return and_exp (btor, e0, BTOR_INVERT_EXP (e1));
  sign_e0 = slice_exp (btor, e0, len - 1, len - 1);
  sign_e1 = slice_exp (btor, e1, len - 1, len - 1);
  neg_e0  = neg_exp (btor, e0);
  neg_e1  = neg_exp (btor, e1);
  /* normalize e0 and e1 if necessary */
  cond_e0  = cond_exp (btor, sign_e0, neg_e0, e0);
  cond_e1  = cond_exp (btor, sign_e1, neg_e1, e1);
  urem     = urem_exp (btor, cond_e0, cond_e1);
  neg_urem = neg_exp (btor, urem);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = cond_exp (btor, sign_e0, neg_urem, urem);
  release_exp (btor, sign_e0);
  release_exp (btor, sign_e1);
  release_exp (btor, neg_e0);
  release_exp (btor, neg_e1);
  release_exp (btor, cond_e0);
  release_exp (btor, cond_e1);
  release_exp (btor, urem);
  release_exp (btor, neg_urem);
  return result;
}

BtorExp *
btor_smod_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1, *cond_e0, *cond_e1;
  BtorExp *cond_case1, *cond_case2, *cond_case3, *cond_case4, *urem;
  BtorExp *neg_urem, *add1, *add2, *or1, *or2, *e0_and_e1, *e0_and_neg_e1;
  BtorExp *neg_e0_and_e1, *neg_e0_and_neg_e1, *zero;
  int len;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_smod_exp'");
  BTOR_ABORT_EXP (e0 == NULL, "'e0' must not be NULL in 'btor_smod_exp'");
  BTOR_ABORT_EXP (e1 == NULL, "'e1' must not be NULL in 'btor_smod_exp'");
  e0 = pointer_chase_simplified_exp (btor, e0);
  e1 = pointer_chase_simplified_exp (btor, e1);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)),
                  "'e0' must not be an array in 'btor_smod_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)),
                  "'e1' must not be an array in 'btor_smod_exp'");
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  BTOR_ABORT_EXP (
      len != BTOR_REAL_ADDR_EXP (e1)->len,
      "length of 'e0' and 'e1' must not be unequal in 'btor_smod_exp'");
  assert (len > 0);
  zero    = zero_exp (btor, len);
  sign_e0 = slice_exp (btor, e0, len - 1, len - 1);
  sign_e1 = slice_exp (btor, e1, len - 1, len - 1);
  neg_e0  = neg_exp (btor, e0);
  neg_e1  = neg_exp (btor, e1);
  e0_and_e1 =
      and_exp (btor, BTOR_INVERT_EXP (sign_e0), BTOR_INVERT_EXP (sign_e1));
  e0_and_neg_e1     = and_exp (btor, BTOR_INVERT_EXP (sign_e0), sign_e1);
  neg_e0_and_e1     = and_exp (btor, sign_e0, BTOR_INVERT_EXP (sign_e1));
  neg_e0_and_neg_e1 = and_exp (btor, sign_e0, sign_e1);
  /* normalize e0 and e1 if necessary */
  cond_e0    = cond_exp (btor, sign_e0, neg_e0, e0);
  cond_e1    = cond_exp (btor, sign_e1, neg_e1, e1);
  urem       = urem_exp (btor, cond_e0, cond_e1);
  neg_urem   = neg_exp (btor, urem);
  add1       = add_exp (btor, neg_urem, e1);
  add2       = add_exp (btor, urem, e1);
  cond_case1 = cond_exp (btor, e0_and_e1, urem, zero);
  cond_case2 = cond_exp (btor, neg_e0_and_e1, add1, zero);
  cond_case3 = cond_exp (btor, e0_and_neg_e1, add2, zero);
  cond_case4 = cond_exp (btor, neg_e0_and_neg_e1, neg_urem, zero);
  or1        = or_exp (btor, cond_case1, cond_case2);
  or2        = or_exp (btor, cond_case3, cond_case4);
  result     = or_exp (btor, or1, or2);
  release_exp (btor, zero);
  release_exp (btor, sign_e0);
  release_exp (btor, sign_e1);
  release_exp (btor, neg_e0);
  release_exp (btor, neg_e1);
  release_exp (btor, cond_e0);
  release_exp (btor, cond_e1);
  release_exp (btor, cond_case1);
  release_exp (btor, cond_case2);
  release_exp (btor, cond_case3);
  release_exp (btor, cond_case4);
  release_exp (btor, urem);
  release_exp (btor, neg_urem);
  release_exp (btor, add1);
  release_exp (btor, add2);
  release_exp (btor, or1);
  release_exp (btor, or2);
  release_exp (btor, e0_and_e1);
  release_exp (btor, neg_e0_and_e1);
  release_exp (btor, e0_and_neg_e1);
  release_exp (btor, neg_e0_and_neg_e1);
  return result;
}

/* returns true if exp1 and exp2 present the same constant */
static int
check_equal_const (Btor *btor, BtorExp *exp1, BtorExp *exp2)
{
  int invert_exp1, invert_exp2, result;
  BtorMemMgr *mm;
  assert (btor != NULL);
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  assert (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (exp1)));
  assert (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (exp2)));
  mm = btor->mm;
  if (exp1 == exp2) return 1;
  if ((((unsigned long int) exp1) ^ ((unsigned long int) exp2)) == 1ul)
    return 0;
  assert (BTOR_REAL_ADDR_EXP (exp1) != BTOR_REAL_ADDR_EXP (exp2));
  invert_exp1 = BTOR_IS_INVERTED_EXP (exp1);
  invert_exp2 = BTOR_IS_INVERTED_EXP (exp2);
  if (invert_exp1) btor_invert_const (mm, BTOR_REAL_ADDR_EXP (exp1)->bits);
  if (invert_exp2) btor_invert_const (mm, BTOR_REAL_ADDR_EXP (exp2)->bits);
  result =
      strcmp (BTOR_REAL_ADDR_EXP (exp1)->bits, BTOR_REAL_ADDR_EXP (exp2)->bits)
      == 0;
  /* invert back (if necessary) */
  if (invert_exp1) btor_invert_const (mm, BTOR_REAL_ADDR_EXP (exp1)->bits);
  if (invert_exp2) btor_invert_const (mm, BTOR_REAL_ADDR_EXP (exp2)->bits);
  return result;
}

static BtorExp *
read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BtorExp *real_write_index, *real_read_index, *cur_array, *write_index;
  int propagate_down, propagations;
  BtorMemMgr *mm;
  assert (btor != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  e_array = pointer_chase_simplified_exp (btor, e_array);
  e_index = pointer_chase_simplified_exp (btor, e_index);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (e_array->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  mm = btor->mm;
  if (btor->rewrite_level > 0 && BTOR_IS_WRITE_EXP (e_array))
  {
    write_index = e_array->e[1];
    /* if read index is equal write index, then return write value */
    if (e_index == write_index
        || (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e_index))
            && BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (write_index))
            && check_equal_const (btor, e_index, write_index)))
      return copy_exp (btor, e_array->e[2]);
    /* we need this so x + 0 is rewritten into x */
    assert (btor->rewrite_level > 0);
    real_read_index = BTOR_REAL_ADDR_EXP (e_index);
    cur_array       = e_array;
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    propagations = 0;
    /* ASSUMPTION: constants are UNIQUELY hashed */
    do
    {
      assert (BTOR_IS_WRITE_EXP (cur_array));
      write_index = cur_array->e[1];
      /* indices are equal */
      if (e_index == write_index
          || (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e_index))
              && BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (write_index))
              && check_equal_const (btor, e_index, write_index)))
        return copy_exp (btor, cur_array->e[2]);
      real_write_index = BTOR_REAL_ADDR_EXP (write_index);
      propagate_down   = 0;
      /* constants have to be different here */
      if ((BTOR_IS_CONST_EXP (real_write_index)
           && BTOR_IS_CONST_EXP (real_read_index)))
        propagate_down = 1;
      else if (real_write_index->kind == BTOR_ADD_EXP
               && BTOR_IS_CONST_EXP (
                      BTOR_REAL_ADDR_EXP (real_write_index->e[0]))
               && real_write_index->e[1] == e_index)
        propagate_down = 1;
      else if (real_write_index->kind == BTOR_ADD_EXP
               && BTOR_IS_CONST_EXP (
                      BTOR_REAL_ADDR_EXP (real_write_index->e[1]))
               && real_write_index->e[0] == e_index)
        propagate_down = 1;
      else if (real_read_index->kind == BTOR_ADD_EXP
               && BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (real_read_index->e[0]))
               && real_read_index->e[1] == write_index)
        propagate_down = 1;
      else if (real_read_index->kind == BTOR_ADD_EXP
               && BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (real_read_index->e[1]))
               && real_read_index->e[0] == write_index)
        propagate_down = 1;
      if (propagate_down)
      {
        cur_array = cur_array->e[0];
        assert (BTOR_IS_REGULAR_EXP (cur_array));
        assert (BTOR_IS_ARRAY_EXP (cur_array));
        propagations++;
      }
      else
        break;
    } while (BTOR_IS_WRITE_EXP (cur_array)
             && propagations < BTOR_READ_OVER_WRITE_DOWN_PROPAGATION_LIMIT);
    return binary_exp (btor, BTOR_READ_EXP, cur_array, e_index, cur_array->len);
  }
  return binary_exp (btor, BTOR_READ_EXP, e_array, e_index, e_array->len);
}

BtorExp *
btor_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_read_exp'");
  BTOR_ABORT_EXP (e_array == NULL,
                  "'e_array' must not be NULL in 'btor_read_exp'");
  BTOR_ABORT_EXP (e_index == NULL,
                  "'e_index' must not be NULL in 'btor_read_exp'");
  e_array = pointer_chase_simplified_exp (btor, e_array);
  e_index = pointer_chase_simplified_exp (btor, e_index);
  BTOR_ABORT_EXP (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
                  "'e_array' must not be a bit vector in 'btor_read_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)),
                  "'e_index' must not be an array in 'btor_read_exp'");
  assert (BTOR_IS_REGULAR_EXP (e_array));
  BTOR_ABORT_EXP (e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
                  "index length of 'e_array' and length of 'e_index' must not "
                  "be unequal in 'btor_read_exp'");
  return read_exp (btor, e_array, e_index);
}

static BtorExp *
write_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index, BtorExp *e_value)
{
  assert (btor != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (e_value != NULL);
  e_array = pointer_chase_simplified_exp (btor, e_array);
  e_index = pointer_chase_simplified_exp (btor, e_index);
  e_value = pointer_chase_simplified_exp (btor, e_value);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)));
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->len == BTOR_REAL_ADDR_EXP (e_value)->len);
  assert (BTOR_REAL_ADDR_EXP (e_value)->len > 0);
  /* if array is a write which writes on the same index we can skip it
   * as we overwrite the value anyhow
   */
  if (btor->rewrite_level > 0 && BTOR_IS_WRITE_EXP (e_array)
      && e_array->e[1] == e_index)
    return ternary_exp (
        btor, BTOR_WRITE_EXP, e_array->e[0], e_index, e_value, 0);
  return ternary_exp (btor, BTOR_WRITE_EXP, e_array, e_index, e_value, 0);
}

BtorExp *
btor_write_exp (Btor *btor,
                BtorExp *e_array,
                BtorExp *e_index,
                BtorExp *e_value)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_write_exp'");
  BTOR_ABORT_EXP (e_array == NULL,
                  "'e_array' must not be NULL in 'btor_write_exp'");
  BTOR_ABORT_EXP (e_index == NULL,
                  "'e_index' must not be NULL in 'btor_write_exp'");
  BTOR_ABORT_EXP (e_value == NULL,
                  "'e_value' must not be NULL in 'btor_write_exp'");
  e_array = pointer_chase_simplified_exp (btor, e_array);
  e_index = pointer_chase_simplified_exp (btor, e_index);
  e_value = pointer_chase_simplified_exp (btor, e_value);
  BTOR_ABORT_EXP (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
                  "'e_array' must not be a bit vector in 'btor_write_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)),
                  "'e_index' must not be an array in 'btor_write_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)),
                  "'e_value' must not be a bit vector in 'btor_write_exp'");
  assert (BTOR_IS_REGULAR_EXP (e_array));
  BTOR_ABORT_EXP (e_array->index_len != BTOR_REAL_ADDR_EXP (e_index)->len,
                  "index length of 'e_array' and length of 'e_index' must not "
                  "be unequal in 'btor_write_exp'");
  BTOR_ABORT_EXP (e_array->len != BTOR_REAL_ADDR_EXP (e_value)->len,
                  "element length of 'e_array' and length of 'e_value' must "
                  "not be unequal in 'btor_write_exp'");
  return write_exp (btor, e_array, e_index, e_value);
}

static BtorExp *
rewrite_binary_exp (Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1)
{
  BtorMemMgr *mm;
  BtorExp *result, *real_e0, *real_e1, *temp, *zero, *one;
  BtorExp *ones, *eq, *temp_left, *temp_right;
  BtorExp *(*fptr) (Btor *, BtorExp *, BtorExp *);
  char *b0, *b1, *bresult;
  int same_children_mem, is_zero, is_one, is_ones;
  int invert_b0 = 0;
  int invert_b1 = 0;
  assert (btor != NULL);
  assert (btor->rewrite_level > 0);
  assert (btor->rewrite_level <= 2);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  mm      = btor->mm;
  result  = NULL;
  e0      = pointer_chase_simplified_exp (btor, e0);
  e1      = pointer_chase_simplified_exp (btor, e1);
  real_e0 = BTOR_REAL_ADDR_EXP (e0);
  real_e1 = BTOR_REAL_ADDR_EXP (e1);
  if (BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
  {
    same_children_mem = real_e0 == real_e1;
    if (same_children_mem)
    {
      b0 = BTOR_BITS_EXP (mm, e0);
      b1 = BTOR_BITS_EXP (mm, e1);
    }
    else
    {
      invert_b0 = BTOR_IS_INVERTED_EXP (e0);
      b0        = real_e0->bits;
      if (invert_b0) btor_invert_const (mm, b0);
      invert_b1 = BTOR_IS_INVERTED_EXP (e1);
      b1        = real_e1->bits;
      if (invert_b1) btor_invert_const (mm, b1);
    }
    switch (kind)
    {
      case BTOR_AND_EXP: bresult = btor_and_const (mm, b0, b1); break;
      case BTOR_BEQ_EXP: bresult = btor_eq_const (mm, b0, b1); break;
      case BTOR_ADD_EXP: bresult = btor_add_const (mm, b0, b1); break;
      case BTOR_MUL_EXP: bresult = btor_mul_const (mm, b0, b1); break;
      case BTOR_ULT_EXP: bresult = btor_ult_const (mm, b0, b1); break;
      case BTOR_UDIV_EXP: bresult = btor_udiv_const (mm, b0, b1); break;
      case BTOR_UREM_EXP: bresult = btor_urem_const (mm, b0, b1); break;
      case BTOR_SLL_EXP: bresult = btor_sll_const (mm, b0, b1); break;
      case BTOR_SRL_EXP: bresult = btor_srl_const (mm, b0, b1); break;
      default:
        assert (kind == BTOR_CONCAT_EXP);
        bresult = btor_concat_const (mm, b0, b1);
        break;
    }
    if (same_children_mem)
    {
      btor_delete_const (mm, b1);
      btor_delete_const (mm, b0);
    }
    else
    {
      /* invert back if necessary */
      if (invert_b0) btor_invert_const (mm, b0);
      if (invert_b1) btor_invert_const (mm, b1);
    }
    result = const_exp (btor, bresult);
    btor_delete_const (mm, bresult);
  }
  else if (BTOR_IS_CONST_EXP (real_e0) && !BTOR_IS_CONST_EXP (real_e1))
  {
    invert_b0 = BTOR_IS_INVERTED_EXP (e0);
    b0        = real_e0->bits;
    if (invert_b0) btor_invert_const (mm, b0);
    is_zero = is_zero_string (btor, b0, real_e0->len);
    is_one  = is_one_string (btor, b0, real_e0->len);
    is_ones = is_ones_string (btor, b0, real_e0->len);
    /* invert back if necessary */
    if (invert_b0) btor_invert_const (mm, b0);
    if (is_zero)
    {
      if (kind == BTOR_BEQ_EXP && real_e0->len == 1)
        result = not_exp (btor, e1);
      if (kind == BTOR_ADD_EXP)
        result = copy_exp (btor, e1);
      else if (kind == BTOR_MUL_EXP || kind == BTOR_SLL_EXP
               || kind == BTOR_SRL_EXP || kind == BTOR_UREM_EXP
               || kind == BTOR_AND_EXP)
        result = zero_exp (btor, real_e0->len);
      else if (kind == BTOR_UDIV_EXP)
      {
        zero   = zero_exp (btor, real_e0->len);
        ones   = ones_exp (btor, real_e0->len);
        eq     = eq_exp (btor, e1, zero);
        result = cond_exp (btor, eq, ones, zero);
        release_exp (btor, zero);
        release_exp (btor, eq);
        release_exp (btor, ones);
      }
    }
    else if (is_one && is_ones)
    {
      assert (real_e0->len == 1);
      if (kind == BTOR_AND_EXP || kind == BTOR_BEQ_EXP || kind == BTOR_MUL_EXP)
        result = copy_exp (btor, e1);
      else if (kind == BTOR_ULT_EXP)
        result = false_exp (btor);
    }
    else if (is_one)
    {
      if (kind == BTOR_MUL_EXP) result = copy_exp (btor, e1);
    }
    else if (is_ones)
    {
      if (kind == BTOR_AND_EXP)
        result = copy_exp (btor, e1);
      else if (kind == BTOR_ULT_EXP) /* UNSIGNED_MAX < x */
        result = false_exp (btor);
    }

    /* TODO: handle all 'result->len == 1' cases */
  }
  else if (!BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
  {
    invert_b1 = BTOR_IS_INVERTED_EXP (e1);
    b1        = real_e1->bits;
    if (invert_b1) btor_invert_const (mm, b1);
    is_zero = is_zero_string (btor, b1, real_e1->len);
    is_one  = is_one_string (btor, b1, real_e1->len);
    is_ones = is_ones_string (btor, b1, real_e1->len);
    /* invert back if necessary */
    if (invert_b1) btor_invert_const (mm, b1);
    if (is_zero)
    {
      if (kind == BTOR_BEQ_EXP && real_e0->len == 1)
        result = not_exp (btor, e0);
      else if (kind == BTOR_SLL_EXP || kind == BTOR_SRL_EXP
               || kind == BTOR_UREM_EXP || kind == BTOR_ADD_EXP)
        result = copy_exp (btor, e0);
      else if (kind == BTOR_MUL_EXP || kind == BTOR_AND_EXP)
        result = zero_exp (btor, real_e0->len);
      else if (kind == BTOR_ULT_EXP) /* x < 0 */
        result = false_exp (btor);
      else if (kind == BTOR_UDIV_EXP)
        result = ones_exp (btor, real_e0->len);
    }
    else if (is_one && is_ones)
    {
      assert (real_e1->len == 1);
      if (kind == BTOR_AND_EXP || kind == BTOR_BEQ_EXP || kind == BTOR_MUL_EXP
          || kind == BTOR_UDIV_EXP)
        result = copy_exp (btor, e0);
    }
    else if (is_one)
    {
      if (kind == BTOR_MUL_EXP || kind == BTOR_UDIV_EXP)
        result = copy_exp (btor, e0);
      else if (kind == BTOR_ULT_EXP)
      {
        temp = zero_exp (btor, real_e0->len);
        /* ATTENTION: indirect recursive call make sure
         * it does not trigger another recurisve calls */
        result = eq_exp (btor, e0, temp);
        release_exp (btor, temp);
      }
    }
    else if (is_ones)
    {
      if (kind == BTOR_AND_EXP)
        result = copy_exp (btor, e0);
      else if (kind == BTOR_ULT_EXP)
        /* ATTENTION: indirect recursive call make sure
         * it does not trigger another recurisve calls */
        result = BTOR_INVERT_EXP (eq_exp (btor, e0, e1));
    }

    /* TODO: handle all 'result->len == 1' cases */
  }
  else if (real_e0 == real_e1
           && (kind == BTOR_BEQ_EXP || kind == BTOR_AEQ_EXP
               || kind == BTOR_ADD_EXP))
  {
    if (kind == BTOR_BEQ_EXP)
    {
      if (e0 == e1)
        result = true_exp (btor); /* x == x */
      else
        result = false_exp (btor); /* x == ~x */
    }
    else if (kind == BTOR_AEQ_EXP)
    {
      /* arrays must not be negated */
      assert (e0 == e1);
      result = true_exp (btor); /* x == x */
    }
    else
    {
      assert (kind == BTOR_ADD_EXP);
      /* replace x + x by x * 2 */
      if (e0 == e1)
      {
        if (real_e0->len >= 2)
        {
          temp   = btor_int_to_exp (btor, 2, real_e0->len);
          result = mul_exp (btor, e0, temp);
          release_exp (btor, temp);
        }
      }
      else
        /* replace x + ~x by -1 */
        result = ones_exp (btor, real_e0->len);
    }

    /* TODO: handle all 'result->len == 1' cases */
  }
  else if (e0 == e1
           && (kind == BTOR_ULT_EXP || kind == BTOR_UREM_EXP
               || kind == BTOR_UDIV_EXP))
  {
    switch (kind)
    {
      case BTOR_ULT_EXP:
        result = false_exp (btor);
        break;
        /* v / v is 1 if v != 0 and UINT_MAX otherwise */
      case BTOR_UDIV_EXP:
        zero   = zero_exp (btor, real_e0->len);
        one    = one_exp (btor, real_e0->len);
        ones   = ones_exp (btor, real_e0->len);
        eq     = eq_exp (btor, e0, zero);
        result = cond_exp (btor, eq, ones, one);
        release_exp (btor, zero);
        release_exp (btor, eq);
        release_exp (btor, ones);
        release_exp (btor, one);
        break;
      default:
        assert (kind == BTOR_UREM_EXP);
        result = zero_exp (btor, real_e0->len);
        break;
    }

    /* TODO: handle all 'result->len == 1' cases */
  }
  else if (BTOR_IS_ARRAY_OR_BV_COND_EXP (real_e0)
           && BTOR_IS_ARRAY_OR_BV_COND_EXP (real_e1)
           && BTOR_IS_INVERTED_EXP (e0) == BTOR_IS_INVERTED_EXP (e1)
           && real_e0->e[0] == real_e1->e[0]
           && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2])
           && (kind == BTOR_ULT_EXP || kind == BTOR_BEQ_EXP
               || kind == BTOR_AEQ_EXP || kind == BTOR_ADD_EXP
               || kind == BTOR_UDIV_EXP))
  {
    switch (kind)
    {
      case BTOR_ULT_EXP: fptr = ult_exp; break;
      case BTOR_BEQ_EXP:
      case BTOR_AEQ_EXP: fptr = eq_exp; break;
      case BTOR_ADD_EXP: fptr = add_exp; break;
      default:
        assert (kind == BTOR_UDIV_EXP);
        fptr = udiv_exp;
        break;
    }
    temp_left  = fptr (btor,
                      BTOR_COND_INVERT_EXP (e0, real_e0->e[1]),
                      BTOR_COND_INVERT_EXP (e0, real_e1->e[1]));
    temp_right = fptr (btor,
                       BTOR_COND_INVERT_EXP (e0, real_e0->e[2]),
                       BTOR_COND_INVERT_EXP (e0, real_e1->e[2]));
    result     = cond_exp (btor, real_e0->e[0], temp_left, temp_right);
    release_exp (btor, temp_left);
    release_exp (btor, temp_right);
  }
  else
  {
    /* TODO: handle all 'result->len == 1' cases */
  }

  /* TODO: lots of word level simplifications:
   * a[7:4] == b[7:4] && a[3:0] == b[3:0] <=> a == b
   * {a,b} == {c,d} with |a|=|c| <=> a == c && b == d
   * ...
   */
  /* TODO a + 2 * a <=> 3 * a <=> and see below */
  /* TODO strength reduction: a * 2 == a << 1 (really ?) */
  /* TODO strength reduction: a * 3 == (a << 1) + a (really ?) */
  /* TODO strength reduction: a / 2 == (a >> 1) (yes!) */
  /* TODO strength reduction: a / 3 =>  higher bits zero (check!) */
  /* TODO 0 < a <=> a != 0 */
  /* TODO a < 1 <=> a == 0 */
  /* TODO MAX-1 < a <=> a == MAX */
  /* TODO a < MAX <=> a != MAX */

  /* TODO (x < ~x) <=> !msb(x) */
  /* TODO (~x < x) <=> msb(x) */

  /* TODO associativity of multiplication (always?) or normalize */
  /* TODO associativity of addition up to a certain level or normalize */

  /* TODO to support GAUSS bubble up odd terms:
   * (2 * a + 3 * y) + 4 * x => 3 * y + (2 * a + 4 * x)
   * or alternatively normalize arithmetic terms/polynomials
   * or simply always replace by equation.
   */

  /* TODO simplify (c * x + 2 * y) + x == 5 at GAUSS application
   * by first (c + 1) * x + 2 * y == 5 and then check whether 'c'
   * is even.
   */

  /* TODO Howto handle 2 * x == 4 && 4 * x + 8 * y == 0 ?
   * Maybe: x[30:0] == 2 && 4 * {x[31],2[30:0]} + 8 * y == 0?
   * Then: x[30:0] == 2 && 8[31:0] + 8 *y == 0?
   * Then: x[30:0] = 2 && 8 * y = -8
   * Finally:  x[30:0] = 2 && y[29:0] = -1
   * etc.
   */
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
  do
  {
    cur = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur));

    if (cur->mark == 2) continue;

    if (cur->mark == 0)
    {
      if (BTOR_IS_CONST_EXP (cur))
      {
        btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
            btor_copy_exp (btor, cur);
        cur->mark = 2;
      }
      else if (BTOR_IS_VAR_EXP (cur) || BTOR_IS_ATOMIC_ARRAY_EXP (cur))
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
            if (BTOR_IS_VAR_EXP (cur))
            {
              assert (cur->symbol != NULL);
              var_name_len =
                  strlen (cur->symbol) + btor_num_digits_util (k) + 2;
              BTOR_NEWN (mm, var_name, var_name_len);
              sprintf (var_name, "%s_%d", cur->symbol, k);
              var = var_exp (btor, cur->len, var_name);
              BTOR_DELETEN (mm, var_name, var_name_len);
            }
            else
            {
              assert (BTOR_IS_ATOMIC_ARRAY_EXP (cur));
              var = array_exp (btor, cur->len, cur->index_len);
            }
            btor_insert_in_ptr_hash_table (input_table, cur)->data.asPtr = var;
            btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
                copy_exp (btor, var);
          }
          else
          {
            assert (bucket->data.asPtr != NULL);
            btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
                copy_exp (btor, (BtorExp *) bucket->data.asPtr);
          }
        }
        else
        {
          assert (bucket->data.asPtr != NULL);
          btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr =
              copy_exp (btor, (BtorExp *) bucket->data.asPtr);
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
      assert (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_CONST_EXP (cur)
              && !BTOR_IS_ATOMIC_ARRAY_EXP (cur));
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
          cur_result = slice_exp (btor, e0, cur->upper, cur->lower);
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
            case BTOR_AND_EXP: bin_func = and_exp; break;
            case BTOR_BEQ_EXP:
            case BTOR_AEQ_EXP: bin_func = eq_exp; break;
            case BTOR_ADD_EXP: bin_func = add_exp; break;
            case BTOR_MUL_EXP: bin_func = mul_exp; break;
            case BTOR_ULT_EXP: bin_func = ult_exp; break;
            case BTOR_SLL_EXP: bin_func = sll_exp; break;
            case BTOR_SRL_EXP: bin_func = srl_exp; break;
            case BTOR_UDIV_EXP: bin_func = udiv_exp; break;
            case BTOR_UREM_EXP: bin_func = urem_exp; break;
            case BTOR_CONCAT_EXP: bin_func = concat_exp; break;
            default:
              assert (BTOR_IS_READ_EXP (cur));
              bin_func = read_exp;
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
          /* condtionals are normalized */
          assert (!BTOR_IS_INVERTED_EXP (cur->e[0]));
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
            cur_result = write_exp (btor, e0, e1, e2);
          else
          {
            assert (cur->kind == BTOR_BCOND_EXP || cur->kind == BTOR_ACOND_EXP);
            cur_result = cond_exp (btor, e0, e1, e2);
          }
          break;
      }
      btor_insert_in_ptr_hash_table (build_table, cur)->data.asPtr = cur_result;
      cur->mark                                                    = 2;
    }
  } while (!BTOR_EMPTY_STACK (stack));
  btor_mark_exp (btor, root, 0);

  bucket = btor_find_in_ptr_hash_table (build_table, BTOR_REAL_ADDR_EXP (root));
  assert (bucket != NULL);
  assert (bucket->data.asPtr != NULL);
  result = copy_exp (btor, (BtorExp *) bucket->data.asPtr);

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
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_inc_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_inc_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'e0' must not be an array in 'btor_inc_exp'");
  one    = one_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = add_exp (btor, exp, one);
  release_exp (btor, one);
  return result;
}

BtorExp *
btor_dec_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *one, *result;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_dec_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_dec_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'e0' must not be an array in 'btor_dec_exp'");
  one    = one_exp (btor, BTOR_REAL_ADDR_EXP (exp)->len);
  result = sub_exp (btor, exp, one);
  release_exp (btor, one);
  return result;
}

int
btor_get_exp_len (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_get_exp_len'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_get_exp_len'");
  exp = pointer_chase_simplified_exp (btor, exp);
  (void) btor;
  return BTOR_REAL_ADDR_EXP (exp)->len;
}

int
btor_is_array_exp (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_is_array_exp'");
  BTOR_ABORT_EXP (exp == NULL, "'exp' must not be NULL in 'btor_is_array_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  (void) btor;
  return BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp));
}

int
btor_get_index_exp_len (Btor *btor, BtorExp *e_array)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_get_index_exp_len'");
  BTOR_ABORT_EXP (e_array == NULL,
                  "'e_array' must not be NULL in 'btor_get_index_exp_len'");
  e_array = pointer_chase_simplified_exp (btor, e_array);
  BTOR_ABORT_EXP (
      !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_array)),
      "'e_array' must not be a bit vector in 'btor_get_index_exp_len'");
  assert (BTOR_IS_REGULAR_EXP (e_array));
  (void) btor;
  return e_array->index_len;
}

char *
btor_get_symbol_exp (Btor *btor, BtorExp *exp)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_get_symbol_exp'");
  BTOR_ABORT_EXP (exp == NULL,
                  "'exp' must not be NULL in 'btor_get_symbol_exp'");
  BTOR_ABORT_EXP (
      btor->rewrite_level > 1,
      "rewrite level must not be greater than 1 in 'btor_get_symbol_exp'");
  assert (!BTOR_IS_PROXY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  BTOR_ABORT_EXP (!BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' has to be a variable in 'btor_get_symbol_exp'");
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

    if (BTOR_IS_PROXY_EXP (e))
    {
      assert (e->simplified);
      BTOR_PUSH_EXP_IF_NOT_MARKED (e->simplified);
    }
    else
    {
#ifndef NPROXY
      assert (!e->simplified);
#endif
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

        if (BTOR_IS_PROXY_EXP (e))
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

      case BTOR_ARRAY_EXP:
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

      case BTOR_CONST_EXP:
        fprintf (file, "const %d %s", e->len, e->bits);
        break;

      default:
      case BTOR_VAR_EXP:
        assert (e->kind == BTOR_VAR_EXP);
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
  int i;
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_dump_exps'");
  BTOR_ABORT_EXP (file == NULL, "'file' must not be NULL in 'btor_dump_exps'");
  BTOR_ABORT_EXP (roots == NULL,
                  "'roots' must not be NULL in 'btor_dump_exps'");
  BTOR_ABORT_EXP (nroots < 1,
                  "There must be at least one root in 'btor_dump_exps'");
  for (i = 0; i < nroots; i++)
  {
    BTOR_ABORT_EXP (roots[i] == NULL,
                    "Root must not be NULL in 'btor_dump_exps'");
  }
  dump_exps (btor, file, roots, nroots);
}

void
btor_dump_exps_after_substitution (Btor *btor,
                                   FILE *file,
                                   BtorExp **roots,
                                   int nroots)
{
  BtorExp *temp, **new_roots;
  BtorPtrHashBucket *b;
  BtorPtrHashTable *constraints;
  int new_nroots, i;
  for (i = 0; i < nroots; i++)
  {
    if (BTOR_REAL_ADDR_EXP (roots[i])->len == 1)
      temp = copy_exp (btor, roots[i]);
    else
      temp = btor_redor_exp (btor, roots[i]);
    add_constraint (btor, temp);
    release_exp (btor, temp);
  }
  process_new_constraints (btor);
  constraints = btor->processed_constraints;
  new_nroots  = (int) constraints->count;
  BTOR_NEWN (btor->mm, new_roots, new_nroots);
  i = 0;
  for (b = constraints->first; b != NULL; b = b->next)
    new_roots[i++] = (BtorExp *) b->key;
  dump_exps (btor, file, new_roots, new_nroots);
  BTOR_DELETEN (btor->mm, new_roots, new_nroots);
}

static void
dump_exp (Btor *btor, FILE *file, BtorExp *root)
{
  assert (btor != NULL);
  assert (file != NULL);
  assert (root != NULL);
  dump_exps (btor, file, &root, 1);
}

void
btor_dump_exp (Btor *btor, FILE *file, BtorExp *root)
{
  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_dump_exp'");
  BTOR_ABORT_EXP (file == NULL, "'file' must not be NULL in 'btor_dump_exp'");
  BTOR_ABORT_EXP (root == NULL, "'root' must not be NULL in 'btor_dump_exp'");
  dump_exp (btor, file, root);
}

void
btor_vis_exp (Btor *btor, BtorExp *exp)
{
  char cmd[100], *path;
  static int idx = 0;
  FILE *file;
  sprintf (cmd, "btorvis ");
  path = cmd + strlen (cmd);
  sprintf (path, "/tmp/btorvisexp.%d.btor", idx++);
  file = fopen (path, "w");
  dump_exp (btor, file, exp);
  fclose (file);
  strcat (cmd, "&");
  system (cmd);
}

static void
btor_dump_smt_id (BtorExp *e, FILE *file)
{
  const char *type, *sym;
  BtorExp *u;

  u = BTOR_REAL_ADDR_EXP (e);

  if (u != e) fputs ("(bvnot ", file);

  if (BTOR_IS_VAR_EXP (u))
  {
    sym = u->symbol;
    if (!isdigit (sym[0]))
    {
      fputs (sym, file);
      goto CLOSE;
    }

    type = "v";
  }
  else if (BTOR_IS_ATOMIC_ARRAY_EXP (u))
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

  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_smt_exp'");
  BTOR_ABORT_EXP (file == NULL, "'file' must not be NULL in 'btor_smt_exp'");
  BTOR_ABORT_EXP (root == NULL, "'root' must not be NULL in 'btor_smt_exp'");

  BTOR_INIT_STACK (stack);
  BTOR_PUSH_EXP_IF_NOT_MARKED (root);

  arrays = 0;
  next   = 0;

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_EXP (e));
    assert (e->mark);

    if (BTOR_IS_CONST_EXP (e)) continue;

    if (BTOR_IS_VAR_EXP (e)) continue;

    if (BTOR_IS_ATOMIC_ARRAY_EXP (e))
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

    if (!BTOR_IS_VAR_EXP (e) && !BTOR_IS_ATOMIC_ARRAY_EXP (e)) continue;

    fputs (":extrafuns ((", file);
    btor_dump_smt_id (e, file);

    if (BTOR_IS_VAR_EXP (e))
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

    if (BTOR_IS_VAR_EXP (e) || BTOR_IS_ATOMIC_ARRAY_EXP (e)) continue;

    lets++;

    fputs ("(let (", file);
    btor_dump_smt_id (e, file);
    fputc (' ', file);

    if (e->kind == BTOR_CONST_EXP)
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
  btor->avmgr                      = btor_new_aigvec_mgr (mm);
  btor->arrays                     = btor_new_ptr_hash_table (mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  btor->id                         = 1;
  btor->valid_assignments          = 1;
  btor->rewrite_level              = 2;
  btor->vread_index_id             = 1;
  btor->exp_pair_cnf_diff_id_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  btor->exp_pair_cnf_eq_id_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  btor->new_constraints =
      btor_new_ptr_hash_table (mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
  btor->processed_constraints =
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
  BTOR_INIT_STACK (btor->replay_constraints);
  return btor;
}

void
btor_set_rewrite_level_btor (Btor *btor, int rewrite_level)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_set_rewrite_level_btor'");
  BTOR_ABORT_EXP (
      rewrite_level < 0 || rewrite_level > 2,
      "'rewrite_level' has to be in [0,2] in 'btor_set_rewrite_level_btor'");
  BTOR_ABORT_EXP (
      btor->id != 1,
      "setting rewrite level must be done before adding expressions");
  btor->rewrite_level = rewrite_level;
}

void
btor_set_replay_btor (Btor *btor, int replay)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_set_replay_btor'");
  BTOR_ABORT_EXP (
      btor->new_constraints->count + btor->processed_constraints->count
              + btor->synthesized_constraints->count + btor->assumptions->count
          > 0u,
      "setting replay must be done before add constraints and assumptions");
  btor->replay = replay;
}

void
btor_set_verbosity_btor (Btor *btor, int verbosity)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_set_verbosity_btor'");
  BTOR_ABORT_EXP (
      verbosity < -1 || verbosity > 3,
      "'verbosity' has to be in [-1,3] in 'btor_set_verbosity_btor'");
  BTOR_ABORT_EXP (btor->id != 1,
                  "'setting verbosity must be done before adding expressions'");
  btor->verbosity = verbosity;
  avmgr           = btor->avmgr;
  amgr            = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr            = btor_get_sat_mgr_aig_mgr (amgr);
  btor_set_verbosity_aigvec_mgr (avmgr, verbosity);
  btor_set_verbosity_aig_mgr (amgr, verbosity);
  btor_set_verbosity_sat_mgr (smgr, verbosity);
}

void
btor_delete_btor (Btor *btor)
{
  BtorMemMgr *mm;
  BtorPtrHashBucket *bucket;
  int i;
  assert (btor != NULL);
  mm = btor->mm;

  for (bucket = btor->exp_pair_cnf_diff_id_table->first; bucket != NULL;
       bucket = bucket->next)
    delete_exp_pair (btor, (BtorExpPair *) bucket->key);
  btor_delete_ptr_hash_table (btor->exp_pair_cnf_diff_id_table);

  for (bucket = btor->exp_pair_cnf_eq_id_table->first; bucket != NULL;
       bucket = bucket->next)
    delete_exp_pair (btor, (BtorExpPair *) bucket->key);
  btor_delete_ptr_hash_table (btor->exp_pair_cnf_eq_id_table);

  /* delete constraints and assumptions */

  for (bucket = btor->new_constraints->first; bucket != NULL;
       bucket = bucket->next)
    release_exp (btor, (BtorExp *) bucket->key);
  btor_delete_ptr_hash_table (btor->new_constraints);

  for (bucket = btor->processed_constraints->first; bucket != NULL;
       bucket = bucket->next)
    release_exp (btor, (BtorExp *) bucket->key);
  btor_delete_ptr_hash_table (btor->processed_constraints);

  for (bucket = btor->synthesized_constraints->first; bucket != NULL;
       bucket = bucket->next)
    release_exp (btor, (BtorExp *) bucket->key);
  btor_delete_ptr_hash_table (btor->synthesized_constraints);

  for (bucket = btor->assumptions->first; bucket != NULL; bucket = bucket->next)
    release_exp (btor, (BtorExp *) bucket->key);
  btor_delete_ptr_hash_table (btor->assumptions);

  for (i = 0; i < BTOR_COUNT_STACK (btor->replay_constraints); i++)
    btor_release_exp (btor, btor->replay_constraints.start[i]);
  BTOR_RELEASE_STACK (mm, btor->replay_constraints);

  assert (btor->table.num_elements == 0);
  BTOR_RELEASE_EXP_UNIQUE_TABLE (mm, btor->table);
  btor_delete_ptr_hash_table (btor->arrays);
  btor_delete_aigvec_mgr (btor->avmgr);
  BTOR_DELETE (mm, btor);
  btor_delete_mem_mgr (mm);
}

static int
constraints_stats_changes (Btor *btor)
{
  int res;

  if (btor->stats.old.constraints.added && !btor->new_constraints->count)
    return INT_MAX;

  if (btor->stats.old.constraints.processed
      && !btor->processed_constraints->count)
    return INT_MAX;

  res = abs (btor->stats.old.constraints.added - btor->new_constraints->count);

  res += abs (btor->stats.old.constraints.processed
              - btor->processed_constraints->count);

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

    if (btor->verbosity == 1 && changes < 1000) return;

    if (btor->verbosity == 2 && changes < 100) return;

    if (btor->verbosity == 3 && changes < 10) return;
  }

  print_verbose_msg ("%d/%d/%d constraints %d/%d/%d %.1f MB",
                     btor->stats.constraints.added,
                     btor->stats.constraints.processed,
                     btor->stats.constraints.synthesized,
                     btor->new_constraints->count,
                     btor->processed_constraints->count,
                     btor->synthesized_constraints->count,
                     btor->mm->allocated / (double) (1 << 20));

  btor->stats.old.constraints.added     = btor->new_constraints->count;
  btor->stats.old.constraints.processed = btor->processed_constraints->count;
  btor->stats.old.constraints.synthesized =
      btor->synthesized_constraints->count;
}

void
btor_print_stats_btor (Btor *btor)
{
  assert (btor != NULL);
  (void) btor;
  report_constraint_stats (btor, 1);
  print_verbose_msg ("number of expressions: %lld", btor->stats.expressions);
  print_verbose_msg ("variable substitutions: %d",
                     btor->stats.var_substitutions);
  print_verbose_msg ("array substitutions: %d",
                     btor->stats.array_substitutions);
  print_verbose_msg ("array equalites: %s",
                     btor->has_array_equalities ? "yes" : "no");
  print_verbose_msg ("assumptions: %u", btor->assumptions->count);
  print_verbose_msg ("refinement iterations: %d", btor->stats.refinements);
  print_verbose_msg ("read-read conflicts: %d",
                     btor->stats.read_read_conflicts);
  print_verbose_msg ("read-write conflicts: %d",
                     btor->stats.read_write_conflicts);
  print_verbose_msg (
      "average lemma size: %.1f",
      BTOR_AVERAGE_EXP (btor->stats.lemmas_size_sum, btor->stats.refinements));
  print_verbose_msg (
      "average linking clause size: %.1f",
      BTOR_AVERAGE_EXP (btor->stats.lclause_size_sum, btor->stats.refinements));
  print_verbose_msg ("linear constraint equations: %d",
                     btor->stats.linear_equations);
  print_verbose_msg ("virtual reads: %d", btor->stats.vreads);
  print_verbose_msg ("synthesis assignment inconsistencies: %d",
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
  BtorExp *result;
  assert (btor != NULL);
  assert (len > 0);
  BTOR_ABORT_EXP (btor->id == INT_MAX, "vread index id overflow");
  symbol = (char *) malloc (
      sizeof (char) * (6 + btor_num_digits_util (btor->vread_index_id) + 1));
  sprintf (symbol, "vindex%d", btor->vread_index_id);
  btor->vread_index_id++;
  result = var_exp (btor, len, symbol);
  free (symbol);
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
  index = vread_index_exp (btor, aeq->e[0]->index_len);

  /* we do not want read optimizations for the virtual
   * reads (e.g. rewriting of reads on array conditionals),
   * so we call binary_exp directly
   */
  read1 = binary_exp (btor, BTOR_READ_EXP, aeq->e[0], index, aeq->e[0]->len);
  read2 = binary_exp (btor, BTOR_READ_EXP, aeq->e[1], index, aeq->e[1]->len);

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

  release_exp (btor, index);
  release_exp (btor, read1);
  release_exp (btor, read2);
}

static void
set_flags_and_synth_aeq (Btor *btor, BtorExp *exp)
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
        case 0: break;
        case 1: BTOR_PUSH_STACK (mm, stack, cur->e[0]); break;
        case 2:
          if (BTOR_IS_ARRAY_EQ_EXP (cur))
          {
            btor->has_array_equalities = 1;
            synthesize_array_equality (btor, cur);
          }
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
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);
}

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

  mm    = btor->mm;
  avmgr = btor->avmgr;
  count = 0;

  BTOR_INIT_STACK (exp_stack);
  BTOR_PUSH_STACK (mm, exp_stack, exp);
  do
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (exp_stack));
    assert (cur->mark >= 0);
    assert (cur->mark <= 2);
    if (!BTOR_IS_SYNTH_EXP (cur) && cur->mark < 2)
    {
      count++;

      if (cur->mark == 0)
      {
        cur->reachable = 1;
        if (BTOR_IS_CONST_EXP (cur))
          cur->av = btor_const_aigvec (avmgr, cur->bits);
        else if (BTOR_IS_VAR_EXP (cur))
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
        else if (!BTOR_IS_ATOMIC_ARRAY_EXP (cur))
        {
          /* special cases */
          if (BTOR_IS_READ_EXP (cur))
          {
            cur->av = btor_var_aigvec (avmgr, cur->len);
            assert (BTOR_IS_REGULAR_EXP (cur->e[0]));
            assert (BTOR_IS_ARRAY_EXP (cur->e[0]));
            /* mark children recursively as reachable */
            set_flags_and_synth_aeq (btor, cur->e[1]);
            set_flags_and_synth_aeq (btor, cur->e[0]);
          }
          else if (BTOR_IS_WRITE_EXP (cur))
          {
            /* set mark flag to explicitly to 2
             * as write has no AIG vector */
            cur->mark = 2;
            /* mark children recursively as reachable */
            set_flags_and_synth_aeq (btor, cur->e[2]);
            set_flags_and_synth_aeq (btor, cur->e[1]);
            set_flags_and_synth_aeq (btor, cur->e[0]);
          }
          else if (BTOR_IS_ARRAY_EQ_EXP (cur))
          {
            btor->has_array_equalities = 1;
            /* generate virtual reads and create AIG
             * variable for array equality */
            synthesize_array_equality (btor, cur);
            /* mark children recursively as reachable */
            set_flags_and_synth_aeq (btor, cur->e[1]);
            set_flags_and_synth_aeq (btor, cur->e[0]);
          }
          else
          {
            /* regular cases */
            cur->mark = 1;
            BTOR_PUSH_STACK (mm, exp_stack, cur);
            for (i = cur->arity - 1; i >= 0; i--)
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[i]);
          }
        }
      }
      else
      {
        assert (cur->mark == 1);
        cur->mark = 2;
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
                /* conditionals are normalized */
                assert (!BTOR_IS_INVERTED_EXP (cur->e[0]));
                av0        = BTOR_REAL_ADDR_EXP (cur->e[0])->av;
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
                if (invert_av1) btor_invert_aigvec (avmgr, av1);
                if (invert_av2) btor_invert_aigvec (avmgr, av2);
              }
            }
            break;
        }
      }
    }
  } while (!BTOR_EMPTY_STACK (exp_stack));

  BTOR_RELEASE_STACK (mm, exp_stack);
  btor_mark_exp (btor, exp, 0);

  if (count > 0 && btor->verbosity > 2)
    print_verbose_msg ("synthesized %u expressions into AIG vectors", count);
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
  found                = 0;
  has_array_equalities = btor->has_array_equalities;
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
      cond = cur->e[0];
      /* conditionals are normalized */
      assert (!BTOR_IS_INVERTED_EXP (cond));
      assignment = btor_get_assignment_aig (amgr, cond->av->aigs[0]);
      assert (assignment == 1 || assignment == -1);
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
        if (next->reachable && next->mark == 0)
        {
          cond = next->e[0];
          /* conditionals are normalized */
          assert (!BTOR_IS_INVERTED_EXP (cond));
          assignment = btor_get_assignment_aig (amgr, cond->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
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
  BtorExpPtrStack writes, aeqs, aconds_sel1, aconds_sel2;
  BtorExp *cur, *cond, *prev;
  BtorMemMgr *mm;
  BtorAIGMgr *amgr;
  int assignment;
  BtorPtrHashTable *table;
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
  BTOR_INIT_STACK (writes);
  BTOR_INIT_STACK (aeqs);
  BTOR_INIT_STACK (aconds_sel1);
  BTOR_INIT_STACK (aconds_sel2);
  table = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);
  bfs (btor, acc1, array);
  prev = NULL;
  for (cur = array; cur != acc1; cur = cur->parent)
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
        (void) btor_insert_in_ptr_hash_table (table, cur);
        BTOR_PUSH_STACK (mm, writes, cur);
      }
      else if (BTOR_IS_ARRAY_EQ_EXP (cur))
      {
        (void) btor_insert_in_ptr_hash_table (table, cur);
        BTOR_PUSH_STACK (mm, aeqs, cur);
      }
      else if (BTOR_IS_ARRAY_COND_EXP (cur))
      {
        cond = cur->e[0];
        /* conditionals are normalized */
        assert (!BTOR_IS_INVERTED_EXP (cond));
        assert (btor->rewrite_level == 0 || !BTOR_IS_CONST_EXP (cond));
        if (!BTOR_IS_CONST_EXP (cond))
        {
          (void) btor_insert_in_ptr_hash_table (table, cur);
          assignment = btor_get_assignment_aig (amgr, cond->av->aigs[0]);
          if (assignment == 1)
            BTOR_PUSH_STACK (mm, aconds_sel1, cur);
          else
            BTOR_PUSH_STACK (mm, aconds_sel2, cur);
        }
      }
    }
    prev = cur;
  }
  bfs (btor, acc2, array);
  prev = NULL;
  for (cur = array; cur != acc2; cur = cur->parent)
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
        if (btor_find_in_ptr_hash_table (table, cur) == NULL)
          BTOR_PUSH_STACK (mm, writes, cur);
      }
      else if (BTOR_IS_ARRAY_EQ_EXP (cur))
      {
        if (btor_find_in_ptr_hash_table (table, cur) == NULL)
          BTOR_PUSH_STACK (mm, aeqs, cur);
      }
      else if (BTOR_IS_ARRAY_COND_EXP (cur))
      {
        cond = cur->e[0];
        /* conditionals are normalized */
        assert (!BTOR_IS_INVERTED_EXP (cond));
        assert (btor->rewrite_level == 0 || !BTOR_IS_CONST_EXP (cond));
        if (!BTOR_IS_CONST_EXP (cond))
        {
          if (btor_find_in_ptr_hash_table (table, cur) == NULL)
          {
            assignment = btor_get_assignment_aig (amgr, cond->av->aigs[0]);
            if (assignment == 1)
              BTOR_PUSH_STACK (mm, aconds_sel1, cur);
            else
              BTOR_PUSH_STACK (mm, aconds_sel2, cur);
          }
        }
      }
    }
    prev = cur;
  }
  btor_delete_ptr_hash_table (table);
  encode_lemma (btor,
                &writes,
                &aeqs,
                &aconds_sel1,
                &aconds_sel2,
                BTOR_GET_INDEX_ACC_EXP (acc1),
                BTOR_GET_INDEX_ACC_EXP (acc2),
                BTOR_GET_VALUE_ACC_EXP (acc1),
                BTOR_GET_VALUE_ACC_EXP (acc2));
  BTOR_RELEASE_STACK (mm, writes);
  BTOR_RELEASE_STACK (mm, aeqs);
  BTOR_RELEASE_STACK (mm, aconds_sel1);
  BTOR_RELEASE_STACK (mm, aconds_sel2);
}

/* Checks if a read conflicts with a write */
static int
check_read_write_conflict (Btor *btor,
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

/* readds assumptions to the SAT solver */
static int
readd_assumptions (Btor *btor)
{
  BtorExp *exp;
  BtorPtrHashBucket *bucket;
  BtorAIG *aig;
  BtorSATMgr *smgr;
  BtorAIGMgr *amgr;
  assert (btor != NULL);
  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  for (bucket = btor->assumptions->first; bucket != NULL; bucket = bucket->next)
  {
    assert (BTOR_REAL_ADDR_EXP ((BtorExp *) bucket->key)->len == 1);
    exp = (BtorExp *) bucket->key;
    assert (BTOR_REAL_ADDR_EXP (exp)->simplified == NULL);
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

/* updates SAT assignments, readds assumptions and
 * returns if an assignment has changed
 */
int
update_sat_assignments (Btor *btor)
{
  int result, found_assumption_false;
  BtorSATMgr *smgr = NULL;
  assert (btor != NULL);
  smgr = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (btor->avmgr));
  found_assumption_false = readd_assumptions (btor);
  assert (!found_assumption_false);
  result = btor_sat_sat (smgr, INT_MAX);
  assert (result == BTOR_SAT);
  return btor_changed_assignments_sat (smgr);
}

/* synthesizes and fully encodes index and value of access expression into SAT
 * (if necessary)
 * it returns if encoding changed assignments made so far
 */
static int
lazy_synthesize_and_encode_acc_exp (Btor *btor, BtorExp *acc)
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
    synthesize_exp (btor, index, NULL);
  if (!BTOR_REAL_ADDR_EXP (index)->sat_both_phases)
  {
    update = 1;
    btor_aigvec_to_sat_both_phases (avmgr, BTOR_REAL_ADDR_EXP (index)->av);
    BTOR_REAL_ADDR_EXP (index)->sat_both_phases = 1;
  }
  if (!BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (value)))
    synthesize_exp (btor, value, NULL);
  if (!BTOR_REAL_ADDR_EXP (value)->sat_both_phases)
  {
    update = 1;
    btor_aigvec_to_sat_both_phases (avmgr, BTOR_REAL_ADDR_EXP (value)->av);
    BTOR_REAL_ADDR_EXP (value)->sat_both_phases = 1;
  }
  /* update assignments if necessary */
  if (update) changed_assignments = update_sat_assignments (btor);
  return changed_assignments;
}

static int
lazy_synthesize_and_encode_acond_exp (Btor *btor, BtorExp *acond)
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
  /* conditionals are normalized */
  assert (!BTOR_IS_INVERTED_EXP (cond));
  if (!BTOR_IS_SYNTH_EXP (cond)) synthesize_exp (btor, cond, NULL);
  if (!cond->sat_both_phases)
  {
    update = 1;
    btor_aigvec_to_sat_both_phases (avmgr, cond->av);
    cond->sat_both_phases = 1;
  }
  /* update assignments if necessary */
  if (update) changed_assignments = update_sat_assignments (btor);
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
  has_array_equalities = btor->has_array_equalities;
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
    assert (acc->simplified == NULL);
    /* synthesize index and value if necessary */
    *assignments_changed = lazy_synthesize_and_encode_acc_exp (btor, acc);
    index                = BTOR_GET_INDEX_ACC_EXP (acc);
    assert (BTOR_REAL_ADDR_EXP (index)->simplified == NULL);
    value = BTOR_GET_VALUE_ACC_EXP (acc);
    assert (BTOR_REAL_ADDR_EXP (value)->simplified == NULL);
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
          btor->stats.read_read_conflicts++;
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
      *assignments_changed = lazy_synthesize_and_encode_acc_exp (btor, array);
      if (*assignments_changed) return 0;
      /* check if read is consistent with write */
      if (check_read_write_conflict (btor, acc, array, &indices_equal))
      {
        btor->stats.read_write_conflicts++;
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
      *assignments_changed = lazy_synthesize_and_encode_acond_exp (btor, array);
      if (*assignments_changed) return 0;
      cond = array->e[0];
      /* conditionals are normalized */
      assert (!BTOR_IS_INVERTED_EXP (cond));
      assert (BTOR_IS_SYNTH_EXP (cond));
      assignment = btor_get_assignment_aig (amgr, cond->av->aigs[0]);
      assert (assignment == 1 || assignment == -1);
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
        if (cur_aeq->reachable && cur_aeq->simplified == NULL)
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
        if (next->reachable && next->simplified == NULL)
        {
          assert (BTOR_IS_REGULAR_EXP (next));
          assert (BTOR_IS_ARRAY_EXP (next));
          assert (next->simplified == NULL);
          *assignments_changed =
              lazy_synthesize_and_encode_acond_exp (btor, next);
          if (*assignments_changed) return 0;
          cond = next->e[0];
          /* conditionals are normalized */
          assert (!BTOR_IS_INVERTED_EXP (cond));
          assignment = btor_get_assignment_aig (amgr, cond->av->aigs[0]);
          assert (assignment == 1 || assignment == -1);
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
        if (next->reachable && next->simplified == NULL)
        {
          assert (BTOR_IS_REGULAR_EXP (next));
          assert (BTOR_IS_ARRAY_EXP (next));
          assert (next->simplified == NULL);
          *assignments_changed =
              lazy_synthesize_and_encode_acc_exp (btor, next);
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
  for (bucket = btor->arrays->first; bucket; bucket = bucket->next)
  {
    cur_array = (BtorExp *) bucket->key;
    assert (BTOR_IS_ATOMIC_ARRAY_EXP (cur_array));
    /* we can safely skip arrays which have been simplified */
    if (cur_array->reachable && cur_array->simplified == NULL)
      BTOR_PUSH_STACK (mm, stack, cur_array);
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
        if (cur_parent->reachable && cur_parent->simplified == NULL)
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
        if (cur_parent->reachable && cur_parent->simplified == NULL)
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
  found_conflict       = 0;
  mm                   = btor->mm;
  has_array_equalities = btor->has_array_equalities;
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
        if ((cur_parent->reachable || cur_parent->vread)
            && cur_parent->simplified == NULL)
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
    btor_delete_ptr_hash_table (cur_array->rho);
    cur_array->rho = NULL;
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
reset_assumptions (Btor *btor)
{
  BtorPtrHashBucket *bucket;
  assert (btor != NULL);
  for (bucket = btor->assumptions->first; bucket != NULL; bucket = bucket->next)
    release_exp (btor, (BtorExp *) bucket->key);
  btor_delete_ptr_hash_table (btor->assumptions);
  btor->assumptions =
      btor_new_ptr_hash_table (btor->mm,
                               (BtorHashPtr) btor_hash_exp_by_id,
                               (BtorCmpPtr) btor_compare_exp_by_id);
}

static int
occurrence_check (Btor *btor, BtorExp *left, BtorExp *right)
{
  BtorExp *cur, *real_left;
  BtorExpPtrStack stack;
  int is_cyclic, i;
  BtorMemMgr *mm;
  assert (btor != NULL);
  assert (left != NULL);
  assert (right != NULL);
  is_cyclic = 0;
  mm        = btor->mm;
  real_left = BTOR_REAL_ADDR_EXP (left);
  /* check if left does not occur on the right side */
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, right);
  do
  {
    cur = BTOR_POP_STACK (stack);
    cur = pointer_chase_simplified_exp (btor, cur);
    cur = BTOR_REAL_ADDR_EXP (cur);
    assert (cur->mark == 0 || cur->mark == 1);
    if (cur->mark == 0)
    {
      cur->mark = 1;
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
  btor_mark_exp (btor, right, 0);
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
    case BTOR_CONST_EXP:
    case BTOR_VAR_EXP:
    case BTOR_ARRAY_EXP: return copy_exp (btor, exp->simplified);
    case BTOR_SLICE_EXP:
      return slice_exp (btor, exp->e[0], exp->upper, exp->lower);
    case BTOR_AND_EXP: return and_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_BEQ_EXP:
    case BTOR_AEQ_EXP: return eq_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ADD_EXP: return add_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_MUL_EXP: return mul_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_ULT_EXP: return ult_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SLL_EXP: return sll_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_SRL_EXP: return srl_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UDIV_EXP: return udiv_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_UREM_EXP: return urem_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_CONCAT_EXP: return concat_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_READ_EXP: return read_exp (btor, exp->e[0], exp->e[1]);
    case BTOR_WRITE_EXP:
      return write_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
    default:
      assert (BTOR_IS_ARRAY_OR_BV_COND_EXP (exp));
      return cond_exp (btor, exp->e[0], exp->e[1], exp->e[2]);
  }
}

/* substitutes variable or atomic array by right side */
static void
substitute_exp (Btor *btor, BtorExp *left, BtorExp *right)
{
  BtorExp *cur, *cur_parent, *rebuilt_exp, **temp, **top;
  BtorExpPtrStack search_stack;
  BtorExpPtrStack subst_stack;
  BtorExpPtrStack root_stack;
  BtorFullParentIterator it;
  BtorMemMgr *mm;
  int is_var_substitution, pushed, i;
  assert (btor->rewrite_level > 1);
  assert (btor != NULL);
  assert (left != NULL);
  assert (right != NULL);
  assert (BTOR_REAL_ADDR_EXP (right)->simplified == NULL);
  assert (BTOR_IS_REGULAR_EXP (left));
  assert (left->simplified == NULL);
  assert (BTOR_IS_VAR_EXP (left) || BTOR_IS_ATOMIC_ARRAY_EXP (left));

  mm = btor->mm;

  is_var_substitution = BTOR_IS_VAR_EXP (left);

  /* search from bottom up */

  BTOR_INIT_STACK (search_stack);
  BTOR_INIT_STACK (subst_stack);
  BTOR_INIT_STACK (root_stack);
  BTOR_PUSH_STACK (mm, search_stack, left);
  do
  {
    cur = BTOR_POP_STACK (search_stack);
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->subst_mark == 0)
    {
      cur->subst_mark = 1;
      init_full_parent_iterator (&it, cur);
      /* are we at a root ? */
      pushed = 0;
      while (has_next_parent_full_parent_iterator (&it))
      {
        cur_parent = next_parent_full_parent_iterator (&it);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        if (cur_parent->simplified == NULL)
        {
          pushed = 1;
          BTOR_PUSH_STACK (mm, search_stack, cur_parent);
        }
      }
      if (!pushed) BTOR_PUSH_STACK (mm, root_stack, btor_copy_exp (btor, cur));
    }
  } while (!BTOR_EMPTY_STACK (search_stack));
  BTOR_RELEASE_STACK (mm, search_stack);

  overwrite_exp (btor, left, right);

  /* copy roots on substitution stack */

  assert (BTOR_EMPTY_STACK (subst_stack));
  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++)
    BTOR_PUSH_STACK (mm, subst_stack, *temp);

  /* substitute */

  while (!BTOR_EMPTY_STACK (subst_stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (subst_stack));
    if (cur->subst_mark == 0) continue;

#ifndef NDEBUG
    if (cur->simplified) assert (cur == left); /* really? */
#endif

    if (cur == left) /* base case */
      continue;

    if (cur->subst_mark == 1)
    {
      cur->subst_mark = 2;
      BTOR_PUSH_STACK (mm, subst_stack, cur);
      for (i = cur->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (mm, subst_stack, cur->e[i]);
    }
    else
    {
      assert (cur->subst_mark == 2);
      assert (!BTOR_IS_CONST_EXP (cur));
      assert (!BTOR_IS_VAR_EXP (cur));
      assert (!BTOR_IS_ATOMIC_ARRAY_EXP (cur));
      cur->subst_mark = 0;
      rebuilt_exp     = rebuild_exp (btor, cur);
      assert (rebuilt_exp != NULL);
      assert (rebuilt_exp != cur);

      overwrite_exp (btor, cur, rebuilt_exp);
      release_exp (btor, rebuilt_exp);
    }
  }
  BTOR_RELEASE_STACK (mm, subst_stack);

  top = root_stack.top;
  for (temp = root_stack.start; temp != top; temp++) release_exp (btor, *temp);
  BTOR_RELEASE_STACK (mm, root_stack);

  if (is_var_substitution)
    btor->stats.var_substitutions++;
  else
    btor->stats.array_substitutions++;
}

/* checks if we can substitute and normalizes arguments to substitution */
static int
is_substitution (Btor *btor,
                 BtorExp *exp,
                 BtorExp **left_result,
                 BtorExp **right_result,
                 int *subst_bool_var)
{
  BtorExp *left, *right, *real_left, *real_right;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (left_result != NULL);
  assert (right_result != NULL);
  assert (subst_bool_var != NULL);
  assert (btor->rewrite_level > 1);
  assert (pointer_chase_simplified_exp (btor, exp) == exp);
  if (BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)))
  {
    assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
    if (BTOR_IS_INVERTED_EXP (exp))
    {
      *left_result  = BTOR_REAL_ADDR_EXP (exp);
      *right_result = zero_exp (btor, 1);
    }
    else
    {
      *left_result  = exp;
      *right_result = one_exp (btor, 1);
    }
    *subst_bool_var = 1;
    return 1;
  }
  if (BTOR_IS_INVERTED_EXP (exp) || !BTOR_IS_ARRAY_OR_BV_EQ_EXP (exp)) return 0;
  *subst_bool_var = 0;
  left            = exp->e[0];
  right           = exp->e[1];
  real_left       = BTOR_REAL_ADDR_EXP (left);
  real_right      = BTOR_REAL_ADDR_EXP (right);
  if (!BTOR_IS_VAR_EXP (real_left) && !BTOR_IS_VAR_EXP (real_right)
      && !BTOR_IS_ATOMIC_ARRAY_EXP (real_left)
      && !BTOR_IS_ATOMIC_ARRAY_EXP (real_right))
    return 0;
  if ((!BTOR_IS_VAR_EXP (real_left) && BTOR_IS_VAR_EXP (real_right))
      || (!BTOR_IS_ATOMIC_ARRAY_EXP (real_left)
          && BTOR_IS_ATOMIC_ARRAY_EXP (real_right)))
  {
    *left_result  = right;
    *right_result = left;
  }
  else
  {
    *left_result  = left;
    *right_result = right;
  }
  if (BTOR_IS_INVERTED_EXP (*left_result))
  {
    *left_result  = BTOR_INVERT_EXP (*left_result);
    *right_result = BTOR_INVERT_EXP (*right_result);
  }
  return !occurrence_check (btor, *left_result, *right_result);
}

#if 0

static int
is_linear_equation_child (Btor * btor, BtorExp * exp, int mul_parent)
{
  BtorExp *real_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (mul_parent == 0 || mul_parent == 1);
  real_exp = BTOR_REAL_ADDR_EXP (exp);
  if (BTOR_IS_VAR_EXP (real_exp) || BTOR_IS_CONST_EXP (real_exp))
    return 1;
  if (mul_parent)               /* children of mul may only be variables and constants */
    return 0;
  if (real_exp->kind == BTOR_ADD_EXP)
    return is_linear_equation_child (btor, real_exp->e[0], 0) &&
      is_linear_equation_child (btor, real_exp->e[1], 0);
  if (real_exp->kind == BTOR_MUL_EXP)
    return is_linear_equation_child (btor, real_exp->e[0], 1) &&
      is_linear_equation_child (btor, real_exp->e[1], 1);
  return 0;
}

static int
is_linear_equation (Btor * btor, BtorExp * exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  if (BTOR_IS_INVERTED_EXP (exp) || !BTOR_IS_BV_EQ_EXP (exp))
    return 0;
  assert (BTOR_IS_REGULAR_EXP (exp));
  if (BTOR_REAL_ADDR_EXP (exp->e[0])->kind != BTOR_ADD_EXP
      && BTOR_REAL_ADDR_EXP (exp->e[1])->kind != BTOR_ADD_EXP
      && BTOR_REAL_ADDR_EXP (exp->e[0])->kind != BTOR_MUL_EXP
      && BTOR_REAL_ADDR_EXP (exp->e[1])->kind != BTOR_MUL_EXP)
    return 0;
  return is_linear_equation_child (btor, exp->e[0], 0) &&
    is_linear_equation_child (btor, exp->e[1], 0);
}

#else

/* TODO this is still not working, I fear ... */

static int is_linear_sum (Btor *, BtorExp *);

static int
is_linear_product (Btor *btor, BtorExp *exp)
{
  BtorExp *factor, *real_factor;

  if (BTOR_IS_INVERTED_EXP (exp))
    return BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp));

  if (BTOR_IS_VAR_EXP (exp)) return 1;

  if (BTOR_IS_CONST_EXP (exp)) return 1;

  if (exp->kind == BTOR_ADD_EXP) return is_linear_sum (btor, exp);

  if (exp->kind == BTOR_MUL_EXP)
  {
    factor      = exp->e[0];
    real_factor = BTOR_REAL_ADDR_EXP (factor);
    if (BTOR_IS_CONST_EXP (real_factor))
      return is_linear_product (btor, exp->e[1]);

    factor      = exp->e[1];
    real_factor = BTOR_REAL_ADDR_EXP (factor);
    if (BTOR_IS_CONST_EXP (real_factor))
      return is_linear_product (btor, exp->e[0]);
  }

  return 0;
}

static int
is_linear_sum (Btor *btor, BtorExp *exp)
{
  if (BTOR_IS_INVERTED_EXP (exp) || exp->kind != BTOR_ADD_EXP)
    return is_linear_product (btor, exp);

  if (is_linear_product (btor, exp->e[0])) return 1;

  if (is_linear_product (btor, exp->e[1])) return 1;

  return 0;
}

static int
is_linear_equation (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);

  if (BTOR_IS_INVERTED_EXP (exp)) return 0;

  if (!BTOR_IS_BV_EQ_EXP (exp)) return 0;

  assert (BTOR_IS_REGULAR_EXP (exp));

  if (is_linear_sum (btor, exp->e[0])) return 1;

  if (is_linear_sum (btor, exp->e[1])) return 1;

  return 0;
}

#endif

static void
process_new_constraints (Btor *btor)
{
  BtorPtrHashTable *new_constraints, *processed_constraints;
  BtorExp *cur, *left, *right;
  BtorPtrHashBucket *bucket;
  int rewrite_level, subst_bool_var;
  assert (btor != NULL);
  new_constraints       = btor->new_constraints;
  processed_constraints = btor->processed_constraints;
  rewrite_level         = btor->rewrite_level;
  while (new_constraints->count > 0)
  {
    bucket = new_constraints->first;
    assert (bucket != NULL);
    cur = (BtorExp *) bucket->key;
    assert (BTOR_REAL_ADDR_EXP (cur)->constraint == 1);
    assert (pointer_chase_simplified_exp (btor, cur) == cur);
    assert (BTOR_IS_INVERTED_EXP (cur) || cur->kind != BTOR_AND_EXP);
    if (rewrite_level > 1
        && is_substitution (btor, cur, &left, &right, &subst_bool_var))
    {
      substitute_exp (btor, left, right);
      if (subst_bool_var) release_exp (btor, right);
    }
    else
    {
      if (btor->verbosity > 0)
      {
        if (is_linear_equation (btor, cur))
        {
          btor->stats.linear_equations++;
#if 0
#if 0
                  btor_dump_exp (btor, stdout, cur);
#else
                  fprintf (stdout, "linear equation: %d\n", cur->id);
#endif
#endif
        }
      }

      if (btor_find_in_ptr_hash_table (processed_constraints, cur) == NULL)
      {
        (void) btor_insert_in_ptr_hash_table (processed_constraints, cur);
        btor_remove_from_ptr_hash_table (new_constraints, cur, 0, 0);

        btor->stats.constraints.processed++;
        report_constraint_stats (btor, 0);
      }
      else
      { /* constraint is already processed */
        btor_remove_from_ptr_hash_table (new_constraints, cur, NULL, NULL);
        release_exp (btor, cur);
      }
    }
  }
}

static void
insert_new_constraint (Btor *btor, BtorExp *exp)
{
  assert (btor != NULL);
  assert (exp != NULL);
  assert (pointer_chase_simplified_exp (btor, exp) == exp);
  if (!btor_find_in_ptr_hash_table (btor->new_constraints, exp)
      && !btor_find_in_ptr_hash_table (btor->processed_constraints, exp)
      && !btor_find_in_ptr_hash_table (btor->synthesized_constraints, exp))
  {
    (void) btor_insert_in_ptr_hash_table (btor->new_constraints,
                                          copy_exp (btor, exp));
    BTOR_REAL_ADDR_EXP (exp)->constraint = 1;

    btor->stats.constraints.added++;
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
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  exp = pointer_chase_simplified_exp (btor, exp);

  mm = btor->mm;
  if (btor->valid_assignments)
  {
    btor->valid_assignments = 0;
    reset_assumptions (btor);
  }
  assert (btor->assumptions != NULL);

  /* we do not add TRUE */
  if (!BTOR_IS_INVERTED_EXP (exp) && BTOR_IS_CONST_EXP (exp)
      && exp->bits[0] == '1')
    return;
  if (BTOR_IS_INVERTED_EXP (exp) && BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (exp))
      && BTOR_REAL_ADDR_EXP (exp)->bits[0] == '0')
    return;

  if (!BTOR_IS_INVERTED_EXP (exp) && exp->kind == BTOR_AND_EXP)
  {
    BTOR_INIT_STACK (stack);
    BTOR_PUSH_STACK (mm, stack, exp);
    do
    {
      cur = BTOR_POP_STACK (stack);
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
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_add_constraint_exp'");
  BTOR_ABORT_EXP (exp == NULL,
                  "'exp' must not be NULL in 'btor_add_constraint_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_add_constraint_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (exp)->len != 1,
      "'exp' has to be a boolean expression in 'btor_add_constraint_exp'");
  if (btor->replay)
    BTOR_PUSH_STACK (
        btor->mm, btor->replay_constraints, btor_copy_exp (btor, exp));

  exp = pointer_chase_simplified_exp (btor, exp);

  add_constraint (btor, exp);
}

void
btor_rewrite_btor (Btor *btor)
{
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_rewrite_btor'");

  process_new_constraints (btor);
}

void
btor_replay_btor (Btor *btor, FILE *file)
{
  BtorExp *result, *temp;
  BtorPtrHashBucket *b;
  int i;
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_replay_btor'");
  BTOR_ABORT_EXP (file == NULL,
                  "'file' must not be NULL in 'btor_replay_btor'");
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
  dump_exp (btor, file, result);
  btor_release_exp (btor, result);
}

void
btor_add_assumption_exp (Btor *btor, BtorExp *exp)
{
  BtorExp *cur, *child;
  BtorExpPtrStack stack;
  BtorMemMgr *mm;

  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_add_assumption_exp'");
  BTOR_ABORT_EXP (exp == NULL,
                  "'exp' must not be NULL in 'btor_add_assumption_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_add_assumption_exp'");
  BTOR_ABORT_EXP (
      BTOR_REAL_ADDR_EXP (exp)->len != 1,
      "'exp' has to be a boolean expression in 'btor_add_assumption_exp'");

  mm = btor->mm;
  if (btor->valid_assignments)
  {
    btor->valid_assignments = 0;
    reset_assumptions (btor);
  }
  if (!BTOR_IS_INVERTED_EXP (exp) && exp->kind == BTOR_AND_EXP)
  {
    BTOR_INIT_STACK (stack);
    BTOR_PUSH_STACK (mm, stack, exp);
    do
    {
      cur = BTOR_POP_STACK (stack);
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
  BtorPtrHashTable *processed_constraints, *synthesized_constraints;
  BtorPtrHashBucket *bucket;
  BtorExp *cur;
  BtorAIG *aig;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  assert (btor != NULL);
  processed_constraints   = btor->processed_constraints;
  synthesized_constraints = btor->synthesized_constraints;
  amgr                    = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr                    = btor_get_sat_mgr_aig_mgr (amgr);
  while (processed_constraints->count > 0)
  {
    bucket = processed_constraints->first;
    assert (bucket != NULL);
    cur = (BtorExp *) bucket->key;

    if (btor_find_in_ptr_hash_table (synthesized_constraints, cur) == NULL)
    {
      aig = exp_to_aig (btor, cur);
      if (aig == BTOR_AIG_FALSE) return 1;

      btor_add_toplevel_aig_to_sat (amgr, aig);
      btor_release_aig (amgr, aig);
      (void) btor_insert_in_ptr_hash_table (synthesized_constraints, cur);
      btor_remove_from_ptr_hash_table (processed_constraints, cur, 0, 0);

      btor->stats.constraints.synthesized++;
      report_constraint_stats (btor, 0);
    }
    else
    {
      /* constraint is already in synthesized_constraints */
      btor_remove_from_ptr_hash_table (processed_constraints, cur, NULL, NULL);
      release_exp (btor, cur);
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
      simp = btor_copy_exp (btor, pointer_chase_simplified_exp (btor, cur));
      btor_release_exp (btor, cur);
      bucket->key = simp;
    }
  }
}

int
btor_sat_btor (Btor *btor, int refinement_limit)
{
  int sat_result, found_conflict, found_constraint_false, verbosity;
  int refinements, found_assumption_false;
  BtorExpPtrStack top_arrays;
  BtorAIGMgr *amgr;
  BtorSATMgr *smgr;
  BtorMemMgr *mm;

  BTOR_ABORT_EXP (btor == NULL, "'btor' must not be NULL in 'btor_sat_btor'");
  BTOR_ABORT_EXP (refinement_limit < 0,
                  "'refinement_limit' must not be negative in 'btor_sat_btor'");

  verbosity = btor->verbosity;
  if (verbosity > 0) print_verbose_msg ("calling SAT");

  process_new_constraints (btor);

  mm          = btor->mm;
  refinements = btor->stats.refinements;

  amgr = btor_get_aig_mgr_aigvec_mgr (btor->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  if (!btor_is_initialized_sat (smgr)) btor_init_sat (smgr);

  /* no added assumptions and constraints -> delete old assumptions */
  if (btor->valid_assignments == 1) reset_assumptions (btor);
  btor->valid_assignments = 1;

  found_constraint_false = process_unsynthesized_constraints (btor);
  if (found_constraint_false) return BTOR_UNSAT;

  /* pointer chase assumptions */
  update_assumptions (btor);

  found_assumption_false = readd_assumptions (btor);
  if (found_assumption_false) return BTOR_UNSAT;

  sat_result = btor_sat_sat (smgr, INT_MAX);
  BTOR_INIT_STACK (top_arrays);
  search_top_arrays (btor, &top_arrays);
  while (sat_result != BTOR_UNSAT && sat_result != BTOR_UNKNOWN
         && btor->stats.refinements < refinement_limit)
  {
    assert (sat_result == BTOR_SAT);
    found_conflict = check_and_resolve_conflicts (btor, &top_arrays);
    if (!found_conflict) break;
    refinements++;
    if (verbosity > 1)
    {
      if (verbosity > 2 || !(refinements % 10))
      {
        fprintf (stdout, "[btorsat] refinement iteration %d\n", refinements);
        fflush (stdout);
      }
    }
    found_assumption_false = readd_assumptions (btor);
    assert (!found_assumption_false);
    sat_result = btor_sat_sat (smgr, INT_MAX);
  }
  btor->stats.refinements = refinements;
  if (refinements == refinement_limit) sat_result = BTOR_UNKNOWN;
  BTOR_RELEASE_STACK (mm, top_arrays);
  return sat_result;
}

char *
btor_assignment_exp (Btor *btor, BtorExp *exp)
{
  BtorAIGVecMgr *avmgr;
  BtorAIGVec *av;
  char *assignment;
  int invert_av, invert_bits;
  BTOR_ABORT_EXP (btor == NULL,
                  "'btor' must not be NULL in 'btor_assignment_exp'");
  BTOR_ABORT_EXP (exp == NULL,
                  "'exp' must not be NULL in 'btor_assignment_exp'");
  BTOR_ABORT_EXP (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)),
                  "'exp' must not be an array in 'btor_assignment_exp'");
  exp = pointer_chase_simplified_exp (btor, exp);
  if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (exp)))
  {
    invert_bits = BTOR_IS_INVERTED_EXP (exp);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_EXP (exp)->bits);
    assignment = btor_copy_const (btor->mm, BTOR_REAL_ADDR_EXP (exp)->bits);
    if (invert_bits)
      btor_invert_const (btor->mm, BTOR_REAL_ADDR_EXP (exp)->bits);
    return assignment;
  }
  if (!BTOR_REAL_ADDR_EXP (exp)->reachable
      || !BTOR_IS_SYNTH_EXP (BTOR_REAL_ADDR_EXP (exp)))
    return NULL;
  avmgr     = btor->avmgr;
  invert_av = BTOR_IS_INVERTED_EXP (exp);
  av        = BTOR_REAL_ADDR_EXP (exp)->av;
  if (invert_av) btor_invert_aigvec (avmgr, av);
  assignment = btor_assignment_aigvec (avmgr, av);
  /* invert back if necessary */
  if (invert_av) btor_invert_aigvec (avmgr, av);
  return assignment;
}

const char *
btor_version (void)
{
  return BTOR_VERSION;
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
