#include "btorexp.h"
#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconst.h"
#include "btorhash.h"
#include "btorsat.h"
#include "btorutil.h"

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

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

struct BtorExpMgr
{
  BtorMemMgr *mm;
  BtorExpUniqueTable table;
  BtorExpPtrStack vars;
  BtorExpPtrStack arrays;
  BtorAIGVecMgr *avmgr;
  int id;
  int rewrite_level;
  int dump_trace;
  int verbosity;
  BtorReadEnc read_enc;
  BtorWriteEnc write_enc;
  FILE *trace_file;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table; /* used for lazy McCarthy */
  BtorPtrHashTable *exp_pair_cnf_eq_id_table;   /* used for lazy McCarthy */
};

struct BtorExpPair
{
  BtorExp *exp1;
  BtorExp *exp2;
};

typedef struct BtorExpPair BtorExpPair;

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Auxilliary                                                             */
/*------------------------------------------------------------------------*/

static void
print_verbose_msg (char *fmt, ...)
{
  va_list ap;
  fputs ("[btorexp] ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static char *
zeros_string (BtorExpMgr *emgr, int len)
{
  int i        = 0;
  char *string = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  BTOR_NEWN (emgr->mm, string, len + 1);
  for (i = 0; i < len; i++) string[i] = '0';
  string[len] = '\0';
  return string;
}

static char *
ones_string (BtorExpMgr *emgr, int len)
{
  int i        = 0;
  char *string = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  BTOR_NEWN (emgr->mm, string, len + 1);
  for (i = 0; i < len; i++) string[i] = '1';
  string[len] = '\0';
  return string;
}

static int
is_zero_string (BtorExpMgr *emgr, const char *string, int len)
{
  int i = 0;
  (void) emgr;
  assert (emgr != NULL);
  assert (string != NULL);
  assert (len > 0);
  for (i = 0; i < len; i++)
    if (string[i] != '0') return 0;
  return 1;
}

static int
is_one_string (BtorExpMgr *emgr, const char *string, int len)
{
  int i = 0;
  (void) emgr;
  assert (emgr != NULL);
  assert (string != NULL);
  assert (len > 0);
  if (string[len - 1] != '1') return 0;
  for (i = 0; i < len - 1; i++)
    if (string[i] != '0') return 0;
  return 1;
}

static BtorExpPair *
new_exp_pair (BtorExpMgr *emgr, BtorExp *exp1, BtorExp *exp2)
{
  BtorExpPair *result = NULL;
  assert (emgr != NULL);
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  BTOR_NEW (emgr->mm, result);
  if (BTOR_REAL_ADDR_EXP (exp2)->id < BTOR_REAL_ADDR_EXP (exp1)->id)
  {
    result->exp1 = btor_copy_exp (emgr, exp2);
    result->exp2 = btor_copy_exp (emgr, exp1);
  }
  else
  {
    result->exp1 = btor_copy_exp (emgr, exp1);
    result->exp2 = btor_copy_exp (emgr, exp2);
  }
  return result;
}

static void
delete_exp_pair (BtorExpMgr *emgr, BtorExpPair *pair)
{
  assert (emgr != NULL);
  assert (pair != NULL);
  btor_release_exp (emgr, pair->exp1);
  btor_release_exp (emgr, pair->exp2);
  BTOR_DELETE (emgr->mm, pair);
}

static unsigned int
hash_exp_pair (void *pair)
{
  unsigned int result   = 0u;
  BtorExpPair *exp_pair = NULL;
  assert (pair != NULL);
  exp_pair = (BtorExpPair *) pair;
  result   = (unsigned int) BTOR_REAL_ADDR_EXP (exp_pair->exp1)->id;
  result += (unsigned int) BTOR_REAL_ADDR_EXP (exp_pair->exp2)->id;
  result *= 7334147u;
  return result;
}

static int
compare_exp_pair (void *pair1, void *pair2)
{
  int result             = 0;
  BtorExpPair *exp_pair1 = NULL;
  BtorExpPair *exp_pair2 = NULL;
  assert (pair1 != NULL);
  assert (pair2 != NULL);
  exp_pair1 = (BtorExpPair *) pair1;
  exp_pair2 = (BtorExpPair *) pair2;
  result    = BTOR_REAL_ADDR_EXP (exp_pair1->exp1)->id;
  result -= BTOR_REAL_ADDR_EXP (exp_pair2->exp1)->id;
  if (result != 0) return result;
  result = BTOR_REAL_ADDR_EXP (exp_pair1->exp2)->id;
  result -= BTOR_REAL_ADDR_EXP (exp_pair2->exp2)->id;
  return result;
}

/*------------------------------------------------------------------------*/
/* BtorExp                                                                */
/*------------------------------------------------------------------------*/

/* Encodes Ackermann constraint of the form index i = index j =>
 * value a = value b directly into CNF.
 * Let n be the number of bits of the indices
 * and m the number of bits of the values:
 * i = j => a = b
 * (i = j => e) ^ (e => a = b)
 * ((i != j) v e) ^ (not e v (a = b))
 * forall (0 <= k < n) (i_k v j_k v not d_k) ^ (not i_k v not j_k v not d_k)) ^
 * (forall (0 <= k < n) (d_k) v e) ^
 * forall (0 <= k < m) ((not e v a_k v not b_k) ^ (not e v not a_k v b_k))
 *
 * This function is called in lazy and eager mode. We have to check
 * if we have to encode a constraint at all. For example if we are in eager
 * mode and the indices are constants and not equal, then we do not have
 * to encode a constraint.
 */
static void
encode_ackermann_constraint (
    BtorExpMgr *emgr, BtorExp *i, BtorExp *j, BtorExp *a, BtorExp *b)
{
  BtorMemMgr *mm       = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorSATMgr *smgr     = NULL;
  BtorAIGVec *av_i     = NULL;
  BtorAIGVec *av_j     = NULL;
  BtorAIGVec *av_a     = NULL;
  BtorAIGVec *av_b     = NULL;
  BtorAIG *aig1        = NULL;
  BtorAIG *aig2        = NULL;
  BtorIntStack diffs;
  int k                   = 0;
  int len                 = 0;
  int i_k                 = 0;
  int j_k                 = 0;
  int d_k                 = 0;
  int e                   = 0;
  int a_k                 = 0;
  int b_k                 = 0;
  int has_inverse_bit_i_j = 0;
  int is_equal_i_j        = 0;
  int is_equal_a_b        = 0;
  assert (emgr != NULL);
  assert (i != NULL);
  assert (j != NULL);
  assert (a != NULL);
  assert (b != NULL);
  mm    = emgr->mm;
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);
  av_i  = BTOR_GET_AIGVEC_EXP (emgr, i);
  av_j  = BTOR_GET_AIGVEC_EXP (emgr, j);
  av_a  = BTOR_GET_AIGVEC_EXP (emgr, a);
  av_b  = BTOR_GET_AIGVEC_EXP (emgr, b);
  assert (av_i != NULL);
  assert (av_j != NULL);
  assert (av_a != NULL);
  assert (av_b != NULL);
  assert (av_i->len == av_j->len);
  assert (av_a->len == av_b->len);
  is_equal_i_j = btor_is_equal_aigvec (avmgr, av_i, av_j);
  is_equal_a_b = btor_is_equal_aigvec (avmgr, av_a, av_b);
  len          = av_i->len;
  for (k = 0; k < len; k++)
  {
    if ((((unsigned long int) av_i->aigs[k])
         ^ ((unsigned long int) av_j->aigs[k]))
        == 1ul)
    {
      has_inverse_bit_i_j = 1;
      break;
    }
  }
  if (is_equal_a_b || has_inverse_bit_i_j)
  {
    /* (i = j => TRUE) <=> TRUE
     * (FALSE => a = b) <=> TRUE
     */
    btor_release_delete_aigvec (avmgr, av_i);
    btor_release_delete_aigvec (avmgr, av_j);
    btor_release_delete_aigvec (avmgr, av_a);
    btor_release_delete_aigvec (avmgr, av_b);
    return;
  }
  /* skip i = j part if i and j are equal:
   * W => a = b  <=>  a = b
   */
  if (!is_equal_i_j)
  {
    if (!BTOR_REAL_ADDR_EXP (i)->full_sat)
    {
      btor_aigvec_to_sat_full (avmgr, av_i);
      BTOR_REAL_ADDR_EXP (i)->full_sat = 1;
    }
    if (!BTOR_REAL_ADDR_EXP (j)->full_sat)
    {
      btor_aigvec_to_sat_full (avmgr, av_j);
      BTOR_REAL_ADDR_EXP (j)->full_sat = 1;
    }
    BTOR_INIT_STACK (diffs);
    for (k = 0; k < len; k++)
    {
      aig1 = av_i->aigs[k];
      aig2 = av_j->aigs[k];
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
      /* The bits cannot be the inverse of each other.
       * We check this at the beginning of the function.
       */
      assert ((((unsigned long int) aig1) ^ ((unsigned long int) aig2)) != 1ul);
      d_k = btor_next_cnf_id_sat_mgr (smgr);
      assert (d_k != 0);
      BTOR_PUSH_STACK (mm, diffs, d_k);
      if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_TRUE)
      {
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, i_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, j_k);
        btor_add_sat (smgr, -d_k);
        btor_add_sat (smgr, 0);
      }
      if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_FALSE)
      {
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, -i_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, -j_k);
        btor_add_sat (smgr, -d_k);
        btor_add_sat (smgr, 0);
      }
    }
    while (!BTOR_EMPTY_STACK (diffs))
    {
      k = BTOR_POP_STACK (diffs);
      assert (k != 0);
      btor_add_sat (smgr, k);
    }
    BTOR_RELEASE_STACK (mm, diffs);
  }
  e = btor_next_cnf_id_sat_mgr (smgr);
  assert (e != 0);
  btor_add_sat (smgr, e);
  btor_add_sat (smgr, 0);
  len = av_a->len;
  if (!BTOR_REAL_ADDR_EXP (a)->full_sat)
  {
    btor_aigvec_to_sat_full (avmgr, av_a);
    BTOR_REAL_ADDR_EXP (a)->full_sat = 1;
  }
  if (!BTOR_REAL_ADDR_EXP (b)->full_sat)
  {
    btor_aigvec_to_sat_full (avmgr, av_b);
    BTOR_REAL_ADDR_EXP (b)->full_sat = 1;
  }
  for (k = 0; k < len; k++)
  {
    aig1 = av_a->aigs[k];
    aig2 = av_b->aigs[k];
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
    /* if AIGs are equal then clauses are satisfied */
    if (aig1 != aig2)
    {
      if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_FALSE)
      {
        btor_add_sat (smgr, -e);
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, a_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, -b_k);
        btor_add_sat (smgr, 0);
      }
      if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_TRUE)
      {
        btor_add_sat (smgr, -e);
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, -a_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, b_k);
        btor_add_sat (smgr, 0);
      }
    }
  }
  btor_release_delete_aigvec (avmgr, av_i);
  btor_release_delete_aigvec (avmgr, av_j);
  btor_release_delete_aigvec (avmgr, av_a);
  btor_release_delete_aigvec (avmgr, av_b);
}

/* This function is used to encode constraints of the form
 * i != k1 ^ i != k2 ^ ... ^ i != kn ^ i = j => a = b
 * The stack 'writes' contains intermediate writes.
 * The indices of the writes represent k.
 *
 * This function is called in lazy mode only. Thus, We have to encode a
 * constraint in every case, because a conflict must have been detected
 * before.
 */
static void
encode_mccarthy_constraint (BtorExpMgr *emgr,
                            BtorExpPtrStack *writes,
                            BtorExp *i,
                            BtorExp *j,
                            BtorExp *a,
                            BtorExp *b)
{
  BtorMemMgr *mm                               = NULL;
  BtorAIGVecMgr *avmgr                         = NULL;
  BtorAIGMgr *amgr                             = NULL;
  BtorSATMgr *smgr                             = NULL;
  BtorAIGVec *av_i                             = NULL;
  BtorAIGVec *av_j                             = NULL;
  BtorAIGVec *av_a                             = NULL;
  BtorAIGVec *av_b                             = NULL;
  BtorAIGVec *av_w                             = NULL;
  BtorAIG *aig1                                = NULL;
  BtorAIG *aig2                                = NULL;
  BtorExp **temp                               = NULL;
  BtorExp *cur_write                           = NULL;
  BtorExp **top                                = NULL;
  BtorExpPair *pair                            = NULL;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table = NULL;
  BtorPtrHashTable *exp_pair_cnf_eq_id_table   = NULL;
  BtorPtrHashBucket *bucket                    = NULL;
  BtorIntStack clause;
  int len      = 0;
  int k        = 0;
  int a_k      = 0;
  int b_k      = 0;
  int i_k      = 0;
  int j_k      = 0;
  int d_k      = 0;
  int w_k      = 0;
  int e        = 0;
  int d_hashed = 0;
  assert (emgr != NULL);
  assert (writes != NULL);
  assert (i != NULL);
  assert (j != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (BTOR_COUNT_STACK (*writes) > 0);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (i)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (j)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (a)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (b)));
  exp_pair_cnf_diff_id_table = emgr->exp_pair_cnf_diff_id_table;
  exp_pair_cnf_eq_id_table   = emgr->exp_pair_cnf_eq_id_table;
  mm                         = emgr->mm;
  avmgr                      = emgr->avmgr;
  amgr                       = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr                       = btor_get_sat_mgr_aig_mgr (amgr);
  av_i                       = BTOR_GET_AIGVEC_EXP (emgr, i);
  av_j                       = BTOR_GET_AIGVEC_EXP (emgr, j);
  av_a                       = BTOR_GET_AIGVEC_EXP (emgr, a);
  av_b                       = BTOR_GET_AIGVEC_EXP (emgr, b);
  assert (av_i != NULL);
  assert (av_j != NULL);
  assert (av_a != NULL);
  assert (av_b != NULL);
  assert (av_i->len == av_j->len);
  assert (av_a->len == av_b->len);
  len = av_i->len;
  if (!BTOR_REAL_ADDR_EXP (i)->full_sat)
  {
    btor_aigvec_to_sat_full (avmgr, av_i);
    BTOR_REAL_ADDR_EXP (i)->full_sat = 1;
  }
  if (!BTOR_REAL_ADDR_EXP (j)->full_sat)
  {
    btor_aigvec_to_sat_full (avmgr, av_j);
    BTOR_REAL_ADDR_EXP (j)->full_sat = 1;
  }
  BTOR_INIT_STACK (clause);
  /* encode i != j */
  if (i != j)
  {
    pair   = new_exp_pair (emgr, i, j);
    bucket = btor_find_in_ptr_hash_table (exp_pair_cnf_diff_id_table, pair);
    if (bucket == NULL)
    {
      /* hash starting cnf id - 1 for d_k */
      d_k = btor_get_last_cnf_id_sat_mgr (smgr);
      btor_insert_in_ptr_hash_table (exp_pair_cnf_diff_id_table, pair)
          ->data.asInt = d_k;
    }
    else
    {
      d_hashed = 1;
      d_k      = bucket->data.asInt;
      delete_exp_pair (emgr, pair);
    }
    for (k = 0; k < len; k++)
    {
      aig1 = av_i->aigs[k];
      aig2 = av_j->aigs[k];
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
      assert ((((unsigned long int) aig1) ^ ((unsigned long int) aig2)) != 1ul);
      if (d_hashed)
        d_k++;
      else
        d_k = btor_next_cnf_id_sat_mgr (smgr);
      assert (d_k != 0);
      BTOR_PUSH_STACK (mm, clause, d_k);
      if (aig1 != BTOR_AIG_TRUE && aig2 != BTOR_AIG_TRUE)
      {
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, i_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, j_k);
        btor_add_sat (smgr, -d_k);
        btor_add_sat (smgr, 0);
      }
      if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_FALSE)
      {
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, -i_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, -j_k);
        btor_add_sat (smgr, -d_k);
        btor_add_sat (smgr, 0);
      }
    }
  }
  /* encode a = b */
  len = av_a->len;
  if (!BTOR_REAL_ADDR_EXP (a)->full_sat)
  {
    btor_aigvec_to_sat_full (avmgr, av_a);
    BTOR_REAL_ADDR_EXP (a)->full_sat = 1;
  }
  if (!BTOR_REAL_ADDR_EXP (b)->full_sat)
  {
    btor_aigvec_to_sat_full (avmgr, av_b);
    BTOR_REAL_ADDR_EXP (b)->full_sat = 1;
  }
  pair   = new_exp_pair (emgr, a, b);
  bucket = btor_find_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair);
  if (bucket == NULL)
  {
    e = btor_next_cnf_id_sat_mgr (smgr);
    btor_insert_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair)->data.asInt =
        e;
  }
  else
  {
    e = bucket->data.asInt;
    delete_exp_pair (emgr, pair);
  }
  BTOR_PUSH_STACK (mm, clause, e);
  for (k = 0; k < len; k++)
  {
    aig1 = av_a->aigs[k];
    aig2 = av_b->aigs[k];
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
        btor_add_sat (smgr, -e);
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, a_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, -b_k);
        btor_add_sat (smgr, 0);
      }
      if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_TRUE)
      {
        btor_add_sat (smgr, -e);
        if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, -a_k);
        if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, b_k);
        btor_add_sat (smgr, 0);
      }
    }
  }
  /* encode i != write index premisses */
  len = av_i->len;
  top = writes->top;
  for (temp = writes->start; temp != top; temp++)
  {
    cur_write = *temp;
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
    av_w = BTOR_GET_AIGVEC_EXP (emgr, cur_write->e[1]);
    assert (av_w->len == len);
    if (!BTOR_REAL_ADDR_EXP (cur_write->e[1])->full_sat)
    {
      btor_aigvec_to_sat_full (avmgr, av_w);
      BTOR_REAL_ADDR_EXP (cur_write->e[1])->full_sat = 1;
    }
    pair   = new_exp_pair (emgr, i, cur_write->e[1]);
    bucket = btor_find_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair);
    if (bucket == NULL)
    {
      e = btor_next_cnf_id_sat_mgr (smgr);
      btor_insert_in_ptr_hash_table (exp_pair_cnf_eq_id_table, pair)
          ->data.asInt = e;
    }
    else
    {
      e = bucket->data.asInt;
      delete_exp_pair (emgr, pair);
    }
    BTOR_PUSH_STACK (mm, clause, e);
    for (k = 0; k < len; k++)
    {
      aig1 = av_i->aigs[k];
      aig2 = av_w->aigs[k];
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
          btor_add_sat (smgr, -e);
          if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, i_k);
          if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, -w_k);
          btor_add_sat (smgr, 0);
        }
        if (aig1 != BTOR_AIG_FALSE && aig2 != BTOR_AIG_TRUE)
        {
          btor_add_sat (smgr, -e);
          if (!BTOR_IS_CONST_AIG (aig1)) btor_add_sat (smgr, -i_k);
          if (!BTOR_IS_CONST_AIG (aig2)) btor_add_sat (smgr, w_k);
          btor_add_sat (smgr, 0);
        }
      }
    }
    btor_release_delete_aigvec (avmgr, av_w);
  }
  while (!BTOR_EMPTY_STACK (clause))
  {
    k = BTOR_POP_STACK (clause);
    assert (k != 0);
    btor_add_sat (smgr, k);
  }
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, clause);
  btor_release_delete_aigvec (avmgr, av_i);
  btor_release_delete_aigvec (avmgr, av_j);
  btor_release_delete_aigvec (avmgr, av_a);
  btor_release_delete_aigvec (avmgr, av_b);
}

/* Encodes read constraint eagerly by adding all
 * read constraints with the reads encoded so far.
 */
static void
encode_read_eagerly (BtorExpMgr *emgr, BtorExp *array, BtorExp *read)
{
  BtorExp *cur = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (read != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  cur = array->first_parent;
  assert (BTOR_IS_REGULAR_EXP (cur));
  /* read expressions are at the beginning and
     write expressions at the end of the parent list. */
  while (cur != NULL && cur->kind != BTOR_WRITE_EXP)
  {
    /* array children are always at position 0 */
    assert (BTOR_GET_TAG_EXP (cur) == 0);
    assert (cur->kind == BTOR_READ_EXP);
    if (cur->encoded_read)
      encode_ackermann_constraint (emgr, cur->e[1], read->e[1], cur, read);
    cur = cur->next_parent[0];
    assert (BTOR_IS_REGULAR_EXP (cur));
  }
  read->encoded_read = 1;
}

static BtorExp *
int_min_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string    = zeros_string (emgr, len);
  string[0] = '1';
  result    = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

BtorExp *
btor_int_to_exp (BtorExpMgr *emgr, int i, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 1);
  string = btor_int_to_const (emgr->mm, i, len);
  result = btor_const_exp (emgr, string);
  btor_delete_const (emgr->mm, string);
  return result;
}

BtorExp *
btor_unsigned_to_exp (BtorExpMgr *emgr, unsigned u, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 1);
  string = btor_unsigned_to_const (emgr->mm, u, len);
  result = btor_const_exp (emgr, string);
  btor_delete_const (emgr->mm, string);
  return result;
}

/* Connects child to its parent and updates list of parent pointers */
static void
connect_child_exp (BtorExpMgr *emgr, BtorExp *parent, BtorExp *child, int pos)
{
  BtorExp *real_parent   = NULL;
  BtorExp *real_child    = NULL;
  BtorExp *first_parent  = NULL;
  BtorExp *tagged_parent = NULL;
  int i                  = 0;
  (void) emgr;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  real_parent         = BTOR_REAL_ADDR_EXP (parent);
  real_child          = BTOR_REAL_ADDR_EXP (child);
  real_parent->e[pos] = child;
  tagged_parent       = BTOR_TAG_EXP (real_parent, pos);
  /* no parent so far? */
  if (real_child->first_parent == NULL)
  {
    assert (real_child->last_parent == NULL);
    real_child->first_parent = tagged_parent;
    real_child->last_parent  = tagged_parent;
    assert (real_parent->prev_parent[pos] == NULL);
    assert (real_parent->next_parent[pos] == NULL);
  }
  /* add parent at the beginning of the list */
  else
  {
    first_parent = real_child->first_parent;
    assert (first_parent != NULL);
    real_parent->next_parent[pos] = first_parent;
    i                             = BTOR_GET_TAG_EXP (first_parent);
    BTOR_REAL_ADDR_EXP (first_parent)->prev_parent[i] = tagged_parent;
    real_child->first_parent                          = tagged_parent;
  }
}

/* Connects child to write parent. Writes can only be parents of arrays
 * and other writes. Writes are appended to the end of array and write
 * parent lists while reads and all other expressions are inserted
 * at the beginning of the parent lists.*/
static void
connect_child_write_exp (BtorExpMgr *emgr, BtorExp *parent, BtorExp *child)
{
  BtorExp *last_parent = NULL;
  (void) emgr;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (BTOR_IS_WRITE_ARRAY_EXP (parent));
  assert (BTOR_IS_REGULAR_EXP (child));
  assert (BTOR_IS_ARRAY_EXP (child));
  /* array children are always at position 0 */
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
    assert (BTOR_IS_REGULAR_EXP (last_parent));
    parent->prev_parent[0]      = last_parent;
    last_parent->next_parent[0] = parent;
    child->last_parent          = parent;
  }
}

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->next_parent[BTOR_GET_TAG_EXP (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_EXP (exp)->prev_parent[BTOR_GET_TAG_EXP (exp)])

/* Disconnects a child from its parent and updates its parent list */
static void
disconnect_child_exp (BtorExpMgr *emgr, BtorExp *parent, int pos)
{
  BtorExp *real_parent       = NULL;
  BtorExp *first_parent      = NULL;
  BtorExp *last_parent       = NULL;
  BtorExp *real_first_parent = NULL;
  BtorExp *real_last_parent  = NULL;
  BtorExp *real_child        = NULL;
  (void) emgr;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (parent)));
  assert (!BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (parent)));
  assert (!BTOR_IS_NATIVE_ARRAY_EXP (BTOR_REAL_ADDR_EXP (parent)));
  real_parent  = BTOR_REAL_ADDR_EXP (parent);
  parent       = BTOR_TAG_EXP (real_parent, pos);
  real_child   = BTOR_REAL_ADDR_EXP (real_parent->e[pos]);
  first_parent = real_child->first_parent;
  last_parent  = real_child->last_parent;
  assert (first_parent != NULL);
  assert (last_parent != NULL);
  real_first_parent = BTOR_REAL_ADDR_EXP (first_parent);
  real_last_parent  = BTOR_REAL_ADDR_EXP (last_parent);
  /* only one parent? */
  if (first_parent == parent && first_parent == last_parent)
  {
    assert (real_parent->next_parent[pos] == NULL);
    assert (real_parent->prev_parent[pos] == NULL);
    real_child->first_parent = NULL;
    real_child->last_parent  = NULL;
  }
  /* is parent first parent in the list? */
  else if (first_parent == parent)
  {
    assert (real_parent->next_parent[pos] != NULL);
    assert (real_parent->prev_parent[pos] == NULL);
    real_child->first_parent                    = real_parent->next_parent[pos];
    BTOR_PREV_PARENT (real_child->first_parent) = NULL;
  }
  /* is parent last parent in the list? */
  else if (last_parent == parent)
  {
    assert (real_parent->next_parent[pos] == NULL);
    assert (real_parent->prev_parent[pos] != NULL);
    real_child->last_parent                    = real_parent->prev_parent[pos];
    BTOR_NEXT_PARENT (real_child->last_parent) = NULL;
  }
  /* hang out parent from list */
  else
  {
    assert (real_parent->next_parent[pos] != NULL);
    assert (real_parent->prev_parent[pos] != NULL);
    BTOR_PREV_PARENT (real_parent->next_parent[pos]) =
        real_parent->prev_parent[pos];
    BTOR_NEXT_PARENT (real_parent->prev_parent[pos]) =
        real_parent->next_parent[pos];
  }
  real_parent->next_parent[pos] = NULL;
  real_parent->prev_parent[pos] = NULL;
  real_parent->e[pos]           = NULL;
}

static BtorExp *
new_const_exp_node (BtorExpMgr *emgr, const char *bits)
{
  BtorExp *exp = NULL;
  int i        = 0;
  int len      = 0;
  assert (emgr != NULL);
  assert (bits != NULL);
  len = strlen (bits);
  assert (len > 0);
  BTOR_CNEW (emgr->mm, exp);
  exp->kind = BTOR_CONST_EXP;
  BTOR_NEWN (emgr->mm, exp->bits, len + 1);
  for (i = 0; i < len; i++) exp->bits[i] = bits[i] == '1' ? '1' : '0';
  exp->bits[len] = '\0';
  exp->len       = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  return exp;
}

static BtorExp *
new_slice_exp_node (BtorExpMgr *emgr, BtorExp *e0, int upper, int lower)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (upper >= lower);
  BtorExp *exp = NULL;
  BTOR_CNEW (emgr->mm, exp);
  exp->kind  = BTOR_SLICE_EXP;
  exp->upper = upper;
  exp->lower = lower;
  exp->len   = upper - lower + 1;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  connect_child_exp (emgr, exp, e0, 0);
  return exp;
}

static BtorExp *
new_binary_exp_node (
    BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1, int len)
{
  BtorExp *exp = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (len > 0);
  BTOR_CNEW (emgr->mm, exp);
  exp->kind = kind;
  exp->len  = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  connect_child_exp (emgr, exp, e0, 0);
  connect_child_exp (emgr, exp, e1, 1);
  return exp;
}

static BtorExp *
new_ternary_exp_node (BtorExpMgr *emgr,
                      BtorExpKind kind,
                      BtorExp *e0,
                      BtorExp *e1,
                      BtorExp *e2,
                      int len)
{
  BtorExp *exp = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (len > 0);
  BTOR_CNEW (emgr->mm, exp);
  exp->kind = kind;
  exp->len  = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  connect_child_exp (emgr, exp, e0, 0);
  connect_child_exp (emgr, exp, e1, 1);
  connect_child_exp (emgr, exp, e2, 2);
  return exp;
}

static BtorExp *
new_write_exp_node (BtorExpMgr *emgr,
                    BtorExp *e_array,
                    BtorExp *e_index,
                    BtorExp *e_value)
{
  BtorMemMgr *mm = NULL;
  BtorExp *exp   = NULL;
  assert (emgr != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (e_value != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)));
  mm = emgr->mm;
  BTOR_CNEW (mm, exp);
  exp->kind      = BTOR_WRITE_EXP;
  exp->index_len = BTOR_REAL_ADDR_EXP (e_index)->len;
  exp->len       = BTOR_REAL_ADDR_EXP (e_value)->len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  BTOR_CNEW (mm, exp->reads);
  /* append writes to the end of parrent list */
  connect_child_write_exp (emgr, exp, e_array);
  connect_child_exp (emgr, exp, e_index, 1);
  connect_child_exp (emgr, exp, e_value, 2);
  return exp;
}

/* Delete expression from memory */
static void
delete_exp_node (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorMemMgr *mm = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  mm = emgr->mm;
  if (BTOR_IS_CONST_EXP (exp))
    btor_freestr (mm, exp->bits);
  else if (BTOR_IS_VAR_EXP (exp))
    btor_freestr (mm, exp->symbol);
  else if (BTOR_IS_NATIVE_ARRAY_EXP (exp))
    BTOR_DELETE (mm, exp->reads);
  else if (BTOR_IS_WRITE_ARRAY_EXP (exp))
  {
    BTOR_DELETE (mm, exp->reads);
    disconnect_child_exp (emgr, exp, 0);
    disconnect_child_exp (emgr, exp, 1);
    disconnect_child_exp (emgr, exp, 2);
  }
  else if (BTOR_IS_UNARY_EXP (exp))
    disconnect_child_exp (emgr, exp, 0);
  else if (BTOR_IS_BINARY_EXP (exp))
  {
    disconnect_child_exp (emgr, exp, 0);
    disconnect_child_exp (emgr, exp, 1);
  }
  else
  {
    assert (BTOR_IS_TERNARY_EXP (exp));
    disconnect_child_exp (emgr, exp, 0);
    disconnect_child_exp (emgr, exp, 1);
    disconnect_child_exp (emgr, exp, 2);
  }
  if (exp->av != NULL)
  {
    assert (emgr->avmgr != NULL);
    btor_release_delete_aigvec (emgr->avmgr, exp->av);
  }
  BTOR_DELETE (mm, exp);
}

/* Computes hash value of expresssion */
static unsigned int
compute_exp_hash (BtorExp *exp, int table_size)
{
  unsigned int hash = 0;
  assert (exp != NULL);
  assert (table_size > 0);
  assert (btor_is_power_of_2_util (table_size));
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (!BTOR_IS_VAR_EXP (exp));
  assert (!BTOR_IS_NATIVE_ARRAY_EXP (exp));
  if (BTOR_IS_CONST_EXP (exp))
    hash = btor_hashstr ((void *) exp->bits);
  else if (BTOR_IS_UNARY_EXP (exp))
  {
    hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id;
    if (exp->kind == BTOR_SLICE_EXP)
      hash += (unsigned int) exp->upper + (unsigned int) exp->lower;
  }
  else if (BTOR_IS_BINARY_EXP (exp))
  {
    hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[1])->id;
  }
  else
  {
    assert (BTOR_IS_TERNARY_EXP (exp));
    hash = (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[0])->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[1])->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (exp->e[2])->id;
  }
  hash = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (table_size - 1);
  return hash;
}

/* Finds constant expression in hash table. Returns NULL if it could not be
 * found. */
static BtorExp **
find_const_exp (BtorExpMgr *emgr, const char *bits)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  unsigned int hash = 0u;
  int len           = 0;
  assert (emgr != NULL);
  assert (bits != NULL);
  len    = strlen (bits);
  hash   = btor_hashstr ((void *) bits);
  hash   = (hash * BTOR_EXP_UNIQUE_TABLE_PRIME) & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
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
find_slice_exp (BtorExpMgr *emgr, BtorExp *e0, int upper, int lower)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  unsigned int hash = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (lower >= 0);
  assert (upper >= lower);
  hash = (((unsigned int) BTOR_REAL_ADDR_EXP (e0)->id + (unsigned int) upper
           + (unsigned int) lower)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
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
find_binary_exp (BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  BtorExp *temp     = NULL;
  unsigned int hash = 0;
  assert (emgr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  hash = (((unsigned int) BTOR_REAL_ADDR_EXP (e0)->id
           + (unsigned int) BTOR_REAL_ADDR_EXP (e1)->id)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
  cur    = *result;
  if (BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
      && BTOR_REAL_ADDR_EXP (e1)->id < BTOR_REAL_ADDR_EXP (e0)->id)
  {
    temp = e0;
    e0   = e1;
    e1   = temp;
  }
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
    BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1, BtorExp *e2)
{
  BtorExp *cur      = NULL;
  BtorExp **result  = NULL;
  unsigned int hash = 0;
  assert (emgr != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  hash = (((unsigned) BTOR_REAL_ADDR_EXP (e0)->id
           + (unsigned) BTOR_REAL_ADDR_EXP (e1)->id
           + (unsigned) BTOR_REAL_ADDR_EXP (e2)->id)
          * BTOR_EXP_UNIQUE_TABLE_PRIME)
         & (emgr->table.size - 1);
  result = emgr->table.chains + hash;
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
enlarge_exp_unique_table (BtorExpMgr *emgr)
{
  BtorMemMgr *mm       = NULL;
  BtorExp **new_chains = NULL;
  int new_size         = 0;
  int i                = 0;
  int size             = 0;
  unsigned int hash    = 0u;
  BtorExp *cur         = NULL;
  BtorExp *temp        = NULL;
  assert (emgr != NULL);
  size     = emgr->table.size;
  new_size = size << 1;
  assert (new_size / size == 2);
  mm = emgr->mm;
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = emgr->table.chains[i];
    while (cur != NULL)
    {
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (!BTOR_IS_VAR_EXP (cur));
      assert (!BTOR_IS_NATIVE_ARRAY_EXP (cur));
      temp             = cur->next;
      hash             = compute_exp_hash (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BTOR_DELETEN (mm, emgr->table.chains, size);
  emgr->table.size   = new_size;
  emgr->table.chains = new_chains;
}

/* Removes expression from unique table and deletes it from memory. */
static void
delete_exp_unique_table_entry (BtorExpMgr *emgr, BtorExp *exp)
{
  unsigned int hash = 0u;
  BtorExp *cur      = NULL;
  BtorExp *prev     = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  hash = compute_exp_hash (exp, emgr->table.size);
  cur  = emgr->table.chains[hash];
  while (cur != exp && cur != NULL)
  {
    assert (BTOR_IS_REGULAR_EXP (cur));
    prev = cur;
    cur  = cur->next;
  }
  assert (cur != NULL);
  if (prev == NULL)
    emgr->table.chains[hash] = cur->next;
  else
    prev->next = cur->next;
  emgr->table.num_elements--;
  delete_exp_node (emgr, cur);
}

static void
inc_exp_ref_counter (BtorExp *exp)
{
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->refs < INT_MAX);
  BTOR_REAL_ADDR_EXP (exp)->refs++;
}

BtorExp *
btor_copy_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  (void) emgr;
  assert (emgr != NULL);
  assert (exp != NULL);
  inc_exp_ref_counter (exp);
  return exp;
}

void
btor_mark_exp (BtorExpMgr *emgr, BtorExp *exp, int new_mark)
{
  BtorMemMgr *mm = NULL;
  BtorExpPtrStack stack;
  BtorExp *cur = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  mm = emgr->mm;
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (cur->mark != new_mark)
    {
      cur->mark = new_mark;
      if (BTOR_IS_UNARY_EXP (cur))
      {
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
      }
      else if (BTOR_IS_BINARY_EXP (cur))
      {
        BTOR_PUSH_STACK (mm, stack, cur->e[1]);
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
      }
      else if (BTOR_IS_TERNARY_EXP (cur))
      {
        BTOR_PUSH_STACK (mm, stack, cur->e[2]);
        BTOR_PUSH_STACK (mm, stack, cur->e[1]);
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
      }
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

/* set mark flags of native arrays and parent writes */
static void
mark_exp_bottom_up_arrays (BtorExpMgr *emgr, BtorExp *array, int new_mark)
{
  BtorMemMgr *mm = NULL;
  BtorExpPtrStack stack;
  BtorExp *cur_array  = NULL;
  BtorExp *cur_parent = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  mm = emgr->mm;
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, array);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_array = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    if (cur_array->array_mark != new_mark)
    {
      cur_array->array_mark = new_mark;
      cur_parent            = cur_array->last_parent;
      assert (BTOR_IS_REGULAR_EXP (cur_parent));
      while (cur_parent != NULL
             && BTOR_REAL_ADDR_EXP (cur_parent)->kind != BTOR_READ_EXP)
      {
        /* array children are always at position 0 */
        assert (BTOR_GET_TAG_EXP (cur_parent) == 0);
        assert (BTOR_IS_WRITE_ARRAY_EXP (cur_parent));
        BTOR_PUSH_STACK (mm, stack, cur_parent);
        cur_parent = cur_parent->prev_parent[0];
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
      }
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

void
btor_release_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorMemMgr *mm = NULL;
  BtorExpPtrStack stack;
  BtorExp *cur = BTOR_REAL_ADDR_EXP (exp);
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (cur->refs > 0);
  mm = emgr->mm;
  if (cur->refs > 1)
  {
    if (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_NATIVE_ARRAY_EXP (cur)) cur->refs--;
  }
  else
  {
    assert (cur->refs == 1);
    BTOR_INIT_STACK (stack);
    BTOR_PUSH_STACK (mm, stack, cur);
    while (!BTOR_EMPTY_STACK (stack))
    {
      cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
      if (cur->refs > 1)
      {
        if (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_NATIVE_ARRAY_EXP (cur))
          cur->refs--;
      }
      else
      {
        assert (cur->refs == 1);
        if (BTOR_IS_UNARY_EXP (cur))
          BTOR_PUSH_STACK (mm, stack, cur->e[0]);
        else if (BTOR_IS_BINARY_EXP (cur))
        {
          BTOR_PUSH_STACK (mm, stack, cur->e[1]);
          BTOR_PUSH_STACK (mm, stack, cur->e[0]);
        }
        else if (BTOR_IS_TERNARY_EXP (cur))
        {
          BTOR_PUSH_STACK (mm, stack, cur->e[2]);
          BTOR_PUSH_STACK (mm, stack, cur->e[1]);
          BTOR_PUSH_STACK (mm, stack, cur->e[0]);
        }
        if (!BTOR_IS_VAR_EXP (cur) && !BTOR_IS_NATIVE_ARRAY_EXP (cur))
          delete_exp_unique_table_entry (emgr, cur);
      }
    }
    BTOR_RELEASE_STACK (mm, stack);
  }
}

BtorExp *
btor_const_exp (BtorExpMgr *emgr, const char *bits)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (bits != NULL);
  assert (strlen (bits) > 0);
  lookup = find_const_exp (emgr, bits);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_const_exp (emgr, bits);
    }
    *lookup = new_const_exp_node (emgr, bits);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
    inc_exp_ref_counter (*lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  ;
  return *lookup;
}

BtorExp *
btor_zeros_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string = zeros_string (emgr, len);
  result = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

BtorExp *
btor_ones_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string = ones_string (emgr, len);
  result = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

BtorExp *
btor_one_exp (BtorExpMgr *emgr, int len)
{
  char *string    = NULL;
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  string                      = zeros_string (emgr, len);
  string[strlen (string) - 1] = '1';
  result                      = btor_const_exp (emgr, string);
  btor_freestr (emgr->mm, string);
  return result;
}

BtorExp *
btor_var_exp (BtorExpMgr *emgr, int len, const char *symbol)
{
  BtorMemMgr *mm = NULL;
  BtorExp *exp   = NULL;
  assert (emgr != NULL);
  assert (len > 0);
  assert (symbol != NULL);
  mm = emgr->mm;
  BTOR_CNEW (mm, exp);
  exp->kind   = BTOR_VAR_EXP;
  exp->symbol = btor_strdup (mm, symbol);
  exp->len    = len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  BTOR_PUSH_STACK (mm, emgr->vars, exp);
  return exp;
}

BtorExp *
btor_array_exp (BtorExpMgr *emgr, int elem_len, int index_len)
{
  BtorMemMgr *mm = NULL;
  BtorExp *exp   = NULL;
  assert (emgr != NULL);
  assert (elem_len > 0);
  assert (index_len > 0);
  mm = emgr->mm;
  BTOR_CNEW (mm, exp);
  exp->kind      = BTOR_ARRAY_EXP;
  exp->index_len = index_len;
  exp->len       = elem_len;
  assert (emgr->id < INT_MAX);
  exp->id   = emgr->id++;
  exp->refs = 1;
  exp->emgr = emgr;
  BTOR_NEW (mm, exp->reads);
  BTOR_PUSH_STACK (mm, emgr->arrays, exp);
  return exp;
}

static BtorExp *
slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower)
{
  BtorExp **lookup = NULL;
  BtorExp *node    = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  lookup = find_slice_exp (emgr, exp, upper, lower);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_slice_exp (emgr, exp, upper, lower);
    }
    *lookup = new_slice_exp_node (emgr, exp, upper, lower);
    inc_exp_ref_counter (exp);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
    node = *lookup;
  }
  else
    inc_exp_ref_counter (*lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  return *lookup;
}

static BtorExp *
rewrite_exp (BtorExpMgr *emgr,
             BtorExpKind kind,
             BtorExp *e0,
             BtorExp *e1,
             BtorExp *e2,
             int upper,
             int lower)
{
  BtorExp *result   = NULL;
  BtorExp *real_e0  = NULL;
  BtorExp *real_e1  = NULL;
  BtorExp *real_e2  = NULL;
  BtorExp *temp     = NULL;
  BtorMemMgr *mm    = NULL;
  char *bits_result = NULL;
  char *bits_e0     = NULL;
  char *bits_e1     = NULL;
  int i             = 0;
  int diff          = 0;
  int len           = 0;
  int counter       = 0;
  int is_zero       = 0;
  int is_one        = 0;
  assert (emgr != NULL);
  assert (emgr->rewrite_level > 0);
  assert (emgr->rewrite_level <= 2);
  assert (lower >= 0);
  assert (lower <= upper);
  mm = emgr->mm;
  if (BTOR_IS_UNARY_EXP_KIND (kind))
  {
    assert (e0 != NULL);
    assert (e1 == NULL);
    assert (e2 == NULL);
    assert (kind == BTOR_SLICE_EXP);
    if (emgr->dump_trace)
    {
      /* TODO */
    }
    else
    {
      real_e0 = BTOR_REAL_ADDR_EXP (e0);
      diff    = upper - lower;
      if (diff + 1 == real_e0->len)
        result = btor_copy_exp (emgr, e0);
      else if (BTOR_IS_CONST_EXP (real_e0))
      {
        counter = 0;
        len     = real_e0->len;
        BTOR_NEWN (mm, bits_result, diff + 2);
        for (i = len - upper - 1; i <= len - upper - 1 + diff; i++)
          bits_result[counter++] = real_e0->bits[i];
        bits_result[counter] = '\0';
        result               = btor_const_exp (emgr, bits_result);
        result               = BTOR_COND_INVERT_EXP (e0, result);
        btor_delete_const (mm, bits_result);
      }
    }
  }
  else if (BTOR_IS_BINARY_EXP_KIND (kind))
  {
    assert (e0 != NULL);
    assert (e1 != NULL);
    assert (e2 == NULL);
    real_e0 = BTOR_REAL_ADDR_EXP (e0);
    real_e1 = BTOR_REAL_ADDR_EXP (e1);
    if (emgr->dump_trace)
    {
      /* TODO */
    }
    else
    {
      if (BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
      {
        bits_e0 = BTOR_GET_BITS_EXP (mm, e0);
        bits_e1 = BTOR_GET_BITS_EXP (mm, e1);
        switch (kind)
        {
          case BTOR_AND_EXP:
            bits_result = btor_and_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_EQ_EXP:
            bits_result = btor_eq_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_ADD_EXP:
            bits_result = btor_add_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_MUL_EXP:
            bits_result = btor_mul_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_ULT_EXP:
            bits_result = btor_ult_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_UDIV_EXP:
            bits_result = btor_udiv_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_UREM_EXP:
            bits_result = btor_urem_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_SLL_EXP:
            bits_result = btor_sll_const (mm, bits_e0, bits_e1);
            break;
          case BTOR_SRL_EXP:
            bits_result = btor_srl_const (mm, bits_e0, bits_e1);
            break;
          default:
            assert (kind == BTOR_CONCAT_EXP);
            bits_result = btor_concat_const (mm, bits_e0, bits_e1);
            break;
        }
        result = btor_const_exp (emgr, bits_result);
        btor_delete_const (mm, bits_result);
        btor_delete_const (mm, bits_e1);
        btor_delete_const (mm, bits_e0);
      }
      else if (BTOR_IS_CONST_EXP (real_e0) && !BTOR_IS_CONST_EXP (real_e1))
      {
        bits_e0 = BTOR_GET_BITS_EXP (mm, e0);
        is_zero = is_zero_string (emgr, bits_e0, real_e0->len);
        is_one  = is_one_string (emgr, bits_e0, real_e0->len);
        if (is_zero)
        {
          if (kind == BTOR_ADD_EXP)
            result = btor_copy_exp (emgr, e1);
          else if (kind == BTOR_MUL_EXP || kind == BTOR_SLL_EXP
                   || kind == BTOR_SRL_EXP || kind == BTOR_UDIV_EXP
                   || kind == BTOR_UREM_EXP)
            result = btor_zeros_exp (emgr, real_e0->len);
        }
        else if (is_one)
        {
          if (kind == BTOR_MUL_EXP) result = btor_copy_exp (emgr, e1);
        }
        btor_delete_const (mm, bits_e0);
      }
      else if (!BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
      {
        bits_e1 = BTOR_GET_BITS_EXP (mm, e1);
        is_zero = is_zero_string (emgr, bits_e1, real_e1->len);
        is_one  = is_one_string (emgr, bits_e1, real_e1->len);
        if (is_zero)
        {
          if (kind == BTOR_ADD_EXP)
            result = btor_copy_exp (emgr, e0);
          else if (kind == BTOR_MUL_EXP || kind == BTOR_SLL_EXP
                   || kind == BTOR_SRL_EXP)
            result = btor_zeros_exp (emgr, real_e0->len);
          else if (kind == BTOR_UDIV_EXP)
            result = btor_ones_exp (emgr, real_e0->len);
          else if (kind == BTOR_UREM_EXP)
            result = btor_copy_exp (emgr, e0);
        }
        else if (is_one)
        {
          if (kind == BTOR_MUL_EXP) result = btor_copy_exp (emgr, e0);
        }
        btor_delete_const (mm, bits_e1);
      }
      else if (real_e0 == real_e1
               && (kind == BTOR_EQ_EXP || kind == BTOR_ADD_EXP))
      {
        if (kind == BTOR_EQ_EXP)
        {
          if (e0 == e1)
            result = btor_one_exp (emgr, 1);
          else
            result = btor_zeros_exp (emgr, 1);
        }
        else
        {
          assert (kind == BTOR_ADD_EXP);
          /* replace x + x by x * 2 */
          if (e0 == e1)
          {
            if (real_e0->len >= 2)
            {
              temp   = btor_int_to_exp (emgr, 2, real_e0->len);
              result = btor_mul_exp (emgr, e0, temp);
              btor_release_exp (emgr, temp);
            }
          }
          else
            /* replace x + ~x by -1 */
            result = btor_ones_exp (emgr, real_e0->len);
        }
      }
      else if (e0 == e1
               && (kind == BTOR_ULT_EXP || kind == BTOR_UDIV_EXP
                   || kind == BTOR_UREM_EXP))
      {
        switch (kind)
        {
          case BTOR_ULT_EXP: result = btor_zeros_exp (emgr, 1); break;
          case BTOR_UDIV_EXP: result = btor_one_exp (emgr, real_e0->len); break;
          default:
            assert (kind == BTOR_UREM_EXP);
            result = btor_zeros_exp (emgr, real_e0->len);
            break;
        }
      }

      /* TODO: add all the O[123] optimization of MEMICS paper.
       * TODO: lots of word level simplifications:
       * a <= b && b <= a  <=> a == b
       * a != b && a == b <=> 0
       * a[7:4] == b[7:4] && a[3:0] == b[3:0] <=> a == b
       * ...
       */
      /* TODO a == ~a <=> 0 */
      /* TODO a + 2 * a <=> 3 * a <=> see below */
      /* TODO strength reduction: a * 2 == a << 1 */
      /* TODO strength reduction: a * 3 == (a << 1) + a */
      /* TODO strength reduction: a / 2 == (a >> 1) */
      /* TODO strength reduction: a / 3 =>  higher bits zero */
      /* TODO a < 0 <=> 0 */
      /* TODO 0 < a <=> a != 0 */
      /* TODO a < 1 <=> a == 0 */
      /* TODO MAX < a <=> 0 */
      /* TODO MAX-1 < a <=> a == MAX */
      /* TODO a < MAX <=> a != MAX */
    }
  }
  else
  {
    assert (BTOR_IS_TERNARY_EXP_KIND (kind));
    assert (e0 != NULL);
    assert (e1 != NULL);
    assert (e2 != NULL);
    assert (kind == BTOR_COND_EXP);
    real_e0 = BTOR_REAL_ADDR_EXP (e0);
    real_e1 = BTOR_REAL_ADDR_EXP (e1);
    real_e2 = BTOR_REAL_ADDR_EXP (e2);
    if (emgr->dump_trace)
    {
      /* TODO */
    }
    else
    {
      if (BTOR_IS_CONST_EXP (real_e0))
      {
        if ((!BTOR_IS_INVERTED_EXP (e0) && e0->bits[0] == '1')
            || (BTOR_IS_INVERTED_EXP (e0) && real_e0->bits[0] == '0'))
          result = btor_copy_exp (emgr, e1);
        else
          result = btor_copy_exp (emgr, e2);
      }
      else if (e1 == e2)
        result = btor_copy_exp (emgr, e1);

      /* TODO e0 ? e1 : ~e1 <=> e0 == e1 */
    }
  }
  return result;
}

BtorExp *
btor_not_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  (void) emgr;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  inc_exp_ref_counter (exp);
  return BTOR_INVERT_EXP (exp);
}

BtorExp *
btor_neg_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *one    = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  one    = btor_one_exp (emgr, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_add_exp (emgr, BTOR_INVERT_EXP (exp), one);
  btor_release_exp (emgr, one);
  return result;
}

BtorExp *
btor_nego_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result   = NULL;
  BtorExp *sign_exp = NULL;
  BtorExp *rest     = NULL;
  BtorExp *zeros    = NULL;
  BtorExp *eq       = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  len = BTOR_REAL_ADDR_EXP (exp)->len;
  if (len == 1) return btor_copy_exp (emgr, exp);
  sign_exp = btor_slice_exp (emgr, exp, len - 1, len - 1);
  rest     = btor_slice_exp (emgr, exp, len - 2, 0);
  zeros    = btor_zeros_exp (emgr, len - 1);
  eq       = btor_eq_exp (emgr, rest, zeros);
  result   = btor_and_exp (emgr, sign_exp, eq);
  btor_release_exp (emgr, sign_exp);
  btor_release_exp (emgr, rest);
  btor_release_exp (emgr, zeros);
  btor_release_exp (emgr, eq);
  return result;
}

BtorExp *
btor_redor_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *zeros  = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  zeros  = btor_zeros_exp (emgr, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_ne_exp (emgr, exp, zeros);
  btor_release_exp (emgr, zeros);
  return result;
}

BtorExp *
btor_redxor_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *slice  = NULL;
  BtorExp * xor   = NULL;
  int i           = 0;
  int len         = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  len    = BTOR_REAL_ADDR_EXP (exp)->len;
  result = btor_slice_exp (emgr, exp, 0, 0);
  for (i = 1; i < len; i++)
  {
    slice = btor_slice_exp (emgr, exp, i, i);
    xor   = btor_xor_exp (emgr, result, slice);
    btor_release_exp (emgr, slice);
    btor_release_exp (emgr, result);
    result = xor;
  }
  return result;
}

BtorExp *
btor_redand_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExp *result = NULL;
  BtorExp *ones   = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 1);
  ones   = btor_ones_exp (emgr, BTOR_REAL_ADDR_EXP (exp)->len);
  result = btor_eq_exp (emgr, exp, ones);
  btor_release_exp (emgr, ones);
  return result;
}

BtorExp *
btor_slice_exp (BtorExpMgr *emgr, BtorExp *exp, int upper, int lower)
{
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (lower >= 0);
  assert (upper >= lower);
  assert (upper < BTOR_REAL_ADDR_EXP (exp)->len);
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_SLICE_EXP, exp, NULL, NULL, upper, lower);
  if (result == NULL) result = slice_exp (emgr, exp, upper, lower);
  return result;
}

BtorExp *
btor_uext_exp (BtorExpMgr *emgr, BtorExp *exp, int len)
{
  BtorExp *result = NULL;
  BtorExp *zeros  = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  assert (len >= 0);
  if (len == 0)
  {
    inc_exp_ref_counter (exp);
    result = exp;
  }
  else
  {
    assert (len > 0);
    zeros  = btor_zeros_exp (emgr, len);
    result = btor_concat_exp (emgr, zeros, exp);
    btor_release_exp (emgr, zeros);
  }
  return result;
}

BtorExp *
btor_sext_exp (BtorExpMgr *emgr, BtorExp *exp, int len)
{
  BtorExp *result = NULL;
  BtorExp *zeros  = NULL;
  BtorExp *ones   = NULL;
  BtorExp *neg    = NULL;
  BtorExp *cond   = NULL;
  int exp_len     = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  assert (len >= 0);
  if (len == 0)
  {
    inc_exp_ref_counter (exp);
    result = exp;
  }
  else
  {
    assert (len > 0);
    zeros   = btor_zeros_exp (emgr, len);
    ones    = btor_ones_exp (emgr, len);
    exp_len = BTOR_REAL_ADDR_EXP (exp)->len;
    neg     = btor_slice_exp (emgr, exp, exp_len - 1, exp_len - 1);
    cond    = btor_cond_exp (emgr, neg, ones, zeros);
    result  = btor_concat_exp (emgr, cond, exp);
    btor_release_exp (emgr, zeros);
    btor_release_exp (emgr, ones);
    btor_release_exp (emgr, neg);
    btor_release_exp (emgr, cond);
  }
  return result;
}

static BtorExp *
binary_exp (
    BtorExpMgr *emgr, BtorExpKind kind, BtorExp *e0, BtorExp *e1, int len)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (len > 0);
  lookup = find_binary_exp (emgr, kind, e0, e1);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_binary_exp (emgr, kind, e0, e1);
    }
    if (BTOR_IS_BINARY_COMMUTATIVE_EXP_KIND (kind)
        && BTOR_REAL_ADDR_EXP (e1)->id < BTOR_REAL_ADDR_EXP (e0)->id)
      *lookup = new_binary_exp_node (emgr, kind, e1, e0, len);
    else
      *lookup = new_binary_exp_node (emgr, kind, e0, e1, len);
    inc_exp_ref_counter (e0);
    inc_exp_ref_counter (e1);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
    inc_exp_ref_counter (*lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_or_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (
      btor_and_exp (emgr, BTOR_INVERT_EXP (e0), BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_nand_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_and_exp (emgr, e0, e1));
}

BtorExp *
btor_nor_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_or_exp (emgr, e0, e1));
}

BtorExp *
btor_implies_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_and_exp (emgr, e0, BTOR_INVERT_EXP (e1)));
}

BtorExp *
btor_iff_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_xnor_exp (emgr, e0, e1);
}

BtorExp *
btor_xor_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp * or    = NULL;
  BtorExp *and    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  or     = btor_or_exp (emgr, e0, e1);
  and    = btor_and_exp (emgr, e0, e1);
  result = btor_and_exp (emgr, or, BTOR_INVERT_EXP (and));
  btor_release_exp (emgr, or);
  btor_release_exp (emgr, and);
  return result;
}

BtorExp *
btor_xnor_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_xor_exp (emgr, e0, e1));
}

BtorExp *
btor_and_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_AND_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_AND_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_eq_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_EQ_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_EQ_EXP, e0, e1, 1);
  return result;
}

BtorExp *
btor_ne_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return BTOR_INVERT_EXP (btor_eq_exp (emgr, e0, e1));
}

BtorExp *
btor_add_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_ADD_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_ADD_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_uaddo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *uext_e1 = NULL;
  BtorExp *uext_e2 = NULL;
  BtorExp *add     = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  uext_e1 = btor_uext_exp (emgr, e0, 1);
  uext_e2 = btor_uext_exp (emgr, e1, 1);
  add     = btor_add_exp (emgr, uext_e1, uext_e2);
  result  = btor_slice_exp (emgr, add, len, len);
  btor_release_exp (emgr, uext_e1);
  btor_release_exp (emgr, uext_e2);
  btor_release_exp (emgr, add);
  return result;
}

BtorExp *
btor_saddo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result      = NULL;
  BtorExp *sign_e1     = NULL;
  BtorExp *sign_e2     = NULL;
  BtorExp *sign_result = NULL;
  BtorExp *add         = NULL;
  BtorExp *and1        = NULL;
  BtorExp *and2        = NULL;
  BtorExp *or1         = NULL;
  BtorExp *or2         = NULL;
  int len              = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len         = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1     = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (emgr, e1, len - 1, len - 1);
  add         = btor_add_exp (emgr, e0, e1);
  sign_result = btor_slice_exp (emgr, add, len - 1, len - 1);
  and1        = btor_and_exp (emgr, sign_e1, sign_e2);
  or1         = btor_and_exp (emgr, and1, BTOR_INVERT_EXP (sign_result));
  and2 =
      btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  or2    = btor_and_exp (emgr, and2, sign_result);
  result = btor_or_exp (emgr, or1, or2);
  btor_release_exp (emgr, and1);
  btor_release_exp (emgr, and2);
  btor_release_exp (emgr, or1);
  btor_release_exp (emgr, or2);
  btor_release_exp (emgr, add);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, sign_result);
  return result;
}

BtorExp *
btor_mul_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_MUL_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_MUL_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_umulo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result    = NULL;
  BtorExp *uext_e1   = NULL;
  BtorExp *uext_e2   = NULL;
  BtorExp *mul       = NULL;
  BtorExp *slice     = NULL;
  BtorExp *and       = NULL;
  BtorExp * or       = NULL;
  BtorExp **temps_e2 = NULL;
  int i              = 0;
  int len            = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return btor_zeros_exp (emgr, 1);
  BTOR_NEWN (emgr->mm, temps_e2, len - 1);
  temps_e2[0] = btor_slice_exp (emgr, e1, len - 1, len - 1);
  for (i = 1; i < len - 1; i++)
  {
    slice       = btor_slice_exp (emgr, e1, len - 1 - i, len - 1 - i);
    temps_e2[i] = btor_or_exp (emgr, temps_e2[i - 1], slice);
    btor_release_exp (emgr, slice);
  }
  slice  = btor_slice_exp (emgr, e0, 1, 1);
  result = btor_and_exp (emgr, slice, temps_e2[0]);
  btor_release_exp (emgr, slice);
  for (i = 1; i < len - 1; i++)
  {
    slice = btor_slice_exp (emgr, e0, i + 1, i + 1);
    and   = btor_and_exp (emgr, slice, temps_e2[i]);
    or    = btor_or_exp (emgr, result, and);
    btor_release_exp (emgr, slice);
    btor_release_exp (emgr, and);
    btor_release_exp (emgr, result);
    result = or ;
  }
  uext_e1 = btor_uext_exp (emgr, e0, 1);
  uext_e2 = btor_uext_exp (emgr, e1, 1);
  mul     = btor_mul_exp (emgr, uext_e1, uext_e2);
  slice   = btor_slice_exp (emgr, mul, len, len);
  or      = btor_or_exp (emgr, result, slice);
  btor_release_exp (emgr, uext_e1);
  btor_release_exp (emgr, uext_e2);
  btor_release_exp (emgr, mul);
  btor_release_exp (emgr, slice);
  btor_release_exp (emgr, result);
  result = or ;
  for (i = 0; i < len - 1; i++) btor_release_exp (emgr, temps_e2[i]);
  BTOR_DELETEN (emgr->mm, temps_e2, len - 1);
  return result;
}

BtorExp *
btor_smulo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result          = NULL;
  BtorExp *sext_e1         = NULL;
  BtorExp *sext_e2         = NULL;
  BtorExp *sign_e1         = NULL;
  BtorExp *sign_e2         = NULL;
  BtorExp *sext_sign_e1    = NULL;
  BtorExp *sext_sign_e2    = NULL;
  BtorExp *xor_sign_e1     = NULL;
  BtorExp *xor_sign_e2     = NULL;
  BtorExp *mul             = NULL;
  BtorExp *slice           = NULL;
  BtorExp *slice_n         = NULL;
  BtorExp *slice_n_minus_1 = NULL;
  BtorExp * xor            = NULL;
  BtorExp *and             = NULL;
  BtorExp * or             = NULL;
  BtorExp **temps_e2       = NULL;
  int i                    = 0;
  int len                  = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return btor_and_exp (emgr, e0, e1);
  if (len == 2)
  {
    sext_e1         = btor_sext_exp (emgr, e0, 1);
    sext_e2         = btor_sext_exp (emgr, e1, 1);
    mul             = btor_mul_exp (emgr, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (emgr, mul, len, len);
    slice_n_minus_1 = btor_slice_exp (emgr, mul, len - 1, len - 1);
    result          = btor_xor_exp (emgr, slice_n, slice_n_minus_1);
    btor_release_exp (emgr, sext_e1);
    btor_release_exp (emgr, sext_e2);
    btor_release_exp (emgr, mul);
    btor_release_exp (emgr, slice_n);
    btor_release_exp (emgr, slice_n_minus_1);
  }
  else
  {
    sign_e1      = btor_slice_exp (emgr, e0, len - 1, len - 1);
    sign_e2      = btor_slice_exp (emgr, e1, len - 1, len - 1);
    sext_sign_e1 = btor_sext_exp (emgr, sign_e1, len - 1);
    sext_sign_e2 = btor_sext_exp (emgr, sign_e2, len - 1);
    xor_sign_e1  = btor_xor_exp (emgr, e0, sext_sign_e1);
    xor_sign_e2  = btor_xor_exp (emgr, e1, sext_sign_e2);
    BTOR_NEWN (emgr->mm, temps_e2, len - 2);
    temps_e2[0] = btor_slice_exp (emgr, xor_sign_e2, len - 2, len - 2);
    for (i = 1; i < len - 2; i++)
    {
      slice = btor_slice_exp (emgr, xor_sign_e2, len - 2 - i, len - 2 - i);
      temps_e2[i] = btor_or_exp (emgr, temps_e2[i - 1], slice);
      btor_release_exp (emgr, slice);
    }
    slice  = btor_slice_exp (emgr, xor_sign_e1, 1, 1);
    result = btor_and_exp (emgr, slice, temps_e2[0]);
    btor_release_exp (emgr, slice);
    for (i = 1; i < len - 2; i++)
    {
      slice = btor_slice_exp (emgr, xor_sign_e1, i + 1, i + 1);
      and   = btor_and_exp (emgr, slice, temps_e2[i]);
      or    = btor_or_exp (emgr, result, and);
      btor_release_exp (emgr, slice);
      btor_release_exp (emgr, and);
      btor_release_exp (emgr, result);
      result = or ;
    }
    sext_e1         = btor_sext_exp (emgr, e0, 1);
    sext_e2         = btor_sext_exp (emgr, e1, 1);
    mul             = btor_mul_exp (emgr, sext_e1, sext_e2);
    slice_n         = btor_slice_exp (emgr, mul, len, len);
    slice_n_minus_1 = btor_slice_exp (emgr, mul, len - 1, len - 1);
    xor             = btor_xor_exp (emgr, slice_n, slice_n_minus_1);
    or              = btor_or_exp (emgr, result, xor);
    btor_release_exp (emgr, sext_e1);
    btor_release_exp (emgr, sext_e2);
    btor_release_exp (emgr, sign_e1);
    btor_release_exp (emgr, sign_e2);
    btor_release_exp (emgr, sext_sign_e1);
    btor_release_exp (emgr, sext_sign_e2);
    btor_release_exp (emgr, xor_sign_e1);
    btor_release_exp (emgr, xor_sign_e2);
    btor_release_exp (emgr, mul);
    btor_release_exp (emgr, slice_n);
    btor_release_exp (emgr, slice_n_minus_1);
    btor_release_exp (emgr, xor);
    btor_release_exp (emgr, result);
    result = or ;
    for (i = 0; i < len - 2; i++) btor_release_exp (emgr, temps_e2[i]);
    BTOR_DELETEN (emgr->mm, temps_e2, len - 2);
  }
  return result;
}

BtorExp *
btor_ult_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_ULT_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_ULT_EXP, e0, e1, 1);
  return result;
}

BtorExp *
btor_slt_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result         = NULL;
  BtorExp *sign_e1        = NULL;
  BtorExp *sign_e2        = NULL;
  BtorExp *rest_e1        = NULL;
  BtorExp *rest_e2        = NULL;
  BtorExp *ult            = NULL;
  BtorExp *e1_signed_only = NULL;
  BtorExp *e1_e2_pos      = NULL;
  BtorExp *e1_e2_signed   = NULL;
  BtorExp *and1           = NULL;
  BtorExp *and2           = NULL;
  BtorExp * or            = NULL;
  int len                 = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return btor_and_exp (emgr, e0, BTOR_INVERT_EXP (e1));
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  /* rest_e1: e0 without sign bit */
  rest_e1 = btor_slice_exp (emgr, e0, len - 2, 0);
  /* rest_e2: e1 without sign bit */
  rest_e2 = btor_slice_exp (emgr, e1, len - 2, 0);
  /* ult: is rest of e0 < rest of e1 ? */
  ult = btor_ult_exp (emgr, rest_e1, rest_e2);
  /* e1_signed_only: only e0 is negative */
  e1_signed_only = btor_and_exp (emgr, sign_e1, BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_pos: e0 and e1 are positive */
  e1_e2_pos =
      btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e1), BTOR_INVERT_EXP (sign_e2));
  /* e1_e2_signed: e0 and e1 are negative */
  e1_e2_signed = btor_and_exp (emgr, sign_e1, sign_e2);
  and1         = btor_and_exp (emgr, e1_e2_pos, ult);
  and2         = btor_and_exp (emgr, e1_e2_signed, ult);
  or           = btor_or_exp (emgr, and1, and2);
  result       = btor_or_exp (emgr, e1_signed_only, or);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, rest_e1);
  btor_release_exp (emgr, rest_e2);
  btor_release_exp (emgr, ult);
  btor_release_exp (emgr, e1_signed_only);
  btor_release_exp (emgr, e1_e2_pos);
  btor_release_exp (emgr, e1_e2_signed);
  btor_release_exp (emgr, and1);
  btor_release_exp (emgr, and2);
  btor_release_exp (emgr, or);
  return result;
}

BtorExp *
btor_ulte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *ugt    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  ugt    = btor_ult_exp (emgr, e1, e0);
  result = btor_not_exp (emgr, ugt);
  btor_release_exp (emgr, ugt);
  return result;
}

BtorExp *
btor_slte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *sgt    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  sgt    = btor_slt_exp (emgr, e1, e0);
  result = btor_not_exp (emgr, sgt);
  btor_release_exp (emgr, sgt);
  return result;
}

BtorExp *
btor_ugt_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_ult_exp (emgr, e1, e0);
}

BtorExp *
btor_sgt_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  return btor_slt_exp (emgr, e1, e0);
}

BtorExp *
btor_ugte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *ult    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  ult    = btor_ult_exp (emgr, e0, e1);
  result = btor_not_exp (emgr, ult);
  btor_release_exp (emgr, ult);
  return result;
}

BtorExp *
btor_sgte_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *slt    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  slt    = btor_slt_exp (emgr, e0, e1);
  result = btor_not_exp (emgr, slt);
  btor_release_exp (emgr, slt);
  return result;
}

BtorExp *
btor_sll_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_SLL_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_SLL_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_srl_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_SRL_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_SRL_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_sra_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *sign_e1 = NULL;
  BtorExp *srl1    = NULL;
  BtorExp *srl2    = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  srl1    = btor_srl_exp (emgr, e0, e1);
  srl2    = btor_srl_exp (emgr, BTOR_INVERT_EXP (e0), e1);
  result  = btor_cond_exp (emgr, sign_e1, BTOR_INVERT_EXP (srl2), srl1);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, srl1);
  btor_release_exp (emgr, srl2);
  return result;
}

BtorExp *
btor_rol_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *sll    = NULL;
  BtorExp *neg_e2 = NULL;
  BtorExp *srl    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  sll    = btor_sll_exp (emgr, e0, e1);
  neg_e2 = btor_neg_exp (emgr, e1);
  srl    = btor_srl_exp (emgr, e0, neg_e2);
  result = btor_or_exp (emgr, sll, srl);
  btor_release_exp (emgr, sll);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, srl);
  return result;
}

BtorExp *
btor_ror_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *srl    = NULL;
  BtorExp *neg_e2 = NULL;
  BtorExp *sll    = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (btor_is_power_of_2_util (BTOR_REAL_ADDR_EXP (e0)->len));
  assert (btor_log_2_util (BTOR_REAL_ADDR_EXP (e0)->len)
          == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 1);
  srl    = btor_srl_exp (emgr, e0, e1);
  neg_e2 = btor_neg_exp (emgr, e1);
  sll    = btor_sll_exp (emgr, e0, neg_e2);
  result = btor_or_exp (emgr, srl, sll);
  btor_release_exp (emgr, srl);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, sll);
  return result;
}

BtorExp *
btor_sub_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  BtorExp *neg_e2 = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  neg_e2 = btor_neg_exp (emgr, e1);
  result = btor_add_exp (emgr, e0, neg_e2);
  btor_release_exp (emgr, neg_e2);
  return result;
}

BtorExp *
btor_usubo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *uext_e1 = NULL;
  BtorExp *uext_e2 = NULL;
  BtorExp *add1    = NULL;
  BtorExp *add2    = NULL;
  BtorExp *one     = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  uext_e1 = btor_uext_exp (emgr, e0, 1);
  uext_e2 = btor_uext_exp (emgr, BTOR_INVERT_EXP (e1), 1);
  assert (len < INT_MAX);
  one    = btor_one_exp (emgr, len + 1);
  add1   = btor_add_exp (emgr, uext_e2, one);
  add2   = btor_add_exp (emgr, uext_e1, add1);
  result = BTOR_INVERT_EXP (btor_slice_exp (emgr, add2, len, len));
  btor_release_exp (emgr, uext_e1);
  btor_release_exp (emgr, uext_e2);
  btor_release_exp (emgr, add1);
  btor_release_exp (emgr, add2);
  btor_release_exp (emgr, one);
  return result;
}

BtorExp *
btor_ssubo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result      = NULL;
  BtorExp *sign_e1     = NULL;
  BtorExp *sign_e2     = NULL;
  BtorExp *sign_result = NULL;
  BtorExp *sub         = NULL;
  BtorExp *and1        = NULL;
  BtorExp *and2        = NULL;
  BtorExp *or1         = NULL;
  BtorExp *or2         = NULL;
  int len              = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len         = BTOR_REAL_ADDR_EXP (e0)->len;
  sign_e1     = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2     = btor_slice_exp (emgr, e1, len - 1, len - 1);
  sub         = btor_sub_exp (emgr, e0, e1);
  sign_result = btor_slice_exp (emgr, sub, len - 1, len - 1);
  and1        = btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e1), sign_e2);
  or1         = btor_and_exp (emgr, and1, sign_result);
  and2        = btor_and_exp (emgr, sign_e1, BTOR_INVERT_EXP (sign_e2));
  or2         = btor_and_exp (emgr, and2, BTOR_INVERT_EXP (sign_result));
  result      = btor_or_exp (emgr, or1, or2);
  btor_release_exp (emgr, and1);
  btor_release_exp (emgr, and2);
  btor_release_exp (emgr, or1);
  btor_release_exp (emgr, or2);
  btor_release_exp (emgr, sub);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, sign_result);
  return result;
}

BtorExp *
btor_udiv_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_UDIV_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_UDIV_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_sdiv_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result   = NULL;
  BtorExp *sign_e1  = NULL;
  BtorExp *sign_e2  = NULL;
  BtorExp * xor     = NULL;
  BtorExp *neg_e1   = NULL;
  BtorExp *neg_e2   = NULL;
  BtorExp *cond_e1  = NULL;
  BtorExp *cond_e2  = NULL;
  BtorExp *udiv     = NULL;
  BtorExp *neg_udiv = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1)
    return BTOR_INVERT_EXP (btor_and_exp (emgr, BTOR_INVERT_EXP (e0), e1));
  sign_e1 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e2 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  /* xor: must result be signed? */
  xor    = btor_xor_exp (emgr, sign_e1, sign_e2);
  neg_e1 = btor_neg_exp (emgr, e0);
  neg_e2 = btor_neg_exp (emgr, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = btor_cond_exp (emgr, sign_e1, neg_e1, e0);
  cond_e2  = btor_cond_exp (emgr, sign_e2, neg_e2, e1);
  udiv     = btor_udiv_exp (emgr, cond_e1, cond_e2);
  neg_udiv = btor_neg_exp (emgr, udiv);
  /* sign result if necessary */
  result = btor_cond_exp (emgr, xor, neg_udiv, udiv);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, sign_e2);
  btor_release_exp (emgr, xor);
  btor_release_exp (emgr, neg_e1);
  btor_release_exp (emgr, neg_e2);
  btor_release_exp (emgr, cond_e1);
  btor_release_exp (emgr, cond_e2);
  btor_release_exp (emgr, udiv);
  btor_release_exp (emgr, neg_udiv);
  return result;
}

BtorExp *
btor_sdivo_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result  = NULL;
  BtorExp *int_min = NULL;
  BtorExp *ones    = NULL;
  BtorExp *eq1     = NULL;
  BtorExp *eq2     = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  int_min = int_min_exp (emgr, BTOR_REAL_ADDR_EXP (e0)->len);
  ones    = btor_ones_exp (emgr, BTOR_REAL_ADDR_EXP (e1)->len);
  eq1     = btor_eq_exp (emgr, e0, int_min);
  eq2     = btor_eq_exp (emgr, e1, ones);
  result  = btor_and_exp (emgr, eq1, eq2);
  btor_release_exp (emgr, int_min);
  btor_release_exp (emgr, ones);
  btor_release_exp (emgr, eq1);
  btor_release_exp (emgr, eq2);
  return result;
}

BtorExp *
btor_urem_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_UREM_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_UREM_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_srem_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result   = NULL;
  BtorExp *sign_e0  = NULL;
  BtorExp *sign_e1  = NULL;
  BtorExp *neg_e0   = NULL;
  BtorExp *neg_e1   = NULL;
  BtorExp *cond_e0  = NULL;
  BtorExp *cond_e1  = NULL;
  BtorExp *urem     = NULL;
  BtorExp *neg_urem = NULL;
  int len           = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e0)->len;
  if (len == 1) return btor_and_exp (emgr, e0, BTOR_INVERT_EXP (e1));
  sign_e0 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e1 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  neg_e0  = btor_neg_exp (emgr, e0);
  neg_e1  = btor_neg_exp (emgr, e1);
  /* normalize e0 and e1 if necessary */
  cond_e0  = btor_cond_exp (emgr, sign_e0, neg_e0, e0);
  cond_e1  = btor_cond_exp (emgr, sign_e1, neg_e1, e1);
  urem     = btor_urem_exp (emgr, cond_e0, cond_e1);
  neg_urem = btor_neg_exp (emgr, urem);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = btor_cond_exp (emgr, sign_e0, neg_urem, urem);
  btor_release_exp (emgr, sign_e0);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, neg_e0);
  btor_release_exp (emgr, neg_e1);
  btor_release_exp (emgr, cond_e0);
  btor_release_exp (emgr, cond_e1);
  btor_release_exp (emgr, urem);
  btor_release_exp (emgr, neg_urem);
  return result;
}

BtorExp *
btor_smod_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result            = NULL;
  BtorExp *sign_e0           = NULL;
  BtorExp *sign_e1           = NULL;
  BtorExp *neg_e0            = NULL;
  BtorExp *neg_e1            = NULL;
  BtorExp *cond_e0           = NULL;
  BtorExp *cond_e1           = NULL;
  BtorExp *cond_case1        = NULL;
  BtorExp *cond_case2        = NULL;
  BtorExp *cond_case3        = NULL;
  BtorExp *cond_case4        = NULL;
  BtorExp *urem              = NULL;
  BtorExp *neg_urem          = NULL;
  BtorExp *add1              = NULL;
  BtorExp *add2              = NULL;
  BtorExp *or1               = NULL;
  BtorExp *or2               = NULL;
  BtorExp *e0_and_e1         = NULL;
  BtorExp *e0_and_neg_e1     = NULL;
  BtorExp *neg_e0_and_e1     = NULL;
  BtorExp *neg_e0_and_neg_e1 = NULL;
  BtorExp *zeros             = NULL;
  int len                    = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  len     = BTOR_REAL_ADDR_EXP (e0)->len;
  zeros   = btor_zeros_exp (emgr, len);
  sign_e0 = btor_slice_exp (emgr, e0, len - 1, len - 1);
  sign_e1 = btor_slice_exp (emgr, e1, len - 1, len - 1);
  neg_e0  = btor_neg_exp (emgr, e0);
  neg_e1  = btor_neg_exp (emgr, e1);
  e0_and_e1 =
      btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e0), BTOR_INVERT_EXP (sign_e1));
  e0_and_neg_e1     = btor_and_exp (emgr, BTOR_INVERT_EXP (sign_e0), sign_e1);
  neg_e0_and_e1     = btor_and_exp (emgr, sign_e0, BTOR_INVERT_EXP (sign_e1));
  neg_e0_and_neg_e1 = btor_and_exp (emgr, sign_e0, sign_e1);
  /* normalize e0 and e1 if necessary */
  cond_e0    = btor_cond_exp (emgr, sign_e0, neg_e0, e0);
  cond_e1    = btor_cond_exp (emgr, sign_e1, neg_e1, e1);
  urem       = btor_urem_exp (emgr, cond_e0, cond_e1);
  neg_urem   = btor_neg_exp (emgr, urem);
  add1       = btor_add_exp (emgr, neg_urem, e1);
  add2       = btor_add_exp (emgr, urem, e1);
  cond_case1 = btor_cond_exp (emgr, e0_and_e1, urem, zeros);
  cond_case2 = btor_cond_exp (emgr, neg_e0_and_e1, add1, zeros);
  cond_case3 = btor_cond_exp (emgr, e0_and_neg_e1, add2, zeros);
  cond_case4 = btor_cond_exp (emgr, neg_e0_and_neg_e1, neg_urem, zeros);
  or1        = btor_or_exp (emgr, cond_case1, cond_case2);
  or2        = btor_or_exp (emgr, cond_case3, cond_case4);
  result     = btor_or_exp (emgr, or1, or2);
  btor_release_exp (emgr, zeros);
  btor_release_exp (emgr, sign_e0);
  btor_release_exp (emgr, sign_e1);
  btor_release_exp (emgr, neg_e0);
  btor_release_exp (emgr, neg_e1);
  btor_release_exp (emgr, cond_e0);
  btor_release_exp (emgr, cond_e1);
  btor_release_exp (emgr, cond_case1);
  btor_release_exp (emgr, cond_case2);
  btor_release_exp (emgr, cond_case3);
  btor_release_exp (emgr, cond_case4);
  btor_release_exp (emgr, urem);
  btor_release_exp (emgr, neg_urem);
  btor_release_exp (emgr, add1);
  btor_release_exp (emgr, add2);
  btor_release_exp (emgr, or1);
  btor_release_exp (emgr, or2);
  btor_release_exp (emgr, e0_and_e1);
  btor_release_exp (emgr, neg_e0_and_e1);
  btor_release_exp (emgr, e0_and_neg_e1);
  btor_release_exp (emgr, neg_e0_and_neg_e1);
  return result;
}

BtorExp *
btor_concat_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->len
          <= INT_MAX - BTOR_REAL_ADDR_EXP (e1)->len);
  len = BTOR_REAL_ADDR_EXP (e0)->len + BTOR_REAL_ADDR_EXP (e1)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_CONCAT_EXP, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, BTOR_CONCAT_EXP, e0, e1, len);
  return result;
}

BtorExp *
btor_read_exp (BtorExpMgr *emgr, BtorExp *e_array, BtorExp *e_index)
{
  BtorExpPtrStack stack;
  BtorExp *eq     = NULL;
  BtorExp *cond   = NULL;
  BtorExp *result = NULL;
  BtorExp *cur    = NULL;
  BtorMemMgr *mm  = NULL;
  int found       = 0;
  assert (emgr != NULL);
  assert (e_array != NULL);
  assert (e_index != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (e_array->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  mm = emgr->mm;
  if (BTOR_IS_WRITE_ARRAY_EXP (e_array)) /* eagerly encode McCarthy axiom */
  {
    if (emgr->write_enc == BTOR_EAGER_WRITE_ENC)
    {
      BTOR_INIT_STACK (stack);
      /* resolve read over writes */
      cur = e_array;
      while (!found)
      {
        assert (BTOR_IS_REGULAR_EXP (cur));
        assert (BTOR_IS_ARRAY_EXP (cur));
        if (BTOR_IS_WRITE_ARRAY_EXP (cur))
        {
          BTOR_PUSH_STACK (mm, stack, cur);
          cur = cur->e[0];
        }
        else
        {
          assert (BTOR_IS_NATIVE_ARRAY_EXP (cur));
          result = binary_exp (emgr, BTOR_READ_EXP, cur, e_index, cur->len);
          found  = 1;
        }
      }
      assert (!BTOR_EMPTY_STACK (stack));
      do
      {
        cur = BTOR_POP_STACK (stack);
        assert (BTOR_IS_REGULAR_EXP (cur));
        assert (BTOR_IS_ARRAY_EXP (cur));
        /* index equal ? */
        eq   = btor_eq_exp (emgr, cur->e[1], e_index);
        cond = btor_cond_exp (emgr, eq, cur->e[2], result);
        btor_release_exp (emgr, eq);
        btor_release_exp (emgr, result);
        result = cond;
      } while (!BTOR_EMPTY_STACK (stack));
      BTOR_RELEASE_STACK (mm, stack);
      return result;
    }
  }
  return binary_exp (emgr, BTOR_READ_EXP, e_array, e_index, e_array->len);
}

static BtorExp *
ternary_exp (BtorExpMgr *emgr,
             BtorExpKind kind,
             BtorExp *e0,
             BtorExp *e1,
             BtorExp *e2,
             int len)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (len > 0);
  lookup = find_ternary_exp (emgr, kind, e0, e1, e2);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_ternary_exp (emgr, kind, e0, e1, e2);
    }
    *lookup = new_ternary_exp_node (emgr, kind, e0, e1, e2, len);
    inc_exp_ref_counter (e0);
    inc_exp_ref_counter (e1);
    inc_exp_ref_counter (e2);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
    inc_exp_ref_counter (*lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  return *lookup;
}

BtorExp *
btor_cond_exp (BtorExpMgr *emgr,
               BtorExp *e_cond,
               BtorExp *e_if,
               BtorExp *e_else)
{
  BtorExp *result = NULL;
  int len         = 0;
  assert (emgr != NULL);
  assert (e_cond != NULL);
  assert (e_if != NULL);
  assert (e_else != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_else)));
  assert (BTOR_REAL_ADDR_EXP (e_cond)->len == 1);
  assert (BTOR_REAL_ADDR_EXP (e_if)->len == BTOR_REAL_ADDR_EXP (e_else)->len);
  assert (BTOR_REAL_ADDR_EXP (e_if)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e_if)->len;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, BTOR_COND_EXP, e_cond, e_if, e_else, 0, 0);
  if (result == NULL)
    result = ternary_exp (emgr, BTOR_COND_EXP, e_cond, e_if, e_else, len);
  return result;
}

BtorExp *
btor_write_exp (BtorExpMgr *emgr,
                BtorExp *e_array,
                BtorExp *e_index,
                BtorExp *e_value)
{
  BtorExp **lookup = NULL;
  assert (emgr != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)));
  assert (e_array->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  lookup = find_ternary_exp (emgr, BTOR_WRITE_EXP, e_array, e_index, e_value);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup =
          find_ternary_exp (emgr, BTOR_WRITE_EXP, e_array, e_index, e_value);
    }
    *lookup = new_write_exp_node (emgr, e_array, e_index, e_value);
    inc_exp_ref_counter (e_array);
    inc_exp_ref_counter (e_index);
    inc_exp_ref_counter (e_value);
    assert (emgr->table.num_elements < INT_MAX);
    emgr->table.num_elements++;
  }
  else
    inc_exp_ref_counter (*lookup);
  assert (BTOR_IS_REGULAR_EXP (*lookup));
  return *lookup;
}

int
btor_get_exp_len (BtorExpMgr *emgr, BtorExp *exp)
{
  (void) emgr;
  assert (emgr != NULL);
  assert (exp != NULL);
  return BTOR_REAL_ADDR_EXP (exp)->len;
}

int
btor_is_array_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  (void) emgr;
  assert (emgr != NULL);
  assert (exp != NULL);
  return BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp));
}

int
btor_get_index_exp_len (BtorExpMgr *emgr, BtorExp *e_array)
{
  (void) emgr;
  assert (emgr != NULL);
  assert (e_array != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  return e_array->index_len;
}

char *
btor_get_symbol_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  (void) emgr;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)));
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

void
btor_dump_exp (BtorExpMgr *emgr, FILE *file, BtorExp *root)
{
  BtorMemMgr *mm = emgr->mm;
  BtorExpPtrStack stack;
  char idbuffer[20];
  int next, i, j;
  const char *op;
  BtorExp *e;

  next = 0;

  BTOR_INIT_STACK (stack);
  BTOR_PUSH_EXP_IF_NOT_MARKED (root);

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_EXP (e));
    assert (e->mark);

    for (i = 0; i < BTOR_ARITY_EXP (e); i++)
      BTOR_PUSH_EXP_IF_NOT_MARKED (e->e[i]);
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
      case BTOR_COND_EXP: op = "cond"; goto PRINT;
      case BTOR_EQ_EXP: op = "eq"; goto PRINT;
      case BTOR_MUL_EXP: op = "mul"; goto PRINT;
      case BTOR_READ_EXP: op = "read"; goto PRINT;
      case BTOR_SLL_EXP: op = "sll"; goto PRINT;
      case BTOR_SRL_EXP: op = "srl"; goto PRINT;
      case BTOR_UDIV_EXP: op = "udiv"; goto PRINT;
      case BTOR_ULT_EXP: op = "ult"; goto PRINT;
      case BTOR_UREM_EXP: op = "urem"; goto PRINT;
      case BTOR_WRITE_EXP:
        op = "write";
      PRINT:
        fputs (op, file);
        fprintf (file, " %d", e->len);
        for (j = 0; j < BTOR_ARITY_EXP (e); j++)
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

  e = BTOR_REAL_ADDR_EXP (root);
  fprintf (file, "%d root %d %d\n", e->id + 1, e->len, BTOR_GET_ID_EXP (root));
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
  else if (BTOR_IS_ARRAY_EXP (u))
    type = "a";
  else
    type = "?e";

  fprintf (file, "%s%d", type, u->id);

CLOSE:
  if (u != e) fputc (')', file);
}

void
btor_dump_smt (BtorExpMgr *emgr, FILE *file, BtorExp *root)
{
  int next, i, j, arrays, lets, pad;
  BtorMemMgr *mm = emgr->mm;
  BtorExpPtrStack stack;
  const char *op;
  char *tmp;
  BtorExp *e;

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

    if (BTOR_IS_ARRAY_EXP (e))
    {
      arrays = 1;
      continue;
    }

    for (i = 0; i < BTOR_ARITY_EXP (e); i++)
      BTOR_PUSH_EXP_IF_NOT_MARKED (e->e[i]);
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

    if (!BTOR_IS_VAR_EXP (e) && !BTOR_IS_ARRAY_EXP (e)) continue;

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

    if (BTOR_IS_VAR_EXP (e) || BTOR_IS_ARRAY_EXP (e)) continue;

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
    else if (e->kind == BTOR_COND_EXP)
    {
      fputs ("(ite (= bv1[1] ", file);
      btor_dump_smt_id (e->e[0], file);
      fputs (") ", file);
      btor_dump_smt_id (e->e[1], file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[2], file);
      fputc (')', file);
    }
    else if (e->kind == BTOR_EQ_EXP || e->kind == BTOR_ULT_EXP)
    {
      fputs ("(ite (", file);
      if (e->kind == BTOR_EQ_EXP)
        fputc ('=', file);
      else
        fputs ("bvult", file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[0], file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[1], file);
      fputs (") bit1 bit0)", file);
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

      for (j = 0; j < BTOR_ARITY_EXP (e); j++)
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

BtorExpMgr *
btor_new_exp_mgr (int rewrite_level,
                  int dump_trace,
                  int verbosity,
                  FILE *trace_file)
{
  BtorMemMgr *mm   = btor_new_mem_mgr ();
  BtorExpMgr *emgr = NULL;
  assert (mm != NULL);
  assert (sizeof (int) == 4);
  assert (rewrite_level >= 0);
  assert (rewrite_level <= 2);
  assert (verbosity >= -1);
  BTOR_NEW (mm, emgr);
  emgr->mm = mm;
  BTOR_INIT_EXP_UNIQUE_TABLE (mm, emgr->table);
  BTOR_INIT_STACK (emgr->vars);
  BTOR_INIT_STACK (emgr->arrays);
  emgr->avmgr         = btor_new_aigvec_mgr (mm, verbosity);
  emgr->id            = 1;
  emgr->rewrite_level = rewrite_level;
  emgr->dump_trace    = dump_trace;
  emgr->verbosity     = verbosity;
  emgr->read_enc      = BTOR_SAT_SOLVER_READ_ENC;
  emgr->write_enc     = BTOR_LAZY_WRITE_ENC;
  emgr->trace_file    = trace_file;
  emgr->exp_pair_cnf_diff_id_table =
      btor_new_ptr_hash_table (mm, hash_exp_pair, compare_exp_pair);
  emgr->exp_pair_cnf_eq_id_table =
      btor_new_ptr_hash_table (mm, hash_exp_pair, compare_exp_pair);
  return emgr;
}

void
btor_delete_exp_mgr (BtorExpMgr *emgr)
{
  BtorExp **cur             = NULL;
  BtorExp **top             = NULL;
  BtorMemMgr *mm            = NULL;
  BtorPtrHashBucket *bucket = NULL;
  assert (emgr != NULL);
  mm = emgr->mm;
  for (bucket = emgr->exp_pair_cnf_diff_id_table->first; bucket != NULL;
       bucket = bucket->next)
    delete_exp_pair (emgr, (BtorExpPair *) bucket->key);
  btor_delete_ptr_hash_table (emgr->exp_pair_cnf_diff_id_table);
  for (bucket = emgr->exp_pair_cnf_eq_id_table->first; bucket != NULL;
       bucket = bucket->next)
    delete_exp_pair (emgr, (BtorExpPair *) bucket->key);
  btor_delete_ptr_hash_table (emgr->exp_pair_cnf_eq_id_table);
  top = emgr->arrays.top;
  for (cur = emgr->arrays.start; cur != top; cur++)
    delete_exp_node (emgr, *cur);
  top = emgr->vars.top;
  for (cur = emgr->vars.start; cur != top; cur++) delete_exp_node (emgr, *cur);
  assert (emgr->table.num_elements == 0);
  BTOR_RELEASE_EXP_UNIQUE_TABLE (mm, emgr->table);
  BTOR_RELEASE_STACK (mm, emgr->vars);
  BTOR_RELEASE_STACK (mm, emgr->arrays);
  btor_delete_aigvec_mgr (emgr->avmgr);
  BTOR_DELETE (mm, emgr);
  btor_delete_mem_mgr (mm);
}

void
btor_set_read_enc_exp_mgr (BtorExpMgr *emgr, BtorReadEnc read_enc)
{
  assert (emgr != NULL);
  emgr->read_enc = read_enc;
}

void
btor_set_write_enc_exp_mgr (BtorExpMgr *emgr, BtorWriteEnc write_enc)
{
  assert (emgr != NULL);
  emgr->write_enc = write_enc;
}

BtorMemMgr *
btor_get_mem_mgr_exp_mgr (const BtorExpMgr *emgr)
{
  assert (emgr != NULL);
  return emgr->mm;
}

BtorAIGVecMgr *
btor_get_aigvec_mgr_exp_mgr (const BtorExpMgr *emgr)
{
  assert (emgr != NULL);
  return emgr->avmgr;
}

static void
mark_reachable_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorExpPtrStack stack;
  BtorExp *cur   = NULL;
  BtorMemMgr *mm = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  mm = emgr->mm;
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, exp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (!cur->reachable)
    {
      cur->reachable = 1;
      if (BTOR_IS_UNARY_EXP (cur))
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
      else if (BTOR_IS_BINARY_EXP (cur))
      {
        BTOR_PUSH_STACK (mm, stack, cur->e[1]);
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
      }
      else if (BTOR_IS_TERNARY_EXP (cur))
      {
        BTOR_PUSH_STACK (mm, stack, cur->e[2]);
        BTOR_PUSH_STACK (mm, stack, cur->e[1]);
        BTOR_PUSH_STACK (mm, stack, cur->e[0]);
      }
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
}

static void
btor_synthesize_exp (BtorExpMgr *emgr,
                     BtorExp *exp,
                     BtorPtrHashTable *backannoation)
{
  BtorExpPtrStack exp_stack;
  BtorExp *cur         = NULL;
  BtorAIGVec *av0      = NULL;
  BtorAIGVec *av1      = NULL;
  BtorAIGVec *av2      = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorMemMgr *mm       = NULL;
  BtorPtrHashBucket *b;
  char *indexed_name;
  const char *name;
  unsigned count;
  size_t len;
  int i;

  assert (emgr != NULL);
  assert (exp != NULL);

  mm    = emgr->mm;
  avmgr = emgr->avmgr;

  BTOR_INIT_STACK (exp_stack);
  BTOR_PUSH_STACK (mm, exp_stack, exp);

  count = 0;

  while (!BTOR_EMPTY_STACK (exp_stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (exp_stack));
    assert (cur->mark >= 0);
    assert (cur->mark <= 2);
    if (cur->av == NULL && cur->mark < 2)
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
            name         = btor_get_symbol_exp (emgr, cur);
            len          = strlen (name) + 40;
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
        else if (!BTOR_IS_NATIVE_ARRAY_EXP (cur))
        {
          if (BTOR_IS_WRITE_ARRAY_EXP (cur))
          {
            /* writes are only reachable in lazy mode */
            assert (emgr->write_enc != BTOR_EAGER_WRITE_ENC);
            cur->mark = 2;
            /* mark children recursively as reachable */
            mark_reachable_exp (emgr, cur->e[2]);
            mark_reachable_exp (emgr, cur->e[1]);
            mark_reachable_exp (emgr, cur->e[0]);
            /* we do not synthesize children as we are
             * in lazy mode */
          }
          else
          {
            cur->mark = 1;
            BTOR_PUSH_STACK (mm, exp_stack, cur);
            if (cur->kind == BTOR_READ_EXP)
            {
              if (emgr->read_enc == BTOR_EAGER_READ_ENC)
              {
                BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
                BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
              }
              else
              {
                /* mark children recursively as reachable */
                mark_reachable_exp (emgr, cur->e[1]);
                mark_reachable_exp (emgr, cur->e[0]);
                /* we do not synthesize children as we are
                 * in lazy mode */
              }
            }
            else if (BTOR_IS_UNARY_EXP (cur))
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
            else if (BTOR_IS_BINARY_EXP (cur))
            {
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
            }
            else
            {
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[2]);
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
            }
          }
        }
      }
      else
      {
        assert (cur->mark == 1);
        cur->mark = 2;
        if (cur->kind == BTOR_READ_EXP)
        {
          /* generate new AIGs for read */
          cur->av = btor_var_aigvec (avmgr, cur->len);
          assert (BTOR_IS_REGULAR_EXP (cur->e[0]));
          assert (BTOR_IS_ARRAY_EXP (cur->e[0]));
          if (emgr->read_enc == BTOR_EAGER_READ_ENC)
            encode_read_eagerly (emgr, cur->e[0], cur);
        }
        else if (BTOR_IS_UNARY_EXP (cur))
        {
          assert (cur->kind == BTOR_SLICE_EXP);
          av0     = BTOR_GET_AIGVEC_EXP (emgr, cur->e[0]);
          cur->av = btor_slice_aigvec (avmgr, av0, cur->upper, cur->lower);
          btor_release_delete_aigvec (avmgr, av0);
        }
        else if (BTOR_IS_BINARY_EXP (cur))
        {
          av0 = BTOR_GET_AIGVEC_EXP (emgr, cur->e[0]);
          av1 = BTOR_GET_AIGVEC_EXP (emgr, cur->e[1]);
          switch (cur->kind)
          {
            case BTOR_AND_EXP:
              cur->av = btor_and_aigvec (avmgr, av0, av1);
              break;
            case BTOR_EQ_EXP: cur->av = btor_eq_aigvec (avmgr, av0, av1); break;
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
          btor_release_delete_aigvec (avmgr, av0);
          btor_release_delete_aigvec (avmgr, av1);
        }
        else
        {
          assert (BTOR_IS_TERNARY_EXP (cur));
          assert (cur->kind == BTOR_COND_EXP);
          av0     = BTOR_GET_AIGVEC_EXP (emgr, cur->e[0]);
          av1     = BTOR_GET_AIGVEC_EXP (emgr, cur->e[1]);
          av2     = BTOR_GET_AIGVEC_EXP (emgr, cur->e[2]);
          cur->av = btor_cond_aigvec (avmgr, av0, av1, av2);
          btor_release_delete_aigvec (avmgr, av2);
          btor_release_delete_aigvec (avmgr, av1);
          btor_release_delete_aigvec (avmgr, av0);
        }
      }
    }
  }

  BTOR_RELEASE_STACK (mm, exp_stack);
  btor_mark_exp (emgr, exp, 0);

  if (count > 0 && emgr->verbosity > 1)
    print_verbose_msg ("synthesized %u expressions into AIG vectors", count);
}

BtorAIG *
btor_exp_to_aig (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorAIGVecMgr *avmgr = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorMemMgr *mm       = NULL;
  BtorAIG *result      = NULL;
  BtorAIGVec *av       = NULL;

  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);

  mm    = emgr->mm;
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);

  btor_synthesize_exp (emgr, exp, 0);
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
btor_exp_to_aigvec (BtorExpMgr *emgr,
                    BtorExp *exp,
                    BtorPtrHashTable *backannoation)
{
  BtorAIGVecMgr *avmgr = NULL;
  BtorMemMgr *mm       = NULL;
  BtorAIGVec *result   = NULL;

  assert (exp != NULL);

  mm    = emgr->mm;
  avmgr = emgr->avmgr;

  btor_synthesize_exp (emgr, exp, backannoation);
  result = BTOR_REAL_ADDR_EXP (exp)->av;
  assert (result);

  if (BTOR_IS_INVERTED_EXP (exp))
    result = btor_not_aigvec (avmgr, result);
  else
    result = btor_copy_aigvec (avmgr, result);

  return result;
}

void
btor_exp_to_sat (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorAIG *aig     = NULL;
  BtorAIGMgr *amgr = NULL;
  BtorSATMgr *smgr = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  aig  = btor_exp_to_aig (emgr, exp);
  btor_aig_to_sat (amgr, aig);
  if (!BTOR_IS_CONST_AIG (aig))
  {
    assert (BTOR_REAL_ADDR_AIG (aig)->cnf_id != 0);
    btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
    btor_add_sat (smgr, 0);
  }
  btor_release_aig (amgr, aig);
}

/* Compares the assignments of two expressions. */
static int
compare_assignments (BtorExpMgr *emgr, BtorExp *exp1, BtorExp *exp2)
{
  int val1             = 0;
  int val2             = 0;
  int i                = 0;
  int len              = 0;
  int return_val       = 0;
  BtorAIGVecMgr *avmgr = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorAIGVec *av1      = NULL;
  BtorAIGVec *av2      = NULL;
  assert (emgr != NULL);
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp1)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp2)));
  assert (BTOR_REAL_ADDR_EXP (exp1)->len == BTOR_REAL_ADDR_EXP (exp2)->len);
  assert (BTOR_REAL_ADDR_EXP (exp1)->av != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp2)->av != NULL);
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  av1   = BTOR_GET_AIGVEC_EXP (emgr, exp1);
  av2   = BTOR_GET_AIGVEC_EXP (emgr, exp2);
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    val1 = btor_get_assignment_aig (amgr, av1->aigs[i]);
    assert (val1 >= -1);
    assert (val1 <= 1);
    if (val1 == 0) val1 = -1;
    val2 = btor_get_assignment_aig (amgr, av2->aigs[i]);
    assert (val1 >= -1);
    assert (val1 <= 1);
    if (val2 == 0) val2 = -1;
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
  btor_release_delete_aigvec (avmgr, av1);
  btor_release_delete_aigvec (avmgr, av2);
  return return_val;
}

static int
compare_reads_by_index (const void *read1, const void *read2)
{
  BtorExp *exp_read1 = NULL;
  BtorExp *exp_read2 = NULL;
  BtorExp *index1    = NULL;
  BtorExp *index2    = NULL;
  BtorExpMgr *emgr   = NULL;
  assert (read1 != NULL);
  assert (read2 != NULL);
  exp_read1 = *((BtorExp **) read1);
  exp_read2 = *((BtorExp **) read2);
  assert (BTOR_IS_REGULAR_EXP (exp_read1));
  assert (BTOR_IS_REGULAR_EXP (exp_read2));
  assert (exp_read1->kind == BTOR_READ_EXP);
  assert (exp_read2->kind == BTOR_READ_EXP);
  index1 = exp_read1->e[1];
  index2 = exp_read2->e[1];
  emgr   = exp_read1->emgr;
  assert (BTOR_REAL_ADDR_EXP (index1)->len == BTOR_REAL_ADDR_EXP (index2)->len);
  return compare_assignments (emgr, index1, index2);
}

/* Checks for read conflicts on one array */
static int
check_read_conflicts_array (BtorExpMgr *emgr,
                            BtorExp *array,
                            BtorExp **conflict_read1,
                            BtorExp **conflict_read2)
{
  int found_conflict     = 0;
  int num_reads          = 0;
  int i                  = 0;
  BtorMemMgr *mm         = NULL;
  BtorExp *read1         = NULL;
  BtorExp *read2         = NULL;
  BtorExpPtrStack *reads = NULL;
  BtorExp **sort_array   = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (conflict_read1 != NULL);
  assert (conflict_read2 != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  mm         = emgr->mm;
  reads      = array->reads;
  sort_array = reads->start;
  num_reads  = BTOR_COUNT_STACK (*reads);
  if (num_reads > 1)
  {
    i = 0;
    qsort (sort_array, num_reads, sizeof (BtorExp *), compare_reads_by_index);
    for (i = 0; i < num_reads - 1; i++)
    {
      read1 = sort_array[i];
      read2 = sort_array[i + 1];
      assert (BTOR_IS_REGULAR_EXP (read1));
      assert (BTOR_IS_REGULAR_EXP (read2));
      if (compare_assignments (emgr, read1->e[1], read2->e[1]) == 0
          && compare_assignments (emgr, read1, read2) != 0)
      {
        found_conflict  = 1;
        *conflict_read1 = read1;
        *conflict_read2 = read2;
        break;
      }
    }
  }
  return found_conflict;
}

/* Resolves read conflict on the same array */
static void
resolve_read_conflict_one_level (BtorExpMgr *emgr,
                                 BtorExp *read1,
                                 BtorExp *read2)
{
  assert (emgr != NULL);
  assert (read1 != NULL);
  assert (read2 != NULL);
  assert (BTOR_IS_REGULAR_EXP (read1));
  assert (BTOR_IS_REGULAR_EXP (read2));
  assert (read1->kind == BTOR_READ_EXP);
  assert (read2->kind == BTOR_READ_EXP);
  encode_ackermann_constraint (emgr, read1->e[1], read2->e[1], read1, read2);
}

/* Resolves a read conflict across multi levels
 * 'array' is the array where the conflict has been detected
 */
static void
resolve_read_conflict_multi_levels (BtorExpMgr *emgr,
                                    BtorExp *array,
                                    BtorExp *read1,
                                    BtorExp *read2)
{
  BtorExpPtrStack writes;
  BtorExp *cur_write = NULL;
  BtorMemMgr *mm     = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (read1 != NULL);
  assert (read2 != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_REGULAR_EXP (read1));
  assert (BTOR_IS_REGULAR_EXP (read2));
  assert (BTOR_IS_ARRAY_EXP (array));
  assert (read1->kind == BTOR_READ_EXP);
  assert (read2->kind == BTOR_READ_EXP);
  mm = emgr->mm;
  /* collect intermediate writes as premisses
   * for McCarthy constraint */
  if (read1->e[0] != array)
  {
    BTOR_INIT_STACK (writes);
    cur_write = read1->e[0];
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
    do
    {
      BTOR_PUSH_STACK (mm, writes, cur_write);
      cur_write = cur_write->e[0];
      assert (BTOR_IS_REGULAR_EXP (cur_write));
      assert (BTOR_IS_ARRAY_EXP (cur_write));
    } while (cur_write != array);
    encode_mccarthy_constraint (
        emgr, &writes, read1->e[1], read2->e[1], read1, read2);
    BTOR_RELEASE_STACK (mm, writes);
  }
  /* collect intermediate writes as premisses
   * for McCarthy constraint */
  if (read2->e[0] != array)
  {
    BTOR_INIT_STACK (writes);
    cur_write = read2->e[0];
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
    do
    {
      BTOR_PUSH_STACK (mm, writes, cur_write);
      cur_write = cur_write->e[0];
      assert (BTOR_IS_REGULAR_EXP (cur_write));
      assert (BTOR_IS_ARRAY_EXP (cur_write));
    } while (cur_write != array);
    encode_mccarthy_constraint (
        emgr, &writes, read1->e[1], read2->e[1], read1, read2);
    BTOR_RELEASE_STACK (mm, writes);
  }
}

/* Checks if a read conflicts with a write */
static int
check_read_write_conflict (BtorExpMgr *emgr,
                           BtorExp *read,
                           BtorExp *write,
                           int *indices_equal)
{
  assert (emgr != NULL);
  assert (read != NULL);
  assert (write != NULL);
  assert (indices_equal != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (BTOR_IS_REGULAR_EXP (write));
  assert (read->kind == BTOR_READ_EXP);
  assert (BTOR_IS_WRITE_ARRAY_EXP (write));
  if ((*indices_equal =
           compare_assignments (emgr, read->e[1], write->e[1]) == 0)
      && compare_assignments (emgr, read, write->e[2]) != 0)
    return 1;
  return 0;
}

/* Resolves a read write conflict on the same array */
static void
resolve_read_write_conflict_one_level (BtorExpMgr *emgr,
                                       BtorExp *read,
                                       BtorExp *write)
{
  assert (emgr != NULL);
  assert (read != NULL);
  assert (write != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (BTOR_IS_REGULAR_EXP (write));
  assert (read->kind == BTOR_READ_EXP);
  assert (BTOR_IS_WRITE_ARRAY_EXP (write));
  encode_ackermann_constraint (
      emgr, read->e[1], write->e[1], read, write->e[2]);
}

/* Resolves a read write conflict across multi levels */
static void
resolve_read_write_conflict_multi_levels (BtorExpMgr *emgr,
                                          BtorExp *read,
                                          BtorExp *write)
{
  BtorExpPtrStack writes;
  BtorExp *cur_write = NULL;
  BtorMemMgr *mm     = NULL;
  assert (emgr != NULL);
  assert (read != NULL);
  assert (write != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (BTOR_IS_REGULAR_EXP (write));
  assert (read->kind == BTOR_READ_EXP);
  assert (BTOR_IS_WRITE_ARRAY_EXP (write));
  mm = emgr->mm;
  /* collect intermediate writes as
   * premisses for McCarthy constraint */
  BTOR_INIT_STACK (writes);
  cur_write = read->e[0];
  assert (BTOR_IS_REGULAR_EXP (cur_write));
  assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
  do
  {
    BTOR_PUSH_STACK (mm, writes, cur_write);
    cur_write = cur_write->e[0];
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
  } while (cur_write != write);
  encode_mccarthy_constraint (
      emgr, &writes, read->e[1], write->e[1], read, write->e[2]);
  BTOR_RELEASE_STACK (mm, writes);
}

/* Releases the temporary read stack, that is needed by the lazy write
 * algrorithm, of all write parents
 */
static void
release_write_parents_read_stack (BtorExpMgr *emgr, BtorExp *array)
{
  BtorMemMgr *mm     = NULL;
  BtorExp *cur_write = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  mm        = emgr->mm;
  cur_write = array->last_parent;
  assert (BTOR_IS_REGULAR_EXP (cur_write));
  while (cur_write != NULL && cur_write->kind != BTOR_READ_EXP)
  {
    /* array children are always at position 0 */
    assert (BTOR_GET_TAG_EXP (cur_write) == 0);
    assert (cur_write->kind == BTOR_WRITE_EXP);
    if (cur_write->reachable) BTOR_RELEASE_STACK (mm, *cur_write->reads);
    cur_write = cur_write->prev_parent[0];
    assert (BTOR_IS_REGULAR_EXP (cur_write));
  }
}

/* builds the AIGs of read indices of reads
 * on this array and encodes them fully into SAT .
 * If the array is a write, then also the write
 * indices and the write value are synthesized
 * and fully encoded into SAT.
 */
static void
synthesize_and_encode_array (BtorExpMgr *emgr, BtorExp *array)
{
  BtorExp *cur         = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorSATMgr *smgr     = NULL;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  assert (array->reachable);
  assert (!array->synth_enc_array);
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);
  cur   = array->first_parent;
  assert (BTOR_IS_REGULAR_EXP (cur));
  while (cur != NULL && !BTOR_IS_WRITE_ARRAY_EXP (cur))
  {
    assert (BTOR_GET_TAG_EXP (cur) == 0);
    assert (cur->kind == BTOR_READ_EXP);
    if (cur->reachable)
    {
      btor_synthesize_exp (emgr, cur->e[1], NULL);
      btor_synthesize_exp (emgr, cur, NULL);
      btor_aigvec_to_sat_full (avmgr, cur->av);
      cur->full_sat = 1;
      btor_aigvec_to_sat_full (avmgr, BTOR_REAL_ADDR_EXP (cur->e[1])->av);
      BTOR_REAL_ADDR_EXP (cur->e[1])->full_sat = 1;
    }
    cur = cur->next_parent[0];
    assert (BTOR_IS_REGULAR_EXP (cur));
  }
  if (BTOR_IS_WRITE_ARRAY_EXP (array))
  {
    btor_synthesize_exp (emgr, array->e[2], NULL);
    btor_synthesize_exp (emgr, array->e[1], NULL);
    btor_aigvec_to_sat_full (avmgr, BTOR_REAL_ADDR_EXP (array->e[2])->av);
    BTOR_REAL_ADDR_EXP (array->e[2])->full_sat = 1;
    btor_aigvec_to_sat_full (avmgr, BTOR_REAL_ADDR_EXP (array->e[1])->av);
    BTOR_REAL_ADDR_EXP (array->e[1])->full_sat = 1;
  }
  array->synth_enc_array = 1;
  /* update assignments */
  (void) btor_sat_sat (smgr, INT_MAX);
}

static int
resolve_read_write_conflicts_array (BtorExpMgr *emgr, BtorExp *array)
{
  BtorMemMgr *mm         = NULL;
  BtorExp *cur_array     = NULL;
  BtorExp *cur_write     = NULL;
  BtorExp *cur_read      = NULL;
  BtorExp **top          = NULL;
  BtorExp **temp         = NULL;
  BtorExpPtrStack *reads = NULL;
  BtorExpPtrStack stack;
  BtorExp *read_conflict1 = NULL;
  BtorExp *read_conflict2 = NULL;
  int found_conflict      = 0;
  int indices_equal       = 0;
  BtorWriteEnc write_enc  = 0;
  assert (emgr != NULL);
  assert (array != NULL);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  mm        = emgr->mm;
  write_enc = emgr->write_enc;
  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, array);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur_array = BTOR_POP_STACK (stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    if (cur_array->array_mark == 0)
    {
      cur_array->array_mark = 1;
      BTOR_PUSH_STACK (mm, stack, cur_array);
      /* ATTENTION: There can be write parents although
       * they are not reachable from the root.
       * For example the parser might still
       * have a reference to a write, thus it is still in the parent list.
       * We use the reachable flag to determine with which reads and writes
       * we have to deal with.
       */
      if (write_enc == BTOR_LAZY_WRITE_ENC)
      {
        /* push writes on stack */
        cur_write = cur_array->last_parent;
        assert (BTOR_IS_REGULAR_EXP (cur_write));
        while (cur_write != NULL && cur_write->kind != BTOR_READ_EXP)
        {
          /* array children are always at position 0 */
          assert (BTOR_GET_TAG_EXP (cur_write) == 0);
          assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
          if (cur_write->reachable) BTOR_PUSH_STACK (mm, stack, cur_write);
          cur_write = cur_write->prev_parent[0];
          assert (BTOR_IS_REGULAR_EXP (cur_write));
        }
      }
    }
    else
    {
      assert (cur_array->array_mark == 1);
      assert (write_enc == BTOR_LAZY_WRITE_ENC || cur_array == array);
      assert (!BTOR_IS_WRITE_ARRAY_EXP (cur_array) || cur_array->reachable);
      reads = cur_array->reads;
      BTOR_INIT_STACK (*reads);
      if (found_conflict)
      {
        release_write_parents_read_stack (emgr, cur_array);
        continue;
      }
      if (!cur_array->synth_enc_array)
        synthesize_and_encode_array (emgr, cur_array);
      /* push reachable parent reads on read stack */
      cur_read = cur_array->first_parent;
      assert (BTOR_IS_REGULAR_EXP (cur_read));
      while (!found_conflict && cur_read != NULL
             && !BTOR_IS_WRITE_ARRAY_EXP (cur_read))
      {
        /* array children are always at position 0 */
        assert (BTOR_GET_TAG_EXP (cur_read) == 0);
        assert (cur_read->kind == BTOR_READ_EXP);
        if (cur_read->reachable)
        {
          if (write_enc == BTOR_LAZY_WRITE_ENC
              && BTOR_IS_WRITE_ARRAY_EXP (cur_array))
          {
            found_conflict = check_read_write_conflict (
                emgr, cur_read, cur_array, &indices_equal);
            if (found_conflict)
              resolve_read_write_conflict_one_level (emgr, cur_read, cur_array);
            else if (!indices_equal)
              BTOR_PUSH_STACK (mm, *reads, cur_read);
          }
          else
            BTOR_PUSH_STACK (mm, *reads, cur_read);
        }
        cur_read = cur_read->next_parent[0];
        assert (BTOR_IS_REGULAR_EXP (cur_read));
      }
      if (found_conflict)
      {
        release_write_parents_read_stack (emgr, cur_array);
        continue;
      }
      if (write_enc == BTOR_LAZY_WRITE_ENC)
      {
        /* push unresolved reads of parent writes on read stack */
        cur_write = cur_array->last_parent;
        assert (BTOR_IS_REGULAR_EXP (cur_write));
        while (!found_conflict && cur_write != NULL
               && cur_write->kind != BTOR_READ_EXP)
        {
          /* array children are always at position 0 */
          assert (BTOR_GET_TAG_EXP (cur_write) == 0);
          top = cur_write->reads->top;
          for (temp = cur_write->reads->start; !found_conflict && temp != top;
               temp++)
          {
            cur_read = *temp;
            assert (BTOR_IS_REGULAR_EXP (cur_read));
            assert (cur_read->kind == BTOR_READ_EXP);
            if (BTOR_IS_WRITE_ARRAY_EXP (cur_array))
            {
              found_conflict = check_read_write_conflict (
                  emgr, cur_read, cur_array, &indices_equal);
              if (found_conflict)
                resolve_read_write_conflict_multi_levels (
                    emgr, cur_read, cur_array);
              else if (!indices_equal)
                BTOR_PUSH_STACK (mm, *reads, cur_read);
            }
            else
              BTOR_PUSH_STACK (mm, *reads, cur_read);
          }
          cur_write = cur_write->prev_parent[0];
          assert (BTOR_IS_REGULAR_EXP (cur_write));
        }
      }
      if (found_conflict)
      {
        release_write_parents_read_stack (emgr, cur_array);
        continue;
      }
      /* check if read conflicts occur */
      found_conflict = check_read_conflicts_array (
          emgr, cur_array, &read_conflict1, &read_conflict2);
      if (found_conflict)
      {
        assert (read_conflict1 != NULL);
        assert (read_conflict2 != NULL);
        assert (BTOR_IS_REGULAR_EXP (read_conflict1));
        assert (BTOR_IS_REGULAR_EXP (read_conflict2));
        assert (read_conflict1->kind == BTOR_READ_EXP);
        assert (read_conflict2->kind == BTOR_READ_EXP);
        /* two reads are in conflict on this array */
        if (read_conflict1->e[0] == cur_array
            && read_conflict2->e[0] == cur_array)
          resolve_read_conflict_one_level (
              emgr, read_conflict1, read_conflict2);
        else
          resolve_read_conflict_multi_levels (
              emgr, cur_array, read_conflict1, read_conflict2);
      }
      /* free read stacks of parent writes */
      release_write_parents_read_stack (emgr, cur_array);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
  /* release stack of starting array */
  BTOR_RELEASE_STACK (mm, *array->reads);
  mark_exp_bottom_up_arrays (emgr, array, 0);
  return found_conflict;
}

static int
resolve_read_write_conflicts (BtorExpMgr *emgr)
{
  int found_conflict = 0;
  BtorExp **top      = NULL;
  BtorExp **temp     = NULL;
  BtorExp *cur       = NULL;
  assert (emgr != NULL);
  top = emgr->arrays.top;
  for (temp = emgr->arrays.start; !found_conflict && temp != top; temp++)
  {
    cur = *temp;
    assert (BTOR_IS_NATIVE_ARRAY_EXP (cur));
    if (cur->reachable)
      found_conflict = resolve_read_write_conflicts_array (emgr, cur);
  }
  return found_conflict;
}

int
btor_sat_exp (BtorExpMgr *emgr, BtorExp *exp, int incremental)
{
  int sat_result     = 0;
  int found_conflict = 0;
  BtorAIG *aig       = NULL;
  BtorAIGMgr *amgr   = NULL;
  BtorSATMgr *smgr   = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp)->len == 1);
  /* eager read has to imply eager write */
  assert (!emgr->read_enc == BTOR_EAGER_READ_ENC
          || emgr->write_enc == BTOR_EAGER_WRITE_ENC);
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  smgr = btor_get_sat_mgr_aig_mgr (amgr);
  aig  = btor_exp_to_aig (emgr, exp);
  if (aig == BTOR_AIG_FALSE) return BTOR_UNSAT;
  btor_aig_to_sat (amgr, aig);
  if (aig != BTOR_AIG_TRUE)
  {
    assert (BTOR_REAL_ADDR_AIG (aig)->cnf_id != 0);
    if (incremental)
      btor_assume_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
    else
    {
      btor_add_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
      btor_add_sat (smgr, 0);
    }
  }
  sat_result = btor_sat_sat (smgr, INT_MAX);
  if (emgr->read_enc == BTOR_LAZY_READ_ENC
      || emgr->write_enc == BTOR_LAZY_WRITE_ENC)
  {
    while (sat_result != BTOR_UNSAT && sat_result != BTOR_UNKNOWN)
    {
      assert (sat_result == BTOR_SAT);
      found_conflict = resolve_read_write_conflicts (emgr);
      if (!found_conflict) break;
      assert (aig != BTOR_AIG_FALSE);
      if (incremental && aig != BTOR_AIG_TRUE)
      {
        assert (BTOR_REAL_ADDR_AIG (aig)->cnf_id != 0);
        btor_assume_sat (smgr, BTOR_GET_CNF_ID_AIG (aig));
      }
      sat_result = btor_sat_sat (smgr, INT_MAX);
    }
  }
  btor_release_aig (amgr, aig);
  return sat_result;
}

char *
btor_assignment_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  BtorAIGVecMgr *avmgr = NULL;
  char *assignment     = NULL;
  BtorAIGVec *av       = NULL;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  avmgr = emgr->avmgr;
  if (!BTOR_REAL_ADDR_EXP (exp)->reachable
      || BTOR_REAL_ADDR_EXP (exp)->av == NULL)
    return NULL;
  av         = BTOR_GET_AIGVEC_EXP (emgr, exp);
  assignment = btor_assignment_aigvec (avmgr, av);
  btor_release_delete_aigvec (avmgr, av);
  return assignment;
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
