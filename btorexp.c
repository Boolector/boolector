#include "btorexp.h"
#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorconfig.h"
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
  /* statistics */
  int refinements;
  int synthesis_assignment_inconsistencies;
  int read_read_conflicts;
  int read_write_conflicts;
};

struct BtorExpPair
{
  BtorExp *exp1;
  BtorExp *exp2;
};

#define BTOR_COND_INVERT_AIG_EXP(exp, aig) \
  ((BtorAIG *) (((unsigned long int) (exp) &1ul) ^ ((unsigned long int) (aig))))

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
  assert (emgr != NULL);
  assert (string != NULL);
  assert (len > 0);
  (void) emgr;
  for (i = 0; i < len; i++)
    if (string[i] != '0') return 0;
  return 1;
}

static int
is_one_string (BtorExpMgr *emgr, const char *string, int len)
{
  int i = 0;
  assert (emgr != NULL);
  assert (string != NULL);
  assert (len > 0);
  (void) emgr;
  if (string[len - 1] != '1') return 0;
  for (i = 0; i < len - 1; i++)
    if (string[i] != '0') return 0;
  return 1;
}

/* Creates an expression pair which can be compared with
 * other expression pairs via the function
 * 'compare_exp_pair'
 */
static BtorExpPair *
new_exp_pair (BtorExpMgr *emgr, BtorExp *exp1, BtorExp *exp2)
{
  int id1             = 0;
  int id2             = 0;
  BtorExpPair *result = NULL;
  assert (emgr != NULL);
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  BTOR_NEW (emgr->mm, result);
  id1 = BTOR_GET_ID_EXP (exp1);
  id2 = BTOR_GET_ID_EXP (exp2);
  assert (id1 != id2);
  if (id2 < id1)
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
hash_exp_pair (BtorExpPair *pair)
{
  unsigned int result = 0u;
  assert (pair != NULL);
  result = (unsigned int) BTOR_REAL_ADDR_EXP (pair->exp1)->id;
  result += (unsigned int) BTOR_REAL_ADDR_EXP (pair->exp2)->id;
  result *= 7334147u;
  return result;
}

static int
compare_exp_pair (BtorExpPair *pair1, BtorExpPair *pair2)
{
  int result = 0;
  assert (pair1 != NULL);
  assert (pair2 != NULL);
  result = BTOR_GET_ID_EXP (pair1->exp1);
  result -= BTOR_GET_ID_EXP (pair2->exp1);
  if (result != 0) return result;
  result = BTOR_GET_ID_EXP (pair1->exp2);
  result -= BTOR_GET_ID_EXP (pair2->exp2);
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
 * forall (0 <= k < n) (i_k v j_k v !d_k) ^ (!i_k v !j_k v !d_k)) ^
 * (forall (0 <= k < n) (d_k) v e) ^
 * forall (0 <= k < m) ((!e v a_k v !b_k) ^ (!e v !a_k v b_k))
 *
 * This function is called in eager read mode only. We have to check
 * if we have to encode a constraint at all. For example if we are in eager
 * mode and the indices are constants and not equal, then we do not have
 * to encode a constraint.
 */
static void
encode_ackermann_constraint_eagerly (
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
  int len_a_b             = 0;
  int len_i_j             = 0;
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
  assert (emgr->read_enc == BTOR_EAGER_READ_ENC);
  mm    = emgr->mm;
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr  = btor_get_sat_mgr_aig_mgr (amgr);
  av_i  = BTOR_REAL_ADDR_EXP (i)->av;
  av_j  = BTOR_REAL_ADDR_EXP (j)->av;
  av_a  = BTOR_REAL_ADDR_EXP (a)->av;
  av_b  = BTOR_REAL_ADDR_EXP (b)->av;
  assert (av_i != NULL);
  assert (av_j != NULL);
  assert (av_a != NULL);
  assert (av_b != NULL);
  assert (av_a->len == av_b->len);
  assert (av_i->len == av_j->len);
  len_a_b = av_a->len;
  len_i_j = av_i->len;
  /* check if a and b have equal AIGs */
  is_equal_a_b = 1;
  for (k = 0; k < len_a_b; k++)
  {
    if (BTOR_COND_INVERT_AIG_EXP (a, av_a->aigs[k])
        != BTOR_COND_INVERT_AIG_EXP (b, av_b->aigs[k]))
    {
      is_equal_a_b = 0;
      break;
    }
  }
  /* check if i and j have equal AIGs */
  is_equal_i_j = 1;
  for (k = 0; k < len_i_j; k++)
  {
    if (BTOR_COND_INVERT_AIG_EXP (i, av_i->aigs[k])
        != BTOR_COND_INVERT_AIG_EXP (j, av_j->aigs[k]))
    {
      is_equal_i_j = 0;
      break;
    }
  }
  for (k = 0; k < len_i_j; k++)
  {
    if ((((unsigned long int) BTOR_COND_INVERT_AIG_EXP (i, av_i->aigs[k]))
         ^ ((unsigned long int) BTOR_COND_INVERT_AIG_EXP (j, av_j->aigs[k])))
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
    for (k = 0; k < len_i_j; k++)
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
  for (k = 0; k < len_a_b; k++)
  {
    aig1 = BTOR_COND_INVERT_AIG_EXP (a, av_a->aigs[k]);
    aig2 = BTOR_COND_INVERT_AIG_EXP (b, av_b->aigs[k]);
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
}

/* Encodes Ackermann constraint of the form index i = index j =>
 * value a = value b directly into CNF.
 * Let n be the number of bits of the indices
 * and m the number of bits of the values:
 * i = j => a = b
 * (i = j => e) ^ (e => a = b)
 * ((i != j) v e) ^ (not e v (a = b))
 * forall (0 <= k < n) (i_k v j_k v !d_k) ^ (!i_k v !j_k v !d_k)) ^
 * (forall (0 <= k < n) (d_k) v e) ^
 * forall (0 <= k < m) ((!e v a_k v !b_k) ^ (!e v !a_k v b_k))
 *
 * This function may not be called from eager read mode. We have to check
 * if we have to encode a constraint at all. For example if we are in eager
 * mode and the indices are constants and not equal, then we do not have
 * to encode a constraint.
 */
static void
encode_ackermann_constraint_lazily (
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
  int k                                        = 0;
  int len_a_b                                  = 0;
  int len_i_j                                  = 0;
  int i_k                                      = 0;
  int j_k                                      = 0;
  int d_k                                      = 0;
  int e                                        = 0;
  int a_k                                      = 0;
  int b_k                                      = 0;
  int is_equal_i_j                             = 0;
  BtorExpPair *pair                            = NULL;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table = NULL;
  BtorPtrHashTable *exp_pair_cnf_eq_id_table   = NULL;
  BtorPtrHashBucket *bucket                    = NULL;
  assert (emgr != NULL);
  assert (i != NULL);
  assert (j != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (emgr->read_enc != BTOR_EAGER_READ_ENC);
  exp_pair_cnf_diff_id_table = emgr->exp_pair_cnf_diff_id_table;
  exp_pair_cnf_eq_id_table   = emgr->exp_pair_cnf_eq_id_table;
  mm                         = emgr->mm;
  avmgr                      = emgr->avmgr;
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
  len_a_b = av_a->len;
  len_i_j = av_i->len;
  BTOR_INIT_STACK (diffs);
  /* check if i and j have equal AIGs */
  is_equal_i_j = 1;
  for (k = 0; k < len_i_j; k++)
  {
    if (BTOR_COND_INVERT_AIG_EXP (i, av_i->aigs[k])
        != BTOR_COND_INVERT_AIG_EXP (j, av_j->aigs[k]))
    {
      is_equal_i_j = 0;
      break;
    }
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
    pair = new_exp_pair (emgr, i, j);
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
      for (k = 0; k < len_i_j; k++)
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
        /* The bits cannot be the inverse of each other.
         * We check this at the beginning of the function.
         */
        assert ((((unsigned long int) aig1) ^ ((unsigned long int) aig2))
                != 1ul);
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
    }
    else
    {
      /* we have already encoded i != j,
       * we simply reuse all diffs */
      d_k = bucket->data.asInt;
      delete_exp_pair (emgr, pair);
      for (k = 0; k < len_i_j; k++)
      {
        d_k++;
        BTOR_PUSH_STACK (mm, diffs, d_k);
      }
    }
  }
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
  pair = new_exp_pair (emgr, a, b);
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
  }
  else
  {
    /* we have already encoded a = b into SAT
     * we simply reuse e */
    e = bucket->data.asInt;
    delete_exp_pair (emgr, pair);
  }
  while (!BTOR_EMPTY_STACK (diffs))
  {
    k = BTOR_POP_STACK (diffs);
    assert (k != 0);
    btor_add_sat (smgr, k);
  }
  assert (e != 0);
  btor_add_sat (smgr, e);
  btor_add_sat (smgr, 0);
  BTOR_RELEASE_STACK (mm, diffs);
}

/* This function is used to encode constraints of the form
 * array equality 1 ^ ... ^ i != k1 ^ i != k2 ^ ... ^ i != kn ^ i = j => a = b
 * The stack 'writes' contains intermediate writes.
 * The stack 'aeqs' contains intermediate array equalities (true)
 * The indices of the writes represent k.
 *
 * This function is called in lazy mode only. Thus, We have to encode a
 * constraint in every case, because a conflict must have been detected
 * before.
 */
static void
encode_mccarthy_constraint (BtorExpMgr *emgr,
                            BtorExpPtrStack *writes,
                            BtorExpPtrStack *aeqs,
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
  BtorExp *w_index                             = NULL;
  BtorExp **temp                               = NULL;
  BtorExp *cur_write                           = NULL;
  BtorExp **top                                = NULL;
  BtorExp *aeq                                 = NULL;
  BtorExpPair *pair                            = NULL;
  BtorPtrHashTable *exp_pair_cnf_diff_id_table = NULL;
  BtorPtrHashTable *exp_pair_cnf_eq_id_table   = NULL;
  BtorPtrHashBucket *bucket                    = NULL;
  BtorIntStack linking_clause;
  int len_a_b   = 0;
  int len_i_j_w = 0;
  int k         = 0;
  int a_k       = 0;
  int b_k       = 0;
  int i_k       = 0;
  int j_k       = 0;
  int d_k       = 0;
  int w_k       = 0;
  int e         = 0;
  assert (emgr != NULL);
  assert (writes != NULL);
  assert (aeqs != NULL);
  assert (i != NULL);
  assert (j != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (i)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (j)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (a)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (b)));
  assert (BTOR_COUNT_STACK (*writes) + BTOR_COUNT_STACK (*aeqs) > 0);
  exp_pair_cnf_diff_id_table = emgr->exp_pair_cnf_diff_id_table;
  exp_pair_cnf_eq_id_table   = emgr->exp_pair_cnf_eq_id_table;
  mm                         = emgr->mm;
  avmgr                      = emgr->avmgr;
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
  BTOR_INIT_STACK (linking_clause);
  /* encode i != j */
  if (i != j)
  {
    pair = new_exp_pair (emgr, i, j);
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
    else
    {
      /* we have already encoded i != j,
       * we simply reuse all diffs for the linking clause */
      d_k = bucket->data.asInt;
      delete_exp_pair (emgr, pair);
      for (k = 0; k < len_i_j_w; k++)
      {
        d_k++;
        BTOR_PUSH_STACK (mm, linking_clause, d_k);
      }
    }
  }
  /* encode a = b */
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
  pair = new_exp_pair (emgr, a, b);
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
  }
  else
  {
    /* we have already encoded a = b into SAT
     * we simply reuse e for the linking clause */
    e = bucket->data.asInt;
    delete_exp_pair (emgr, pair);
  }
  assert (e != 0);
  BTOR_PUSH_STACK (mm, linking_clause, e);
  /* encode i != write index premisses */
  top = writes->top;
  for (temp = writes->start; temp != top; temp++)
  {
    cur_write = *temp;
    assert (BTOR_IS_REGULAR_EXP (cur_write));
    assert (BTOR_IS_WRITE_ARRAY_EXP (cur_write));
    w_index = cur_write->e[1];
    av_w    = BTOR_REAL_ADDR_EXP (w_index)->av;
    assert (av_w->len == len_i_j_w);
    if (!BTOR_REAL_ADDR_EXP (w_index)->full_sat)
    {
      btor_aigvec_to_sat_full (avmgr, av_w);
      BTOR_REAL_ADDR_EXP (w_index)->full_sat = 1;
    }
    pair = new_exp_pair (emgr, i, w_index);
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
    }
    else
    {
      /* we have already encoded i != w_j into SAT
       * we simply reuse e for the linking clause */
      e = bucket->data.asInt;
      delete_exp_pair (emgr, pair);
    }
    assert (e != 0);
    BTOR_PUSH_STACK (mm, linking_clause, e);
  }
  /* add to linking clause array equalites in the premisse */
  top = aeqs->top;
  for (temp = aeqs->start; temp != top; temp++)
  {
    aeq = *temp;
    assert (BTOR_IS_REGULAR_EXP (aeq));
    assert (aeq->kind == BTOR_AEQ_EXP);
    assert (aeq->av->len == 1);
    assert (!BTOR_IS_INVERTED_AIG (aeq->av->aigs[0]));
    assert (!BTOR_IS_CONST_AIG (aeq->av->aigs[0]));
    assert (BTOR_IS_VAR_AIG (aeq->av->aigs[0]));
    k = aeq->av->aigs[0]->cnf_id;
    BTOR_PUSH_STACK (mm, linking_clause, -k);
  }
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
encode_array_inequality_virtual_reads (BtorExpMgr *emgr, BtorExp *aeq)
{
  BtorExpPair *vreads  = NULL;
  BtorExp *read1       = NULL;
  BtorExp *read2       = NULL;
  BtorMemMgr *mm       = NULL;
  BtorAIGVec *av1      = NULL;
  BtorAIGVec *av2      = NULL;
  BtorAIG *aig1        = NULL;
  BtorAIG *aig2        = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorSATMgr *smgr     = NULL;
  int k                = 0;
  int len              = 0;
  int d_k              = 0;
  int r1_k             = 0;
  int r2_k             = 0;
  int e                = 0;
  BtorIntStack diffs;
  assert (emgr != NULL);
  assert (aeq != NULL);
  assert (BTOR_IS_REGULAR_EXP (aeq));
  assert (aeq->kind == BTOR_AEQ_EXP);
  assert (!aeq->full_sat);
  assert (aeq->vreads != NULL);
  mm     = emgr->mm;
  avmgr  = emgr->avmgr;
  amgr   = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr   = btor_get_sat_mgr_aig_mgr (amgr);
  vreads = aeq->vreads;

  read1 = vreads->exp1;
  assert (BTOR_IS_REGULAR_EXP (read1));
  assert (read1->kind == BTOR_READ_EXP);
  assert (read1->av != NULL);
  assert (!read1->full_sat);

  read2 = vreads->exp2;
  assert (BTOR_IS_REGULAR_EXP (read2));
  assert (read2->kind == BTOR_READ_EXP);
  assert (read2->av != NULL);
  assert (!read2->full_sat);

  assert (read1->e[1] == read2->e[1]);
  assert (BTOR_IS_REGULAR_EXP (read1->e[1]));
  assert (BTOR_IS_VAR_EXP (read1->e[1]));
  assert (read1->len == read2->len);

  /* assign aig cnf indices as there are only variables,
   * no SAT constraints are generated */
  btor_aigvec_to_sat_full (avmgr, aeq->av);
  aeq->full_sat = 1;
  btor_aigvec_to_sat_full (avmgr, read1->av);
  read1->full_sat = 1;
  btor_aigvec_to_sat_full (avmgr, read2->av);
  read2->full_sat = 1;

  /* encode !e => r1 != r2 */

  BTOR_INIT_STACK (diffs);
  len = read1->len;

  av1 = read1->av;
  assert (av1 != NULL);
  av2 = read2->av;
  assert (av2 != NULL);

  /* we do not need to hash the diffs as we never use
   * value1 != value2 in a lazy constraint read encoding */

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

  assert (aeq->av != NULL);
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

  /* encode r1 != r2 => !e */

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

    btor_add_sat (smgr, -e);
    btor_add_sat (smgr, r1_k);
    btor_add_sat (smgr, -r2_k);
    btor_add_sat (smgr, 0);

    btor_add_sat (smgr, -e);
    btor_add_sat (smgr, -r1_k);
    btor_add_sat (smgr, r2_k);
    btor_add_sat (smgr, 0);
  }
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
  /* read expressions are at the beginning of the parent list */
  while (cur != NULL && BTOR_REAL_ADDR_EXP (cur)->kind == BTOR_READ_EXP)
  {
    assert (BTOR_GET_TAG_EXP (cur) == 0);
    assert (BTOR_IS_REGULAR_EXP (cur));
    if (cur->encoded_read)
      encode_ackermann_constraint_eagerly (
          emgr, cur->e[1], read->e[1], cur, read);
    cur = cur->next_parent[0];
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
  assert (len > 0);
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
  assert (len > 0);
  string = btor_unsigned_to_const (emgr->mm, u, len);
  result = btor_const_exp (emgr, string);
  btor_delete_const (emgr->mm, string);
  return result;
}

/* Connects child to its parent and updates list of parent pointers.
 * Expressions are inserted in front of the parent list
 */
static void
connect_child_exp (BtorExpMgr *emgr, BtorExp *parent, BtorExp *child, int pos)
{
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
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (!BTOR_IS_WRITE_ARRAY_EXP (parent) || pos == 1 || pos == 2);
  assert (parent->kind != BTOR_AEQ_EXP);
  assert (parent->kind != BTOR_ACOND_EXP);
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
    i                        = BTOR_GET_TAG_EXP (first_parent);
    BTOR_REAL_ADDR_EXP (first_parent)->prev_parent[i] = tagged_parent;
    real_child->first_parent                          = tagged_parent;
  }
}

/* Connects array child to write parent.
 * Writes are appended to the end of the parent list
 */
static void
connect_child_write_exp (BtorExpMgr *emgr, BtorExp *parent, BtorExp *child)
{
  BtorExp *last_parent = NULL;
  int i                = 0;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (BTOR_IS_WRITE_ARRAY_EXP (parent));
  assert (BTOR_IS_REGULAR_EXP (child));
  assert (BTOR_IS_ARRAY_EXP (child));
  (void) emgr;
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
    i                      = BTOR_GET_TAG_EXP (last_parent);
    BTOR_REAL_ADDR_EXP (last_parent)->next_parent[i] = parent;
    child->last_parent                               = parent;
  }
}

/* Connects array child to array equality parent or array conditional parent.
 * Array equalites and array conditionals are inserted in the middle
 * of the parent list
 */
static void
connect_child_aeq_acond_exp (BtorExpMgr *emgr,
                             BtorExp *parent,
                             BtorExp *child,
                             int pos)
{
  BtorExp *first_parent           = NULL;
  BtorExp *last_parent            = NULL;
  BtorExp *prev_parent            = NULL;
  BtorExp *cur_parent             = NULL;
  BtorExp *tagged_parent          = NULL;
  BtorExp *first_aeq_acond_parent = NULL;
  int i                           = 0;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (child != NULL);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (parent->kind == BTOR_AEQ_EXP || parent->kind == BTOR_ACOND_EXP);
  assert (BTOR_IS_REGULAR_EXP (child));
  assert (BTOR_IS_ARRAY_EXP (child));
  assert (parent->kind != BTOR_AEQ_EXP || pos == 0 || pos == 1);
  assert (parent->kind != BTOR_ACOND_EXP || pos == 1 || pos == 2);
  (void) emgr;
  parent->e[pos]         = child;
  tagged_parent          = BTOR_TAG_EXP (parent, pos);
  first_aeq_acond_parent = child->first_aeq_acond_parent;
  if (first_aeq_acond_parent == NULL)
  {
    /* set first aeq acond parent */
    child->first_aeq_acond_parent = tagged_parent;
    /* no parent so far ? */
    if (child->first_parent == NULL)
    {
      assert (child->last_parent == NULL);
      child->first_parent = tagged_parent;
      child->last_parent  = tagged_parent;
      assert (parent->prev_parent[pos] == NULL);
      assert (parent->next_parent[pos] == NULL);
    }
    else
    {
      /* look for insertion place */
      assert (child->first_parent != NULL);
      assert (child->last_parent != NULL);
      /* check if no reads have been inserted in parent list so far */
      if (BTOR_REAL_ADDR_EXP (child->first_parent)->kind != BTOR_READ_EXP)
      {
        first_parent = child->first_parent;
        assert (BTOR_IS_REGULAR_EXP (first_parent));
        assert (BTOR_IS_WRITE_ARRAY_EXP (first_parent));
        assert (BTOR_GET_TAG_EXP (first_parent) == 0);
        /* insert at the beginning of the list */
        parent->next_parent[pos]     = first_parent;
        first_parent->prev_parent[0] = tagged_parent;
        child->first_parent          = tagged_parent;
      }
      /* check if no writes have been inserted in parent list so far */
      else if (!BTOR_IS_WRITE_ARRAY_EXP (
                   BTOR_REAL_ADDR_EXP (child->last_parent)))
      {
        last_parent = child->last_parent;
        assert (BTOR_IS_REGULAR_EXP (last_parent));
        assert (last_parent->kind == BTOR_READ_EXP);
        assert (BTOR_GET_TAG_EXP (last_parent) == 0);
        /* append to the end of the list */
        parent->prev_parent[pos]    = last_parent;
        last_parent->next_parent[0] = tagged_parent;
        child->last_parent          = tagged_parent;
      }
      else
      {
        /* search from the end of the list until we reach the
         * first write after a read
         */
        assert (BTOR_IS_REGULAR_EXP (child->first_parent));
        assert (child->first_parent->kind == BTOR_READ_EXP);
        assert (BTOR_GET_TAG_EXP (child->first_parent) == 0);
        assert (BTOR_IS_REGULAR_EXP (child->last_parent));
        assert (BTOR_IS_WRITE_ARRAY_EXP (child->last_parent));
        assert (BTOR_GET_TAG_EXP (child->last_parent) == 0);
        prev_parent = child->last_parent;
        do
        {
          cur_parent = prev_parent;
          assert (BTOR_IS_REGULAR_EXP (cur_parent));
          assert (BTOR_IS_WRITE_ARRAY_EXP (cur_parent));
          assert (BTOR_GET_TAG_EXP (cur_parent) == 0);
          prev_parent = cur_parent->prev_parent[0];
          assert (prev_parent != NULL);
          assert (BTOR_IS_REGULAR_EXP (prev_parent));
          assert (prev_parent->kind == BTOR_READ_EXP
                  || BTOR_IS_WRITE_ARRAY_EXP (prev_parent));
        } while (BTOR_IS_WRITE_ARRAY_EXP (prev_parent));
        /* insert */
        assert (BTOR_IS_REGULAR_EXP (prev_parent));
        assert (prev_parent->kind == BTOR_READ_EXP);
        assert (BTOR_GET_TAG_EXP (prev_parent) == 0);
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
        assert (BTOR_IS_WRITE_ARRAY_EXP (cur_parent));
        assert (BTOR_GET_TAG_EXP (cur_parent) == 0);
        prev_parent->next_parent[0] = tagged_parent;
        cur_parent->prev_parent[0]  = tagged_parent;
        parent->next_parent[pos]    = cur_parent;
        parent->prev_parent[pos]    = prev_parent;
      }
    }
  }
  else
  {
    /* insert in front of other array equalities and array conditionals,
     * in the middle of the parent list
     */
    parent->next_parent[pos] = first_aeq_acond_parent;
    i                        = BTOR_GET_TAG_EXP (first_aeq_acond_parent);
    prev_parent = BTOR_REAL_ADDR_EXP (first_aeq_acond_parent)->prev_parent[i];
    if (prev_parent != NULL)
    {
      assert (BTOR_IS_REGULAR_EXP (prev_parent));
      assert (prev_parent->kind == BTOR_READ_EXP);
      assert (BTOR_GET_TAG_EXP (prev_parent) == 0);
      prev_parent->next_parent[0] = tagged_parent;
      parent->prev_parent[pos]    = prev_parent;
    }
    else
    {
      assert (parent->prev_parent[pos] == NULL);
      assert (child->first_parent == first_aeq_acond_parent);
      child->first_parent = tagged_parent;
    }
    BTOR_REAL_ADDR_EXP (first_aeq_acond_parent)->prev_parent[i] = tagged_parent;
    child->first_aeq_acond_parent                               = tagged_parent;
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
  BtorExp *first_aeq_acond_parent = NULL;
  BtorExp *next_parent            = NULL;
  BtorExp *tagged_parent          = NULL;
  BtorExp *first_parent           = NULL;
  BtorExp *last_parent            = NULL;
  BtorExp *real_first_parent      = NULL;
  BtorExp *real_last_parent       = NULL;
  BtorExp *real_child             = NULL;
  int i                           = 0;
  assert (emgr != NULL);
  assert (parent != NULL);
  assert (pos >= 0);
  assert (pos <= 2);
  assert (BTOR_IS_REGULAR_EXP (parent));
  assert (!BTOR_IS_CONST_EXP (parent));
  assert (!BTOR_IS_VAR_EXP (parent));
  assert (!BTOR_IS_NATIVE_ARRAY_EXP (parent));
  (void) emgr;
  tagged_parent = BTOR_TAG_EXP (parent, pos);
  real_child    = BTOR_REAL_ADDR_EXP (parent->e[pos]);
  first_parent  = real_child->first_parent;
  last_parent   = real_child->last_parent;
  assert (first_parent != NULL);
  assert (last_parent != NULL);
  real_first_parent = BTOR_REAL_ADDR_EXP (first_parent);
  real_last_parent  = BTOR_REAL_ADDR_EXP (last_parent);
  /* special treatment of aeq and acond parents */
  assert (!(parent->kind == BTOR_AEQ_EXP || parent->kind == BTOR_ACOND_EXP)
          || real_child->first_aeq_acond_parent != NULL);
  if ((parent->kind == BTOR_AEQ_EXP || parent->kind == BTOR_ACOND_EXP)
      && BTOR_REAL_ADDR_EXP (real_child->first_aeq_acond_parent) == parent)
  {
    first_aeq_acond_parent = real_child->first_aeq_acond_parent;
    /* update first_aeq_acond_parent pointer */
    i           = BTOR_GET_TAG_EXP (first_aeq_acond_parent);
    next_parent = BTOR_REAL_ADDR_EXP (first_aeq_acond_parent)->next_parent[i];
    /* last aeq or acond ? */
    if (next_parent == NULL
        || BTOR_IS_WRITE_ARRAY_EXP (BTOR_REAL_ADDR_EXP (next_parent)))
      real_child->first_aeq_acond_parent = NULL;
    else
    {
      /* first aeq or acond parent is next parent */
      assert (BTOR_REAL_ADDR_EXP (next_parent)->kind == BTOR_AEQ_EXP
              || BTOR_REAL_ADDR_EXP (next_parent)->kind == BTOR_ACOND_EXP);
      real_child->first_aeq_acond_parent = next_parent;
    }
  }
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
  parent->next_parent[pos] = NULL;
  parent->prev_parent[pos] = NULL;
  parent->e[pos]           = NULL;
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
  /* special treatment of array equalities in parent list */
  if (kind == BTOR_AEQ_EXP)
  {
    connect_child_aeq_acond_exp (emgr, exp, e0, 0);
    connect_child_aeq_acond_exp (emgr, exp, e1, 1);
  }
  else
  {
    connect_child_exp (emgr, exp, e0, 0);
    connect_child_exp (emgr, exp, e1, 1);
  }
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
  assert (kind == BTOR_BCOND_EXP);
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
  /* append writes to the end of parrent list */
  connect_child_write_exp (emgr, exp, e_array);
  connect_child_exp (emgr, exp, e_index, 1);
  connect_child_exp (emgr, exp, e_value, 2);
  return exp;
}

static BtorExp *
new_acond_exp_node (BtorExpMgr *emgr,
                    BtorExp *e_cond,
                    BtorExp *a_if,
                    BtorExp *a_else)
{
  BtorMemMgr *mm = NULL;
  BtorExp *exp   = NULL;
  assert (emgr != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (BTOR_IS_REGULAR_EXP (a_if));
  assert (BTOR_IS_REGULAR_EXP (a_else));
  assert (BTOR_IS_ARRAY_EXP (a_if));
  assert (BTOR_IS_ARRAY_EXP (a_else));
  assert (a_if->index_len == a_else->index_len);
  assert (a_if->index_len > 0);
  assert (a_if->len == a_else->len);
  assert (a_if->len > 0);
  mm = emgr->mm;
  BTOR_CNEW (mm, exp);
  exp->kind      = BTOR_ACOND_EXP;
  exp->index_len = a_if->index_len;
  exp->len       = a_if->len;
  exp->id        = emgr->id++;
  exp->refs      = 1;
  exp->emgr      = emgr;
  connect_child_exp (emgr, exp, e_cond, 0);
  connect_child_exp (emgr, exp, a_if, 1);
  connect_child_exp (emgr, exp, a_else, 2);
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
  if (!BTOR_IS_NATIVE_ARRAY_EXP (exp))
  {
    if (BTOR_IS_CONST_EXP (exp))
      btor_freestr (mm, exp->bits);
    else if (BTOR_IS_VAR_EXP (exp))
      btor_freestr (mm, exp->symbol);
    else if (BTOR_IS_WRITE_ARRAY_EXP (exp))
    {
      disconnect_child_exp (emgr, exp, 0);
      disconnect_child_exp (emgr, exp, 1);
      disconnect_child_exp (emgr, exp, 2);
    }
    else if (BTOR_IS_UNARY_EXP (exp))
      disconnect_child_exp (emgr, exp, 0);
    else if (BTOR_IS_BINARY_EXP (exp))
    {
      /* release virtual reads */
      if (exp->kind == BTOR_AEQ_EXP && exp->vreads != NULL)
        delete_exp_pair (emgr, exp->vreads);
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
  assert (emgr != NULL);
  assert (exp != NULL);
  (void) emgr;
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
  BtorExp *result       = NULL;
  BtorExp *real_e0      = NULL;
  BtorExp *real_e1      = NULL;
  BtorExp *real_e2      = NULL;
  BtorExp *temp         = NULL;
  BtorMemMgr *mm        = NULL;
  char *bresult         = NULL;
  char *b0              = NULL;
  char *b1              = NULL;
  int invert_b0         = 0;
  int invert_b1         = 0;
  int same_children_mem = 0;
  int i                 = 0;
  int diff              = 0;
  int len               = 0;
  int counter           = 0;
  int is_zero           = 0;
  int is_one            = 0;
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
    real_e0 = BTOR_REAL_ADDR_EXP (e0);
    diff    = upper - lower;
    if (diff + 1 == real_e0->len)
      result = btor_copy_exp (emgr, e0);
    else if (BTOR_IS_CONST_EXP (real_e0))
    {
      counter = 0;
      len     = real_e0->len;
      BTOR_NEWN (mm, bresult, diff + 2);
      for (i = len - upper - 1; i <= len - upper - 1 + diff; i++)
        bresult[counter++] = real_e0->bits[i];
      bresult[counter] = '\0';
      result           = btor_const_exp (emgr, bresult);
      result           = BTOR_COND_INVERT_EXP (e0, result);
      btor_delete_const (mm, bresult);
    }
  }
  else if (BTOR_IS_BINARY_EXP_KIND (kind))
  {
    assert (e0 != NULL);
    assert (e1 != NULL);
    assert (e2 == NULL);
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
      result = btor_const_exp (emgr, bresult);
      btor_delete_const (mm, bresult);
    }
    else if (BTOR_IS_CONST_EXP (real_e0) && !BTOR_IS_CONST_EXP (real_e1))
    {
      invert_b0 = BTOR_IS_INVERTED_EXP (e0);
      b0        = real_e0->bits;
      if (invert_b0) btor_invert_const (mm, b0);
      is_zero = is_zero_string (emgr, b0, real_e0->len);
      is_one  = is_one_string (emgr, b0, real_e0->len);
      /* invert back if necessary */
      if (invert_b0) btor_invert_const (mm, b0);
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
    }
    else if (!BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
    {
      invert_b1 = BTOR_IS_INVERTED_EXP (e1);
      b1        = real_e1->bits;
      if (invert_b1) btor_invert_const (mm, b1);
      is_zero = is_zero_string (emgr, b1, real_e1->len);
      is_one  = is_one_string (emgr, b1, real_e1->len);
      /* invert back if necessary */
      if (invert_b1) btor_invert_const (mm, b1);
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
    }
    else if (real_e0 == real_e1
             && (kind == BTOR_BEQ_EXP || kind == BTOR_ADD_EXP))
    {
      if (kind == BTOR_BEQ_EXP)
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
  else
  {
    assert (BTOR_IS_TERNARY_EXP_KIND (kind));
    assert (e0 != NULL);
    assert (e1 != NULL);
    assert (e2 != NULL);
    assert (kind == BTOR_BCOND_EXP || kind == BTOR_ACOND_EXP);
    real_e0 = BTOR_REAL_ADDR_EXP (e0);
    real_e1 = BTOR_REAL_ADDR_EXP (e1);
    real_e2 = BTOR_REAL_ADDR_EXP (e2);
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
  return result;
}

BtorExp *
btor_not_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  assert (BTOR_REAL_ADDR_EXP (exp)->len > 0);
  (void) emgr;
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
  BtorExpKind kind = BTOR_BEQ_EXP;
  BtorExp *result  = NULL;
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  /* both children are arrays or not */
  assert (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0))
          == BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)));
  /* if both children are arrays then they must have the same index length */
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0))
          || (BTOR_REAL_ADDR_EXP (e0)->index_len
              == BTOR_REAL_ADDR_EXP (e1)->index_len));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0))
          || (BTOR_REAL_ADDR_EXP (e0)->index_len > 0));
  /* arrays may not be tagged or inverted */
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0))
          || (BTOR_IS_REGULAR_EXP (e0) && BTOR_IS_REGULAR_EXP (e1)));
  assert (BTOR_REAL_ADDR_EXP (e0)->len == BTOR_REAL_ADDR_EXP (e1)->len);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0))) kind = BTOR_AEQ_EXP;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, kind, e0, e1, NULL, 0, 0);
  if (result == NULL) result = binary_exp (emgr, kind, e0, e1, 1);
  return result;
}

BtorExp *
btor_ne_exp (BtorExpMgr *emgr, BtorExp *e0, BtorExp *e1)
{
  assert (emgr != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
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
  assert (kind != BTOR_BEQ_EXP || len > 0);
  lookup = find_ternary_exp (emgr, kind, e0, e1, e2);
  if (*lookup == NULL)
  {
    if (emgr->table.num_elements == emgr->table.size
        && btor_log_2_util (emgr->table.size) < BTOR_EXP_UNIQUE_TABLE_LIMIT)
    {
      enlarge_exp_unique_table (emgr);
      lookup = find_ternary_exp (emgr, kind, e0, e1, e2);
    }
    switch (kind)
    {
      case BTOR_WRITE_EXP:
        *lookup = new_write_exp_node (emgr, e0, e1, e2);
        break;
      case BTOR_ACOND_EXP:
        *lookup = new_acond_exp_node (emgr, e0, e1, e2);
        break;
      default:
        assert (kind == BTOR_BCOND_EXP);
        *lookup = new_ternary_exp_node (emgr, kind, e0, e1, e2, len);
        break;
    }
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
  BtorExpKind kind = BTOR_BCOND_EXP;
  BtorExp *result  = NULL;
  int len          = 0;
  assert (emgr != NULL);
  assert (e_cond != NULL);
  assert (e_if != NULL);
  assert (e_else != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_cond)));
  assert (BTOR_REAL_ADDR_EXP (e_cond)->len == 1);
  /* both children are arrays or not */
  assert (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if))
          == BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_else)));
  /* if both children are arrays then they must have the same index length */
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if))
          || (BTOR_REAL_ADDR_EXP (e_if)->index_len
              == BTOR_REAL_ADDR_EXP (e_else)->index_len));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if))
          || (BTOR_REAL_ADDR_EXP (e_if->index_len > 0)));
  /* arrays may not be tagged or inverted */
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if))
          || (BTOR_IS_REGULAR_EXP (e_if) && BTOR_IS_REGULAR_EXP (e_else)));
  assert (BTOR_REAL_ADDR_EXP (e_if)->len == BTOR_REAL_ADDR_EXP (e_else)->len);
  assert (BTOR_REAL_ADDR_EXP (e_if)->len > 0);
  len = BTOR_REAL_ADDR_EXP (e_if)->len;
  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if))) kind = BTOR_ACOND_EXP;
  if (emgr->rewrite_level > 0)
    result = rewrite_exp (emgr, kind, e_cond, e_if, e_else, 0, 0);
  if (result == NULL)
    result = ternary_exp (emgr, kind, e_cond, e_if, e_else, len);
  return result;
}

BtorExp *
btor_write_exp (BtorExpMgr *emgr,
                BtorExp *e_array,
                BtorExp *e_index,
                BtorExp *e_value)
{
  assert (emgr != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_index)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_value)));
  assert (e_array->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e_index)->len > 0);
  assert (e_array->index_len == BTOR_REAL_ADDR_EXP (e_index)->len);
  return ternary_exp (emgr, BTOR_WRITE_EXP, e_array, e_index, e_value, 0);
}

int
btor_get_exp_len (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  (void) emgr;
  return BTOR_REAL_ADDR_EXP (exp)->len;
}

int
btor_is_array_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  (void) emgr;
  return BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp));
}

int
btor_get_index_exp_len (BtorExpMgr *emgr, BtorExp *e_array)
{
  assert (emgr != NULL);
  assert (e_array != NULL);
  assert (BTOR_IS_REGULAR_EXP (e_array));
  assert (BTOR_IS_ARRAY_EXP (e_array));
  (void) emgr;
  return e_array->index_len;
}

char *
btor_get_symbol_exp (BtorExpMgr *emgr, BtorExp *exp)
{
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_VAR_EXP (BTOR_REAL_ADDR_EXP (exp)));
  (void) emgr;
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
      case BTOR_BCOND_EXP:
      case BTOR_ACOND_EXP: op = "cond"; goto PRINT;
      case BTOR_BEQ_EXP:
      case BTOR_AEQ_EXP: op = "eq"; goto PRINT;
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
  else if (BTOR_IS_NATIVE_ARRAY_EXP (u))
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

    if (BTOR_IS_NATIVE_ARRAY_EXP (e))
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

    if (!BTOR_IS_VAR_EXP (e) && !BTOR_IS_NATIVE_ARRAY_EXP (e)) continue;

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

    if (BTOR_IS_VAR_EXP (e) || BTOR_IS_NATIVE_ARRAY_EXP (e)) continue;

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
    else if (e->kind == BTOR_BCOND_EXP)
    {
      fputs ("(ite (= bv1[1] ", file);
      btor_dump_smt_id (e->e[0], file);
      fputs (") ", file);
      btor_dump_smt_id (e->e[1], file);
      fputc (' ', file);
      btor_dump_smt_id (e->e[2], file);
      fputc (')', file);
    }
    else if (e->kind == BTOR_BEQ_EXP || e->kind == BTOR_AEQ_EXP
             || e->kind == BTOR_ULT_EXP)
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
  BTOR_CNEW (mm, emgr);
  emgr->mm = mm;
  BTOR_INIT_EXP_UNIQUE_TABLE (mm, emgr->table);
  BTOR_INIT_STACK (emgr->vars);
  BTOR_INIT_STACK (emgr->arrays);
  emgr->avmgr                      = btor_new_aigvec_mgr (mm, verbosity);
  emgr->id                         = 1;
  emgr->rewrite_level              = rewrite_level;
  emgr->dump_trace                 = dump_trace;
  emgr->verbosity                  = verbosity;
  emgr->read_enc                   = BTOR_SAT_SOLVER_READ_ENC;
  emgr->write_enc                  = BTOR_LAZY_WRITE_ENC;
  emgr->trace_file                 = trace_file;
  emgr->exp_pair_cnf_diff_id_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
  emgr->exp_pair_cnf_eq_id_table = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) hash_exp_pair, (BtorCmpPtr) compare_exp_pair);
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

void
btor_print_stats_exp_mgr (BtorExpMgr *emgr)
{
  assert (emgr != NULL);
  (void) emgr;
  print_verbose_msg ("lazy read-read conflicts: %d", emgr->read_read_conflicts);
  print_verbose_msg ("lazy read-write conflicts: %d",
                     emgr->read_write_conflicts);

  print_verbose_msg ("lazy refinement iterations: %d", emgr->refinements);
  print_verbose_msg ("lazy synthesis assignment inconsistencies: %d",
                     emgr->synthesis_assignment_inconsistencies);
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
  BtorExp *index       = NULL;
  BtorExp *read1       = NULL;
  BtorExp *read2       = NULL;
  BtorAIGVec *av0      = NULL;
  BtorAIGVec *av1      = NULL;
  BtorAIGVec *av2      = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorMemMgr *mm       = NULL;
  BtorPtrHashBucket *b;
  int same_children_mem = 0;
  int invert_av0        = 0;
  int invert_av1        = 0;
  int invert_av2        = 0;
  BtorReadEnc read_enc  = BTOR_EAGER_READ_ENC;
  char *indexed_name;
  const char *name;
  unsigned count;
  size_t len;
  int i;

  assert (emgr != NULL);
  assert (exp != NULL);

  read_enc = emgr->read_enc;
  mm       = emgr->mm;
  avmgr    = emgr->avmgr;

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
          /* special cases */
          if (cur->kind == BTOR_READ_EXP)
          {
            if (read_enc == BTOR_EAGER_READ_ENC)
            {
              cur->mark = 1;
              BTOR_PUSH_STACK (mm, exp_stack, cur);
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[1]);
              assert (BTOR_IS_REGULAR_EXP (cur->e[0]));
              assert (BTOR_IS_NATIVE_ARRAY_EXP (cur->e[0]));
              BTOR_PUSH_STACK (mm, exp_stack, cur->e[0]);
            }
            else
            {
              cur->mark = 2;
              cur->av   = btor_var_aigvec (avmgr, cur->len);
              /* mark children recursively as reachable */
              mark_reachable_exp (emgr, cur->e[1]);
              mark_reachable_exp (emgr, cur->e[0]);
              /* we do not synthesize children as we are
               * in lazy mode */
            }
          }
          else if (BTOR_IS_WRITE_ARRAY_EXP (cur))
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
          else if (cur->kind == BTOR_AEQ_EXP)
          {
            cur->mark = 2;
            cur->av   = btor_var_aigvec (avmgr, 1);
            /* mark children recursively as reachable */
            mark_reachable_exp (emgr, cur->e[1]);
            mark_reachable_exp (emgr, cur->e[0]);

            /* generate virtual reads */
            index = btor_var_exp (emgr, cur->e[0]->index_len, "vreadindex");
            read1 = btor_read_exp (emgr, cur->e[0], index);
            read2 = btor_read_exp (emgr, cur->e[1], index);
            cur->vreads = new_exp_pair (emgr, read1, read2);

            /* synthesize values of virtual reads */
            read1->av = btor_var_aigvec (avmgr, read1->len);
            read2->av = btor_var_aigvec (avmgr, read2->len);
            /* index gets synthesized later (if necessary) */

            /* eagerly encode array inequality constraint */
            encode_array_inequality_virtual_reads (emgr, cur);

            btor_release_exp (emgr, index);
            btor_release_exp (emgr, read1);
            btor_release_exp (emgr, read2);
          }
          else
          {
            /* regular cases */
            cur->mark = 1;
            BTOR_PUSH_STACK (mm, exp_stack, cur);
            if (BTOR_IS_UNARY_EXP (cur))
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
          assert (read_enc == BTOR_EAGER_READ_ENC);
          cur->av = btor_var_aigvec (avmgr, cur->len);
          encode_read_eagerly (emgr, cur->e[0], cur);
        }
        else if (BTOR_IS_UNARY_EXP (cur))
        {
          assert (cur->kind == BTOR_SLICE_EXP);
          invert_av0 = BTOR_IS_INVERTED_EXP (cur->e[0]);
          av0        = BTOR_REAL_ADDR_EXP (cur->e[0])->av;
          if (invert_av0) btor_invert_aigvec (avmgr, av0);
          cur->av = btor_slice_aigvec (avmgr, av0, cur->upper, cur->lower);
          /* invert back if necessary */
          if (invert_av0) btor_invert_aigvec (avmgr, av0);
        }
        else if (BTOR_IS_BINARY_EXP (cur))
        {
          /* we have to check if the children are
           * in the same memory place
           * if they are in the same memory place,
           * then we need to allocate memory for the
           * AIG vectors
           * if they are not, then we can invert them
           * in place and invert them back afterwards
           * (only if necessary)  */
          same_children_mem =
              BTOR_REAL_ADDR_EXP (cur->e[0]) == BTOR_REAL_ADDR_EXP (cur->e[1]);
          if (same_children_mem)
          {
            av0 = BTOR_AIGVEC_EXP (emgr, cur->e[0]);
            av1 = BTOR_AIGVEC_EXP (emgr, cur->e[1]);
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
        }
        else
        {
          assert (BTOR_IS_TERNARY_EXP (cur));
          assert (cur->kind == BTOR_BCOND_EXP);
          same_children_mem =
              BTOR_REAL_ADDR_EXP (cur->e[0]) == BTOR_REAL_ADDR_EXP (cur->e[1])
              || BTOR_REAL_ADDR_EXP (cur->e[0])
                     == BTOR_REAL_ADDR_EXP (cur->e[2])
              || BTOR_REAL_ADDR_EXP (cur->e[1])
                     == BTOR_REAL_ADDR_EXP (cur->e[2]);
          if (same_children_mem)
          {
            av0 = BTOR_AIGVEC_EXP (emgr, cur->e[0]);
            av1 = BTOR_AIGVEC_EXP (emgr, cur->e[1]);
            av2 = BTOR_AIGVEC_EXP (emgr, cur->e[2]);
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
compare_assignments (BtorExp *exp1, BtorExp *exp2)
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
  BtorAIG *aig1        = NULL;
  BtorAIG *aig2        = NULL;
  BtorExpMgr *emgr     = NULL;
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp1)));
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp2)));
  assert (BTOR_REAL_ADDR_EXP (exp1)->len == BTOR_REAL_ADDR_EXP (exp2)->len);
  assert (BTOR_REAL_ADDR_EXP (exp1)->av != NULL);
  assert (BTOR_REAL_ADDR_EXP (exp2)->av != NULL);
  emgr = BTOR_REAL_ADDR_EXP (exp1)->emgr;
  assert (emgr != NULL);
  avmgr = emgr->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
  av1   = BTOR_REAL_ADDR_EXP (exp1)->av;
  av2   = BTOR_REAL_ADDR_EXP (exp2)->av;
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    aig1 = BTOR_COND_INVERT_AIG_EXP (exp1, av1->aigs[i]);
    aig2 = BTOR_COND_INVERT_AIG_EXP (exp2, av2->aigs[i]);
    val1 = btor_get_assignment_aig (amgr, aig1);
    assert (val1 >= -1);
    assert (val1 <= 1);
    if (val1 == 0) val1 = -1;
    val2 = btor_get_assignment_aig (amgr, aig2);
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
  return return_val;
}

static unsigned int
hash_assignment (BtorExp *exp)
{
  unsigned int hash    = 0u;
  BtorExpMgr *emgr     = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorExp *real_exp    = NULL;
  BtorAIGVec *av       = NULL;
  int invert_av        = 0;
  char *assignment     = NULL;
  assert (exp != NULL);
  real_exp  = BTOR_REAL_ADDR_EXP (exp);
  emgr      = real_exp->emgr;
  avmgr     = emgr->avmgr;
  av        = real_exp->av;
  invert_av = BTOR_IS_INVERTED_EXP (exp);
  if (invert_av) btor_invert_aigvec (avmgr, av);
  assignment = btor_assignment_aigvec (avmgr, av);
  hash       = btor_hashstr (assignment);
  btor_freestr (emgr->mm, assignment);
  /* invert back if necessary */
  if (invert_av) btor_invert_aigvec (avmgr, av);
  return hash;
}

/* This function breath first searches the shortest path from a read to an array
 * After the function is completed the parent pointers can be followed
 * from the array to the read
 */
static void
extensionality_read_array_bfs_multiple_levels (BtorExpMgr *emgr,
                                               BtorExp *read,
                                               BtorExp *array)
{
  BtorExp *cur            = NULL;
  BtorExp *next           = NULL;
  BtorExp *aeq_acond      = NULL;
  BtorExp *real_aeq_acond = NULL;
  BtorMemMgr *mm          = NULL;
  BtorAIGMgr *amgr        = NULL;
  BtorExpPtrQueue queue;
  BtorExpPtrStack unmark_stack;
  int i     = 0;
  int found = 0;
  assert (emgr != NULL);
  assert (read != NULL);
  assert (array != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (read->kind == BTOR_READ_EXP);
  assert (BTOR_IS_REGULAR_EXP (array));
  assert (BTOR_IS_ARRAY_EXP (array));
  mm   = emgr->mm;
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_QUEUE (queue);
  cur = read->e[0];
  assert (BTOR_IS_REGULAR_EXP (cur));
  assert (cur != array);
  assert (BTOR_IS_ARRAY_EXP (cur));
  assert (cur->mark == 0);
  cur->parent = read;
  cur->mark   = 1;
  BTOR_ENQUEUE (mm, queue, cur);
  BTOR_PUSH_STACK (mm, unmark_stack, cur);
  while (!BTOR_EMPTY_QUEUE (queue))
  {
    cur = BTOR_DEQUEUE (queue);
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_ARRAY_EXP (cur));
    assert (
        !BTOR_IS_WRITE_ARRAY_EXP (cur)
        || (BTOR_IS_REGULAR_EXP (cur->e[0]) && BTOR_IS_ARRAY_EXP (cur->e[0])));
    if (cur == array)
    {
      found = 1;
      break;
    }
    if (BTOR_IS_WRITE_ARRAY_EXP (cur) && cur->e[0]->mark == 0)
    {
      next         = cur->e[0];
      next->mark   = 1;
      next->parent = cur;
      BTOR_ENQUEUE (mm, queue, next);
      BTOR_PUSH_STACK (mm, unmark_stack, next);
    }
    /* enqueue all arrays which are reachable via equality
     * where equality is set to true by the SAT solver */
    aeq_acond      = cur->first_aeq_acond_parent;
    real_aeq_acond = BTOR_REAL_ADDR_EXP (aeq_acond);
    while (real_aeq_acond != NULL
           && (real_aeq_acond->kind == BTOR_AEQ_EXP
               || real_aeq_acond->kind == BTOR_ACOND_EXP))
    {
      if (real_aeq_acond->reachable && real_aeq_acond->mark == 0)
      {
        real_aeq_acond->mark = 1;
        BTOR_PUSH_STACK (mm, unmark_stack, real_aeq_acond);
        if (real_aeq_acond->kind == BTOR_AEQ_EXP)
        {
          assert (real_aeq_acond->av != NULL);
          assert (real_aeq_acond->full_sat);
          assert (real_aeq_acond->len == 1);
          if (btor_get_assignment_aig (amgr, real_aeq_acond->av->aigs[0]) == 1)
          {
            /* set parent of array equality */
            real_aeq_acond->parent = cur;
            i                      = BTOR_GET_TAG_EXP (aeq_acond);
            assert (i == 0 || i == 1);
            /* we need the other child */
            next = real_aeq_acond->e[!i];
            assert (BTOR_IS_REGULAR_EXP (next));
            assert (BTOR_IS_ARRAY_EXP (next));
            /* set parent of next */
            next->parent = real_aeq_acond;
            next->mark   = 1;
            BTOR_ENQUEUE (mm, queue, next);
            BTOR_PUSH_STACK (mm, unmark_stack, next);
          }
        }
        else
        {
          assert (real_aeq_acond->kind == BTOR_ACOND_EXP);
          /* TODO: deal with acond */
          assert (0);
        }
      }
      i              = BTOR_GET_TAG_EXP (aeq_acond);
      aeq_acond      = real_aeq_acond->next_parent[i];
      real_aeq_acond = BTOR_REAL_ADDR_EXP (aeq_acond);
    }
  }
  assert (found);
  BTOR_RELEASE_QUEUE (mm, queue);
  /* reset mark flags */
  while (!BTOR_EMPTY_STACK (unmark_stack))
  {
    cur = BTOR_POP_STACK (unmark_stack);
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_ARRAY_EXP (cur) || cur->kind == BTOR_AEQ_EXP
            || cur->kind == BTOR_ACOND_EXP);
    cur->mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);
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
  encode_ackermann_constraint_lazily (
      emgr, read1->e[1], read2->e[1], read1, read2);
}

static unsigned int
hash_regular_exp_by_id (BtorExp *exp)
{
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  return (unsigned int) exp->id * 7334147u;
}

static int
compare_regular_exps_by_id (BtorExp *exp1, BtorExp *exp2)
{
  int id1 = 0;
  int id2 = 0;
  assert (exp1 != NULL);
  assert (exp2 != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp1));
  assert (BTOR_IS_REGULAR_EXP (exp2));
  id1 = exp1->id;
  id2 = exp2->id;
  if (id1 < id2) return -1;
  if (id1 > id2) return 1;
  return 0;
}

/* Resolves a read conflict across multiple levels
 * 'array' is the array where the conflict has been detected
 */
static void
resolve_read_conflict_multiple_levels (BtorExpMgr *emgr,
                                       BtorExp *array,
                                       BtorExp *read1,
                                       BtorExp *read2)
{
  BtorExpPtrStack writes;
  BtorExpPtrStack aeqs;
  BtorExp *cur            = NULL;
  BtorExp *next           = NULL;
  BtorMemMgr *mm          = NULL;
  BtorPtrHashTable *table = NULL;
  int need_hashing        = 0;
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
  assert (read1->e[0] != array || read2->e[0] != array);
  /* collect intermediate writes, array equalities and array conditionals
   * as premisses for McCarthy constraint */
  BTOR_INIT_STACK (writes);
  BTOR_INIT_STACK (aeqs);
  /* both reads are not local to the array */
  need_hashing = read1->e[0] != array && read2->e[0] != array;
  if (need_hashing)
    table = btor_new_ptr_hash_table (mm,
                                     (BtorHashPtr) hash_regular_exp_by_id,
                                     (BtorCmpPtr) compare_regular_exps_by_id);
  if (read1->e[0] != array)
  {
    extensionality_read_array_bfs_multiple_levels (emgr, read1, array);
    cur = array;
    do
    {
      next = cur->parent;
      assert (next != NULL);
      assert (BTOR_IS_REGULAR_EXP (next));
      assert (BTOR_IS_ARRAY_EXP (next) || next->kind == BTOR_AEQ_EXP
              || next->kind == BTOR_ACOND_EXP || next->kind == BTOR_READ_EXP);

      /* if next is a native array, then we do not have to do anything */
      if (BTOR_IS_WRITE_ARRAY_EXP (next))
      {
        if (need_hashing) btor_insert_in_ptr_hash_table (table, next);
        BTOR_PUSH_STACK (mm, writes, next);
      }
      else if (next->kind == BTOR_AEQ_EXP)
      {
        if (need_hashing) btor_insert_in_ptr_hash_table (table, next);
        BTOR_PUSH_STACK (mm, aeqs, next);
      }
      else if (next->kind == BTOR_ACOND_EXP)
      {
        /* TODO: deal with acond */
        assert (0);
      }
      cur = next;
    } while (cur != read1);
  }
  if (read2->e[0] != array)
  {
    extensionality_read_array_bfs_multiple_levels (emgr, read2, array);
    cur = array;
    do
    {
      next = cur->parent;
      assert (next != NULL);
      assert (BTOR_IS_REGULAR_EXP (next));
      assert (BTOR_IS_ARRAY_EXP (next) || next->kind == BTOR_AEQ_EXP
              || next->kind == BTOR_ACOND_EXP || next->kind == BTOR_READ_EXP);

      /* if next is a native array, then we do not have to do anything */
      if (BTOR_IS_WRITE_ARRAY_EXP (next))
      {
        if (!need_hashing || btor_find_in_ptr_hash_table (table, next) == NULL)
          BTOR_PUSH_STACK (mm, writes, next);
      }
      else if (next->kind == BTOR_AEQ_EXP)
      {
        if (!need_hashing || btor_find_in_ptr_hash_table (table, next) == NULL)
          BTOR_PUSH_STACK (mm, aeqs, next);
      }
      else if (next->kind == BTOR_ACOND_EXP)
      {
        /* TODO: deal with acond */
        assert (0);
      }
      cur = next;
    } while (cur != read2);
  }
  encode_mccarthy_constraint (
      emgr, &writes, &aeqs, read1->e[1], read2->e[1], read1, read2);
  BTOR_RELEASE_STACK (mm, writes);
  BTOR_RELEASE_STACK (mm, aeqs);
  if (need_hashing) btor_delete_ptr_hash_table (table);
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
  (void) emgr;
  if ((*indices_equal = compare_assignments (read->e[1], write->e[1]) == 0)
      && compare_assignments (read, write->e[2]) != 0)
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
  encode_ackermann_constraint_lazily (
      emgr, read->e[1], write->e[1], read, write->e[2]);
}

/* Resolves a read write conflict across multi levels */
static void
resolve_read_write_conflict_multiple_levels (BtorExpMgr *emgr,
                                             BtorExp *read,
                                             BtorExp *write)
{
  BtorExpPtrStack writes;
  BtorExpPtrStack aeqs;
  BtorExp *cur   = NULL;
  BtorExp *next  = NULL;
  BtorMemMgr *mm = NULL;
  assert (emgr != NULL);
  assert (read != NULL);
  assert (write != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (BTOR_IS_REGULAR_EXP (write));
  assert (read->kind == BTOR_READ_EXP);
  assert (BTOR_IS_WRITE_ARRAY_EXP (write));
  mm = emgr->mm;
  /* collect intermediate writes and array equalities as
   * premisses for McCarthy constraint */
  extensionality_read_array_bfs_multiple_levels (emgr, read, write);
  /* follow path from write to read */
  BTOR_INIT_STACK (writes);
  BTOR_INIT_STACK (aeqs);
  cur = write;
  /* read is not a direct parent of write */
  assert (cur->parent != read);
  do
  {
    next = cur->parent;
    assert (next != NULL);
    assert (BTOR_IS_REGULAR_EXP (next));
    assert (BTOR_IS_ARRAY_EXP (next) || next->kind == BTOR_AEQ_EXP
            || next->kind == BTOR_ACOND_EXP || next->kind == BTOR_READ_EXP);

    /* if next is a native array, then we do not have to do anything */
    if (BTOR_IS_WRITE_ARRAY_EXP (next))
      BTOR_PUSH_STACK (mm, writes, next);
    else if (next->kind == BTOR_AEQ_EXP)
      BTOR_PUSH_STACK (mm, aeqs, next);
    else if (next->kind == BTOR_ACOND_EXP)
      assert (0); /* TODO: deal with acond */
    cur = next;
  } while (cur != read);
  encode_mccarthy_constraint (
      emgr, &writes, &aeqs, read->e[1], write->e[1], read, write->e[2]);
  BTOR_RELEASE_STACK (mm, writes);
  BTOR_RELEASE_STACK (mm, aeqs);
}

/* synthesizes and fully encodes write index and value to SAT
 * (if necessary )
 * it returns if encoding changed assignments made so far
 */
static int
lazy_synthesize_and_encode_write_exp (BtorExpMgr *emgr, BtorExp *write)
{
  int changed_assignments = 0;
  int update              = 0;
  BtorAIGVecMgr *avmgr    = NULL;
  BtorSATMgr *smgr        = NULL;
  assert (emgr != NULL);
  assert (write != NULL);
  assert (BTOR_IS_REGULAR_EXP (write));
  assert (BTOR_IS_WRITE_ARRAY_EXP (write));
  avmgr = emgr->avmgr;
  smgr  = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (avmgr));
  if (BTOR_REAL_ADDR_EXP (write->e[1])->av == NULL)
    btor_synthesize_exp (emgr, write->e[1], NULL);
  if (!BTOR_REAL_ADDR_EXP (write->e[1])->full_sat)
  {
    update = 1;
    btor_aigvec_to_sat_full (avmgr, BTOR_REAL_ADDR_EXP (write->e[1])->av);
    BTOR_REAL_ADDR_EXP (write->e[1])->full_sat = 1;
  }
  if (BTOR_REAL_ADDR_EXP (write->e[2])->av == NULL)
    btor_synthesize_exp (emgr, write->e[2], NULL);
  if (!BTOR_REAL_ADDR_EXP (write->e[2])->full_sat)
  {
    update = 1;
    btor_aigvec_to_sat_full (avmgr, BTOR_REAL_ADDR_EXP (write->e[2])->av);
    BTOR_REAL_ADDR_EXP (write->e[2])->full_sat = 1;
  }
  /* update assignments if necessary */
  if (update)
  {
    (void) btor_sat_sat (smgr, INT_MAX);
    changed_assignments = btor_changed_assignments_sat (smgr);
  }
  return changed_assignments;
}

/* synthesizes and fully encodes read index and value to SAT
 * (if necessary )
 * it returns if encoding changed assignments made so far
 */
static int
lazy_synthesize_and_encode_read_exp (BtorExpMgr *emgr, BtorExp *read)
{
  int changed_assignments = 0;
  int update              = 0;
  BtorAIGVecMgr *avmgr    = NULL;
  BtorSATMgr *smgr        = NULL;
  assert (emgr != NULL);
  assert (read != NULL);
  assert (BTOR_IS_REGULAR_EXP (read));
  assert (read->kind == BTOR_READ_EXP);
  avmgr = emgr->avmgr;
  smgr  = btor_get_sat_mgr_aig_mgr (btor_get_aig_mgr_aigvec_mgr (avmgr));
  if (read->av == NULL) btor_synthesize_exp (emgr, read, NULL);
  if (!read->full_sat)
  {
    update = 1;
    btor_aigvec_to_sat_full (avmgr, read->av);
    read->full_sat = 1;
  }
  if (BTOR_REAL_ADDR_EXP (read->e[1])->av == NULL)
    btor_synthesize_exp (emgr, read->e[1], NULL);
  if (!BTOR_REAL_ADDR_EXP (read->e[1])->full_sat)
  {
    update = 1;
    btor_aigvec_to_sat_full (avmgr, BTOR_REAL_ADDR_EXP (read->e[1])->av);
    BTOR_REAL_ADDR_EXP (read->e[1])->full_sat = 1;
  }
  /* update assignments if necessary */
  if (update)
  {
    (void) btor_sat_sat (smgr, INT_MAX);
    changed_assignments = btor_changed_assignments_sat (smgr);
  }
  return changed_assignments;
}

static int
process_working_stack (BtorExpMgr *emgr,
                       BtorExpPtrStack *stack,
                       BtorExpPtrStack *cleanup_stack,
                       int *assignments_changed)
{
  int indices_equal         = 0;
  BtorExp *read             = NULL;
  BtorExp *array            = NULL;
  BtorExp *hashed_read      = NULL;
  BtorExp *cur_aeq_acond    = NULL;
  BtorExp *real_aeq_acond   = NULL;
  BtorPtrHashBucket *bucket = NULL;
  BtorMemMgr *mm            = NULL;
  BtorAIGMgr *amgr          = NULL;
  int i                     = 0;
  assert (emgr != NULL);
  assert (stack != NULL);
  assert (cleanup_stack != NULL);
  assert (assignments_changed != NULL);
  mm   = emgr->mm;
  amgr = btor_get_aig_mgr_aigvec_mgr (emgr->avmgr);
  while (!BTOR_EMPTY_STACK (*stack))
  {
    array = BTOR_POP_STACK (*stack);
    assert (BTOR_IS_REGULAR_EXP (array));
    assert (BTOR_IS_ARRAY_EXP (array));
    assert (!BTOR_EMPTY_STACK (*stack));
    read = BTOR_POP_STACK (*stack);
    assert (BTOR_IS_REGULAR_EXP (read));
    assert (read->kind == BTOR_READ_EXP);
    /* synthesize read index and value if necessary */
    *assignments_changed = lazy_synthesize_and_encode_read_exp (emgr, read);
    if (*assignments_changed) return 0;
    /* hash table lookup */
    if (array->table == NULL)
    {
      array->table = btor_new_ptr_hash_table (
          mm, (BtorHashPtr) hash_assignment, (BtorCmpPtr) compare_assignments);
      BTOR_PUSH_STACK (mm, *cleanup_stack, array);
    }
    else
    {
      bucket = btor_find_in_ptr_hash_table (array->table, read->e[1]);
      if (bucket != NULL)
      {
        hashed_read = (BtorExp *) bucket->data.asPtr;
        /* we have to check if values are equal */
        if (compare_assignments (hashed_read, read) != 0)
        {
          emgr->read_read_conflicts++;
          /* local conflict ? */
          if (hashed_read->e[0] == array && read->e[0] == array)
            resolve_read_conflict_one_level (emgr, hashed_read, read);
          else
            resolve_read_conflict_multiple_levels (
                emgr, array, hashed_read, read);
          return 1;
        }
        /* in the other case we have already propagated a representative with
           same index and same value */
        else
          continue;
      }
    }
    if (BTOR_IS_WRITE_ARRAY_EXP (array))
    {
      *assignments_changed = lazy_synthesize_and_encode_write_exp (emgr, array);
      if (*assignments_changed) return 0;
      /* check if read is consistent with write */
      if (check_read_write_conflict (emgr, read, array, &indices_equal))
      {
        emgr->read_write_conflicts++;
        /* check if local or propagated read conflicts with write */
        if (read->e[0] == array)
          resolve_read_write_conflict_one_level (emgr, read, array);
        else
          resolve_read_write_conflict_multiple_levels (emgr, read, array);
        return 1;
      }
      else if (!indices_equal)
      {
        /* propagate read-array pair */
        BTOR_PUSH_STACK (mm, *stack, read);
        BTOR_PUSH_STACK (mm, *stack, array->e[0]);
        continue;
      }
    }
    assert (array->table != NULL);
    /* insert into hash table */
    btor_insert_in_ptr_hash_table (array->table, read->e[1])->data.asPtr = read;
    /* propagate read-array pairs wich are reachable via array equality */
    cur_aeq_acond  = array->first_aeq_acond_parent;
    real_aeq_acond = BTOR_REAL_ADDR_EXP (cur_aeq_acond);
    while (real_aeq_acond != NULL
           && (real_aeq_acond->kind == BTOR_AEQ_EXP
               || real_aeq_acond->kind == BTOR_ACOND_EXP))
    {
      if (real_aeq_acond->reachable)
      {
        if (real_aeq_acond->kind == BTOR_AEQ_EXP)
        {
          assert (real_aeq_acond->av != NULL);
          assert (real_aeq_acond->full_sat);
          assert (!BTOR_IS_INVERTED_AIG (real_aeq_acond->av->aigs[0]));
          assert (!BTOR_IS_CONST_AIG (real_aeq_acond->av->aigs[0]));
          assert (BTOR_IS_VAR_AIG (real_aeq_acond->av->aigs[0]));
          if (btor_get_assignment_aig (amgr, real_aeq_acond->av->aigs[0]) == 1)
          {
            i = BTOR_GET_TAG_EXP (cur_aeq_acond);
            assert (i == 0 || i == 1);
            /* we need the other child */
            array = real_aeq_acond->e[!i];
            assert (BTOR_IS_REGULAR_EXP (array));
            assert (BTOR_IS_ARRAY_EXP (array));
            BTOR_PUSH_STACK (mm, *stack, read);
            BTOR_PUSH_STACK (mm, *stack, array);
          }
        }
        else
        {
          assert (real_aeq_acond->kind == BTOR_ACOND_EXP);
          /* TODO: deal with acond */
          assert (0);
        }
      }
      i              = BTOR_GET_TAG_EXP (cur_aeq_acond);
      cur_aeq_acond  = real_aeq_acond->e[i];
      real_aeq_acond = BTOR_REAL_ADDR_EXP (cur_aeq_acond);
    }
  }
  return 0;
}

static int
resolve_read_write_conflicts (BtorExpMgr *emgr)
{
  BtorExpPtrStack array_stack;
  BtorExpPtrStack cleanup_stack;
  BtorExpPtrStack working_stack;
  BtorExpPtrStack unmark_stack;
  BtorMemMgr *mm          = NULL;
  BtorExp *cur_array      = NULL;
  BtorExp *cur_write      = NULL;
  BtorExp *cur_read       = NULL;
  BtorExp **top           = NULL;
  BtorExp **temp          = NULL;
  int found_conflict      = 0;
  int changed_assignments = 0;
  BtorWriteEnc write_enc  = 0;
  assert (emgr != NULL);
  mm        = emgr->mm;
  write_enc = emgr->write_enc;
BTOR_READ_WRITE_ARRAY_CONFLICT_CHECK:
  BTOR_INIT_STACK (unmark_stack);
  BTOR_INIT_STACK (working_stack);
  BTOR_INIT_STACK (cleanup_stack);
  BTOR_INIT_STACK (array_stack);
  top = emgr->arrays.top;
  /* push all native arrays on the stack */
  for (temp = emgr->arrays.start; temp != top; temp++)
  {
    cur_array = *temp;
    assert (BTOR_IS_NATIVE_ARRAY_EXP (cur_array));
    if (cur_array->reachable) BTOR_PUSH_STACK (mm, array_stack, cur_array);
  }
  while (!BTOR_EMPTY_STACK (array_stack))
  {
    cur_array = BTOR_POP_STACK (array_stack);
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    assert (cur_array->array_mark >= 0);
    assert (cur_array->array_mark <= 2);
    if (cur_array->array_mark == 0)
    {
      cur_array->array_mark = 1;
      BTOR_PUSH_STACK (mm, unmark_stack, cur_array);
      BTOR_PUSH_STACK (mm, array_stack, cur_array);
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
        /* writes are at the end of the parent list */
        cur_write = cur_array->last_parent;
        while (cur_write != NULL
               && BTOR_IS_WRITE_ARRAY_EXP (BTOR_REAL_ADDR_EXP (cur_write)))
        {
          assert (BTOR_GET_TAG_EXP (cur_write) == 0);
          assert (BTOR_IS_REGULAR_EXP (cur_write));
          if (cur_write->reachable)
          {
            assert (cur_write->array_mark == 0);
            BTOR_PUSH_STACK (mm, array_stack, cur_write);
          }
          cur_write = cur_write->prev_parent[0];
        }
      }
    }
    else if (cur_array->array_mark == 1)
    {
      cur_array->array_mark = 2;
      assert (cur_array->reachable);
      cur_read = cur_array->first_parent;
      while (cur_read != NULL
             && BTOR_REAL_ADDR_EXP (cur_read)->kind == BTOR_READ_EXP)
      {
        assert (BTOR_GET_TAG_EXP (cur_read) == 0);
        assert (BTOR_IS_REGULAR_EXP (cur_read));
        /* push read-array pair on working stack */
        BTOR_PUSH_STACK (mm, working_stack, cur_read);
        BTOR_PUSH_STACK (mm, working_stack, cur_array);
        found_conflict = process_working_stack (
            emgr, &working_stack, &cleanup_stack, &changed_assignments);
        if (found_conflict || changed_assignments)
          goto BTOR_READ_WRITE_ARRAY_CONFLICT_CLEANUP;
        cur_read = cur_read->next_parent[0];
      }
    }
  }
BTOR_READ_WRITE_ARRAY_CONFLICT_CLEANUP:
  while (!BTOR_EMPTY_STACK (cleanup_stack))
  {
    cur_array = BTOR_POP_STACK (cleanup_stack);
    btor_delete_ptr_hash_table (cur_array->table);
    cur_array->table = NULL;
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
    cur_array->array_mark = 0;
  }
  BTOR_RELEASE_STACK (mm, unmark_stack);
  /* restart? (assignments changed during lazy synthesis and encoding) */
  if (changed_assignments)
  {
    emgr->synthesis_assignment_inconsistencies++;
    goto BTOR_READ_WRITE_ARRAY_CONFLICT_CHECK;
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
      emgr->refinements++;
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
  int invert_av        = 0;
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (exp)));
  avmgr = emgr->avmgr;
  if (!BTOR_REAL_ADDR_EXP (exp)->reachable
      || BTOR_REAL_ADDR_EXP (exp)->av == NULL)
    return NULL;
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
