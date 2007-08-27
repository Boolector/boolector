#include "btoraigvec.h"
#include "btorsat.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

struct BtorReadObj
{
  BtorAIGVec *var;
  BtorAIGVec *index;
};

typedef struct BtorReadObj BtorReadObj;

BTOR_DECLARE_STACK (ReadObjPtr, BtorReadObj *);

struct BtorAIGVecMgr
{
  BtorMemMgr *mm;
  int verbosity;
  BtorReadEnc read_enc;
  BtorAIGMgr *amgr;
  BtorReadObjPtrStack reads;
};

/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
/*------------------------------------------------------------------------*/

static BtorAIGVec *
new_aigvec (BtorAIGVecMgr *avmgr, int len)
{
  BtorAIGVec *result = NULL;
  assert (avmgr != NULL);
  assert (len > 0);
  result       = (BtorAIGVec *) btor_malloc (avmgr->mm, sizeof (BtorAIGVec));
  result->aigs = (BtorAIG **) btor_malloc (avmgr->mm, sizeof (BtorAIG *) * len);
  result->len  = len;
  return result;
}

BtorAIGVec *
btor_const_aigvec (BtorAIGVecMgr *avmgr, const char *bits)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (bits != NULL);
  len = (int) strlen (bits);
  assert (len > 0);
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = bits[i] == '0' ? BTOR_AIG_FALSE : BTOR_AIG_TRUE;
  return result;
}

BtorAIGVec *
btor_var_aigvec (BtorAIGVecMgr *avmgr, int len)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  assert (avmgr != NULL);
  assert (len > 0);
  result = new_aigvec (avmgr, len);
  for (i = len - 1; i >= 0; i--) result->aigs[i] = btor_var_aig (avmgr->amgr);
  return result;
}

BtorAIGVec *
btor_not_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  len    = av->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_not_aig (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_slice_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av, int upper, int lower)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  int diff           = 0;
  int counter        = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  assert (upper < av->len);
  assert (lower >= 0);
  assert (lower <= upper);
  len    = av->len;
  diff   = upper - lower;
  result = new_aigvec (avmgr, diff + 1);
  for (i = len - upper - 1; i <= len - upper - 1 + diff; i++)
    result->aigs[counter++] = btor_copy_aig (avmgr->amgr, av->aigs[i]);
  return result;
}

BtorAIGVec *
btor_and_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len    = av1->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_and_aig (avmgr->amgr, av1->aigs[i], av2->aigs[i]);
  return result;
}

static void
ripple_compare_aig (BtorAIGMgr *amgr,
                    BtorAIG *x,
                    BtorAIG *y,
                    BtorAIG *lt_in,
                    BtorAIG *eq_in,
                    BtorAIG *gt_in,
                    BtorAIG **lt_out,
                    BtorAIG **eq_out,
                    BtorAIG **gt_out)
{
  BtorAIG *lt     = NULL;
  BtorAIG *eq     = NULL;
  BtorAIG *gt     = NULL;
  BtorAIG *temp   = NULL;
  BtorAIG *x_lt_y = NULL;
  BtorAIG *x_eq_y = NULL;
  BtorAIG *x_gt_y = NULL;
  assert (amgr != NULL);
  assert (lt_out != NULL);
  assert (eq_out != NULL);
  assert (gt_out != NULL);

  x_lt_y = btor_and_aig (amgr, BTOR_INVERT_AIG (x), y);
  x_eq_y = btor_eq_aig (amgr, x, y);
  x_gt_y = btor_and_aig (amgr, x, BTOR_INVERT_AIG (y));

  temp = btor_and_aig (amgr, lt_in, BTOR_INVERT_AIG (eq_in));
  lt   = btor_and_aig (amgr, temp, BTOR_INVERT_AIG (gt_in));
  btor_release_aig (amgr, temp);

  temp = btor_and_aig (amgr, BTOR_INVERT_AIG (lt_in), eq_in);
  eq   = btor_and_aig (amgr, temp, BTOR_INVERT_AIG (gt_in));
  btor_release_aig (amgr, temp);

  temp = btor_and_aig (amgr, BTOR_INVERT_AIG (lt_in), BTOR_INVERT_AIG (eq_in));
  gt   = btor_and_aig (amgr, temp, gt_in);
  btor_release_aig (amgr, temp);

  temp    = btor_and_aig (amgr, eq, x_lt_y);
  *lt_out = btor_or_aig (amgr, lt, temp);
  btor_release_aig (amgr, temp);

  *eq_out = btor_and_aig (amgr, eq, x_eq_y);

  temp    = btor_and_aig (amgr, eq, x_gt_y);
  *gt_out = btor_or_aig (amgr, gt, temp);
  btor_release_aig (amgr, temp);

  btor_release_aig (amgr, x_lt_y);
  btor_release_aig (amgr, x_eq_y);
  btor_release_aig (amgr, x_gt_y);
  btor_release_aig (amgr, lt);
  btor_release_aig (amgr, eq);
  btor_release_aig (amgr, gt);
}

static void
ripple_compare_aigvec (BtorAIGVecMgr *avmgr,
                       BtorAIGVec *av1,
                       BtorAIGVec *av2,
                       BtorAIG **lt,
                       BtorAIG **eq,
                       BtorAIG **gt)
{
  int i          = 0;
  int len        = 0;
  BtorAIG *lt_in = NULL;
  BtorAIG *eq_in = NULL;
  BtorAIG *gt_in = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (lt != NULL);
  assert (eq != NULL);
  assert (gt != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len = av1->len;
  if (len == 1)
  {
    *lt = btor_and_aig (
        avmgr->amgr, BTOR_INVERT_AIG (av1->aigs[0]), av2->aigs[0]);
    *eq = btor_eq_aig (avmgr->amgr, av1->aigs[0], av2->aigs[0]);
    *gt = btor_and_aig (
        avmgr->amgr, av1->aigs[0], BTOR_INVERT_AIG (av2->aigs[0]));
  }
  else
  {
    lt_in = btor_and_aig (
        avmgr->amgr, BTOR_INVERT_AIG (av1->aigs[0]), av2->aigs[0]);
    eq_in = btor_eq_aig (avmgr->amgr, av1->aigs[0], av2->aigs[0]);
    gt_in = btor_and_aig (
        avmgr->amgr, av1->aigs[0], BTOR_INVERT_AIG (av2->aigs[0]));
    for (i = 1; i < len; i++)
    {
      ripple_compare_aig (avmgr->amgr,
                          av1->aigs[i],
                          av2->aigs[i],
                          lt_in,
                          eq_in,
                          gt_in,
                          lt,
                          eq,
                          gt);
      btor_release_aig (avmgr->amgr, lt_in);
      btor_release_aig (avmgr->amgr, eq_in);
      btor_release_aig (avmgr->amgr, gt_in);
      lt_in = *lt;
      eq_in = *eq;
      gt_in = *gt;
    }
  }
}

BtorAIGVec *
btor_ult_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIG *lt        = NULL;
  BtorAIG *eq        = NULL;
  BtorAIG *gt        = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  result = new_aigvec (avmgr, 1);
  ripple_compare_aigvec (avmgr, av1, av2, &lt, &eq, &gt);
  result->aigs[0] = lt;
  btor_release_aig (avmgr->amgr, eq);
  btor_release_aig (avmgr->amgr, gt);
  return result;
}

BtorAIGVec *
btor_eq_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result  = NULL;
  BtorAIG *result_aig = NULL;
  BtorAIG *temp1      = NULL;
  BtorAIG *temp2      = NULL;
  int i               = 0;
  int len             = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len        = av1->len;
  result     = new_aigvec (avmgr, 1);
  result_aig = btor_eq_aig (avmgr->amgr, av1->aigs[0], av2->aigs[0]);
  for (i = 1; i < len; i++)
  {
    temp1 = btor_eq_aig (avmgr->amgr, av1->aigs[i], av2->aigs[i]);
    temp2 = btor_and_aig (avmgr->amgr, result_aig, temp1);
    btor_release_aig (avmgr->amgr, temp1);
    btor_release_aig (avmgr->amgr, result_aig);
    result_aig = temp2;
  }
  result->aigs[0] = result_aig;
  return result;
}

static BtorAIG *
full_add_aig (
    BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG *cin, BtorAIG **cout)
{
  BtorAIG *cout_and1 = NULL;
  BtorAIG *cout_and2 = NULL;
  BtorAIG *cout_and3 = NULL;
  BtorAIG *result    = NULL;
  BtorAIG * or       = NULL;
  BtorAIG * xor      = NULL;
  assert (amgr != NULL);
  assert (cout != NULL);

  cout_and1 = btor_and_aig (amgr, x, cin);
  cout_and2 = btor_and_aig (amgr, y, cin);
  cout_and3 = btor_and_aig (amgr, x, y);

  or     = btor_or_aig (amgr, cout_and1, cout_and2);
  *cout  = btor_or_aig (amgr, or, cout_and3);
  xor    = btor_xor_aig (amgr, x, y);
  result = btor_xor_aig (amgr, xor, cin);

  btor_release_aig (amgr, or);
  btor_release_aig (amgr, xor);
  btor_release_aig (amgr, cout_and1);
  btor_release_aig (amgr, cout_and2);
  btor_release_aig (amgr, cout_and3);
  return result;
}

BtorAIGVec *
btor_add_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIG *cout      = NULL;
  BtorAIG *cin       = NULL;
  int i              = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  result = new_aigvec (avmgr, av1->len);
  cin    = BTOR_AIG_FALSE;
  for (i = av1->len - 1; i >= 0; i--)
  {
    result->aigs[i] =
        full_add_aig (avmgr->amgr, av1->aigs[i], av2->aigs[i], cin, &cout);
    btor_release_aig (avmgr->amgr, cin);
    cin = cout;
  }
  btor_release_aig (avmgr->amgr, cout);
  return result;
}

static BtorAIGVec *
sll_n_bits (BtorAIGVecMgr *avmgr, BtorAIGVec *av, int n, BtorAIG *shift)
{
  BtorAIGVec *result = NULL;
  BtorAIG *and1      = NULL;
  BtorAIG *and2      = NULL;
  BtorAIG *not_shift = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  assert (n >= 0);
  assert (n < av->len);
  len = av->len;
  if (n == 0) return btor_copy_aigvec (avmgr, av);
  not_shift = btor_not_aig (avmgr->amgr, shift);
  result    = new_aigvec (avmgr, len);
  for (i = 0; i < len - n; i++)
  {
    and1            = btor_and_aig (avmgr->amgr, av->aigs[i], not_shift);
    and2            = btor_and_aig (avmgr->amgr, av->aigs[i + n], shift);
    result->aigs[i] = btor_or_aig (avmgr->amgr, and1, and2);
    btor_release_aig (avmgr->amgr, and1);
    btor_release_aig (avmgr->amgr, and2);
  }
  for (i = len - n; i < len; i++)
    result->aigs[i] = btor_and_aig (avmgr->amgr, av->aigs[i], not_shift);
  btor_release_aig (avmgr->amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_sll_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIGVec *temp   = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len > 1);
  assert (btor_is_power_of_2_util (av1->len));
  assert (btor_log_2_util (av1->len) == av2->len);
  len    = av2->len;
  result = sll_n_bits (avmgr, av1, 1, av2->aigs[av2->len - 1]);
  for (i = len - 2; i >= 0; i--)
  {
    temp = result;
    result =
        sll_n_bits (avmgr, temp, btor_pow_2_util (len - i - 1), av2->aigs[i]);
    btor_release_delete_aigvec (avmgr, temp);
  }
  return result;
}

static BtorAIGVec *
srl_n_bits (BtorAIGVecMgr *avmgr, BtorAIGVec *av, int n, BtorAIG *shift)
{
  BtorAIGVec *result = NULL;
  BtorAIG *and1      = NULL;
  BtorAIG *and2      = NULL;
  BtorAIG *not_shift = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  assert (n >= 0);
  assert (n < av->len);
  len = av->len;
  if (n == 0) return btor_copy_aigvec (avmgr, av);
  not_shift = btor_not_aig (avmgr->amgr, shift);
  result    = new_aigvec (avmgr, len);
  for (i = 0; i < n; i++)
    result->aigs[i] = btor_and_aig (avmgr->amgr, av->aigs[i], not_shift);
  for (i = n; i < len; i++)
  {
    and1            = btor_and_aig (avmgr->amgr, av->aigs[i], not_shift);
    and2            = btor_and_aig (avmgr->amgr, av->aigs[i - n], shift);
    result->aigs[i] = btor_or_aig (avmgr->amgr, and1, and2);
    btor_release_aig (avmgr->amgr, and1);
    btor_release_aig (avmgr->amgr, and2);
  }
  btor_release_aig (avmgr->amgr, not_shift);
  return result;
}

BtorAIGVec *
btor_srl_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIGVec *temp   = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len > 1);
  assert (btor_is_power_of_2_util (av1->len));
  assert (btor_log_2_util (av1->len) == av2->len);
  len    = av2->len;
  result = srl_n_bits (avmgr, av1, 1, av2->aigs[av2->len - 1]);
  for (i = len - 2; i >= 0; i--)
  {
    temp = result;
    result =
        srl_n_bits (avmgr, temp, btor_pow_2_util (len - i - 1), av2->aigs[i]);
    btor_release_delete_aigvec (avmgr, temp);
  }
  return result;
}

BtorAIGVec *
btor_umul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIGVec *and    = NULL;
  BtorAIGVec *shift  = NULL;
  BtorAIGVec *add    = NULL;
  int i              = 0;
  int j              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len    = av1->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++) result->aigs[i] = BTOR_AIG_FALSE;
  for (i = len - 1; i >= 0; i--)
  {
    and = new_aigvec (avmgr, len);
    for (j = 0; j < len; j++)
      and->aigs[j] = btor_and_aig (avmgr->amgr, av1->aigs[j], av2->aigs[i]);
    shift = sll_n_bits (avmgr, and, len - 1 - i, BTOR_AIG_TRUE);
    add   = btor_add_aigvec (avmgr, result, shift);
    btor_release_delete_aigvec (avmgr, result);
    btor_release_delete_aigvec (avmgr, and);
    btor_release_delete_aigvec (avmgr, shift);
    result = add;
  }
  return result;
}

static BtorAIGVec *
sub_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIGVec *neg    = NULL;
  BtorAIG *cin       = NULL;
  BtorAIG *cout      = NULL;
  int len            = 0;
  int i              = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len    = av1->len;
  neg    = btor_not_aigvec (avmgr, av2);
  result = new_aigvec (avmgr, len);
  cin    = BTOR_AIG_TRUE;
  for (i = len - 1; i >= 0; i--)
  {
    result->aigs[i] =
        full_add_aig (avmgr->amgr, av1->aigs[i], neg->aigs[i], cin, &cout);
    btor_release_aig (avmgr->amgr, cin);
    cin = cout;
  }
  btor_release_delete_aigvec (avmgr, neg);
  btor_release_aig (avmgr->amgr, cout);
  return result;
}

static BtorAIGVec *
ugte_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  BtorAIG *lt        = NULL;
  BtorAIG *eq        = NULL;
  BtorAIG *gt        = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  result = new_aigvec (avmgr, 1);
  ripple_compare_aigvec (avmgr, av1, av2, &lt, &eq, &gt);
  result->aigs[0] = btor_or_aig (avmgr->amgr, gt, eq);
  btor_release_aig (avmgr->amgr, lt);
  btor_release_aig (avmgr->amgr, eq);
  btor_release_aig (avmgr->amgr, gt);
  return result;
}

static void
udiv_umod_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *av1,
                  BtorAIGVec *av2,
                  BtorAIGVec **quotient,
                  BtorAIGVec **remainder)
{
  BtorAIGVec *b_i           = NULL;
  BtorAIGVec *b_i_optimized = NULL;
  BtorAIGVec *temp          = NULL;
  BtorAIGVec *is_gte        = NULL;
  BtorAIGVec *sub           = NULL;
  BtorAIGVec *remainder_2n  = NULL;
  int len                   = 0;
  int len_2n                = 0;
  int i                     = 0;
  int j                     = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (remainder != NULL);
  assert (av1->len == av2->len);
  len = av1->len;
  assert (len <= INT_MAX / 2);
  len_2n       = len << 1;
  *quotient    = new_aigvec (avmgr, len);
  b_i          = new_aigvec (avmgr, len_2n);
  remainder_2n = new_aigvec (avmgr, len_2n);
  for (i = 0; i < len; i++)
  {
    b_i->aigs[i]          = btor_copy_aig (avmgr->amgr, av2->aigs[i]);
    remainder_2n->aigs[i] = BTOR_AIG_FALSE;
  }
  for (i = len; i < len_2n; i++)
  {
    b_i->aigs[i]          = BTOR_AIG_FALSE;
    remainder_2n->aigs[i] = btor_copy_aig (avmgr->amgr, av1->aigs[i - len]);
  }
  for (i = len - 1; i >= 0; i--)
  {
    temp = srl_n_bits (avmgr, b_i, 1, BTOR_AIG_TRUE);
    btor_release_delete_aigvec (avmgr, b_i);
    b_i    = temp;
    is_gte = ugte_aigvec (avmgr, remainder_2n, b_i);
    (*quotient)->aigs[len - 1 - i] =
        btor_copy_aig (avmgr->amgr, is_gte->aigs[0]);
    b_i_optimized = new_aigvec (avmgr, len_2n);
    /* The first len bits of b_i have to be zero in the case
     * where subtraction is computed */
    for (j = 0; j < len; j++) b_i_optimized->aigs[j] = BTOR_AIG_FALSE;
    for (j = len; j < len_2n; j++)
      b_i_optimized->aigs[j] = btor_copy_aig (avmgr->amgr, b_i->aigs[j]);
    sub  = sub_aigvec (avmgr, remainder_2n, b_i_optimized);
    temp = btor_cond_aigvec (avmgr, is_gte, sub, remainder_2n);
    btor_release_delete_aigvec (avmgr, remainder_2n);
    remainder_2n = temp;
    btor_release_delete_aigvec (avmgr, is_gte);
    btor_release_delete_aigvec (avmgr, sub);
    btor_release_delete_aigvec (avmgr, b_i_optimized);
  }
  btor_release_delete_aigvec (avmgr, b_i);
  *remainder = new_aigvec (avmgr, len);
  for (i = len; i < len_2n; i++)
    (*remainder)->aigs[i - len] =
        btor_copy_aig (avmgr->amgr, remainder_2n->aigs[i]);
  btor_release_delete_aigvec (avmgr, remainder_2n);
}

BtorAIGVec *
btor_udiv_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient  = NULL;
  BtorAIGVec *remainder = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  udiv_umod_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_release_delete_aigvec (avmgr, remainder);
  return quotient;
}

BtorAIGVec *
btor_umod_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient  = NULL;
  BtorAIGVec *remainder = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  udiv_umod_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_release_delete_aigvec (avmgr, quotient);
  return remainder;
}

BtorAIGVec *
btor_concat_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int pos            = 0;
  int len_av1        = 0;
  int len_av2        = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len > 0);
  assert (av2->len > 0);
  assert (INT_MAX - av1->len >= av2->len);
  len_av1 = av1->len;
  len_av2 = av2->len;
  result  = new_aigvec (avmgr, len_av1 + len_av2);
  for (i = 0; i < len_av1; i++)
    result->aigs[pos++] = btor_copy_aig (avmgr->amgr, av1->aigs[i]);
  for (i = 0; i < len_av2; i++)
    result->aigs[pos++] = btor_copy_aig (avmgr->amgr, av2->aigs[i]);
  return result;
}

BtorAIGVec *
btor_cond_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *av_cond,
                  BtorAIGVec *av_if,
                  BtorAIGVec *av_else)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av_cond != NULL);
  assert (av_if != NULL);
  assert (av_else != NULL);
  assert (av_cond->len == 1);
  assert (av_if->len == av_else->len);
  assert (av_if->len > 0);
  len    = av_if->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_cond_aig (
        avmgr->amgr, av_cond->aigs[0], av_if->aigs[i], av_else->aigs[i]);
  return result;
}

BtorAIGVec *
btor_copy_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  len    = av->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_copy_aig (avmgr->amgr, av->aigs[i]);
  return result;
}

void
btor_release_delete_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  int i   = 0;
  int len = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  len = av->len;
  for (i = 0; i < len; i++) btor_release_aig (avmgr->amgr, av->aigs[i]);
  btor_free (avmgr->mm, av->aigs, sizeof (BtorAIGVec *) * len);
  btor_free (avmgr->mm, av, sizeof (BtorAIGVec));
}

static BtorReadObj *
new_read_object (BtorAIGVecMgr *avmgr, BtorAIGVec *av_var, BtorAIGVec *av_index)
{
  BtorReadObj *result = NULL;
  assert (avmgr != NULL);
  assert (av_var != NULL);
  assert (av_index != NULL);
  result        = (BtorReadObj *) btor_malloc (avmgr->mm, sizeof (BtorReadObj));
  result->var   = btor_copy_aigvec (avmgr, av_var);
  result->index = btor_copy_aigvec (avmgr, av_index);
  return result;
}

static void
delete_read_object (BtorAIGVecMgr *avmgr, BtorReadObj *obj)
{
  assert (avmgr != NULL);
  assert (obj != NULL);
  btor_release_delete_aigvec (avmgr, obj->var);
  btor_release_delete_aigvec (avmgr, obj->index);
  btor_free (avmgr->mm, obj, sizeof (BtorReadObj));
}

void
btor_read_object_aigvec_mgr (BtorAIGVecMgr *avmgr,
                             BtorAIGVec *av_var,
                             BtorAIGVec *av_index)
{
  BtorReadObj *obj = NULL;
  assert (avmgr != NULL);
  assert (av_var != NULL);
  assert (av_index != NULL);
  obj = new_read_object (avmgr, av_var, av_index);
  BTOR_PUSH_STACK (avmgr->mm, avmgr->reads, obj);
}

static int
is_const_aigvec (BtorAIGVec *av)
{
  int i   = 0;
  int len = 0;
  assert (av != NULL);
  len = av->len;
  for (i = 0; i < len; i++)
  {
    if (!BTOR_IS_CONST_AIG (av->aigs[i])) return 0;
  }
  return 1;
}

static int
is_different_aigvec (BtorAIGVec *av1, BtorAIGVec *av2)
{
  int i   = 0;
  int len = 0;
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
  {
    if (av1->aigs[i] != av2->aigs[i]) return 1;
  }
  return 0;
}

static void
encode_read_constraint (BtorAIGVecMgr *avmgr,
                        BtorAIGVec *av_index1,
                        BtorAIGVec *av_index2,
                        BtorAIGVec *av_var1,
                        BtorAIGVec *av_var2)
{
  BtorMemMgr *mm   = NULL;
  BtorAIGMgr *amgr = NULL;
  BtorSATMgr *smgr = NULL;
  BtorAIG *aig1    = NULL;
  BtorAIG *aig2    = NULL;
  BtorIntStack diffs;
  int k            = 0;
  int len          = 0;
  int i_k          = 0;
  int j_k          = 0;
  int d_k          = 0;
  int e            = 0;
  int a_k          = 0;
  int b_k          = 0;
  int is_different = 0;
  assert (avmgr != NULL);
  assert (av_index1 != NULL);
  assert (av_index2 != NULL);
  assert (av_var1 != NULL);
  assert (av_var2 != NULL);
  mm           = avmgr->mm;
  amgr         = btor_get_aig_mgr_aigvec_mgr (avmgr);
  smgr         = btor_get_sat_mgr_aig_mgr (amgr);
  is_different = is_different_aigvec (av_index1, av_index2);
  if (is_different && is_const_aigvec (av_index1)
      && is_const_aigvec (av_index2))
    return;
  len = av_index1->len;
  if (is_different)
  {
    BTOR_INIT_STACK (diffs);
    for (k = 0; k < len; k++)
    {
      aig1 = av_index1->aigs[k];
      aig2 = av_index2->aigs[k];
      if (!BTOR_IS_CONST_AIG (aig1))
      {
        if (BTOR_REAL_ADDR_AIG (aig1)->cnf_id == 0)
          BTOR_REAL_ADDR_AIG (aig1)->cnf_id = btor_next_cnf_id_sat_mgr (smgr);
        if (BTOR_IS_INVERTED_AIG (aig1))
          i_k = -BTOR_REAL_ADDR_AIG (aig1)->cnf_id;
        else
          i_k = aig1->cnf_id;
        assert (i_k != 0);
      }
      if (!BTOR_IS_CONST_AIG (aig2))
      {
        if (BTOR_REAL_ADDR_AIG (aig2)->cnf_id == 0)
          BTOR_REAL_ADDR_AIG (aig2)->cnf_id = btor_next_cnf_id_sat_mgr (smgr);
        if (BTOR_IS_INVERTED_AIG (aig2))
          j_k = -BTOR_REAL_ADDR_AIG (aig2)->cnf_id;
        else
          j_k = aig2->cnf_id;
        assert (j_k != 0);
      }
      if ((((unsigned long int) aig1) ^ ((unsigned long int) aig2)) != 1ul)
      {
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
  assert (av_var1->len == av_var2->len);
  len = av_var1->len;
  for (k = 0; k < len; k++)
  {
    aig1 = av_var1->aigs[k];
    aig2 = av_var2->aigs[k];
    assert (!BTOR_IS_CONST_AIG (aig1));
    assert (!BTOR_IS_INVERTED_AIG (aig1));
    assert (!BTOR_IS_CONST_AIG (aig2));
    assert (!BTOR_IS_INVERTED_AIG (aig2));
    a_k = aig1->cnf_id;
    assert (a_k != 0);
    b_k = aig2->cnf_id;
    assert (b_k != 0);
    btor_add_sat (smgr, -e);
    btor_add_sat (smgr, a_k);
    btor_add_sat (smgr, -b_k);
    btor_add_sat (smgr, 0);
    btor_add_sat (smgr, -e);
    btor_add_sat (smgr, -a_k);
    btor_add_sat (smgr, b_k);
    btor_add_sat (smgr, 0);
  }
}

static void
handle_eager_read_constraints (BtorAIGVecMgr *avmgr)
{
  BtorReadObj **cur1 = NULL;
  BtorReadObj **cur2 = NULL;
  BtorReadObj *obj1  = NULL;
  BtorReadObj *obj2  = NULL;
  assert (avmgr != NULL);
  cur1 = avmgr->reads.top;
  while (cur1 != avmgr->reads.start)
  {
    cur1--;
    obj1 = *cur1;
    cur2 = cur1;
    while (cur2 != avmgr->reads.start)
    {
      cur2--;
      obj2 = *cur2;
      encode_read_constraint (
          avmgr, obj1->index, obj2->index, obj1->var, obj2->var);
    }
  }
}

void
btor_handle_read_constraints_aigvec_mgr (BtorAIGVecMgr *avmgr)
{
  assert (avmgr != NULL);
  if (avmgr->read_enc == BTOR_EAGER_READ_ENC)
    handle_eager_read_constraints (avmgr);
}

BtorAIGVecMgr *
btor_new_aigvec_mgr (BtorMemMgr *mm, int verbosity)
{
  BtorAIGVecMgr *avmgr = NULL;
  assert (mm != NULL);
  assert (verbosity >= -1);
  avmgr            = (BtorAIGVecMgr *) btor_malloc (mm, sizeof (BtorAIGVecMgr));
  avmgr->mm        = mm;
  avmgr->verbosity = verbosity;
  avmgr->read_enc  = BTOR_SAT_SOLVER_READ_ENC;
  avmgr->amgr      = btor_new_aig_mgr (mm, verbosity);
  BTOR_INIT_STACK (avmgr->reads);
  return avmgr;
}

void
btor_set_read_enc_aigvec_mgr (BtorAIGVecMgr *avmgr, BtorReadEnc read_enc)
{
  assert (avmgr != NULL);
  avmgr->read_enc = read_enc;
}

void
btor_delete_aigvec_mgr (BtorAIGVecMgr *avmgr)
{
  BtorReadObj **cur = NULL;
  assert (avmgr != NULL);
  for (cur = avmgr->reads.start; cur != avmgr->reads.top; cur++)
    delete_read_object (avmgr, *cur);
  btor_delete_aig_mgr (avmgr->amgr);
  BTOR_RELEASE_STACK (avmgr->mm, avmgr->reads);
  btor_free (avmgr->mm, avmgr, sizeof (BtorAIGVecMgr));
}

BtorAIGMgr *
btor_get_aig_mgr_aigvec_mgr (BtorAIGVecMgr *avmgr)
{
  assert (avmgr != NULL);
  return avmgr->amgr;
}

char *
btor_get_assignment_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  int i        = 0;
  int cur      = 0;
  int len      = 0;
  char *result = NULL;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  len    = av->len;
  result = (char *) btor_malloc (avmgr->mm, sizeof (char) * (len + 1));
  for (i = 0; i < len; i++)
  {
    assert (!BTOR_IS_INVERTED_AIG (av->aigs[i]));
    assert (BTOR_IS_VAR_AIG (av->aigs[i]));
    cur = btor_get_assignment_aig (avmgr->amgr, av->aigs[i]);
    if (cur == 1)
      result[i] = '1';
    else if (cur == -1)
      result[i] = '0';
    else
      result[i] = 'x';
  }
  result[i] = '\0';
  return result;
}

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
