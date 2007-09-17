#include "btoraigvec.h"
#include "btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/

struct BtorAIGVecMgr
{
  BtorMemMgr *mm;
  int verbosity;
  BtorAIGMgr *amgr;
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
  BTOR_NEW (avmgr->mm, result);
  BTOR_NEWN (avmgr->mm, result->aigs, len);
  result->len = len;
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

static BtorAIG *
lt_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr = NULL;
  BtorAIG *res, *tmp, *term0, *term1;
  int i;

  amgr = avmgr->amgr;
  res  = BTOR_AIG_FALSE;
  for (i = av1->len - 1; i >= 0; i--)
  {
    term0 = btor_and_aig (amgr, av1->aigs[i], BTOR_INVERT_AIG (av2->aigs[i]));

    tmp = btor_and_aig (amgr, BTOR_INVERT_AIG (term0), res);
    btor_release_aig (amgr, term0);
    btor_release_aig (amgr, res);
    res = tmp;

    term1 = btor_and_aig (amgr, BTOR_INVERT_AIG (av1->aigs[i]), av2->aigs[i]);

    tmp = btor_or_aig (amgr, term1, res);
    btor_release_aig (amgr, term1);
    btor_release_aig (amgr, res);
    res = tmp;
  }

  return res;
}

BtorAIGVec *
btor_ult_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *result = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  result          = new_aigvec (avmgr, 1);
  result->aigs[0] = lt_aigvec (avmgr, av1, av2);
  return result;
}

BtorAIGVec *
btor_eq_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr    = NULL;
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
  amgr       = avmgr->amgr;
  len        = av1->len;
  result     = new_aigvec (avmgr, 1);
  result_aig = btor_eq_aig (amgr, av1->aigs[0], av2->aigs[0]);
  for (i = 1; i < len; i++)
  {
    temp1 = btor_eq_aig (amgr, av1->aigs[i], av2->aigs[i]);
    temp2 = btor_and_aig (amgr, result_aig, temp1);
    btor_release_aig (amgr, temp1);
    btor_release_aig (amgr, result_aig);
    result_aig = temp2;
  }
  result->aigs[0] = result_aig;
  return result;
}

static BtorAIG *
half_adder (BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG **cout)
{
  BtorAIG *res, *x_and_y, *not_x, *not_y, *not_x_and_not_y, *x_xnor_y;
  x_and_y         = btor_and_aig (amgr, x, y);
  not_x           = BTOR_INVERT_AIG (x);
  not_y           = BTOR_INVERT_AIG (y);
  not_x_and_not_y = btor_and_aig (amgr, not_x, not_y);
  x_xnor_y        = btor_or_aig (amgr, x_and_y, not_x_and_not_y);
  res             = BTOR_INVERT_AIG (x_xnor_y);
  *cout           = x_and_y;
  btor_release_aig (amgr, not_x_and_not_y);
  return res;
}

static BtorAIG *
full_adder (
    BtorAIGMgr *amgr, BtorAIG *x, BtorAIG *y, BtorAIG *cin, BtorAIG **cout)
{
  BtorAIG *sum, *c1, *c2, *res;
  sum   = half_adder (amgr, x, y, &c1);
  res   = half_adder (amgr, sum, cin, &c2);
  *cout = btor_or_aig (amgr, c1, c2);
  btor_release_aig (amgr, sum);
  btor_release_aig (amgr, c1);
  btor_release_aig (amgr, c2);
  return res;
}

BtorAIGVec *
btor_add_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr   = NULL;
  BtorAIGVec *result = NULL;
  BtorAIG *cout      = NULL;
  BtorAIG *cin       = NULL;
  int i              = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  amgr   = avmgr->amgr;
  result = new_aigvec (avmgr, av1->len);
  cin    = BTOR_AIG_FALSE;
  for (i = av1->len - 1; i >= 0; i--)
  {
    result->aigs[i] = full_adder (amgr, av1->aigs[i], av2->aigs[i], cin, &cout);
    btor_release_aig (amgr, cin);
    cin = cout;
  }
  btor_release_aig (amgr, cout);
  return result;
}

static BtorAIGVec *
sll_n_bits (BtorAIGVecMgr *avmgr, BtorAIGVec *av, int n, BtorAIG *shift)
{
  BtorAIGMgr *amgr   = NULL;
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
  amgr = avmgr->amgr;
  len  = av->len;
  if (n == 0) return btor_copy_aigvec (avmgr, av);
  not_shift = btor_not_aig (amgr, shift);
  result    = new_aigvec (avmgr, len);
  for (i = 0; i < len - n; i++)
  {
    and1            = btor_and_aig (amgr, av->aigs[i], not_shift);
    and2            = btor_and_aig (amgr, av->aigs[i + n], shift);
    result->aigs[i] = btor_or_aig (amgr, and1, and2);
    btor_release_aig (amgr, and1);
    btor_release_aig (amgr, and2);
  }
  for (i = len - n; i < len; i++)
    result->aigs[i] = btor_and_aig (amgr, av->aigs[i], not_shift);
  btor_release_aig (amgr, not_shift);
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
  BtorAIGMgr *amgr   = NULL;
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
  amgr = avmgr->amgr;
  len  = av->len;
  if (n == 0) return btor_copy_aigvec (avmgr, av);
  not_shift = btor_not_aig (amgr, shift);
  result    = new_aigvec (avmgr, len);
  for (i = 0; i < n; i++)
    result->aigs[i] = btor_and_aig (amgr, av->aigs[i], not_shift);
  for (i = n; i < len; i++)
  {
    and1            = btor_and_aig (amgr, av->aigs[i], not_shift);
    and2            = btor_and_aig (amgr, av->aigs[i - n], shift);
    result->aigs[i] = btor_or_aig (amgr, and1, and2);
    btor_release_aig (amgr, and1);
    btor_release_aig (amgr, and2);
  }
  btor_release_aig (amgr, not_shift);
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

#if 0 /* word level multiplier */

static BtorAIGVec *
mul_aigvec (BtorAIGVecMgr * avmgr, BtorAIGVec * av1, BtorAIGVec * av2)
{
  BtorAIGVec *result = NULL;
  BtorAIGVec *and = NULL;
  BtorAIGVec *shift = NULL;
  BtorAIGVec *add = NULL;
  int i = 0;
  int j = 0;
  int len = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  len = av1->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = BTOR_AIG_FALSE;
  for (i = len - 1; i >= 0; i--)
    {
      and = new_aigvec (avmgr, len);
      for (j = 0; j < len; j++)
        and->aigs[j] = btor_and_aig (avmgr->amgr, av1->aigs[j], av2->aigs[i]);
      shift = sll_n_bits (avmgr, and, len - 1 - i, BTOR_AIG_TRUE);
      add = btor_add_aigvec (avmgr, result, shift);
      btor_release_delete_aigvec (avmgr, result);
      btor_release_delete_aigvec (avmgr, and);
      btor_release_delete_aigvec (avmgr, shift);
      result = add;
    }
  return result;
}

#endif

#if 1 /* gate level multiplier */

/* NOTE: word and gate level produce the same result */

static BtorAIGVec *
mul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  BtorAIG *cin, *cout, *and, *tmp;
  BtorAIGMgr *amgr;
  BtorAIGVec *res;
  int len, i, j;

  len  = a->len;
  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);

  assert (len > 0);

  res = new_aigvec (avmgr, len);

  for (j = 0; j < len; j++)
    res->aigs[j] = btor_and_aig (amgr, a->aigs[j], b->aigs[len - 1]);

  for (i = len - 2; i >= 0; i--)
  {
    cout = BTOR_AIG_FALSE;
    for (j = i; j >= 0; j--)
    {
      and          = btor_and_aig (amgr, a->aigs[len - 1 - i + j], b->aigs[i]);
      tmp          = res->aigs[j];
      cin          = cout;
      res->aigs[j] = full_adder (amgr, tmp, and, cin, &cout);
      btor_release_aig (amgr, and);
      btor_release_aig (amgr, tmp);
      btor_release_aig (amgr, cin);
    }
    btor_release_aig (amgr, cout);
  }

  return res;
}

#endif

#if 0 /* gate level carry save adder */

/* NOTE: this version of a carry save adder is working and has the same
 * size, but does not seem to be faster (for the SAT solver).  Some
 * benchmarking results gave slower performance.
 */
static BtorAIGVec *
mul_aigvec_csa (BtorAIGVecMgr * avmgr, BtorAIGVec * a, BtorAIGVec * b)
{
  BtorAIG * cin, * cout, * and, * tmp;
  BtorAIGVec * res, * carries;
  BtorAIGMgr * amgr;
  int len, i, j;

  len = a->len;
  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);

  assert (len > 0);

  res = new_aigvec (avmgr, len);
  carries = new_aigvec (avmgr, len);

  for (j = 0; j < len; j++)
    res->aigs[j] = btor_and_aig (amgr, a->aigs[j], b->aigs[len - 1]);

  for (j = 0; j < len; j++)
    carries->aigs[j] = BTOR_AIG_FALSE;

  for (i = len - 2; i >= 0; i--)
    {
      cout = BTOR_AIG_FALSE;
      for (j = i; j >= 0; j--)
	{
	  and = btor_and_aig (amgr, a->aigs[len - 1 - i + j], b->aigs[i]);
	  tmp = res->aigs[j];
	  cin = carries->aigs[j + 1];
	  res->aigs[j] = full_adder (amgr, tmp, and, cin, &cout);
	  carries->aigs[j + 1] = cout;
	  btor_release_aig (amgr, and);
	  btor_release_aig (amgr, tmp);
	  btor_release_aig (amgr, cin);
	}

      btor_release_aig (amgr, carries->aigs[0]);
      for (j = 0; j < len - 1; j++)
	carries->aigs[j] = carries->aigs[j+1];
      carries->aigs[len-1] = BTOR_AIG_FALSE;
    }

  btor_release_delete_aigvec (avmgr, carries);

  return res;
}

#endif

BtorAIGVec *
btor_mul_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *a, BtorAIGVec *b)
{
  return mul_aigvec (avmgr, a, b);
}

#if 0 /* restoring word level divider */

static BtorAIGVec *
sub_aigvec (BtorAIGVecMgr * avmgr,
            BtorAIGVec * av1, BtorAIGVec * av2,
	    BtorAIG ** cout_ptr)
{
  BtorAIGMgr *amgr = NULL;
  BtorAIGVec *result = NULL;
  BtorAIGVec *neg = NULL;
  BtorAIG *cin = NULL;
  BtorAIG *cout = NULL;
  int len = 0;
  int i = 0;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  amgr = avmgr->amgr;
  len = av1->len;
  neg = btor_not_aigvec (avmgr, av2);
  result = new_aigvec (avmgr, len);
  cin = BTOR_AIG_TRUE;
  for (i = len - 1; i >= 0; i--)
    {
      result->aigs[i] = full_adder (amgr, av1->aigs[i],
                                    neg->aigs[i], cin, &cout);
      btor_release_aig (amgr, cin);
      cin = cout;
    }
  btor_release_delete_aigvec (avmgr, neg);
  *cout_ptr = cin;
  return result;
}

static void
udiv_urem_aigvec (BtorAIGVecMgr * avmgr, 
                  BtorAIGVec * av1, BtorAIGVec * av2,
		  BtorAIGVec ** quotient_ptr, BtorAIGVec ** remainder_ptr)
{
  BtorAIGVec * quotient, * remainder, * sub, * tmp;
  BtorAIGMgr * amgr;
  BtorAIG * cout;
  int len, i, j;

  len = av1->len;
  assert (len > 0);
  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);

  quotient = new_aigvec (avmgr, len);
  remainder = new_aigvec (avmgr, len);

  for (j = 0; j < len; j++)
    remainder->aigs[j] = BTOR_AIG_FALSE;

  for (i = 0; i < len; i++)
    {
      btor_release_aig (amgr, remainder->aigs[0]);

      for (j = 0 ; j < len - 1; j++)
	remainder->aigs[j] = remainder->aigs[j+1];
      remainder->aigs[len - 1] = btor_copy_aig (amgr, av1->aigs[i]);

      sub = sub_aigvec (avmgr, remainder, av2, &cout);
      quotient->aigs[i] = cout;

      tmp = new_aigvec (avmgr, len);
      for (j = 0; j < len; j++)
	tmp->aigs[j] = btor_cond_aig (amgr,
	                              cout,
				      sub->aigs[j],
				      remainder->aigs[j]);

      btor_release_delete_aigvec (avmgr, remainder);
      btor_release_delete_aigvec (avmgr, sub);
      remainder = tmp;
    }

  *quotient_ptr = quotient;
  *remainder_ptr = remainder;
}

#endif

#if 1 /* restoring gate level divider */

/* NOTE: seems to be fastest, needs 8786 AIG nodes */

static void
SC_GATE_CO (BtorAIGMgr *amgr, BtorAIG **CO, BtorAIG *R, BtorAIG *D, BtorAIG *CI)
{
  BtorAIG *D_or_CI, *D_and_CI, *M;
  D_or_CI  = btor_or_aig (amgr, D, CI);
  D_and_CI = btor_and_aig (amgr, D, CI);
  M        = btor_and_aig (amgr, D_or_CI, R);
  *CO      = btor_or_aig (amgr, M, D_and_CI);
  btor_release_aig (amgr, D_or_CI);
  btor_release_aig (amgr, D_and_CI);
  btor_release_aig (amgr, M);
}

static void
SC_GATE_S (BtorAIGMgr *amgr,
           BtorAIG **S,
           BtorAIG *R,
           BtorAIG *D,
           BtorAIG *CI,
           BtorAIG *Q)
{
#if 1 /* xor at input of full adder (smaller) */
  BtorAIG *D_and_CI, *D_or_CI;
  BtorAIG *T2_or_R, *T2_and_R;
  BtorAIG *T1, *T2;
  D_or_CI  = btor_or_aig (amgr, D, CI);
  D_and_CI = btor_and_aig (amgr, D, CI);
  T1       = btor_and_aig (amgr, D_or_CI, BTOR_INVERT_AIG (D_and_CI));
  T2       = btor_and_aig (amgr, T1, Q);
  T2_or_R  = btor_or_aig (amgr, T2, R);
  T2_and_R = btor_and_aig (amgr, T2, R);
  *S       = btor_and_aig (amgr, T2_or_R, BTOR_INVERT_AIG (T2_and_R));
  btor_release_aig (amgr, T1);
  btor_release_aig (amgr, T2);
  btor_release_aig (amgr, D_and_CI);
  btor_release_aig (amgr, D_or_CI);
  btor_release_aig (amgr, T2_and_R);
  btor_release_aig (amgr, T2_or_R);
#else /* ite at output of full adder (larger but 'abc' likes it more) */
  BtorAIG *T1, *T2, *T3, *T4;
  BtorAIG *D_and_CI, *D_or_CI;
  D_or_CI  = btor_or_aig (amgr, D, CI);
  D_and_CI = btor_and_aig (amgr, D, CI);
  T1       = btor_and_aig (amgr, D_or_CI, BTOR_INVERT_AIG (D_and_CI));
  T2       = btor_xor_aig (amgr, T1, R);
  T3       = btor_or_aig (amgr, T2, BTOR_INVERT_AIG (Q));
  T4       = btor_or_aig (amgr, R, (Q));
  *S       = btor_and_aig (amgr, T3, T4);
  btor_release_aig (amgr, T4);
  btor_release_aig (amgr, T3);
  btor_release_aig (amgr, T2);
  btor_release_aig (amgr, T1);
  btor_release_aig (amgr, D_and_CI);
  btor_release_aig (amgr, D_or_CI);
#endif
}

static void
udiv_urem_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *Ain,
                  BtorAIGVec *Din,
                  BtorAIGVec **Qptr,
                  BtorAIGVec **Rptr)
{
  BtorAIG **A, **nD, ***S, ***C;
  BtorAIGVec *Q, *R;
  BtorAIGMgr *amgr;
  BtorMemMgr *mem;
  int size, i, j;

  size = Ain->len;
  assert (size > 0);

  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);
  mem  = avmgr->mm;

  BTOR_NEWN (mem, A, size);
  for (i = 0; i < size; i++) A[i] = Ain->aigs[size - 1 - i];

  BTOR_NEWN (mem, nD, size);
  for (i = 0; i < size; i++) nD[i] = BTOR_INVERT_AIG (Din->aigs[size - 1 - i]);

  BTOR_NEWN (mem, S, size + 1);
  for (j = 0; j <= size; j++)
  {
    BTOR_NEWN (mem, S[j], size + 1);
    for (i = 0; i <= size; i++) S[j][i] = BTOR_AIG_FALSE;
  }

  BTOR_NEWN (mem, C, size + 1);
  for (j = 0; j <= size; j++)
  {
    BTOR_NEWN (mem, C[j], size + 1);
    for (i = 0; i <= size; i++) C[j][i] = BTOR_AIG_FALSE;
  }

  R = new_aigvec (avmgr, size);
  Q = new_aigvec (avmgr, size);

  for (j = 0; j <= size - 1; j++)
  {
    S[j][0] = btor_copy_aig (amgr, A[size - j - 1]);
    C[j][0] = BTOR_AIG_TRUE;

    for (i = 0; i <= size - 1; i++)
      SC_GATE_CO (amgr, &C[j][i + 1], S[j][i], nD[i], C[j][i]);

    Q->aigs[j] = btor_or_aig (amgr, C[j][size], S[j][size]);

    for (i = 0; i <= size - 1; i++)
      SC_GATE_S (amgr, &S[j + 1][i + 1], S[j][i], nD[i], C[j][i], Q->aigs[j]);

#if 0
      {
	char name[100];
	FILE * file;
	sprintf (name, "/tmp/C%02d.aig", j);
	file = fopen (name, "w");
	btor_dump_aigs (amgr, 1, file, C[j], size + 1);
	fclose (file);
      }
      
      {
	char name[100];
	FILE * file;
	sprintf (name, "/tmp/S%02d.aig", j + 1);
	file = fopen (name, "w");
	btor_dump_aigs (amgr, 1, file, S[j+1], size + 1);
	fclose (file);
      }
#endif
  }

  for (i = size; i >= 1; i--)
    R->aigs[size - i] = btor_copy_aig (amgr, S[size][i]);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_release_aig (amgr, C[j][i]);
    BTOR_DELETEN (mem, C[j], size + 1);
  }
  BTOR_DELETEN (mem, C, size + 1);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) btor_release_aig (amgr, S[j][i]);
    BTOR_DELETEN (mem, S[j], size + 1);
  }
  BTOR_DELETEN (mem, S, size + 1);

  BTOR_DELETEN (mem, nD, size);
  BTOR_DELETEN (mem, A, size);

  *Qptr = Q;
  *Rptr = R;
}

#endif

#if 0 /* non restoring gate level divider */

static void
udiv_urem_aigvec (BtorAIGVecMgr * avmgr,
                  BtorAIGVec * A, 
		  BtorAIGVec * D,
		  BtorAIGVec ** Qptr,
		  BtorAIGVec ** Rptr)
{
  BtorAIG ** R, * RMSB, * sub, * ci, * co, * sum, * xor, * masked;
  BtorAIGMgr * amgr;
  BtorMemMgr * mem;
  BtorAIGVec * Q;
  int len, i, j;

  amgr = btor_get_aig_mgr_aigvec_mgr (avmgr);
  mem = avmgr->mm;

  len = A->len;
  assert (len > 0);
  assert (len == D->len);

  BTOR_NEWN (mem, R, len);
  for (i = 0; i < len; i++)
    R[i] = BTOR_AIG_FALSE;

  RMSB = BTOR_AIG_FALSE;

  Q = new_aigvec (avmgr, len);

  sub = BTOR_AIG_TRUE;
  for (i = 0; i < len; i++)
    {
      btor_release_aig (amgr, RMSB);
      RMSB = R[0];
      for (j = 0; j < len - 1; j++)
	R[j] = R[j+1];
      R[len-1] = btor_copy_aig (amgr, A->aigs[i]);

      ci = btor_copy_aig (amgr, sub);
      for (j = len-1; j >= 0; j--)
	{
	  xor = btor_xor_aig (amgr, D->aigs[j], sub);
	  sum = full_adder (amgr, xor, R[j], ci, &co);
	  btor_release_aig (amgr, xor);
	  btor_release_aig (amgr, ci);
	  btor_release_aig (amgr, R[j]);
	  R[j] = sum;
	  ci = co;
	}

      sum = full_adder (amgr, sub, RMSB, ci, &co);
      btor_release_aig (amgr, ci);
      btor_release_aig (amgr, co);
      btor_release_aig (amgr, RMSB);
      RMSB = sum;

      btor_release_aig (amgr, sub);
      sub = btor_not_aig (amgr, RMSB);

      Q->aigs[i] = btor_copy_aig (amgr, sub);
    }

  btor_release_aig (amgr, RMSB);

  ci = BTOR_AIG_FALSE;
  for (j = len-1; j >= 0; j--)
    {
      masked = btor_and_aig (amgr, BTOR_INVERT_AIG (sub), D->aigs[j]);
      sum = full_adder (amgr, masked, R[j], ci, &co);
      btor_release_aig (amgr, masked);
      btor_release_aig (amgr, ci);
      btor_release_aig (amgr, R[j]);
      R[j] = sum;
      ci = co;
    }

  btor_release_aig (amgr, sub);
  btor_release_aig (amgr, ci);

  *Rptr = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    (*Rptr)->aigs[i] = R[i];

  BTOR_DELETEN (mem, R, len);

  *Qptr = Q;
}

#endif

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
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_release_delete_aigvec (avmgr, remainder);
  return quotient;
}

BtorAIGVec *
btor_urem_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGVec *quotient  = NULL;
  BtorAIGVec *remainder = NULL;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  assert (av1->len > 0);
  udiv_urem_aigvec (avmgr, av1, av2, &quotient, &remainder);
  btor_release_delete_aigvec (avmgr, quotient);
  return remainder;
}

BtorAIGVec *
btor_concat_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av1, BtorAIGVec *av2)
{
  BtorAIGMgr *amgr   = NULL;
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
  amgr    = avmgr->amgr;
  len_av1 = av1->len;
  len_av2 = av2->len;
  result  = new_aigvec (avmgr, len_av1 + len_av2);
  for (i = 0; i < len_av1; i++)
    result->aigs[pos++] = btor_copy_aig (amgr, av1->aigs[i]);
  for (i = 0; i < len_av2; i++)
    result->aigs[pos++] = btor_copy_aig (amgr, av2->aigs[i]);
  return result;
}

BtorAIGVec *
btor_cond_aigvec (BtorAIGVecMgr *avmgr,
                  BtorAIGVec *av_cond,
                  BtorAIGVec *av_if,
                  BtorAIGVec *av_else)
{
  BtorAIGMgr *amgr   = NULL;
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
  amgr   = avmgr->amgr;
  len    = av_if->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++)
    result->aigs[i] = btor_cond_aig (
        amgr, av_cond->aigs[0], av_if->aigs[i], av_else->aigs[i]);
  return result;
}

BtorAIGVec *
btor_copy_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorAIGMgr *amgr   = NULL;
  BtorAIGVec *result = NULL;
  int i              = 0;
  int len            = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  amgr   = avmgr->amgr;
  len    = av->len;
  result = new_aigvec (avmgr, len);
  for (i = 0; i < len; i++) result->aigs[i] = btor_copy_aig (amgr, av->aigs[i]);
  return result;
}

int
btor_is_const_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  int i   = 0;
  int len = 0;
  (void) avmgr;
  assert (avmgr != NULL);
  assert (av != NULL);
  len = av->len;
  for (i = 0; i < len; i++)
    if (!BTOR_IS_CONST_AIG (av->aigs[i])) return 0;
  return 1;
}

int
btor_is_different_aigvec (BtorAIGVecMgr *avmgr,
                          BtorAIGVec *av1,
                          BtorAIGVec *av2)
{
  int i   = 0;
  int len = 0;
  (void) avmgr;
  assert (avmgr != NULL);
  assert (av1 != NULL);
  assert (av2 != NULL);
  assert (av1->len == av2->len);
  len = av1->len;
  for (i = 0; i < len; i++)
    if (av1->aigs[i] != av2->aigs[i]) return 1;
  return 0;
}

void
btor_release_delete_aigvec (BtorAIGVecMgr *avmgr, BtorAIGVec *av)
{
  BtorMemMgr *mm   = NULL;
  BtorAIGMgr *amgr = NULL;
  int i            = 0;
  int len          = 0;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  mm   = avmgr->mm;
  amgr = avmgr->amgr;
  len  = av->len;
  for (i = 0; i < len; i++) btor_release_aig (amgr, av->aigs[i]);
  BTOR_DELETEN (mm, av->aigs, len);
  BTOR_DELETE (mm, av);
}

BtorAIGVecMgr *
btor_new_aigvec_mgr (BtorMemMgr *mm, int verbosity)
{
  BtorAIGVecMgr *avmgr = NULL;
  assert (mm != NULL);
  assert (verbosity >= -1);
  BTOR_NEW (mm, avmgr);
  avmgr->mm        = mm;
  avmgr->verbosity = verbosity;
  avmgr->amgr      = btor_new_aig_mgr (mm, verbosity);
  return avmgr;
}

void
btor_delete_aigvec_mgr (BtorAIGVecMgr *avmgr)
{
  assert (avmgr != NULL);
  btor_delete_aig_mgr (avmgr->amgr);
  BTOR_DELETE (avmgr->mm, avmgr);
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
  BtorAIGMgr *amgr = NULL;
  int i            = 0;
  int cur          = 0;
  int len          = 0;
  char *result     = NULL;
  assert (avmgr != NULL);
  assert (av != NULL);
  assert (av->len > 0);
  amgr = avmgr->amgr;
  len  = av->len;
  BTOR_NEWN (avmgr->mm, result, len + 1);
  for (i = 0; i < len; i++)
  {
    cur = btor_get_assignment_aig (amgr, av->aigs[i]);
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
