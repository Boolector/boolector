#include "btorrewrite.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorutil.h"

#include <assert.h>

/* Rewriting bounds */
#define BTOR_SLICE_OVER_CONCAT_EXP_RW_BOUND 128
#define BTOR_EQ_EXP_RW_BOUND 128
#define BTOR_MUL_EXP_RW_BOUND 128
#define BTOR_READ_OVER_WRITE_DOWN_PROPAGATION_LIMIT 128
#define BTOR_WRITE_CHAIN_EXP_RW_BOUND 20
#define BTOR_COND_EXP_RW_BOUND 128

static BtorExp *rewrite_cond_exp_bounded (
    Btor *, BtorExp *, BtorExp *, BtorExp *, int *);

static int
is_const_one_exp (Btor *btor, BtorExp *exp)
{
  int result;
  BtorExp *real_exp;
  assert (btor != NULL);
  assert (exp != NULL);
  assert (btor->rewrite_level > 0);

  /* constants are normalized and even,
   * constant 'one' has to be inverted */
  if (!BTOR_IS_INVERTED_EXP (exp)) return 0;

  if (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (exp))) return 0;

  real_exp = BTOR_REAL_ADDR_EXP (exp);
  btor_invert_const (btor->mm, real_exp->bits);
  result = btor_is_special_const (real_exp->bits) == BTOR_SPECIAL_CONST_ONE;
  btor_invert_const (btor->mm, real_exp->bits);

  return result;
}

static char *
compute_slice_3vl (Btor *btor, BtorExp *e0, int upper, int lower)
{
  int invert_e0;
  char *b0, *result;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (e0 != NULL);
  assert (upper < BTOR_REAL_ADDR_EXP (e0)->len);
  assert (upper >= lower);
  assert (lower >= 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->bits != NULL);
  assert (btor->rewrite_level > 1);

  mm        = btor->mm;
  b0        = BTOR_REAL_ADDR_EXP (e0)->bits;
  invert_e0 = 0;

  if (BTOR_IS_INVERTED_EXP (e0))
  {
    invert_e0 = 1;
    btor_invert_const_3vl (mm, b0);
  }

  result = btor_slice_const_3vl (mm, b0, upper, lower);

  if (invert_e0) btor_invert_const_3vl (mm, b0);

  return result;
}

static BtorExp *
slice_exp_node_3vl (Btor *btor, BtorExp *exp, int upper, int lower)
{
  char *bits_3vl = NULL;
  BtorExp *result;
  BtorMemMgr *mm;

  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_slice_3vl (btor, exp, upper, lower);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_slice_exp_node (btor, exp, upper, lower);
  assert (result != NULL);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_slice_exp_bounded (
    Btor *btor, BtorExp *exp, int upper, int lower, int *calls)
{
  BtorMemMgr *mm;
  BtorExp *real_exp, *result;
  char *bresult;
  int len, len_result;

  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));
  assert (calls != NULL);
  assert (*calls >= 0);

  result     = NULL;
  mm         = btor->mm;
  real_exp   = BTOR_REAL_ADDR_EXP (exp);
  len        = real_exp->len;
  len_result = upper - lower + 1;

  if (len == len_result) /* handles result->len == 1 */
    result = btor_copy_exp (btor, exp);
  else if (BTOR_IS_CONST_EXP (real_exp))
  {
    bresult = btor_slice_const (mm, real_exp->bits, upper, lower);
    result  = btor_const_exp (btor, bresult);
    result  = BTOR_COND_INVERT_EXP (exp, result);
    btor_delete_const (mm, bresult);
  }
  /* check if slice and child of concat matches */
  else if (real_exp->kind == BTOR_CONCAT_EXP)
  {
    if (lower == 0 && BTOR_REAL_ADDR_EXP (real_exp->e[1])->len == len_result)
    {
      if (BTOR_IS_INVERTED_EXP (exp))
        result = BTOR_INVERT_EXP (btor_copy_exp (btor, real_exp->e[1]));
      else
        result = btor_copy_exp (btor, real_exp->e[1]);
    }
    else if (btor->rewrite_level < 3)
    {
      /* we look just one level down */
      if (upper == len - 1
          && BTOR_REAL_ADDR_EXP (real_exp->e[0])->len == len_result)
      {
        if (BTOR_IS_INVERTED_EXP (exp))
          result = BTOR_INVERT_EXP (btor_copy_exp (btor, real_exp->e[0]));
        else
          result = btor_copy_exp (btor, real_exp->e[0]);
      }
    }
    else if (*calls < BTOR_SLICE_OVER_CONCAT_EXP_RW_BOUND)
    {
      assert (btor->rewrite_level >= 3);
      /* concats are normalized at rewrite level 3 */
      /* we recursively check if slice and child of concat matches */
      if (lower >= BTOR_REAL_ADDR_EXP (real_exp->e[1])->len)
      {
        *calls += 1;
        len = BTOR_REAL_ADDR_EXP (real_exp->e[1])->len;
        if (BTOR_IS_INVERTED_EXP (exp))
          result = rewrite_slice_exp_bounded (btor,
                                              BTOR_INVERT_EXP (real_exp->e[0]),
                                              upper - len,
                                              lower - len,
                                              calls);
        else
          result = rewrite_slice_exp_bounded (
              btor, real_exp->e[0], upper - len, lower - len, calls);
      }
    }
  }

  if (result == NULL) result = slice_exp_node_3vl (btor, exp, upper, lower);

  return result;
}

BtorExp *
btor_rewrite_slice_exp (Btor *btor, BtorExp *exp, int upper, int lower)
{
  int calls;
  char *bits_3vl = NULL;
  BtorExp *result;
  BtorMemMgr *mm;

  exp = btor_pointer_chase_simplified_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_slice_3vl (btor, exp, upper, lower);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  calls  = 0;
  result = rewrite_slice_exp_bounded (btor, exp, upper, lower, &calls);
  assert (result != NULL);

  return result;
}

static char *
compute_binary_3vl (Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1)
{
  int invert_e0, invert_e1, same_children_mem;
  char *b0, *b1, *result;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (kind != BTOR_READ_EXP);
  assert (kind != BTOR_AEQ_EXP);
  assert (BTOR_REAL_ADDR_EXP (e0)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->bits != NULL);
  assert (BTOR_REAL_ADDR_EXP (e1)->bits != NULL);
  assert (btor->rewrite_level > 1);

  mm        = btor->mm;
  b0        = BTOR_REAL_ADDR_EXP (e0)->bits;
  b1        = BTOR_REAL_ADDR_EXP (e1)->bits;
  invert_e0 = 0;
  invert_e1 = 0;

  same_children_mem = b0 == b1;

  if (same_children_mem)
  {
    if (BTOR_IS_INVERTED_EXP (e0))
      b0 = btor_not_const_3vl (mm, b0);
    else
      b0 = btor_copy_const (mm, b0);

    if (BTOR_IS_INVERTED_EXP (e1))
      b1 = btor_not_const_3vl (mm, b1);
    else
      b1 = btor_copy_const (mm, b1);
  }
  else
  {
    if (BTOR_IS_INVERTED_EXP (e0))
    {
      invert_e0 = 1;
      btor_invert_const_3vl (mm, b0);
    }

    if (BTOR_IS_INVERTED_EXP (e1))
    {
      invert_e1 = 1;
      btor_invert_const_3vl (mm, b1);
    }
  }

  switch (kind)
  {
    case BTOR_AND_EXP: result = btor_and_const_3vl (mm, b0, b1); break;
    case BTOR_BEQ_EXP: result = btor_eq_const_3vl (mm, b0, b1); break;
    case BTOR_ADD_EXP: result = btor_add_const_3vl (mm, b0, b1); break;
    case BTOR_MUL_EXP: result = btor_mul_const_3vl (mm, b0, b1); break;
    case BTOR_ULT_EXP: result = btor_ult_const_3vl (mm, b0, b1); break;
    case BTOR_SLL_EXP: result = btor_sll_const_3vl (mm, b0, b1); break;
    case BTOR_SRL_EXP: result = btor_srl_const_3vl (mm, b0, b1); break;
    case BTOR_UDIV_EXP: result = btor_udiv_const_3vl (mm, b0, b1); break;
    case BTOR_UREM_EXP: result = btor_urem_const_3vl (mm, b0, b1); break;
    default:
      assert (kind == BTOR_CONCAT_EXP);
      result = btor_concat_const_3vl (mm, b0, b1);
      break;
  }

  if (same_children_mem)
  {
    btor_delete_const (mm, b0);
    btor_delete_const (mm, b1);
  }
  else
  {
    if (invert_e0) btor_invert_const_3vl (mm, b0);
    if (invert_e1) btor_invert_const_3vl (mm, b1);
  }

  return result;
}

static BtorExp *
rewrite_binary_exp (Btor *btor, BtorExpKind kind, BtorExp *e0, BtorExp *e1)
{
  BtorMemMgr *mm;
  BtorExp *result, *real_e0, *real_e1, *temp, *zero, *one;
  BtorExp *ones, *eq, *temp_left, *temp_right;
  BtorExp *(*fptr) (Btor *, BtorExp *, BtorExp *);
  char *b0, *b1, *bresult;
  int same_children_mem;
  int invert_b0 = 0;
  int invert_b1 = 0;
  BtorSpecialConst sc;
  assert (btor != NULL);
  assert (btor->rewrite_level > 0);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (e0 != NULL);
  assert (e1 != NULL);
  mm      = btor->mm;
  result  = NULL;
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
    result = btor_const_exp (btor, bresult);
    btor_delete_const (mm, bresult);
  }
  else if (BTOR_IS_CONST_EXP (real_e0) && !BTOR_IS_CONST_EXP (real_e1))
  {
    invert_b0 = BTOR_IS_INVERTED_EXP (e0);
    b0        = real_e0->bits;
    if (invert_b0) btor_invert_const (mm, b0);
    sc = btor_is_special_const (b0);
    /* invert back if necessary */
    if (invert_b0) btor_invert_const (mm, b0);
    switch (sc)
    {
      case BTOR_SPECIAL_CONST_ZERO:
        if (kind == BTOR_BEQ_EXP && real_e0->len == 1)
          result = btor_not_exp (btor, e1);
        else if (kind == BTOR_ULT_EXP) /* 0 < a --> a != 0 */
          result = BTOR_INVERT_EXP (btor_eq_exp (btor, e0, e1));
        else if (kind == BTOR_ADD_EXP)
          result = btor_copy_exp (btor, e1);
        else if (kind == BTOR_MUL_EXP || kind == BTOR_SLL_EXP
                 || kind == BTOR_SRL_EXP || kind == BTOR_UREM_EXP
                 || kind == BTOR_AND_EXP)
          result = btor_zero_exp (btor, real_e0->len);
        else if (kind == BTOR_UDIV_EXP)
        {
          zero   = btor_zero_exp (btor, real_e0->len);
          ones   = btor_ones_exp (btor, real_e0->len);
          eq     = btor_eq_exp (btor, e1, zero);
          result = btor_cond_exp (btor, eq, ones, zero);
          btor_release_exp (btor, zero);
          btor_release_exp (btor, eq);
          btor_release_exp (btor, ones);
        }
        break;
      case BTOR_SPECIAL_CONST_ONE_ONES:
        assert (real_e0->len == 1);
        if (kind == BTOR_AND_EXP || kind == BTOR_BEQ_EXP
            || kind == BTOR_MUL_EXP)
          result = btor_copy_exp (btor, e1);
        else if (kind == BTOR_ULT_EXP)
          result = btor_false_exp (btor);
        break;
      case BTOR_SPECIAL_CONST_ONE:
        if (kind == BTOR_MUL_EXP) result = btor_copy_exp (btor, e1);
        break;
      case BTOR_SPECIAL_CONST_ONES:
        if (kind == BTOR_AND_EXP)
          result = btor_copy_exp (btor, e1);
        else if (kind == BTOR_ULT_EXP) /* UNSIGNED_MAX < x */
          result = btor_false_exp (btor);
        break;
      default: assert (sc == BTOR_SPECIAL_CONST_NONE); break;
    }
  }
  else if (!BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1))
  {
    invert_b1 = BTOR_IS_INVERTED_EXP (e1);
    b1        = real_e1->bits;
    if (invert_b1) btor_invert_const (mm, b1);
    sc = btor_is_special_const (b1);
    /* invert back if necessary */
    if (invert_b1) btor_invert_const (mm, b1);
    switch (sc)
    {
      case BTOR_SPECIAL_CONST_ZERO:
        if (kind == BTOR_BEQ_EXP && real_e0->len == 1)
          result = btor_not_exp (btor, e0);
        else if (kind == BTOR_SLL_EXP || kind == BTOR_SRL_EXP
                 || kind == BTOR_UREM_EXP || kind == BTOR_ADD_EXP)
          result = btor_copy_exp (btor, e0);
        else if (kind == BTOR_MUL_EXP || kind == BTOR_AND_EXP)
          result = btor_zero_exp (btor, real_e0->len);
        else if (kind == BTOR_ULT_EXP) /* x < 0 */
          result = btor_false_exp (btor);
        else if (kind == BTOR_UDIV_EXP)
          result = btor_ones_exp (btor, real_e0->len);
        break;
      case BTOR_SPECIAL_CONST_ONE_ONES:
        assert (real_e1->len == 1);
        if (kind == BTOR_AND_EXP || kind == BTOR_BEQ_EXP || kind == BTOR_MUL_EXP
            || kind == BTOR_UDIV_EXP)
          result = btor_copy_exp (btor, e0);
        break;
      case BTOR_SPECIAL_CONST_ONE:
        if (kind == BTOR_MUL_EXP || kind == BTOR_UDIV_EXP)
          result = btor_copy_exp (btor, e0);
        else if (kind == BTOR_UREM_EXP)
          result = btor_zero_exp (btor, real_e0->len);
        else if (kind == BTOR_ULT_EXP)
        {
          temp   = btor_zero_exp (btor, real_e0->len);
          result = btor_eq_exp (btor, e0, temp);
          btor_release_exp (btor, temp);
        }
        break;
      case BTOR_SPECIAL_CONST_ONES:
        if (kind == BTOR_AND_EXP)
          result = btor_copy_exp (btor, e0);
        else if (kind == BTOR_ULT_EXP)
          result = BTOR_INVERT_EXP (btor_eq_exp (btor, e0, e1));
        break;
      default: assert (sc == BTOR_SPECIAL_CONST_NONE); break;
    }
  }
  else if (real_e0 == real_e1
           && (kind == BTOR_BEQ_EXP || kind == BTOR_AEQ_EXP
               || kind == BTOR_ADD_EXP))
  {
    if (kind == BTOR_BEQ_EXP)
    {
      if (e0 == e1)
        result = btor_true_exp (btor); /* x == x */
      else
        result = btor_false_exp (btor); /* x == ~x */
    }
    else if (kind == BTOR_AEQ_EXP)
    {
      /* arrays must not be negated */
      assert (e0 == e1);
      result = btor_true_exp (btor); /* x == x */
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
          result = btor_mul_exp (btor, e0, temp);
          btor_release_exp (btor, temp);
        }
      }
      else
        /* replace x + ~x by -1 */
        result = btor_ones_exp (btor, real_e0->len);
    }
  }
  else if (e0 == e1
           && (kind == BTOR_ULT_EXP || kind == BTOR_UREM_EXP
               || kind == BTOR_UDIV_EXP))
  {
    switch (kind)
    {
      case BTOR_ULT_EXP:
        result = btor_false_exp (btor);
        break;
        /* v / v is 1 if v != 0 and UINT_MAX otherwise */
      case BTOR_UDIV_EXP:
        zero   = btor_zero_exp (btor, real_e0->len);
        one    = btor_one_exp (btor, real_e0->len);
        ones   = btor_ones_exp (btor, real_e0->len);
        eq     = btor_eq_exp (btor, e0, zero);
        result = btor_cond_exp (btor, eq, ones, one);
        btor_release_exp (btor, zero);
        btor_release_exp (btor, eq);
        btor_release_exp (btor, ones);
        btor_release_exp (btor, one);
        break;
      default:
        assert (kind == BTOR_UREM_EXP);
        result = btor_zero_exp (btor, real_e0->len);
        break;
    }
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
      case BTOR_ULT_EXP: fptr = btor_ult_exp; break;
      case BTOR_BEQ_EXP:
      case BTOR_AEQ_EXP: fptr = btor_eq_exp; break;
      case BTOR_ADD_EXP: fptr = btor_add_exp; break;
      default:
        assert (kind == BTOR_UDIV_EXP);
        fptr = btor_udiv_exp;
        break;
    }
    temp_left  = fptr (btor,
                      BTOR_COND_INVERT_EXP (e0, real_e0->e[1]),
                      BTOR_COND_INVERT_EXP (e0, real_e1->e[1]));
    temp_right = fptr (btor,
                       BTOR_COND_INVERT_EXP (e0, real_e0->e[2]),
                       BTOR_COND_INVERT_EXP (e0, real_e1->e[2]));
    result     = btor_cond_exp (btor, real_e0->e[0], temp_left, temp_right);
    btor_release_exp (btor, temp_left);
    btor_release_exp (btor, temp_right);
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
  /* TODO MAX-1 < a <=> a == MAX */

  /* TODO (x < ~x) <=> !msb(x) */
  /* TODO (~x < x) <=> msb(x) */

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

static int
is_always_unequal (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1;
  int result;
  char *bits_3vl = NULL;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  /* we need this so that a + 0 is rewritten to a,
   * and constants are normalized (all inverted constants are odd) */
  assert (btor->rewrite_level > 0);

  result = 0;

  real_e0 = BTOR_REAL_ADDR_EXP (e0);
  real_e1 = BTOR_REAL_ADDR_EXP (e1);

  if (BTOR_IS_ARRAY_EXP (real_e0))
  {
    assert (BTOR_IS_ARRAY_EXP (real_e1));
    return 0;
  }

  assert (!BTOR_IS_ARRAY_EXP (real_e1));

  if (e0 == BTOR_INVERT_EXP (e1)) return 1;

  if (BTOR_IS_CONST_EXP (real_e0) && BTOR_IS_CONST_EXP (real_e1) && e0 != e1)
    return 1;

  if (real_e0->kind == BTOR_ADD_EXP)
  {
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (real_e0->e[0]))
        && BTOR_COND_INVERT_EXP (e0, real_e0->e[1]) == e1)
      return 1;
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (real_e0->e[1]))
        && BTOR_COND_INVERT_EXP (e0, real_e0->e[0]) == e1)
      return 1;
  }

  if (real_e1->kind == BTOR_ADD_EXP)
  {
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (real_e1->e[0]))
        && BTOR_COND_INVERT_EXP (e1, real_e1->e[1]) == e0)
      return 1;
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (real_e1->e[1]))
        && BTOR_COND_INVERT_EXP (e1, real_e1->e[0]) == e0)
      return 1;
  }

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_BEQ_EXP, e0, e1);
    if (bits_3vl[0] == '0') result = 1;
    btor_delete_const (btor->mm, bits_3vl);
    return result;
  }

  return 0;
}

static void
normalize_binary_comm_ass_exp (Btor *btor,
                               BtorExp *e0,
                               BtorExp *e1,
                               BtorExp **e0_norm,
                               BtorExp **e1_norm,
                               BtorExp *(*fptr) (Btor *, BtorExp *, BtorExp *),
                               BtorExpKind kind)
{
  BtorMemMgr *mm;
  BtorExpPtrStack stack;
  BtorExp *cur, *result, *temp, *common;
  int i;
  BtorPtrHashTable *left, *right, *comm;
  BtorPtrHashBucket *b;
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e0_norm != NULL);
  assert (e1_norm != NULL);
  assert (fptr != NULL);
  assert (BTOR_IS_BINARY_EXP_KIND (kind));
  assert (!BTOR_IS_INVERTED_EXP (e0));
  assert (!BTOR_IS_INVERTED_EXP (e1));
  assert (e0->kind == kind);
  assert (e1->kind == kind);
  assert (btor->rewrite_level > 2);

  mm    = btor->mm;
  left  = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);
  right = btor_new_ptr_hash_table (mm,
                                   (BtorHashPtr) btor_hash_exp_by_id,
                                   (BtorCmpPtr) btor_compare_exp_by_id);
  comm  = btor_new_ptr_hash_table (mm,
                                  (BtorHashPtr) btor_hash_exp_by_id,
                                  (BtorCmpPtr) btor_compare_exp_by_id);

  BTOR_INIT_STACK (stack);
  BTOR_PUSH_STACK (mm, stack, e0);
  do
  {
    cur = BTOR_POP_STACK (stack);
    if (!BTOR_IS_INVERTED_EXP (cur) && cur->kind == kind)
    {
      BTOR_PUSH_STACK (mm, stack, cur->e[1]);
      BTOR_PUSH_STACK (mm, stack, cur->e[0]);
    }
    else
    {
      b = btor_find_in_ptr_hash_table (left, cur);
      if (b == NULL)
        btor_insert_in_ptr_hash_table (left, cur)->data.asInt = 1;
      else
        b->data.asInt++;
    }
  } while (!BTOR_EMPTY_STACK (stack));

  BTOR_PUSH_STACK (mm, stack, e1);
  do
  {
    cur = BTOR_POP_STACK (stack);
    if (!BTOR_IS_INVERTED_EXP (cur) && cur->kind == kind)
    {
      BTOR_PUSH_STACK (mm, stack, cur->e[1]);
      BTOR_PUSH_STACK (mm, stack, cur->e[0]);
    }
    else
    {
      b = btor_find_in_ptr_hash_table (left, cur);
      if (b != NULL)
      {
        /* we found one common operand */

        /* remove operand from left */
        if (b->data.asInt > 1)
          b->data.asInt--;
        else
        {
          assert (b->data.asInt == 1);
          btor_remove_from_ptr_hash_table (left, cur, NULL, NULL);
        }

        /* insert into common table */
        b = btor_find_in_ptr_hash_table (comm, cur);
        if (b == NULL)
          btor_insert_in_ptr_hash_table (comm, cur)->data.asInt = 1;
        else
          b->data.asInt++;
      }
      else
      {
        /* operand is not common */
        b = btor_find_in_ptr_hash_table (right, cur);
        if (b == NULL)
          btor_insert_in_ptr_hash_table (right, cur)->data.asInt = 1;
        else
          b->data.asInt++;
      }
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (mm, stack);

  /* no operand or only one operand in common? leave everything as it is */
  if (comm->count < 2u)
  {
    /* clean up */
    btor_delete_ptr_hash_table (left);
    btor_delete_ptr_hash_table (right);
    btor_delete_ptr_hash_table (comm);
    *e0_norm = btor_copy_exp (btor, e0);
    *e1_norm = btor_copy_exp (btor, e1);
    return;
  }

  if (kind == BTOR_ADD_EXP)
    btor->stats.adds_normalized++;
  else
  {
    assert (kind == BTOR_MUL_EXP);
    btor->stats.muls_normalized++;
  }

  assert (comm->count >= 2u);
  b      = comm->first;
  common = btor_copy_exp (btor, (BtorExp *) b->key);
  if (b->data.asInt > 0)
    b->data.asInt--;
  else
    b = b->next;
  while (b != NULL)
  {
    cur = b->key;
    for (i = 0; i < b->data.asInt; i++)
    {
      temp = fptr (btor, common, cur);
      btor_release_exp (btor, common);
      common = temp;
    }
    b = b->next;
  }

  /* normalize left side */
  result = btor_copy_exp (btor, common);
  for (b = left->first; b != NULL; b = b->next)
  {
    cur = b->key;
    for (i = 0; i < b->data.asInt; i++)
    {
      temp = fptr (btor, result, cur);
      btor_release_exp (btor, result);
      result = temp;
    }
  }
  *e0_norm = result;

  /* normalize right side */
  result = btor_copy_exp (btor, common);
  for (b = right->first; b != NULL; b = b->next)
  {
    cur = b->key;
    for (i = 0; i < b->data.asInt; i++)
    {
      temp = fptr (btor, result, cur);
      btor_release_exp (btor, result);
      result = temp;
    }
  }
  *e1_norm = result;

  /* clean up */
  btor_release_exp (btor, common);
  btor_delete_ptr_hash_table (left);
  btor_delete_ptr_hash_table (right);
  btor_delete_ptr_hash_table (comm);
}

static void
normalize_adds_exp (
    Btor *btor, BtorExp *e0, BtorExp *e1, BtorExp **e0_norm, BtorExp **e1_norm)
{
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e0_norm != NULL);
  assert (e1_norm != NULL);
  assert (!BTOR_IS_INVERTED_EXP (e0));
  assert (!BTOR_IS_INVERTED_EXP (e1));
  assert (e0->kind == BTOR_ADD_EXP);
  assert (e1->kind == BTOR_ADD_EXP);
  normalize_binary_comm_ass_exp (
      btor, e0, e1, e0_norm, e1_norm, btor_add_exp, BTOR_ADD_EXP);
}

static void
normalize_muls_exp (
    Btor *btor, BtorExp *e0, BtorExp *e1, BtorExp **e0_norm, BtorExp **e1_norm)
{
  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e0_norm != NULL);
  assert (e1_norm != NULL);
  assert (!BTOR_IS_INVERTED_EXP (e0));
  assert (!BTOR_IS_INVERTED_EXP (e1));
  assert (e0->kind == BTOR_MUL_EXP);
  assert (e1->kind == BTOR_MUL_EXP);
  normalize_binary_comm_ass_exp (
      btor, e0, e1, e0_norm, e1_norm, btor_mul_exp, BTOR_MUL_EXP);
}

static BtorExp *
and_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_AND_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_and_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *real_e0, *real_e1, *result, *e0_norm, *e1_norm, *temp;
  int normalized;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  real_e0    = BTOR_REAL_ADDR_EXP (e0);
  real_e1    = BTOR_REAL_ADDR_EXP (e1);
  normalized = 0;

  /* two level optimization [MEMICS] for BTOR_AND_EXP */
BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN:
  if (e0 == e1) /* x & x == x */
    return btor_copy_exp (btor, e0);
  if (BTOR_INVERT_EXP (e0) == e1) /* x & ~x == 0 */
    return btor_zero_exp (btor, real_e0->len);

  if (real_e0->kind == BTOR_AND_EXP && real_e1->kind == BTOR_AND_EXP)
  {
    if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1))
    {
      /* second rule of contradiction */
      if (real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[0])
          || real_e0->e[0] == BTOR_INVERT_EXP (real_e1->e[1])
          || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0])
          || real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
        return btor_zero_exp (btor, real_e0->len);
      /* symmetric rule of idempotency */
      if (real_e0->e[0] == real_e1->e[0] || real_e0->e[1] == real_e1->e[0])
      {
        e1      = real_e1->e[1];
        real_e1 = BTOR_REAL_ADDR_EXP (e1);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }
      /* use commutativity */
      if (real_e0->e[0] == real_e1->e[1] || real_e0->e[1] == real_e1->e[1])
      {
        e1      = real_e1->e[0];
        real_e1 = BTOR_REAL_ADDR_EXP (e1);
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
        return btor_copy_exp (btor, e0);
      /* symmetric rule of substitution */
      if ((real_e1->e[0] == real_e0->e[1]) || (real_e1->e[0] == real_e0->e[0]))
      {
        e1      = BTOR_INVERT_EXP (real_e1->e[1]);
        real_e1 = BTOR_REAL_ADDR_EXP (e1);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }
      /* symmetric rule of substitution */
      if ((real_e1->e[1] == real_e0->e[1]) || (real_e1->e[1] == real_e0->e[0]))
      {
        e1      = BTOR_INVERT_EXP (real_e1->e[0]);
        real_e1 = BTOR_REAL_ADDR_EXP (e1);
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
        return btor_copy_exp (btor, e1);
      /* symmetric rule of substitution */
      if ((real_e0->e[1] == real_e1->e[0]) || (real_e0->e[1] == real_e1->e[1]))
      {
        e0      = BTOR_INVERT_EXP (real_e0->e[0]);
        real_e0 = BTOR_REAL_ADDR_EXP (e0);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }
      /* symmetric rule of substitution */
      if ((real_e0->e[0] == real_e1->e[0]) || (real_e0->e[0] == real_e1->e[1]))
      {
        e0      = BTOR_INVERT_EXP (real_e0->e[1]);
        real_e0 = BTOR_REAL_ADDR_EXP (e0);
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
        return btor_eq_exp (btor,
                            BTOR_REAL_ADDR_EXP (real_e0->e[0]),
                            BTOR_REAL_ADDR_EXP (real_e0->e[1]));
      /* rule of resolution */
      if ((real_e0->e[0] == real_e1->e[0]
           && real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[1]))
          || (real_e0->e[0] == real_e1->e[1]
              && real_e0->e[1] == BTOR_INVERT_EXP (real_e1->e[0])))
        return BTOR_INVERT_EXP (btor_copy_exp (btor, real_e0->e[0]));
      /* rule of resolution */
      if ((real_e1->e[1] == real_e0->e[1]
           && real_e1->e[0] == BTOR_INVERT_EXP (real_e0->e[0]))
          || (real_e1->e[1] == real_e0->e[0]
              && real_e1->e[0] == BTOR_INVERT_EXP (real_e0->e[1])))
        return BTOR_INVERT_EXP (btor_copy_exp (btor, real_e1->e[1]));
    }
  }

  if (real_e0->kind == BTOR_AND_EXP)
  {
    if (BTOR_IS_INVERTED_EXP (e0))
    {
      /* first rule of subsumption */
      if (real_e0->e[0] == BTOR_INVERT_EXP (e1)
          || real_e0->e[1] == BTOR_INVERT_EXP (e1))
        return btor_copy_exp (btor, e1);

      /* asymmetric rule of substitution */
      if (real_e0->e[1] == e1)
      {
        e0      = BTOR_INVERT_EXP (real_e0->e[0]);
        real_e0 = BTOR_REAL_ADDR_EXP (e0);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }

      /* asymmetric rule of substitution */
      if (real_e0->e[0] == e1)
      {
        e0      = BTOR_INVERT_EXP (real_e0->e[1]);
        real_e0 = BTOR_REAL_ADDR_EXP (e0);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }
    }
    else
    {
      assert (!BTOR_IS_INVERTED_EXP (e0));

      /* first rule of contradiction */
      if (e0->e[0] == BTOR_INVERT_EXP (e1) || e0->e[1] == BTOR_INVERT_EXP (e1))
        return btor_zero_exp (btor, e0->len);

      /* asymmetric rule of idempotency */
      if (e0->e[0] == e1 || e0->e[1] == e1) return btor_copy_exp (btor, e0);

      if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1)))
      {
        /* recursion is no problem here, as one call leads to
         * folding of constants, and the other call can not
         * trigger the same kind of recursion anymore */

        if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0])))
        {
          assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1])));
          temp   = btor_and_exp (btor, e1, e0->e[0]);
          result = btor_and_exp (btor, temp, e0->e[1]);
          btor_release_exp (btor, temp);
          return result;
        }

        if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1])))
        {
          assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0])));
          temp   = btor_and_exp (btor, e1, e0->e[1]);
          result = btor_and_exp (btor, temp, e0->e[0]);
          btor_release_exp (btor, temp);
          return result;
        }
      }
    }
  }

  if (real_e1->kind == BTOR_AND_EXP)
  {
    if (BTOR_IS_INVERTED_EXP (e1))
    {
      /* first rule of subsumption */
      if (real_e1->e[0] == BTOR_INVERT_EXP (e0)
          || real_e1->e[1] == BTOR_INVERT_EXP (e0))
        return btor_copy_exp (btor, e0);
      /* asymmetric rule of substitution */
      if (real_e1->e[0] == e0)
      {
        e1      = BTOR_INVERT_EXP (real_e1->e[1]);
        real_e1 = BTOR_REAL_ADDR_EXP (e1);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }
      /* asymmetric rule of substitution */
      if (real_e1->e[1] == e0)
      {
        e1      = BTOR_INVERT_EXP (real_e1->e[0]);
        real_e1 = BTOR_REAL_ADDR_EXP (e1);
        goto BTOR_EXP_TWO_LEVEL_OPT_TRY_AGAIN;
      }
    }
    else
    {
      assert (!BTOR_IS_INVERTED_EXP (e1));

      /* first rule of contradiction */
      if (e1->e[0] == BTOR_INVERT_EXP (e0) || e1->e[1] == BTOR_INVERT_EXP (e0))
        return btor_zero_exp (btor, real_e0->len);

      /* asymmetric rule of idempotency */
      if (e1->e[0] == e0 || e1->e[1] == e0) return btor_copy_exp (btor, e1);

      if (BTOR_IS_CONST_EXP (real_e0))
      {
        /* recursion is no problem here, as one call leads to
         * folding of constants, and the other call can not
         * trigger the same kind of recursion anymore */

        if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0])))
        {
          assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1])));
          temp   = btor_and_exp (btor, e0, e1->e[0]);
          result = btor_and_exp (btor, temp, e1->e[1]);
          btor_release_exp (btor, temp);
          return result;
        }

        if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1])))
        {
          assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0])));
          temp   = btor_and_exp (btor, e0, e1->e[1]);
          result = btor_and_exp (btor, temp, e1->e[0]);
          btor_release_exp (btor, temp);
          return result;
        }
      }
    }
  }

  if (real_e0->kind == BTOR_ULT_EXP && real_e1->kind == BTOR_ULT_EXP)
  {
    /* a < b && b < a simplifies to FALSE */
    if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1)
        && e0->e[0] == e1->e[1] && e0->e[1] == e1->e[0])
      return btor_false_exp (btor);
    /* NOT (a < b) && NOT (b < a) simplifies to a == b */
    if (BTOR_IS_INVERTED_EXP (e0) && BTOR_IS_INVERTED_EXP (e1)
        && real_e0->e[0] == real_e1->e[1] && real_e0->e[1] == real_e1->e[0])
      return btor_eq_exp (btor,
                          BTOR_REAL_ADDR_EXP (real_e0->e[0]),
                          BTOR_REAL_ADDR_EXP (real_e0->e[1]));
  }

  if (btor->rewrite_level > 2 && !BTOR_IS_INVERTED_EXP (e0)
      && !BTOR_IS_INVERTED_EXP (e1) && e0->kind == e1->kind)
  {
    if (e0->kind == BTOR_ADD_EXP)
    {
      assert (e1->kind == BTOR_ADD_EXP);
      normalize_adds_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
    else if (e0->kind == BTOR_MUL_EXP)
    {
      assert (e1->kind == BTOR_MUL_EXP);
      normalize_muls_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_AND_EXP, e0, e1);

  if (result == NULL) result = and_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_AND_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  result = rewrite_and_exp (btor, e0, e1);
  assert (result != NULL);

  return result;
}

static BtorExp *
eq_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)))
      bits_3vl = btor_x_const_3vl (mm, 1);
    else
      bits_3vl = compute_binary_3vl (btor, BTOR_BEQ_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_eq_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_eq_exp_bounded (Btor *btor, BtorExp *e0, BtorExp *e1, int *calls)
{
  BtorExp *left, *right, *e0_0, *e0_1, *e1_0, *e1_1, *result, *eq;
  BtorExp *e0_norm, *e1_norm, *real_e0, *real_e1;
  int normalized, upper, lower;
  BtorExpKind kind;

  assert (btor_precond_eq_exp_dbg (btor, e0, e1));
  assert (calls != NULL);
  assert (*calls >= 0);

  real_e0    = BTOR_REAL_ADDR_EXP (e0);
  real_e1    = BTOR_REAL_ADDR_EXP (e1);
  normalized = 0;

  if (BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)))
    kind = BTOR_AEQ_EXP;
  else
    kind = BTOR_BEQ_EXP;

  /* write (a, i, e1) = write (a, i, e2) ----> e1 = e2 */
  if (kind == BTOR_AEQ_EXP && BTOR_IS_WRITE_EXP (e0) && BTOR_IS_WRITE_EXP (e1)
      && e0->e[0] == e1->e[0] && e0->e[1] == e1->e[1])
  {
    e0   = e0->e[2];
    e1   = e1->e[2];
    kind = BTOR_BEQ_EXP;
  }

  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (BTOR_IS_INVERTED_EXP (e0) && BTOR_IS_INVERTED_EXP (e1))
  {
    e0 = BTOR_REAL_ADDR_EXP (e0);
    e1 = BTOR_REAL_ADDR_EXP (e1);
  }

  /* we do not rewrite eq in the boolean case, as we
   * cannot extract the resulting XNOR on top level again and
   * would therefore lose substitutions
   * additionally, we do not rewrite eq in the boolean case, as
   * we rewrite a != b to a = ~b and substitute.
   * */

  if (e0 == e1) return btor_true_exp (btor);

  if (is_always_unequal (btor, e0, e1)) return btor_false_exp (btor);

  if (btor->rewrite_level > 2)
  {
    if (!BTOR_IS_INVERTED_EXP (e0))
    {
      /* a + b = a ----> b = 0,
       * this rule does not lead to less substitutions. 'a' cannot
       * be substituted as the occurrence check would fail */
      if (e0->kind == BTOR_ADD_EXP)
      {
        if (e0->e[0] == e1)
        {
          *calls += 1;
          left   = btor_zero_exp (btor, e0->len);
          result = rewrite_eq_exp_bounded (btor, left, e0->e[1], calls);
          btor_release_exp (btor, left);
          return result;
        }

        if (e0->e[1] == e1)
        {
          *calls += 1;
          left   = btor_zero_exp (btor, e0->len);
          result = rewrite_eq_exp_bounded (btor, left, e0->e[0], calls);
          btor_release_exp (btor, left);
          return result;
        }
      }

      /* b ? a : t = d  ---a != d-->  !b AND d = t */
      if (e0->kind == BTOR_BCOND_EXP)
      {
        if (is_always_unequal (btor, e0->e[1], e1))
        {
          *calls += 1;
          eq     = rewrite_eq_exp_bounded (btor, e0->e[2], e1, calls);
          result = btor_and_exp (btor, BTOR_INVERT_EXP (e0->e[0]), eq);
          btor_release_exp (btor, eq);
          return result;
        }

        if (is_always_unequal (btor, e0->e[2], e1))
        {
          *calls += 1;
          eq     = rewrite_eq_exp_bounded (btor, e0->e[1], e1, calls);
          result = btor_and_exp (btor, e0->e[0], eq);
          btor_release_exp (btor, eq);
          return result;
        }
      }
    }

    if (!BTOR_IS_INVERTED_EXP (e1))
    {
      /* a = a + b  ----> b = 0,
       * this rule does not lead to less substitutions. 'a' cannot
       * be substituted as the occurrence check would fail */
      if (e1->kind == BTOR_ADD_EXP)
      {
        if (e1->e[0] == e0)
        {
          *calls += 1;
          left   = btor_zero_exp (btor, e1->len);
          result = rewrite_eq_exp_bounded (btor, left, e1->e[1], calls);
          btor_release_exp (btor, left);
          return result;
        }

        if (e1->e[1] == e0)
        {
          *calls += 1;
          left   = btor_zero_exp (btor, e1->len);
          result = rewrite_eq_exp_bounded (btor, left, e1->e[0], calls);
          btor_release_exp (btor, left);
          return result;
        }
      }

      /* d = b ? a : t  ---a != d-->  !b AND d = t */
      if (e1->kind == BTOR_BCOND_EXP)
      {
        if (is_always_unequal (btor, e1->e[1], e0))
        {
          *calls += 1;
          eq     = rewrite_eq_exp_bounded (btor, e1->e[2], e0, calls);
          result = btor_and_exp (btor, BTOR_INVERT_EXP (e1->e[0]), eq);
          btor_release_exp (btor, eq);
          return result;
        }

        if (is_always_unequal (btor, e1->e[2], e0))
        {
          *calls += 1;
          eq     = rewrite_eq_exp_bounded (btor, e1->e[1], e0, calls);
          result = btor_and_exp (btor, e1->e[0], eq);
          btor_release_exp (btor, eq);
          return result;
        }
      }
    }

    if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1))
    {
      /* a + b = a + c ---> b = c */
      if (e0->kind == BTOR_ADD_EXP && e1->kind == BTOR_ADD_EXP)
      {
        if (e0->e[0] == e1->e[0])
        {
          *calls += 1;
          return rewrite_eq_exp_bounded (btor, e0->e[1], e1->e[1], calls);
        }

        if (e0->e[0] == e1->e[1])
        {
          *calls += 1;
          return rewrite_eq_exp_bounded (btor, e0->e[1], e1->e[0], calls);
        }

        if (e0->e[1] == e1->e[0])
        {
          *calls += 1;
          return rewrite_eq_exp_bounded (btor, e0->e[0], e1->e[1], calls);
        }

        if (e0->e[1] == e1->e[1])
        {
          *calls += 1;
          return rewrite_eq_exp_bounded (btor, e0->e[0], e1->e[0], calls);
        }
      }
    }

    /* a = b ? a : c is rewritten to  b OR a = c
     * a = ~(b ? a : c) is rewritten to  !b AND a = ~c
     */
    if (BTOR_IS_ARRAY_OR_BV_COND_EXP (real_e0) && *calls < BTOR_EQ_EXP_RW_BOUND)
    {
      if (real_e0->e[1] == e1)
      {
        *calls += 1;
        if (BTOR_IS_INVERTED_EXP (e0))
        {
          eq = rewrite_eq_exp_bounded (
              btor, BTOR_INVERT_EXP (real_e0->e[2]), e1, calls);
          result = btor_and_exp (btor, BTOR_INVERT_EXP (real_e0->e[0]), eq);
        }
        else
        {
          eq     = rewrite_eq_exp_bounded (btor, real_e0->e[2], e1, calls);
          result = btor_or_exp (btor, real_e0->e[0], eq);
        }
        btor_release_exp (btor, eq);
        return result;
      }

      if (real_e0->e[2] == e1)
      {
        *calls += 1;
        if (BTOR_IS_INVERTED_EXP (e0))
        {
          eq = rewrite_eq_exp_bounded (
              btor, BTOR_INVERT_EXP (real_e0->e[1]), e1, calls);
          result = btor_and_exp (btor, real_e0->e[0], eq);
        }
        else
        {
          eq     = rewrite_eq_exp_bounded (btor, real_e0->e[1], e1, calls);
          result = btor_or_exp (btor, BTOR_INVERT_EXP (real_e0->e[0]), eq);
        }
        btor_release_exp (btor, eq);
        return result;
      }
    }

    if (BTOR_IS_ARRAY_OR_BV_COND_EXP (real_e1) && *calls < BTOR_EQ_EXP_RW_BOUND)
    {
      if (real_e1->e[1] == e0)
      {
        *calls += 1;
        if (BTOR_IS_INVERTED_EXP (e1))
        {
          eq = rewrite_eq_exp_bounded (
              btor, BTOR_INVERT_EXP (real_e1->e[2]), e0, calls);
          result = btor_and_exp (btor, BTOR_INVERT_EXP (real_e1->e[0]), eq);
        }
        else
        {
          eq     = rewrite_eq_exp_bounded (btor, real_e1->e[2], e0, calls);
          result = btor_or_exp (btor, real_e1->e[0], eq);
        }
        btor_release_exp (btor, eq);
        return result;
      }

      if (real_e1->e[2] == e0)
      {
        *calls += 1;
        if (BTOR_IS_INVERTED_EXP (e1))
        {
          eq = rewrite_eq_exp_bounded (
              btor, BTOR_INVERT_EXP (real_e1->e[1]), e0, calls);
          result = btor_and_exp (btor, real_e1->e[0], eq);
        }
        else
        {
          eq     = rewrite_eq_exp_bounded (btor, real_e1->e[1], e0, calls);
          result = btor_or_exp (btor, BTOR_INVERT_EXP (real_e1->e[0]), eq);
        }
        btor_release_exp (btor, eq);
        return result;
      }
    }

    /* normalize adds and muls on demand */
    if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1)
        && (e0->kind == BTOR_ADD_EXP || e0->kind == BTOR_MUL_EXP)
        && e0->kind == e1->kind)

    {
      if (e0->kind == BTOR_ADD_EXP)
      {
        assert (e1->kind == BTOR_ADD_EXP);
        normalize_adds_exp (btor, e0, e1, &e0_norm, &e1_norm);
        normalized = 1;
        e0         = e0_norm;
        e1         = e1_norm;
      }
      else
      {
        assert (e0->kind == BTOR_MUL_EXP);
        assert (e1->kind == BTOR_MUL_EXP);
        normalize_muls_exp (btor, e0, e1, &e0_norm, &e1_norm);
        normalized = 1;
        e0         = e0_norm;
        e1         = e1_norm;
      }
    }
    else if (kind == BTOR_BEQ_EXP && *calls < BTOR_EQ_EXP_RW_BOUND)
    {
      /* push eq down over concats */
      if ((real_e0->kind == BTOR_CONCAT_EXP && real_e1->kind == BTOR_CONCAT_EXP
           && BTOR_REAL_ADDR_EXP (real_e0->e[0])->len
                  == BTOR_REAL_ADDR_EXP (real_e1->e[0])->len)
          || (real_e0->kind == BTOR_CONCAT_EXP && BTOR_IS_CONST_EXP (real_e1))
          || (real_e1->kind == BTOR_CONCAT_EXP && BTOR_IS_CONST_EXP (real_e0)))
      {
        *calls += 1;
        assert (real_e0->kind == BTOR_CONCAT_EXP
                || real_e1->kind == BTOR_CONCAT_EXP);

        upper = real_e0->len - 1;
        if (real_e0->kind == BTOR_CONCAT_EXP)
          lower = upper - BTOR_REAL_ADDR_EXP (real_e0->e[0])->len + 1;
        else
          lower = upper - BTOR_REAL_ADDR_EXP (real_e1->e[0])->len + 1;

        e0_0 = btor_slice_exp (btor, e0, upper, lower);
        e1_0 = btor_slice_exp (btor, e1, upper, lower);
        lower--;
        e0_1   = btor_slice_exp (btor, e0, lower, 0);
        e1_1   = btor_slice_exp (btor, e1, lower, 0);
        left   = rewrite_eq_exp_bounded (btor, e0_0, e1_0, calls);
        right  = rewrite_eq_exp_bounded (btor, e0_1, e1_1, calls);
        result = btor_and_exp (btor, left, right);

        btor_release_exp (btor, left);
        btor_release_exp (btor, right);
        btor_release_exp (btor, e0_0);
        btor_release_exp (btor, e0_1);
        btor_release_exp (btor, e1_0);
        btor_release_exp (btor, e1_1);
        return result;
      }
    }
  }

  result = rewrite_binary_exp (btor, kind, e0, e1);
  if (result == NULL) result = eq_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;
  int calls;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    if (!BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e0)))
    {
      bits_3vl = compute_binary_3vl (btor, BTOR_BEQ_EXP, e0, e1);
      if (btor_is_const_2vl (mm, bits_3vl))
      {
        result = btor_const_exp (btor, bits_3vl);
        btor_delete_const (mm, bits_3vl);
        btor->stats.simplifications_3vl++;
        return result;
      }
      btor_delete_const (mm, bits_3vl);
    }
  }

  calls  = 0;
  result = rewrite_eq_exp_bounded (btor, e0, e1, &calls);
  assert (result != NULL);

  return result;
}

static BtorExp *
add_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_ADD_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_add_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *e0_norm, *e1_norm, *temp;
  int normalized;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  normalized = 0;

  /* boolean case */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1) return btor_xor_exp (btor, e0, e1);

  /* a - a == 0 */
  if (!BTOR_IS_INVERTED_EXP (e1) && e1->kind == BTOR_ADD_EXP
      && e0 == BTOR_INVERT_EXP (e1->e[0]) && is_const_one_exp (btor, e1->e[1]))
    return btor_zero_exp (btor, e1->len);

  if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0)) && !BTOR_IS_INVERTED_EXP (e1)
      && e1->kind == BTOR_ADD_EXP)
  {
    /* recursion is no problem here, as one call leads to
     * folding of constants, and the other call can not
     * trigger the same kind of recursion anymore */

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1])));
      temp   = btor_add_exp (btor, e0, e1->e[0]);
      result = btor_add_exp (btor, temp, e1->e[1]);
      btor_release_exp (btor, temp);
      return result;
    }

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0])));
      temp   = btor_add_exp (btor, e0, e1->e[1]);
      result = btor_add_exp (btor, temp, e1->e[0]);
      btor_release_exp (btor, temp);
      return result;
    }
  }

  else if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1))
           && !BTOR_IS_INVERTED_EXP (e0) && e0->kind == BTOR_ADD_EXP)
  {
    /* recursion is no problem here, as one call leads to
     * folding of constants, and the other call can not
     * trigger the same kind of recursion anymore */

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1])));
      temp   = btor_add_exp (btor, e1, e0->e[0]);
      result = btor_add_exp (btor, temp, e0->e[1]);
      btor_release_exp (btor, temp);
      return result;
    }

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0])));
      temp   = btor_add_exp (btor, e1, e0->e[1]);
      result = btor_add_exp (btor, temp, e0->e[0]);
      btor_release_exp (btor, temp);
      return result;
    }
  }

  if (btor->rewrite_level > 2 && !BTOR_IS_INVERTED_EXP (e0)
      && !BTOR_IS_INVERTED_EXP (e1) && e0->kind == BTOR_MUL_EXP
      && e1->kind == BTOR_MUL_EXP)
  {
    /* normalize muls on demand */
    normalize_muls_exp (btor, e0, e1, &e0_norm, &e1_norm);
    normalized = 1;
    e0         = e0_norm;
    e1         = e1_norm;
  }

  result = rewrite_binary_exp (btor, BTOR_ADD_EXP, e0, e1);
  if (result == NULL) result = add_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_ADD_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  result = rewrite_add_exp (btor, e0, e1);
  assert (result != NULL);

  return result;
}

static BtorExp *
mul_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_MUL_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_mul_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_mul_exp_bounded (Btor *btor, BtorExp *e0, BtorExp *e1, int *calls)
{
  BtorExp *result, *e0_norm, *e1_norm, *left, *right;
  int normalized;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (calls != NULL);
  assert (*calls >= 0);

  normalized = 0;

  /* we do not need the optimization for term * power_of_2_constant as
   * the AIG level does this optimization already */

  /* boolean case */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1) return btor_and_exp (btor, e0, e1);

  if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0)) && !BTOR_IS_INVERTED_EXP (e1)
      && e1->kind == BTOR_MUL_EXP && *calls < BTOR_MUL_EXP_RW_BOUND)
  {
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1])));
      left   = rewrite_mul_exp_bounded (btor, e0, e1->e[0], calls);
      result = rewrite_mul_exp_bounded (btor, left, e1->e[1], calls);
      btor_release_exp (btor, left);
      return result;
    }

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0])));
      left   = rewrite_mul_exp_bounded (btor, e0, e1->e[1], calls);
      result = rewrite_mul_exp_bounded (btor, left, e1->e[0], calls);
      btor_release_exp (btor, left);
      return result;
    }
  }

  else if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1))
           && !BTOR_IS_INVERTED_EXP (e0) && e0->kind == BTOR_MUL_EXP
           && *calls < BTOR_MUL_EXP_RW_BOUND)

  {
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1])));
      left   = rewrite_mul_exp_bounded (btor, e1, e0->e[0], calls);
      result = rewrite_mul_exp_bounded (btor, left, e0->e[1], calls);
      btor_release_exp (btor, left);
      return result;
    }

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1])))
    {
      assert (!BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0])));
      left   = rewrite_mul_exp_bounded (btor, e1, e0->e[1], calls);
      result = rewrite_mul_exp_bounded (btor, left, e0->e[0], calls);
      btor_release_exp (btor, left);
      return result;
    }
  }

  /* const * (t + const) =recursively= const * t + const * const */
  if (btor->rewrite_level > 2 && *calls < BTOR_MUL_EXP_RW_BOUND)
  {
    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0)) && BTOR_IS_REGULAR_EXP (e1)
        && e1->kind == BTOR_ADD_EXP
        && (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[0]))
            || BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1->e[1]))))
    {
      *calls += 1;
      left   = rewrite_mul_exp_bounded (btor, e0, e1->e[0], calls);
      right  = rewrite_mul_exp_bounded (btor, e0, e1->e[1], calls);
      result = btor_add_exp (btor, left, right);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
      return result;
    }

    if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1)) && BTOR_IS_REGULAR_EXP (e0)
        && e0->kind == BTOR_ADD_EXP
        && (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[0]))
            || BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e0->e[1]))))
    {
      *calls += 1;
      left   = rewrite_mul_exp_bounded (btor, e1, e0->e[0], calls);
      right  = rewrite_mul_exp_bounded (btor, e1, e0->e[1], calls);
      result = btor_add_exp (btor, left, right);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
      return result;
    }

    if (!BTOR_IS_INVERTED_EXP (e0) && !BTOR_IS_INVERTED_EXP (e1)
        && e0->kind == BTOR_ADD_EXP && e1->kind == BTOR_ADD_EXP)
    {
      /* normalize adds on demand */
      normalize_adds_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_MUL_EXP, e0, e1);
  if (result == NULL) result = mul_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;
  int calls;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_MUL_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  calls  = 0;
  result = rewrite_mul_exp_bounded (btor, e0, e1, &calls);
  assert (result != NULL);

  return result;
}

static BtorExp *
ult_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_ULT_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_ult_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *e0_norm, *e1_norm, *temp;
  int normalized;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  normalized = 0;

  if (BTOR_IS_INVERTED_EXP (e0) && BTOR_IS_INVERTED_EXP (e1))
  {
    /* ~a < ~b  is the same as  b < a */
    temp = BTOR_REAL_ADDR_EXP (e1);
    e1   = BTOR_REAL_ADDR_EXP (e0);
    e0   = temp;
  }

  /* boolean case */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1)
    return btor_and_exp (btor, BTOR_INVERT_EXP (e0), e1);

  if (btor->rewrite_level > 2 && !BTOR_IS_INVERTED_EXP (e0)
      && !BTOR_IS_INVERTED_EXP (e1) && e0->kind == e1->kind)
  {
    if (e0->kind == BTOR_ADD_EXP)
    {
      assert (e1->kind == BTOR_ADD_EXP);
      normalize_adds_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
    else if (e0->kind == BTOR_MUL_EXP)
    {
      assert (e1->kind == BTOR_MUL_EXP);
      normalize_muls_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_ULT_EXP, e0, e1);
  if (result == NULL) result = ult_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_ULT_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  result = rewrite_ult_exp (btor, e0, e1);
  assert (result != NULL);

  return result;
}

BtorExp *
btor_rewrite_sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_SLL_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_SLL_EXP, e0, e1);
  if (result == NULL) result = btor_sll_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

BtorExp *
btor_rewrite_srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_SRL_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_SRL_EXP, e0, e1);
  if (result == NULL) result = btor_srl_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
udiv_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_UDIV_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_udiv_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *e0_norm, *e1_norm;
  int normalized;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  normalized = 0;
  /* we do not need the optimization for term / power_of_2_constant as
   * the AIG level does this optimization already */

  /* boolean case */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1)
    return BTOR_INVERT_EXP (btor_and_exp (btor, BTOR_INVERT_EXP (e0), e1));

  /* normalize adds and muls on demand */
  if (btor->rewrite_level > 2 && !BTOR_IS_INVERTED_EXP (e0)
      && !BTOR_IS_INVERTED_EXP (e1) && e0->kind == e1->kind)
  {
    if (e0->kind == BTOR_ADD_EXP)
    {
      assert (e1->kind == BTOR_ADD_EXP);
      normalize_adds_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
    else if (e0->kind == BTOR_MUL_EXP)
    {
      assert (e1->kind == BTOR_MUL_EXP);
      normalize_muls_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_UDIV_EXP, e0, e1);
  if (result == NULL) result = udiv_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_UDIV_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  result = rewrite_udiv_exp (btor, e0, e1);
  assert (result != NULL);

  return result;
}

static BtorExp *
urem_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_UREM_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_urem_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1)
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
rewrite_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *e0_norm, *e1_norm;
  int normalized;

  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  normalized = 0;

  /* we do not need the optimization for term % power_of_2_constant as
   * the AIG level does this optimization already */

  /* boolean case */
  if (BTOR_REAL_ADDR_EXP (e0)->len == 1)
    return btor_and_exp (btor, e0, BTOR_INVERT_EXP (e1));

  /* normalize adds and muls on demand */
  if (btor->rewrite_level > 2 && !BTOR_IS_INVERTED_EXP (e0)
      && !BTOR_IS_INVERTED_EXP (e1) && e0->kind == e1->kind)
  {
    if (e0->kind == BTOR_ADD_EXP)
    {
      assert (e1->kind == BTOR_ADD_EXP);
      normalize_adds_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
    else if (e0->kind == BTOR_MUL_EXP)
    {
      assert (e1->kind == BTOR_MUL_EXP);
      normalize_muls_exp (btor, e0, e1, &e0_norm, &e1_norm);
      normalized = 1;
      e0         = e0_norm;
      e1         = e1_norm;
    }
  }

  result = rewrite_binary_exp (btor, BTOR_UREM_EXP, e0, e1);
  if (result == NULL) result = urem_exp_node_3vl (btor, e0, e1);

  if (normalized)
  {
    btor_release_exp (btor, e0_norm);
    btor_release_exp (btor, e1_norm);
  }

  return result;
}

BtorExp *
btor_rewrite_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_UREM_EXP, e0, e1);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  result = rewrite_urem_exp (btor, e0, e1);
  assert (result != NULL);

  return result;
}

BtorExp *
btor_rewrite_concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1)
{
  BtorExp *result, *temp, *cur;
  BtorExpPtrStack stack, po_stack;
  BtorMemMgr *mm;
  int i;
  char *bits_3vl = NULL;

  e0 = btor_pointer_chase_simplified_exp (btor, e0);
  e1 = btor_pointer_chase_simplified_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));
  assert (btor->rewrite_level > 0);

  if (BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (e1))
      && BTOR_REAL_ADDR_EXP (e0)->kind == BTOR_CONCAT_EXP
      && BTOR_IS_CONST_EXP (BTOR_REAL_ADDR_EXP (BTOR_REAL_ADDR_EXP (e0)->e[1])))
  {
    /* recursion is no problem here, as one call leads to
     * folding of constants, and the other call can not
     * trigger the same kind of recursion anymore */

    if (!BTOR_IS_INVERTED_EXP (e0))
    {
      temp   = btor_concat_exp (btor, e0->e[1], e1);
      result = btor_concat_exp (btor, e0->e[0], temp);
      btor_release_exp (btor, temp);
    }
    else
    {
      temp = btor_concat_exp (
          btor, BTOR_INVERT_EXP (BTOR_REAL_ADDR_EXP (e0)->e[1]), e1);
      result = btor_concat_exp (
          btor, BTOR_INVERT_EXP (BTOR_REAL_ADDR_EXP (e0)->e[0]), temp);
      btor_release_exp (btor, temp);
    }
    return result;
  }

  /* normalize concats --> left-associative */
  if (btor->rewrite_level > 2
      && BTOR_REAL_ADDR_EXP (e1)->kind == BTOR_CONCAT_EXP)
  {
    mm = btor->mm;

    BTOR_INIT_STACK (po_stack);
    BTOR_PUSH_STACK (mm, po_stack, e0);

    BTOR_INIT_STACK (stack);
    BTOR_PUSH_STACK (mm, stack, e1);
    do
    {
      cur = BTOR_POP_STACK (stack);
      if (BTOR_REAL_ADDR_EXP (cur)->kind == BTOR_CONCAT_EXP)
      {
        BTOR_PUSH_STACK (
            mm,
            stack,
            BTOR_COND_INVERT_EXP (cur, BTOR_REAL_ADDR_EXP (cur)->e[1]));
        BTOR_PUSH_STACK (
            mm,
            stack,
            BTOR_COND_INVERT_EXP (cur, BTOR_REAL_ADDR_EXP (cur)->e[0]));
      }
      else
        BTOR_PUSH_STACK (mm, po_stack, cur);
    } while (!BTOR_EMPTY_STACK (stack));

    assert (BTOR_COUNT_STACK (po_stack) >= 3);
    result =
        btor_rewrite_concat_exp (btor, po_stack.start[0], po_stack.start[1]);
    for (i = 2; i < BTOR_COUNT_STACK (po_stack); i++)
    {
      cur = po_stack.start[i];
      assert (BTOR_REAL_ADDR_EXP (cur)->kind != BTOR_CONCAT_EXP);
      temp = btor_rewrite_concat_exp (btor, result, cur);
      btor_release_exp (btor, result);
      result = temp;
    }

    BTOR_RELEASE_STACK (mm, stack);
    BTOR_RELEASE_STACK (mm, po_stack);

    return result;
  }

  result = rewrite_binary_exp (btor, BTOR_CONCAT_EXP, e0, e1);
  if (result == NULL) result = btor_concat_exp_node (btor, e0, e1);

  if (btor->rewrite_level > 1 && result->bits == NULL)
  {
    bits_3vl = compute_binary_3vl (btor, BTOR_CONCAT_EXP, e0, e1);
    if (btor_is_const_2vl (btor->mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (btor->mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    result->bits = bits_3vl;
  }

  return result;
}

BtorExp *
btor_rewrite_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index)
{
  BtorExp *result, *cur_array, *write_index;
  int propagations;
  BtorMemMgr *mm;

  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  assert (btor_precond_read_exp_dbg (btor, e_array, e_index));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (BTOR_IS_WRITE_EXP (e_array))
  {
    write_index = e_array->e[1];
    /* if read index is equal write index, then return write value */
    if (e_index == write_index) return btor_copy_exp (btor, e_array->e[2]);

    cur_array = e_array;
    assert (BTOR_IS_REGULAR_EXP (cur_array));
    assert (BTOR_IS_ARRAY_EXP (cur_array));
    propagations = 0;

    do
    {
      assert (BTOR_IS_WRITE_EXP (cur_array));
      write_index = cur_array->e[1];

      if (e_index == write_index) return btor_copy_exp (btor, cur_array->e[2]);

      if (is_always_unequal (btor, e_index, write_index))
      {
        cur_array = cur_array->e[0];
        assert (BTOR_IS_REGULAR_EXP (cur_array));
        assert (BTOR_IS_ARRAY_EXP (cur_array));
        propagations++;
        btor->stats.read_props_construct++;
      }
      else
        break;

    } while (BTOR_IS_WRITE_EXP (cur_array)
             && propagations < BTOR_READ_OVER_WRITE_DOWN_PROPAGATION_LIMIT);

    result = btor_read_exp_node (btor, cur_array, e_index);
  }
  else
    result = btor_read_exp_node (btor, e_array, e_index);
  assert (result != NULL);

  /* currently we do not know anything about 3vl bits of reads */
  if (result->bits == NULL) result->bits = btor_x_const_3vl (mm, e_array->len);

  return result;
}

BtorExp *
btor_rewrite_write_exp (Btor *btor,
                        BtorExp *e_array,
                        BtorExp *e_index,
                        BtorExp *e_value)
{
  BtorExp *cur, *cur_write, *temp, *result;
  BtorExp *chain[BTOR_WRITE_CHAIN_EXP_RW_BOUND];
  int depth;

  e_array = btor_pointer_chase_simplified_exp (btor, e_array);
  e_index = btor_pointer_chase_simplified_exp (btor, e_index);
  e_value = btor_pointer_chase_simplified_exp (btor, e_value);
  assert (btor_precond_write_exp_dbg (btor, e_array, e_index, e_value));
  assert (btor->rewrite_level > 0);

  result = NULL;

  if (btor->rewrite_level > 2 && BTOR_IS_WRITE_EXP (e_array))
  {
    depth = 0;
    cur   = e_array;
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_WRITE_EXP (cur));

    while (BTOR_IS_WRITE_EXP (cur) && cur->e[1] != e_index
           && depth < BTOR_WRITE_CHAIN_EXP_RW_BOUND)
    {
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (BTOR_IS_WRITE_EXP (cur));
      chain[depth++] = cur;
      cur            = cur->e[0];
      assert (BTOR_IS_REGULAR_EXP (cur));
      assert (BTOR_IS_ARRAY_EXP (cur));
    }

    if (depth < BTOR_WRITE_CHAIN_EXP_RW_BOUND && BTOR_IS_WRITE_EXP (cur))
    {
      assert (cur->e[1] == e_index);
      /* we overwrite this position anyhow, so we can skip
       * this intermediate write */
      cur = btor_copy_exp (btor, cur->e[0]);
      depth--;
      while (depth >= 0)
      {
        cur_write = chain[depth--];
        assert (BTOR_IS_REGULAR_EXP (cur_write));
        assert (BTOR_IS_WRITE_EXP (cur_write));
        temp =
            btor_write_exp_node (btor, cur, cur_write->e[1], cur_write->e[2]);
        btor_release_exp (btor, cur);
        cur = temp;
      }

      result = btor_write_exp_node (btor, cur, e_index, e_value);
      btor_release_exp (btor, cur);
    }
  }

  if (result == NULL)
    result = btor_write_exp_node (btor, e_array, e_index, e_value);

  return result;
}

static char *
compute_bcond_3vl (Btor *btor, BtorExp *e0, BtorExp *e1, BtorExp *e2)
{
  int invert_e0, invert_e1, invert_e2;
  char *b0, *b1, *b2, *result;
  int same_children_mem;
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (BTOR_REAL_ADDR_EXP (e0)->len == 1);
  assert (BTOR_REAL_ADDR_EXP (e1)->len == BTOR_REAL_ADDR_EXP (e2)->len);
  assert (BTOR_REAL_ADDR_EXP (e1)->len > 0);
  assert (BTOR_REAL_ADDR_EXP (e0)->bits != NULL);
  assert (BTOR_REAL_ADDR_EXP (e1)->bits != NULL);
  assert (BTOR_REAL_ADDR_EXP (e2)->bits != NULL);
  assert (btor->rewrite_level > 1);

  mm                = btor->mm;
  b0                = BTOR_REAL_ADDR_EXP (e0)->bits;
  b1                = BTOR_REAL_ADDR_EXP (e1)->bits;
  b2                = BTOR_REAL_ADDR_EXP (e2)->bits;
  same_children_mem = b0 == b1 || b0 == b2 || b1 == b2;
  invert_e0         = 0;
  invert_e1         = 0;
  invert_e2         = 0;

  if (same_children_mem)
  {
    if (BTOR_IS_INVERTED_EXP (e0))
      b0 = btor_not_const_3vl (mm, b0);
    else
      b0 = btor_copy_const (mm, b0);

    if (BTOR_IS_INVERTED_EXP (e1))
      b1 = btor_not_const_3vl (mm, b1);
    else
      b1 = btor_copy_const (mm, b1);

    if (BTOR_IS_INVERTED_EXP (e2))
      b2 = btor_not_const_3vl (mm, b2);
    else
      b2 = btor_copy_const (mm, b2);
  }
  else
  {
    if (BTOR_IS_INVERTED_EXP (e0))
    {
      invert_e0 = 1;
      btor_invert_const_3vl (mm, b0);
    }

    if (BTOR_IS_INVERTED_EXP (e1))
    {
      invert_e1 = 1;
      btor_invert_const_3vl (mm, b1);
    }

    if (BTOR_IS_INVERTED_EXP (e2))
    {
      invert_e2 = 1;
      btor_invert_const_3vl (mm, b2);
    }
  }

  result = btor_cond_const_3vl (mm, b0, b1, b2);

  if (same_children_mem)
  {
    btor_delete_const (mm, b0);
    btor_delete_const (mm, b1);
    btor_delete_const (mm, b2);
  }
  else
  {
    if (invert_e0) btor_invert_const_3vl (mm, b0);
    if (invert_e1) btor_invert_const_3vl (mm, b1);
    if (invert_e2) btor_invert_const_3vl (mm, b2);
  }

  return result;
}

static BtorExp *
cond_exp_node_3vl (Btor *btor, BtorExp *e0, BtorExp *e1, BtorExp *e2)
{
  BtorExp *result;
  char *bits_3vl = NULL;
  BtorMemMgr *mm;

  assert (btor_precond_cond_exp_dbg (btor, e0, e1, e2));

  mm = btor->mm;

  if (btor->rewrite_level > 1 && !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)))
  {
    bits_3vl = compute_bcond_3vl (btor, e0, e1, e2);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
  }

  result = btor_cond_exp_node (btor, e0, e1, e2);

  if (btor->rewrite_level > 1 && !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e1)))
  {
    if (result->bits == NULL)
      result->bits = bits_3vl;
    else
      btor_delete_const (mm, bits_3vl);
  }

  return result;
}

static BtorExp *
ternary_cond_exp_bounded (Btor *btor,
                          BtorExpKind kind,
                          BtorExp *e0,
                          BtorExp *e1,
                          BtorExp *e2,
                          int *calls)
{
  BtorExp *result, *left, *right, *cond, *uext, *and, *econd0, *econd1, *econd2;
  BtorExp *(*fptr) (Btor *, BtorExp *, BtorExp *);
  BtorMemMgr *mm;

  assert (btor != NULL);
  assert (btor->rewrite_level > 0);
  assert (BTOR_IS_TERNARY_EXP_KIND (kind));
  assert (kind == BTOR_BCOND_EXP || kind == BTOR_ACOND_EXP);
  assert (e0 != NULL);
  assert (e1 != NULL);
  assert (e2 != NULL);
  assert (calls != NULL);
  assert (*calls >= 0);

  result = NULL;
  mm     = btor->mm;

  if (e1 == e2) return btor_copy_exp (btor, e1);

  if (BTOR_IS_CONST_EXP (e0))
  {
    /* condtionals are normalized if rewrite level > 0 */
    assert (!BTOR_IS_INVERTED_EXP (e0));
    if (e0->bits[0] == '1')
      result = btor_copy_exp (btor, e1);
    else
      result = btor_copy_exp (btor, e2);
    return result;
  }

  if (BTOR_IS_ARRAY_OR_BV_COND_EXP (BTOR_REAL_ADDR_EXP (e1))
      && *calls < BTOR_COND_EXP_RW_BOUND)

  {
    econd0 = BTOR_REAL_ADDR_EXP (e1)->e[0];

    if (BTOR_IS_INVERTED_EXP (e1))
    {
      econd1 = BTOR_INVERT_EXP (BTOR_REAL_ADDR_EXP (e1)->e[1]);
      econd2 = BTOR_INVERT_EXP (BTOR_REAL_ADDR_EXP (e1)->e[2]);
    }
    else
    {
      econd1 = e1->e[1];
      econd2 = e1->e[2];
    }

    if (econd1 == e2)
    {
      *calls += 1;
      and    = btor_and_exp (btor, e0, BTOR_INVERT_EXP (econd0));
      result = rewrite_cond_exp_bounded (btor, and, econd2, e2, calls);
      btor_release_exp (btor, and);
      return result;
    }

    if (econd2 == e2)
    {
      *calls += 1;
      and    = btor_and_exp (btor, e0, econd0);
      result = rewrite_cond_exp_bounded (btor, and, econd1, e2, calls);
      btor_release_exp (btor, and);
      return result;
    }
  }

  if (BTOR_IS_ARRAY_OR_BV_COND_EXP (BTOR_REAL_ADDR_EXP (e2))
      && *calls < BTOR_COND_EXP_RW_BOUND)
  {
    econd0 = BTOR_REAL_ADDR_EXP (e2)->e[0];

    if (BTOR_IS_INVERTED_EXP (e2))
    {
      econd1 = BTOR_INVERT_EXP (BTOR_REAL_ADDR_EXP (e2)->e[1]);
      econd2 = BTOR_INVERT_EXP (BTOR_REAL_ADDR_EXP (e2)->e[2]);
    }
    else
    {
      econd1 = e2->e[1];
      econd2 = e2->e[2];
    }

    if (econd1 == e1)
    {
      *calls += 1;
      and = btor_and_exp (btor, BTOR_INVERT_EXP (e0), BTOR_INVERT_EXP (econd0));
      result = rewrite_cond_exp_bounded (btor, and, econd2, e1, calls);
      btor_release_exp (btor, and);
      return result;
    }

    if (econd2 == e1)
    {
      *calls += 1;
      and    = btor_and_exp (btor, BTOR_INVERT_EXP (e0), econd0);
      result = rewrite_cond_exp_bounded (btor, and, econd1, e1, calls);
      btor_release_exp (btor, and);
      return result;
    }
  }

  if (kind == BTOR_BCOND_EXP)
  {
    if (BTOR_REAL_ADDR_EXP (e1)->len == 1)
    {
      left   = btor_or_exp (btor, BTOR_INVERT_EXP (e0), e1);
      right  = btor_or_exp (btor, e0, e2);
      result = btor_and_exp (btor, left, right);
      btor_release_exp (btor, left);
      btor_release_exp (btor, right);
      return result;
    }

    if (!BTOR_IS_INVERTED_EXP (e1) && e1->kind == BTOR_ADD_EXP
        && ((e1->e[0] == e2 && is_const_one_exp (btor, e1->e[1]))
            || (e1->e[1] == e2 && is_const_one_exp (btor, e1->e[0]))))
    {
      uext   = btor_uext_exp (btor, e0, BTOR_REAL_ADDR_EXP (e1)->len - 1);
      result = btor_add_exp (btor, e2, uext);
      btor_release_exp (btor, uext);
      return result;
    }

    if (!BTOR_IS_INVERTED_EXP (e2) && e2->kind == BTOR_ADD_EXP
        && ((e2->e[0] == e1 && is_const_one_exp (btor, e2->e[1]))
            || (e2->e[1] == e1 && is_const_one_exp (btor, e2->e[0]))))
    {
      uext = btor_uext_exp (
          btor, BTOR_INVERT_EXP (e0), BTOR_REAL_ADDR_EXP (e1)->len - 1);
      result = btor_add_exp (btor, e1, uext);
      btor_release_exp (btor, uext);
      return result;
    }

    if (btor->rewrite_level > 2 && !BTOR_IS_INVERTED_EXP (e1)
        && !BTOR_IS_INVERTED_EXP (e2) && e1->kind == e2->kind
        && *calls < BTOR_COND_EXP_RW_BOUND)
    {
      fptr = NULL;
      switch (e1->kind)
      {
        case BTOR_ADD_EXP: fptr = btor_add_exp; break;
        case BTOR_AND_EXP: fptr = btor_and_exp; break;
        case BTOR_MUL_EXP: fptr = btor_mul_exp; break;
        case BTOR_UDIV_EXP: fptr = btor_udiv_exp; break;
        case BTOR_UREM_EXP: fptr = btor_urem_exp; break;
        default: break;
      }

      if (fptr != NULL)
      {
        if (e1->e[0] == e2->e[0])
        {
          *calls += 1;
          cond = rewrite_cond_exp_bounded (btor, e0, e1->e[1], e2->e[1], calls);
          result = fptr (btor, e1->e[0], cond);
          btor_release_exp (btor, cond);
          return result;
        }

        if (e1->e[1] == e2->e[1])
        {
          *calls += 1;
          cond = rewrite_cond_exp_bounded (btor, e0, e1->e[0], e2->e[0], calls);
          result = fptr (btor, cond, e1->e[1]);
          btor_release_exp (btor, cond);
          return result;
        }

        if (fptr != btor_udiv_exp && fptr != btor_urem_exp)
        {
          /* works only for commutative operators: */
          if (e1->e[0] == e2->e[1])
          {
            *calls += 1;
            cond =
                rewrite_cond_exp_bounded (btor, e0, e1->e[1], e2->e[0], calls);
            result = fptr (btor, e1->e[0], cond);
            btor_release_exp (btor, cond);
            return result;
          }

          if (e1->e[1] == e2->e[0])
          {
            *calls += 1;
            cond =
                rewrite_cond_exp_bounded (btor, e0, e1->e[0], e2->e[1], calls);
            result = fptr (btor, e1->e[1], cond);
            btor_release_exp (btor, cond);
            return result;
          }
        }
      }
    }
  }
  return result;
}

static BtorExp *
rewrite_cond_exp_bounded (
    Btor *btor, BtorExp *e_cond, BtorExp *e_if, BtorExp *e_else, int *calls)
{
  BtorExp *result, *temp;
  BtorExpKind kind;

  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));
  assert (calls != NULL);
  assert (*calls >= 0);

  /* normalization: ~e0 ? e1 : e2 is the same as e0 ? e2: e1 */
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

  result = ternary_cond_exp_bounded (btor, kind, e_cond, e_if, e_else, calls);
  if (result == NULL) result = cond_exp_node_3vl (btor, e_cond, e_if, e_else);

  assert (result != NULL);
  return result;
}

BtorExp *
btor_rewrite_cond_exp (Btor *btor,
                       BtorExp *e_cond,
                       BtorExp *e_if,
                       BtorExp *e_else)
{
  BtorExp *result;
  BtorMemMgr *mm;
  char *bits_3vl = NULL;
  int calls;

  e_cond = btor_pointer_chase_simplified_exp (btor, e_cond);
  e_if   = btor_pointer_chase_simplified_exp (btor, e_if);
  e_else = btor_pointer_chase_simplified_exp (btor, e_else);
  assert (btor_precond_cond_exp_dbg (btor, e_cond, e_if, e_else));
  assert (btor->rewrite_level > 0);

  mm = btor->mm;

  if (btor->rewrite_level > 1 && !BTOR_IS_ARRAY_EXP (BTOR_REAL_ADDR_EXP (e_if)))
  {
    bits_3vl = compute_bcond_3vl (btor, e_cond, e_if, e_else);
    if (btor_is_const_2vl (mm, bits_3vl))
    {
      result = btor_const_exp (btor, bits_3vl);
      btor_delete_const (mm, bits_3vl);
      btor->stats.simplifications_3vl++;
      return result;
    }
    btor_delete_const (mm, bits_3vl);
  }

  calls  = 0;
  result = rewrite_cond_exp_bounded (btor, e_cond, e_if, e_else, &calls);
  assert (result != NULL);

  return result;
}
