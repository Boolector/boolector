/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorrewrite.h"
#include "btorbeta.h"
#include "btorconst.h"
#include "btorlog.h"
#include "utils/btoriter.h"
#include "utils/btormem.h"
#include "utils/btormisc.h"
#include "utils/btorutil.h"

#include <assert.h>

// TODO: mul: power of 2 optimizations

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

/* recursive rewriting bound */
#define BTOR_REC_RW_BOUND (1 << 12)

/* iterative rewriting bounds */
#define BTOR_WRITE_CHAIN_NODE_RW_BOUND (1 << 5)
#define BTOR_READ_OVER_WRITE_DOWN_PROPAGATION_LIMIT (1 << 11)
#define BTOR_APPLY_PROPAGATION_LIMIT (1 << 13)

/* other rewriting bounds */
#define BTOR_FIND_AND_NODE_CONTRADICTION_LIMIT (1 << 4)

#define BTOR_INC_REC_RW_CALL(btor)                             \
  do                                                           \
  {                                                            \
    (btor)->rec_rw_calls++;                                    \
    if ((btor)->rec_rw_calls > (btor)->stats.max_rec_rw_calls) \
      (btor)->stats.max_rec_rw_calls = (btor)->rec_rw_calls;   \
  } while (0)

#define BTOR_DEC_REC_RW_CALL(btor)     \
  do                                   \
  {                                    \
    assert ((btor)->rec_rw_calls > 0); \
    (btor)->rec_rw_calls--;            \
  } while (0)

// TODO: special_const_binary rewriting may return 0, hence the check if
//       (result), may be obsolete if special_const_binary will be split
#define ADD_RW_RULE(rw_rule, ...)                 \
  if (applies_##rw_rule (btor, __VA_ARGS__))      \
  {                                               \
    assert (!result);                             \
    result = apply_##rw_rule (btor, __VA_ARGS__); \
    if (result) goto DONE;                        \
  }
//      fprintf (stderr, "apply: %s (%s)\n", #rw_rule, __FUNCTION__);

/* -------------------------------------------------------------------------- */
/* util functions */

static int
is_const_one_exp (Btor *btor, BtorNode *exp)
{
  char *bits;
  int result;
  BtorNode *real_exp;

  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);

  if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp))) return 0;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  bits     = btor_const_get_bits (real_exp);
  if (BTOR_IS_INVERTED_NODE (exp)) btor_invert_const (btor->mm, bits);
  result = btor_is_special_const (bits) == BTOR_SPECIAL_CONST_ONE;
  if (BTOR_IS_INVERTED_NODE (exp)) btor_invert_const (btor->mm, bits);

  return result;
}

static int
is_const_zero_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int result;

  exp = btor_simplify_exp (btor, exp);

  if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp))) return 0;

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_is_ones_const (btor_const_get_bits (exp));
  else
    result = btor_is_zero_const (btor_const_get_bits (exp));

  return result;
}

#if 0
static int
is_const_ones_exp (Btor * btor, BtorNode * exp)
{
  assert (btor);
  assert (exp);

  int result;

  exp = btor_simplify_exp (btor, exp);

  if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp)))
    return 0;

  if (BTOR_IS_INVERTED_NODE (exp))
    result = btor_is_zero_const (btor_const_get_bits (exp));
  else
    result = btor_is_ones_const (btor_const_get_bits (exp));

  return result;
}
#endif

static int
is_const_zero_or_ones_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  int result;

  exp = btor_simplify_exp (btor, exp);

  if (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp))) return 0;

  result = btor_is_zero_or_ones_const (btor_const_get_bits (exp));

  return result;
}

static int
is_odd_const_exp (BtorNode *exp)
{
  char *bits;

  if (BTOR_IS_INVERTED_NODE (exp)) return 0;

  if (exp->kind != BTOR_BV_CONST_NODE) return 0;

  bits = btor_const_get_bits (exp);
  return bits[btor_get_exp_width (exp->btor, exp) - 1] == '1';
}

static int
is_xor_exp (Btor *btor, BtorNode *exp)
{
  BtorNode *e0, *e1, *e0_0, *e0_1, *e1_0, *e1_1;

  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  (void) btor;

  if (BTOR_REAL_ADDR_NODE (exp)->kind != BTOR_AND_NODE) return 0;

  e0 = BTOR_REAL_ADDR_NODE (exp)->e[0];
  if (!(BTOR_IS_INVERTED_NODE (e0)
        && BTOR_REAL_ADDR_NODE (e0)->kind == BTOR_AND_NODE))
    return 0;

  e1 = BTOR_REAL_ADDR_NODE (exp)->e[1];
  if (!(BTOR_IS_INVERTED_NODE (e1)
        && BTOR_REAL_ADDR_NODE (e1)->kind == BTOR_AND_NODE))
    return 0;

  e0_0 = BTOR_REAL_ADDR_NODE (e0)->e[0];
  e0_1 = BTOR_REAL_ADDR_NODE (e0)->e[1];
  e1_0 = BTOR_REAL_ADDR_NODE (e1)->e[0];
  e1_1 = BTOR_REAL_ADDR_NODE (e1)->e[1];

  /* we assume that the children of commutative operators are sorted by id */
  /* are children of e0 the same children as of e1 (ignoring sign) ? */
  /* if not we terminate with false */
  if (BTOR_REAL_ADDR_NODE (e0_0) != BTOR_REAL_ADDR_NODE (e1_0)) return 0;
  if (BTOR_REAL_ADDR_NODE (e0_1) != BTOR_REAL_ADDR_NODE (e1_1)) return 0;

  /* we check for two cases */
  /* first case: !(!a && !b) && !(a && b) */
  if (!BTOR_IS_INVERTED_NODE (exp))
  {
    if (BTOR_IS_INVERTED_NODE (e0_0) == BTOR_IS_INVERTED_NODE (e0_1)
        && BTOR_IS_INVERTED_NODE (e1_0) == BTOR_IS_INVERTED_NODE (e1_1)
        && BTOR_IS_INVERTED_NODE (e0_0) != BTOR_IS_INVERTED_NODE (e1_0))
      return 1;
  }
  /* second case: !((!a && b) && !(a && !b)) */
  else
  {
    if (BTOR_IS_INVERTED_NODE (e0_0) != BTOR_IS_INVERTED_NODE (e1_0)
        && BTOR_IS_INVERTED_NODE (e0_1) != BTOR_IS_INVERTED_NODE (e1_1)
        && BTOR_IS_INVERTED_NODE (e0_0) != BTOR_IS_INVERTED_NODE (e0_1))
      return 1;
  }
  return 0;
}

static int
is_xnor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  return is_xor_exp (btor, BTOR_INVERT_NODE (exp));
}

static int
slice_simplifiable (BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  return BTOR_IS_BV_VAR_NODE (exp) || BTOR_IS_BV_CONST_NODE (exp)
         || BTOR_IS_SLICE_NODE (exp);
}

static int
is_always_unequal (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor);
  assert (e0);
  assert (e1);
  /* we need this so that a + 0 is rewritten to a,
   * and constants are normalized (all inverted constants are odd) */
  assert (btor->options.rewrite_level.val > 0);

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  if (!real_e0 || !real_e1) return 0;

  if (BTOR_IS_FUN_NODE (real_e0))
  {
    assert (BTOR_IS_FUN_NODE (real_e1));
    return 0;
  }

  assert (!BTOR_IS_FUN_NODE (real_e1));

  if (e0 == BTOR_INVERT_NODE (e1)) return 1;

  if (BTOR_IS_BV_CONST_NODE (real_e0) && BTOR_IS_BV_CONST_NODE (real_e1)
      && e0 != e1)
    return 1;

  if (real_e0->kind == BTOR_ADD_NODE)
  {
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e0->e[0]))
        && !is_const_zero_exp (btor, real_e0->e[0])
        && BTOR_COND_INVERT_NODE (e0, real_e0->e[1]) == e1)
      return 1;
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e0->e[1]))
        && !is_const_zero_exp (btor, real_e0->e[1])
        && BTOR_COND_INVERT_NODE (e0, real_e0->e[0]) == e1)
      return 1;
  }

  if (real_e1->kind == BTOR_ADD_NODE)
  {
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e1->e[0]))
        && !is_const_zero_exp (btor, real_e1->e[0])
        && BTOR_COND_INVERT_NODE (e1, real_e1->e[1]) == e0)
      return 1;
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e1->e[1]))
        && !is_const_zero_exp (btor, real_e1->e[1])
        && BTOR_COND_INVERT_NODE (e1, real_e1->e[0]) == e0)
      return 1;
  }

  return 0;
}

static int
cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return BTOR_REAL_ADDR_NODE (a)->id - BTOR_REAL_ADDR_NODE (b)->id;
}

static int
find_and_contradiction_exp (
    Btor *btor, BtorNode *exp, BtorNode *e0, BtorNode *e1, int *calls)
{
  assert (btor);
  assert (exp);
  assert (e0);
  assert (e1);
  assert (calls);
  assert (*calls >= 0);
  (void) btor;

  if (*calls >= BTOR_FIND_AND_NODE_CONTRADICTION_LIMIT) return 0;

  if (!BTOR_IS_INVERTED_NODE (exp) && exp->kind == BTOR_AND_NODE)
  {
    if (exp->e[0] == BTOR_INVERT_NODE (e0) || exp->e[0] == BTOR_INVERT_NODE (e1)
        || exp->e[1] == BTOR_INVERT_NODE (e0)
        || exp->e[1] == BTOR_INVERT_NODE (e1))
      return 1;
    *calls += 1;
    return find_and_contradiction_exp (btor, exp->e[0], e0, e1, calls)
           || find_and_contradiction_exp (btor, exp->e[1], e0, e1, calls);
  }
  return 0;
}

static int
concat_simplifiable (BtorNode *exp)
{
  exp = BTOR_REAL_ADDR_NODE (exp);
  return BTOR_IS_BV_VAR_NODE (exp) || BTOR_IS_BV_CONST_NODE (exp);
}

static int
is_write_exp (BtorNode *exp,
              BtorNode **array,
              BtorNode **index,
              BtorNode **value)
{
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  BtorNode *param, *body, *eq, *app;

  if (!BTOR_IS_LAMBDA_NODE (exp) || btor_get_fun_arity (exp->btor, exp) > 1)
    return 0;

  param = (BtorNode *) BTOR_LAMBDA_GET_PARAM (exp);
  body  = BTOR_LAMBDA_GET_BODY (exp);

  if (BTOR_IS_INVERTED_NODE (body) || !BTOR_IS_BV_COND_NODE (body)) return 0;

  /* check condition */
  eq = body->e[0];
  if (BTOR_IS_INVERTED_NODE (eq) || !BTOR_IS_BV_EQ_NODE (eq)
      || !eq->parameterized || (eq->e[0] != param && eq->e[1] != param))
    return 0;

  /* check value */
  if (BTOR_REAL_ADDR_NODE (body->e[1])->parameterized) return 0;

  /* check apply on unmodified array */
  app = body->e[2];
  if (BTOR_IS_INVERTED_NODE (app) || !BTOR_IS_APPLY_NODE (app)
      || btor_get_args_arity (app->btor, app->e[1]) > 1
      || app->e[1]->e[0] != param)
    return 0;

  if (array) *array = app->e[0];
  if (index) *index = eq->e[1] == param ? eq->e[0] : eq->e[1];
  if (value) *value = body->e[1];
  return 1;
}

static int
is_true_cond (BtorNode *cond)
{
  assert (cond);
  assert (btor_get_exp_width (BTOR_REAL_ADDR_NODE (cond)->btor, cond) == 1);

  if (BTOR_IS_INVERTED_NODE (cond) && btor_const_get_bits (cond)[0] == '0')
    return 1;
  else if (!BTOR_IS_INVERTED_NODE (cond)
           && btor_const_get_bits (cond)[0] == '1')
    return 1;

  return 0;
}

static int
is_bit_mask (BtorNode *exp, int *upper, int *lower)
{
  char bit, *bits;
  int i, len, inv, first = -1, last = -1;
  BtorNode *real_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);

  *upper = 0;
  *lower = 0;

  if (!BTOR_IS_BV_CONST_NODE (real_exp)) return 0;

  bits = btor_const_get_bits (real_exp);
  inv  = BTOR_IS_INVERTED_NODE (exp);
  len  = btor_get_exp_width (real_exp->btor, real_exp);
  for (i = 0; i < len; i++)
  {
    bit = bits[i];
    if (inv) bit = bit == '1' ? '0' : '1';

    if (bit == '1' && first == -1)
      first = i;
    else if (bit == '0' && first > -1 && last == -1)
      last = i - 1;

    if (bit == '1' && last > -1) return 0;
  }
  if (last == -1) last = len - 1;

  *upper = len - first - 1;
  *lower = len - last - 1;
  return 1;
}

/* -------------------------------------------------------------------------- */

static BtorNode *rewrite_slice_exp (Btor *, BtorNode *, uint32_t, uint32_t);
static BtorNode *rewrite_eq_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_ult_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_and_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_add_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_mul_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_udiv_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_urem_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_concat_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_sll_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_srl_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_apply_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_lambda_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_cond_exp (Btor *, BtorNode *, BtorNode *, BtorNode *);

/* -------------------------------------------------------------------------- */
/* const term rewriting */

/* match:  binary op with two constants
 * result: constant
 */
static inline int
applies_const_binary_exp (Btor *btor,
                          BtorNodeKind kind,
                          BtorNode *e0,
                          BtorNode *e1)
{
  (void) btor;
  (void) kind;
  return BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1));
}

static inline BtorNode *
apply_const_binary_exp (Btor *btor,
                        BtorNodeKind kind,
                        BtorNode *e0,
                        BtorNode *e1)
{
  assert (applies_const_binary_exp (btor, kind, e0, e1));

  int same_mem, invert_b0 = 0, invert_b1 = 0;
  char *b0, *b1, *bresult;
  BtorMemMgr *mm;
  BtorNode *result, *real_e0, *real_e1;

  mm      = btor->mm;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  same_mem = real_e0 == real_e1;
  if (same_mem)
  {
    b0 = BTOR_BITS_NODE (mm, e0);
    b1 = BTOR_BITS_NODE (mm, e1);
  }
  else
  {
    invert_b0 = BTOR_IS_INVERTED_NODE (e0);
    b0        = btor_const_get_bits (real_e0);
    if (invert_b0) btor_invert_const (mm, b0);
    invert_b1 = BTOR_IS_INVERTED_NODE (e1);
    b1        = btor_const_get_bits (real_e1);
    if (invert_b1) btor_invert_const (mm, b1);
  }
  switch (kind)
  {
    case BTOR_AND_NODE: bresult = btor_and_const (mm, b0, b1); break;
    case BTOR_BEQ_NODE: bresult = btor_eq_const (mm, b0, b1); break;
    case BTOR_ADD_NODE: bresult = btor_add_const (mm, b0, b1); break;
    case BTOR_MUL_NODE: bresult = btor_mul_const (mm, b0, b1); break;
    case BTOR_ULT_NODE: bresult = btor_ult_const (mm, b0, b1); break;
    case BTOR_UDIV_NODE: bresult = btor_udiv_const (mm, b0, b1); break;
    case BTOR_UREM_NODE: bresult = btor_urem_const (mm, b0, b1); break;
    case BTOR_SLL_NODE: bresult = btor_sll_const (mm, b0, b1); break;
    case BTOR_SRL_NODE: bresult = btor_srl_const (mm, b0, b1); break;
    default:
      assert (kind == BTOR_CONCAT_NODE);
      bresult = btor_concat_const (mm, b0, b1);
      break;
  }
  if (same_mem)
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
  return result;
}

/* match:  binary op with one constant
 * result: constant
 */
static inline int
applies_special_const_lhs_binary_exp (Btor *btor,
                                      BtorNodeKind kind,
                                      BtorNode *e0,
                                      BtorNode *e1)
{
  (void) btor;
  (void) kind;
  return BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1));
}

static inline BtorNode *
apply_special_const_lhs_binary_exp (Btor *btor,
                                    BtorNodeKind kind,
                                    BtorNode *e0,
                                    BtorNode *e1)
{
  assert (applies_special_const_lhs_binary_exp (btor, kind, e0, e1));

  char *b0, *bv_const;
  char tmpString[2] = {'\0', '\0'};
  int invert_b0, pos, len, width_e0;
  BtorMemMgr *mm;
  BtorSpecialConst sc;
  BtorNode *result = 0, *real_e0, *real_e1, *left, *right, *tmp1, *tmp2, *tmp3;
  BtorNode *tmp4, *eq;
  BtorNodePtrStack stack;

  mm        = btor->mm;
  real_e0   = BTOR_REAL_ADDR_NODE (e0);
  real_e1   = BTOR_REAL_ADDR_NODE (e1);
  invert_b0 = BTOR_IS_INVERTED_NODE (e0);
  b0        = btor_const_get_bits (real_e0);
  width_e0  = btor_get_exp_width (btor, real_e0);

  if (invert_b0) btor_invert_const (mm, b0);

  sc = btor_is_special_const (b0);

  /* invert back if necessary */
  if (invert_b0) btor_invert_const (mm, b0);

  switch (sc)
  {
    case BTOR_SPECIAL_CONST_ZERO:
      switch (kind)
      {
        case BTOR_BEQ_NODE:
          if (width_e0 == 1)
            result = btor_not_exp (btor, e1);
          else if (is_xor_exp (btor, e1)) /* 0 == (a ^ b)  -->  a = b */
          {
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              result = rewrite_eq_exp (
                  btor,
                  BTOR_REAL_ADDR_NODE (
                      BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e1)->e[0])
                          ->e[0]),
                  BTOR_REAL_ADDR_NODE (
                      BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e1)->e[0])
                          ->e[1]));
              BTOR_DEC_REC_RW_CALL (btor);
            }
          }
          else if (BTOR_IS_INVERTED_NODE (e1) && real_e1->kind == BTOR_AND_NODE)
          { /* 0 == a | b  -->  a == 0 && b == 0 */
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              left =
                  rewrite_eq_exp (btor, BTOR_INVERT_NODE (real_e1->e[0]), e0);
              right =
                  rewrite_eq_exp (btor, BTOR_INVERT_NODE (real_e1->e[1]), e0);
              result = rewrite_and_exp (btor, left, right);
              BTOR_DEC_REC_RW_CALL (btor);
              btor_release_exp (btor, left);
              btor_release_exp (btor, right);
            }
          }
          break;
        case BTOR_ULT_NODE: /* 0 < a --> a != 0 */
          result = BTOR_INVERT_NODE (rewrite_eq_exp (btor, e0, e1));
          break;
        case BTOR_ADD_NODE: result = btor_copy_exp (btor, e1); break;
        case BTOR_MUL_NODE:
        case BTOR_SLL_NODE:
        case BTOR_SRL_NODE:
        case BTOR_UREM_NODE:
        case BTOR_AND_NODE: result = btor_zero_exp (btor, width_e0); break;
        case BTOR_UDIV_NODE:
          tmp2   = btor_zero_exp (btor, width_e0);
          tmp4   = btor_ones_exp (btor, width_e0);
          eq     = rewrite_eq_exp (btor, e1, tmp2);
          result = rewrite_cond_exp (btor, eq, tmp4, tmp2);
          btor_release_exp (btor, tmp2);
          btor_release_exp (btor, eq);
          btor_release_exp (btor, tmp4);
          break;
        default: break;
      }
      break;
    case BTOR_SPECIAL_CONST_ONE_ONES:
      assert (width_e0 == 1);
      if (kind == BTOR_AND_NODE || kind == BTOR_BEQ_NODE
          || kind == BTOR_MUL_NODE)
        result = btor_copy_exp (btor, e1);
      else if (kind == BTOR_ULT_NODE)
        result = btor_false_exp (btor);
      break;
    case BTOR_SPECIAL_CONST_ONE:
      if (kind == BTOR_MUL_NODE) result = btor_copy_exp (btor, e1);
      break;
    case BTOR_SPECIAL_CONST_ONES:
      if (kind == BTOR_BEQ_NODE)
      {
        if (is_xnor_exp (btor, e1)) /* 1+ == (a XNOR b)  -->  a = b */
        {
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            result = rewrite_eq_exp (
                btor,
                BTOR_REAL_ADDR_NODE (
                    BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e1)->e[0])->e[0]),
                BTOR_REAL_ADDR_NODE (
                    BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e1)->e[0])
                        ->e[1]));
            BTOR_DEC_REC_RW_CALL (btor);
          }
        }
        else if (!BTOR_IS_INVERTED_NODE (e1) && e1->kind == BTOR_AND_NODE)
        { /* 1+ == a & b  -->  a == 1+ && b == 1+ */
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            left   = rewrite_eq_exp (btor, e1->e[0], e0);
            right  = rewrite_eq_exp (btor, e1->e[1], e0);
            result = rewrite_and_exp (btor, left, right);
            BTOR_DEC_REC_RW_CALL (btor);
            btor_release_exp (btor, left);
            btor_release_exp (btor, right);
          }
        }
      }
      else if (kind == BTOR_AND_NODE)
        result = btor_copy_exp (btor, e1);
      else if (kind == BTOR_ULT_NODE) /* UNSIGNED_MAX < x */
        result = btor_false_exp (btor);
      break;
    default:
      assert (sc == BTOR_SPECIAL_CONST_NONE);
      if (kind == BTOR_BEQ_NODE && real_e1->kind == BTOR_AND_NODE
          && btor->rec_rw_calls < BTOR_REC_RW_BOUND)
      {
        BTOR_INC_REC_RW_CALL (btor);
        BTOR_INIT_STACK (stack);
        if (BTOR_IS_INVERTED_NODE (e0))
          bv_const = btor_not_const (btor->mm, btor_const_get_bits (real_e0));
        else
          bv_const = btor_copy_const (btor->mm, btor_const_get_bits (real_e0));

        pos = 0;
        /* const == a | b */
        if (BTOR_IS_INVERTED_NODE (e1))
        {
          while (pos < width_e0)
          {
            tmpString[0] = bv_const[pos];
            len          = (int) strspn (bv_const + pos, tmpString);
            tmp1         = rewrite_slice_exp (btor,
                                      BTOR_INVERT_NODE (real_e1->e[0]),
                                      width_e0 - 1 - pos,
                                      width_e0 - pos - len);
            tmp2         = rewrite_slice_exp (btor,
                                      BTOR_INVERT_NODE (real_e1->e[1]),
                                      width_e0 - 1 - pos,
                                      width_e0 - pos - len);
            if (tmpString[0] == '0')
            {
              tmp3 = btor_zero_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_release_exp (btor, tmp3);
            }
            else
            {
              assert (tmpString[0] == '1');
              tmp3 = btor_or_exp (btor, tmp1, tmp2);
              tmp4 = btor_ones_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_release_exp (btor, tmp3);
              btor_release_exp (btor, tmp4);
            }
            btor_release_exp (btor, tmp1);
            btor_release_exp (btor, tmp2);
            pos += len;
          }
        }
        else
        {
          assert (!BTOR_IS_INVERTED_NODE (e1));
          /* const == a & b */
          while (pos < width_e0)
          {
            tmpString[0] = bv_const[pos];
            len          = (int) strspn (bv_const + pos, tmpString);
            tmp1         = rewrite_slice_exp (
                btor, e1->e[0], width_e0 - 1 - pos, width_e0 - pos - len);
            tmp2 = rewrite_slice_exp (
                btor, e1->e[1], width_e0 - 1 - pos, width_e0 - pos - len);
            if (tmpString[0] == '1')
            {
              tmp3 = btor_ones_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_release_exp (btor, tmp3);
            }
            else
            {
              assert (tmpString[0] == '0');
              tmp3 = rewrite_and_exp (btor, tmp1, tmp2);
              tmp4 = btor_zero_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_release_exp (btor, tmp3);
              btor_release_exp (btor, tmp4);
            }
            btor_release_exp (btor, tmp1);
            btor_release_exp (btor, tmp2);
            pos += len;
          }
        }

        result = btor_true_exp (btor);
        assert (!BTOR_EMPTY_STACK (stack));
        do
        {
          tmp1 = BTOR_POP_STACK (stack);
          tmp2 = rewrite_and_exp (btor, result, tmp1);
          btor_release_exp (btor, result);
          result = tmp2;
          btor_release_exp (btor, tmp1);
        } while (!BTOR_EMPTY_STACK (stack));
        btor_delete_const (btor->mm, bv_const);
        BTOR_RELEASE_STACK (btor->mm, stack);
        BTOR_DEC_REC_RW_CALL (btor);
      }
      break;
  }

  return result;
}

/* match:  binary op with one constant
 * result: constant
 */
static inline int
applies_special_const_rhs_binary_exp (Btor *btor,
                                      BtorNodeKind kind,
                                      BtorNode *e0,
                                      BtorNode *e1)
{
  (void) btor;
  (void) kind;
  return !BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1));
}

static inline BtorNode *
apply_special_const_rhs_binary_exp (Btor *btor,
                                    BtorNodeKind kind,
                                    BtorNode *e0,
                                    BtorNode *e1)
{
  assert (applies_special_const_rhs_binary_exp (btor, kind, e0, e1));

  char *b1, *bv_const;
  char tmpString[2] = {'\0', '\0'};
  int invert_b1, pos, len, width_e0, width_e1;
  BtorMemMgr *mm;
  BtorSpecialConst sc;
  BtorNode *result = 0, *real_e0, *real_e1, *left, *right, *tmp1, *tmp2, *tmp3;
  BtorNode *tmp4;
  BtorNodePtrStack stack;

  mm        = btor->mm;
  real_e0   = BTOR_REAL_ADDR_NODE (e0);
  real_e1   = BTOR_REAL_ADDR_NODE (e1);
  invert_b1 = BTOR_IS_INVERTED_NODE (e1);
  b1        = btor_const_get_bits (real_e1);
  width_e0  = btor_get_exp_width (btor, real_e0);
  width_e1  = btor_get_exp_width (btor, real_e1);
  if (invert_b1) btor_invert_const (mm, b1);
  sc = btor_is_special_const (b1);
  /* invert back if necessary */
  if (invert_b1) btor_invert_const (mm, b1);
  switch (sc)
  {
    case BTOR_SPECIAL_CONST_ZERO:
      switch (kind)
      {
        case BTOR_BEQ_NODE:
          if (width_e0 == 1)
            result = btor_not_exp (btor, e0);
          else if (is_xor_exp (btor, e0)) /* (a ^ b) == 0 -->  a = b */
          {
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              result = rewrite_eq_exp (
                  btor,
                  BTOR_REAL_ADDR_NODE (
                      BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e0)->e[0])
                          ->e[0]),
                  BTOR_REAL_ADDR_NODE (
                      BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e0)->e[0])
                          ->e[1]));
              BTOR_DEC_REC_RW_CALL (btor);
            }
          }
          else if (BTOR_IS_INVERTED_NODE (e0) && real_e0->kind == BTOR_AND_NODE)
          { /*  a | b == 0  -->  a == 0 && b == 0 */
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              left =
                  rewrite_eq_exp (btor, BTOR_INVERT_NODE (real_e0->e[0]), e1);
              right =
                  rewrite_eq_exp (btor, BTOR_INVERT_NODE (real_e0->e[1]), e1);
              result = rewrite_and_exp (btor, left, right);
              BTOR_DEC_REC_RW_CALL (btor);
              btor_release_exp (btor, left);
              btor_release_exp (btor, right);
            }
          }
          break;
        case BTOR_SLL_NODE:
        case BTOR_SRL_NODE:
        case BTOR_UREM_NODE:
        case BTOR_ADD_NODE: result = btor_copy_exp (btor, e0); break;
        case BTOR_MUL_NODE:
        case BTOR_AND_NODE: result = btor_zero_exp (btor, width_e0); break;
        case BTOR_ULT_NODE: /* x < 0 */ result = btor_false_exp (btor); break;
        case BTOR_UDIV_NODE: result = btor_ones_exp (btor, width_e0); break;
        default: break;
      }
      break;
    case BTOR_SPECIAL_CONST_ONE_ONES:
      assert (width_e1 == 1);
      if (kind == BTOR_AND_NODE || kind == BTOR_BEQ_NODE
          || kind == BTOR_MUL_NODE || kind == BTOR_UDIV_NODE)
        result = btor_copy_exp (btor, e0);
      break;
    case BTOR_SPECIAL_CONST_ONE:
      if (kind == BTOR_MUL_NODE || kind == BTOR_UDIV_NODE)
        result = btor_copy_exp (btor, e0);
      else if (kind == BTOR_UREM_NODE)
        result = btor_zero_exp (btor, width_e0);
      else if (kind == BTOR_ULT_NODE)
      {
        tmp1   = btor_zero_exp (btor, width_e0);
        result = rewrite_eq_exp (btor, e0, tmp1);
        btor_release_exp (btor, tmp1);
      }
      break;
    case BTOR_SPECIAL_CONST_ONES:
      if (kind == BTOR_BEQ_NODE)
      {
        if (is_xnor_exp (btor, e0)) /* (a XNOR b) == 1 -->  a = b */
        {
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            result = rewrite_eq_exp (
                btor,
                BTOR_REAL_ADDR_NODE (
                    BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e0)->e[0])->e[0]),
                BTOR_REAL_ADDR_NODE (
                    BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e0)->e[0])
                        ->e[1]));
            BTOR_DEC_REC_RW_CALL (btor);
          }
        }
        else if (!BTOR_IS_INVERTED_NODE (e0) && e0->kind == BTOR_AND_NODE)
        {
          /* a & b == 1+ -->  a == 1+ && b == 1+ */
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            left   = rewrite_eq_exp (btor, e0->e[0], e1);
            right  = rewrite_eq_exp (btor, e0->e[1], e1);
            result = rewrite_and_exp (btor, left, right);
            BTOR_DEC_REC_RW_CALL (btor);
            btor_release_exp (btor, left);
            btor_release_exp (btor, right);
          }
        }
      }
      else if (kind == BTOR_AND_NODE)
        result = btor_copy_exp (btor, e0);
      else if (kind == BTOR_ULT_NODE)
        result = BTOR_INVERT_NODE (rewrite_eq_exp (btor, e0, e1));
      break;
    default:
      assert (sc == BTOR_SPECIAL_CONST_NONE);
      if (kind == BTOR_BEQ_NODE && real_e0->kind == BTOR_AND_NODE
          && btor->rec_rw_calls < BTOR_REC_RW_BOUND)
      {
        BTOR_INC_REC_RW_CALL (btor);
        BTOR_INIT_STACK (stack);
        if (BTOR_IS_INVERTED_NODE (e1))
          bv_const = btor_not_const (btor->mm, btor_const_get_bits (real_e1));
        else
          bv_const = btor_copy_const (btor->mm, btor_const_get_bits (real_e1));

        pos = 0;
        /* a | b == const */
        if (BTOR_IS_INVERTED_NODE (e0))
        {
          while (pos < width_e1)
          {
            tmpString[0] = bv_const[pos];
            len          = (int) strspn (bv_const + pos, tmpString);
            tmp1         = rewrite_slice_exp (btor,
                                      BTOR_INVERT_NODE (real_e0->e[0]),
                                      width_e1 - 1 - pos,
                                      width_e1 - pos - len);
            tmp2         = rewrite_slice_exp (btor,
                                      BTOR_INVERT_NODE (real_e0->e[1]),
                                      width_e1 - 1 - pos,
                                      width_e1 - pos - len);
            if (tmpString[0] == '0')
            {
              tmp3 = btor_zero_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_release_exp (btor, tmp3);
            }
            else
            {
              assert (tmpString[0] == '1');
              tmp3 = btor_or_exp (btor, tmp1, tmp2);
              tmp4 = btor_ones_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_release_exp (btor, tmp3);
              btor_release_exp (btor, tmp4);
            }
            btor_release_exp (btor, tmp1);
            btor_release_exp (btor, tmp2);
            pos += len;
          }
        }
        else
        {
          assert (!BTOR_IS_INVERTED_NODE (e0));
          /* a & b == const */
          while (pos < width_e1)
          {
            tmpString[0] = bv_const[pos];
            len          = (int) strspn (bv_const + pos, tmpString);
            tmp1         = rewrite_slice_exp (
                btor, e0->e[0], width_e1 - 1 - pos, width_e1 - pos - len);
            tmp2 = rewrite_slice_exp (
                btor, e0->e[1], width_e1 - 1 - pos, width_e1 - pos - len);
            if (tmpString[0] == '1')
            {
              tmp3 = btor_ones_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_release_exp (btor, tmp3);
            }
            else
            {
              assert (tmpString[0] == '0');
              tmp3 = rewrite_and_exp (btor, tmp1, tmp2);
              tmp4 = btor_zero_exp (btor, len);
              BTOR_PUSH_STACK (
                  btor->mm, stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_release_exp (btor, tmp3);
              btor_release_exp (btor, tmp4);
            }
            btor_release_exp (btor, tmp1);
            btor_release_exp (btor, tmp2);
            pos += len;
          }
        }

        result = btor_true_exp (btor);
        assert (!BTOR_EMPTY_STACK (stack));
        do
        {
          tmp1 = BTOR_POP_STACK (stack);
          tmp2 = rewrite_and_exp (btor, result, tmp1);
          btor_release_exp (btor, result);
          result = tmp2;
          btor_release_exp (btor, tmp1);
        } while (!BTOR_EMPTY_STACK (stack));
        btor_delete_const (btor->mm, bv_const);
        BTOR_RELEASE_STACK (btor->mm, stack);
        BTOR_DEC_REC_RW_CALL (btor);
      }
      break;
  }

  return result;
}

/* -------------------------------------------------------------------------- */
/* linear term rewriting */

/* Can we rewrite 'term' as 'factor*lhs + rhs' where 'lhs' is a variable,
 * and 'factor' is odd?  We check whether this is possible but do not use
 * more than 'bound' recursive calls.
 */
static int
rewrite_linear_term_bounded (Btor *btor,
                             BtorNode *term,
                             char **factor_ptr,
                             BtorNode **lhs_ptr,
                             BtorNode **rhs_ptr,
                             int *bound_ptr)
{
  BtorNode *tmp, *other;
  char *factor;
  int term_width;

  if (*bound_ptr <= 0) return 0;

  *bound_ptr -= 1;

  if (BTOR_IS_INVERTED_NODE (term))
  {
    /* term = ~subterm
     *      = -1 - subterm
     *      = -1 - (factor * lhs + rhs)
     *      = (-factor) * lhs + (-1 -rhs)
     *      = (-factor) * lhs + ~rhs
     */
    if (!rewrite_linear_term_bounded (btor,
                                      BTOR_INVERT_NODE (term),
                                      &factor,
                                      lhs_ptr,
                                      rhs_ptr,
                                      bound_ptr))
      return 0;

    *rhs_ptr    = BTOR_INVERT_NODE (*rhs_ptr);
    *factor_ptr = btor_neg_const (btor->mm, factor);
    btor_delete_const (btor->mm, factor);
  }
  else if (term->kind == BTOR_ADD_NODE)
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

    *rhs_ptr = rewrite_add_exp (btor, other, tmp);
    btor_release_exp (btor, tmp);
  }
  else if (term->kind == BTOR_MUL_NODE)
  {
    if (is_odd_const_exp (term->e[0]))
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
    else if (is_odd_const_exp (term->e[1]))
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

    assert (!BTOR_IS_INVERTED_NODE (other));
    *factor_ptr =
        btor_mul_const (btor->mm, btor_const_get_bits (other), factor);
    btor_delete_const (btor->mm, factor);
    *rhs_ptr = rewrite_mul_exp (btor, other, tmp);
    btor_release_exp (btor, tmp);
  }
  else if (term->kind == BTOR_BV_VAR_NODE)
  {
    term_width  = btor_get_exp_width (btor, term);
    *lhs_ptr    = btor_copy_exp (btor, term);
    *rhs_ptr    = btor_zero_exp (btor, term_width);
    *factor_ptr = btor_one_const (btor->mm, term_width);
  }
  else
    return 0;

  return 1;
}

int
btor_rewrite_linear_term (
    Btor *btor, BtorNode *term, char **fp, BtorNode **lp, BtorNode **rp)
{
  int bound = 100, res;
  res       = rewrite_linear_term_bounded (btor, term, fp, lp, rp, &bound);
  if (res) btor->stats.linear_equations++;
  return res;
}

/* -------------------------------------------------------------------------- */
/* rewriting rules
 *
 * for each rule we define two functions:

static inline int
applies_<rw_rule> (Btor * btor, ...)
{

}

static inline BtorNode *
apply_<rw_rule> (Btor * btor, ...)
{
  assert (applies_<rw_rule> (...));

}

 * where the first one determines if <rw_rule> is applicable, and the second
 * one applies the rule.
 *
 * for adding rw rules to a rewrite function use the ADD_RW_RULE macro.
 *
 */

/* SLICE rules */

/* match:  exp[len(exp) - 1:0]
 * result: exp
 */
static inline int
applies_full_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) btor;
  return btor_get_exp_width (btor, exp) == upper - lower + 1;
}

static inline BtorNode *
apply_full_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_full_slice (btor, exp, upper, lower));
  (void) btor;
  (void) upper;
  (void) lower;
  return btor_copy_exp (btor, exp);
}

/* match: exp[upper:lower], where exp is a constant
 * result: constant
 */
static inline int
applies_const_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) btor;
  (void) upper;
  (void) lower;
  return BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (exp));
}

static inline BtorNode *
apply_const_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_const_slice (btor, exp, upper, lower));

  char *bits;
  BtorNode *result;

  bits   = btor_slice_const (btor->mm, btor_const_get_bits (exp), upper, lower);
  result = btor_const_exp (btor, bits);
  result = BTOR_COND_INVERT_NODE (exp, result);
  btor_delete_const (btor->mm, bits);
  return result;
}

/* match:  (exp[u:l])[upper:lower]
 * result: exp[l+upper:l+lower]
 */
static inline int
applies_slice_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_SLICE_NODE (BTOR_REAL_ADDR_NODE (exp));
}

static inline BtorNode *
apply_slice_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_slice_slice (btor, exp, upper, lower));

  BtorNode *result, *real_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (btor,
                              BTOR_COND_INVERT_NODE (exp, real_exp->e[0]),
                              btor_slice_get_lower (real_exp) + upper,
                              btor_slice_get_lower (real_exp) + lower);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: (a::b)[len(b)-1:0]
 * result: b
 */
static inline int
applies_concat_lower_slice (Btor *btor,
                            BtorNode *exp,
                            uint32_t upper,
                            uint32_t lower)
{
  (void) btor;
  return BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (exp)) && lower == 0
         && btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[1])
                == upper - lower + 1;
}

static inline BtorNode *
apply_concat_lower_slice (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  assert (applies_concat_lower_slice (btor, exp, upper, lower));
  (void) upper;
  (void) lower;

  BtorNode *result;

  result = BTOR_COND_INVERT_NODE (exp, BTOR_REAL_ADDR_NODE (exp)->e[1]);
  return btor_copy_exp (btor, result);
}

/* match: (a::b)[len(a)+len(b)-1:len(b)]
 * result: a
 */
static inline int
applies_concat_upper_slice (Btor *btor,
                            BtorNode *exp,
                            uint32_t upper,
                            uint32_t lower)
{
  return BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (exp))
         && btor->options.rewrite_level.val < 3
         && upper == btor_get_exp_width (btor, exp) - 1
         && btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[0])
                == upper - lower + 1;
}

static inline BtorNode *
apply_concat_upper_slice (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  assert (applies_concat_upper_slice (btor, exp, upper, lower));
  (void) upper;
  (void) lower;

  BtorNode *result;

  result = BTOR_COND_INVERT_NODE (exp, BTOR_REAL_ADDR_NODE (exp)->e[0]);
  return btor_copy_exp (btor, result);
}

/* match:  (a::b)[upper:lower], where lower >= len(b)
 * result: a[upper-len(b):lower-len(b)]
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline int
applies_concat_rec_upper_slice (Btor *btor,
                                BtorNode *exp,
                                uint32_t upper,
                                uint32_t lower)
{
  (void) upper;
  return btor->options.rewrite_level.val >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (exp))
         && lower >= btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[1]);
}

static inline BtorNode *
apply_concat_rec_upper_slice (Btor *btor,
                              BtorNode *exp,
                              uint32_t upper,
                              uint32_t lower)
{
  assert (applies_concat_rec_upper_slice (btor, exp, upper, lower));

  int len;
  BtorNode *result, *real_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  len      = btor_get_exp_width (btor, real_exp->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (btor,
                              BTOR_COND_INVERT_NODE (exp, real_exp->e[0]),
                              upper - len,
                              lower - len);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (a::b)[upper:lower], where upper < len(b)
 * result: b[upper:lower]
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline int
applies_concat_rec_lower_slice (Btor *btor,
                                BtorNode *exp,
                                uint32_t upper,
                                uint32_t lower)
{
  (void) lower;
  return btor->options.rewrite_level.val >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (exp))
         && upper < btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[1]);
}

static inline BtorNode *
apply_concat_rec_lower_slice (Btor *btor,
                              BtorNode *exp,
                              uint32_t upper,
                              uint32_t lower)
{
  assert (applies_concat_rec_lower_slice (btor, exp, upper, lower));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (
      btor,
      BTOR_COND_INVERT_NODE (exp, BTOR_REAL_ADDR_NODE (exp)->e[1]),
      upper,
      lower);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (a::b)[upper:lower], where lower = 0 and upper >= len(b)
 * result: a[upper-len(b):0]::b
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline int
applies_concat_rec_slice (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  return BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (exp))
         && btor->options.rewrite_level.val >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && lower == 0
         && upper >= btor_get_exp_width (btor, BTOR_REAL_ADDR_NODE (exp)->e[1]);
}

static inline BtorNode *
apply_concat_rec_slice (Btor *btor,
                        BtorNode *exp,
                        uint32_t upper,
                        uint32_t lower)
{
  assert (applies_concat_rec_slice (btor, exp, upper, lower));
  (void) lower;

  int len;
  BtorNode *result, *real_exp, *tmp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  len      = btor_get_exp_width (btor, real_exp->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp = rewrite_slice_exp (
      btor, BTOR_COND_INVERT_NODE (exp, real_exp->e[0]), upper - len, 0);
  result = rewrite_concat_exp (
      btor, tmp, BTOR_COND_INVERT_NODE (exp, real_exp->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  (a & b)[upper:lower]
 * result: a[upper:lower] & b[upper:lower]
 */
static inline int
applies_and_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return btor->options.rewrite_level.val >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (exp))
         && (slice_simplifiable (BTOR_REAL_ADDR_NODE (exp)->e[0])
             || slice_simplifiable (BTOR_REAL_ADDR_NODE (exp)->e[1]));
}

static inline BtorNode *
apply_and_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_and_slice (btor, exp, upper, lower));

  BtorNode *result, *left, *right, *real_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_slice_exp (btor, real_exp->e[0], upper, lower);
  right  = rewrite_slice_exp (btor, real_exp->e[1], upper, lower);
  result = btor_and_exp (btor, left, right);
  btor_release_exp (btor, right);
  btor_release_exp (btor, left);
  result = BTOR_COND_INVERT_NODE (exp, result);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (c ? a : b)[upper:lower]
 * result: c ? a[upper:lower] : b[upper:lower]
 */
static inline int
applies_bcond_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return btor->options.rewrite_level.val >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (exp))
         && (slice_simplifiable (BTOR_REAL_ADDR_NODE (exp)->e[1])
             || slice_simplifiable (BTOR_REAL_ADDR_NODE (exp)->e[2]));
}

static inline BtorNode *
apply_bcond_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_bcond_slice (btor, exp, upper, lower));

  BtorNode *t, *e, *result, *real_exp;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_INC_REC_RW_CALL (btor);
  t      = rewrite_slice_exp (btor, real_exp->e[1], upper, lower);
  e      = rewrite_slice_exp (btor, real_exp->e[2], upper, lower);
  result = rewrite_cond_exp (btor, real_exp->e[0], t, e);
  btor_release_exp (btor, e);
  btor_release_exp (btor, t);
  result = BTOR_COND_INVERT_NODE (exp, result);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

static inline int
applies_zero_lower_slice (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  (void) upper;
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && lower == 0
         && upper < btor_get_exp_width (btor, exp) / 2
         && (BTOR_IS_MUL_NODE (BTOR_REAL_ADDR_NODE (exp))
             || BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (exp)));
  //	     || BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (exp)));
}

static inline BtorNode *
apply_zero_lower_slice (Btor *btor,
                        BtorNode *exp,
                        uint32_t upper,
                        uint32_t lower)
{
  BtorNode *result, *real_exp, *tmp1, *tmp2;

  real_exp = BTOR_REAL_ADDR_NODE (exp);
  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = rewrite_slice_exp (btor, real_exp->e[0], upper, lower);
  tmp2   = rewrite_slice_exp (btor, real_exp->e[1], upper, lower);
  result = btor_rewrite_binary_exp (btor, real_exp->kind, tmp1, tmp2);
  result = BTOR_COND_INVERT_NODE (exp, result);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp1);
  btor_release_exp (btor, tmp2);
  return result;
}

/* EQ rules */

/* match:  a = a
 * result: true
 */
static inline int
applies_true_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return e0 == e1;
}

static inline BtorNode *
apply_true_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_true_eq (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_true_exp (btor);
}

/* match:  a = b, where a != b
 * result: false
 */
static inline int
applies_false_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return is_always_unequal (btor, e0, e1);
}

static inline BtorNode *
apply_false_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_false_eq (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_false_exp (btor);
}

/* match:  a + b = a
 * result: b = 0
 *
 * This rule does not lead to less substitutions. 'a' cannot
 * be substituted as the occurrence check would fail
 */
static inline int
applies_add_left_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && e0->kind == BTOR_ADD_NODE
         && e0->e[0] == e1;
}

static inline BtorNode *
apply_add_left_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_left_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_zero_exp (btor, btor_get_exp_width (btor, e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, tmp, e0->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  b + a = a
 * result: b = 0
 *
 * This rule does not lead to less substitutions. 'a' cannot
 * be substituted as the occurrence check would fail
 */
static inline int
applies_add_right_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && e0->kind == BTOR_ADD_NODE
         && e0->e[1] == e1;
}

static inline BtorNode *
apply_add_right_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_right_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_zero_exp (btor, btor_get_exp_width (btor, e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, tmp, e0->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  a + b = a + c
 * result: b = c
 */
static inline int
applies_add_add_1_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_ADD_NODE && e1->kind == BTOR_ADD_NODE
         && e0->e[0] == e1->e[0];
}

static inline BtorNode *
apply_add_add_1_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_add_1_eq (btor, e0, e1));

  BtorNode *result;
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[1], e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a + b = c + a
 * result: b = c
 */
static inline int
applies_add_add_2_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_ADD_NODE && e1->kind == BTOR_ADD_NODE
         && e0->e[0] == e1->e[1];
}

static inline BtorNode *
apply_add_add_2_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_add_2_eq (btor, e0, e1));

  BtorNode *result;
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[1], e1->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  b + a = a + c
 * result: b = c
 */
static inline int
applies_add_add_3_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_ADD_NODE && e1->kind == BTOR_ADD_NODE
         && e0->e[1] == e1->e[0];
}

static inline BtorNode *
apply_add_add_3_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_add_3_eq (btor, e0, e1));

  BtorNode *result;
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[0], e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  b + a = c + a
 * result: b = c
 */
static inline int
applies_add_add_4_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_ADD_NODE && e1->kind == BTOR_ADD_NODE
         && e0->e[1] == e1->e[1];
}

static inline BtorNode *
apply_add_add_4_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_add_4_eq (btor, e0, e1));

  BtorNode *result;
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[0], e1->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a & b = ~a & ~b
 * result: a = ~b
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline int
applies_and_and_1_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_AND_NODE && e1->kind == BTOR_AND_NODE
         && e0->e[0] == BTOR_INVERT_NODE (e1->e[0])
         && e0->e[1] == BTOR_INVERT_NODE (e1->e[1])
         && BTOR_IS_INVERTED_NODE (e0->e[0])
                == BTOR_IS_INVERTED_NODE (e0->e[1]);
}

static inline BtorNode *
appy_and_and_1_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_and_1_eq (btor, e0, e1));
  assert (BTOR_IS_INVERTED_NODE (e1->e[0]) == BTOR_IS_INVERTED_NODE (e1->e[1]));
  (void) e1;

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[0], BTOR_INVERT_NODE (e0->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  ~a & b = a & ~b
 * result: a = b
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline int
applies_and_and_2_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_AND_NODE && e1->kind == BTOR_AND_NODE
         && e0->e[0] == BTOR_INVERT_NODE (e1->e[0])
         && e0->e[1] == BTOR_INVERT_NODE (e1->e[1])
         && BTOR_IS_INVERTED_NODE (e0->e[0])
                != BTOR_IS_INVERTED_NODE (e0->e[1]);
}

static inline BtorNode *
appy_and_and_2_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_and_2_eq (btor, e0, e1));
  assert (BTOR_IS_INVERTED_NODE (e1->e[0]) != BTOR_IS_INVERTED_NODE (e1->e[1]));
  (void) e1;

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (
      btor, BTOR_REAL_ADDR_NODE (e0->e[0]), BTOR_REAL_ADDR_NODE (e0->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a & b = a & ~b
 * result: a = 0
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline int
applies_and_and_3_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_AND_NODE && e1->kind == BTOR_AND_NODE
         && e0->e[0] == e1->e[0] && e0->e[1] == BTOR_INVERT_NODE (e1->e[1]);
}

static inline BtorNode *
appy_and_and_3_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_and_3_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_zero_exp (btor, btor_get_exp_width (btor, e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[0], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  a & b = ~a & b
 * result: b = 0
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline int
applies_and_and_4_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->kind == BTOR_AND_NODE && e1->kind == BTOR_AND_NODE
         && e0->e[0] == BTOR_INVERT_NODE (e1->e[0]) && e0->e[1] == e1->e[1];
}

static inline BtorNode *
appy_and_and_4_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_and_4_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_zero_exp (btor, btor_get_exp_width (btor, e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[1], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  b ? a : t = d, where a != d
 * result: !b AND d = t
 */
static inline int
applies_bcond_uneq_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && BTOR_IS_BV_COND_NODE (e0)
         && is_always_unequal (btor, e0->e[1], e1);
}

static inline BtorNode *
apply_bcond_uneq_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_uneq_if_eq (btor, e0, e1));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_eq_exp (btor, e0->e[2], e1);
  result = rewrite_and_exp (btor, BTOR_INVERT_NODE (e0->e[0]), tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  b ? a : t = d, where a != d
 * result: !b AND d = t
 */
static inline int
applies_bcond_uneq_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && BTOR_IS_BV_COND_NODE (e0)
         && is_always_unequal (btor, e0->e[2], e1);
}

static inline BtorNode *
apply_bcond_uneq_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_uneq_else_eq (btor, e0, e1));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_eq_exp (btor, e0->e[1], e1);
  result = rewrite_and_exp (btor, e0->e[0], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  a = b ? a : c
 * result: b OR a = c
 * match:  a = ~(b ? a : c)
 * result: !b AND a = ~c
 */
static inline int
applies_bcond_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (e1))
         && BTOR_REAL_ADDR_NODE (e1)->e[1] == e0;
}

static inline BtorNode *
apply_bcond_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_if_eq (btor, e0, e1));

  BtorNode *tmp, *result, *real_e1;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  BTOR_INC_REC_RW_CALL (btor);
  if (BTOR_IS_INVERTED_NODE (e1))
  {
    tmp    = rewrite_eq_exp (btor, BTOR_INVERT_NODE (real_e1->e[2]), e0);
    result = rewrite_and_exp (btor, BTOR_INVERT_NODE (real_e1->e[0]), tmp);
  }
  else
  {
    tmp    = rewrite_eq_exp (btor, real_e1->e[2], e0);
    result = btor_or_exp (btor, real_e1->e[0], tmp);
  }
  btor_release_exp (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a = b ? c : a
 * result: !b OR a = c
 * match:  a = ~(b ? c : a)
 * result: b AND a = ~c
 */
static inline int
applies_bcond_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (BTOR_REAL_ADDR_NODE (e1))
         && BTOR_REAL_ADDR_NODE (e1)->e[2] == e0;
}

static inline BtorNode *
apply_bcond_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_else_eq (btor, e0, e1));

  BtorNode *tmp, *result, *real_e1;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  BTOR_INC_REC_RW_CALL (btor);
  if (BTOR_IS_INVERTED_NODE (e1))
  {
    tmp    = rewrite_eq_exp (btor, BTOR_INVERT_NODE (real_e1->e[1]), e0);
    result = rewrite_and_exp (btor, real_e1->e[0], tmp);
  }
  else
  {
    tmp    = rewrite_eq_exp (btor, real_e1->e[1], e0);
    result = btor_or_exp (btor, BTOR_INVERT_NODE (real_e1->e[0]), tmp);
  }
  btor_release_exp (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (x ? a : b) = (x : c : d), where either a = c or b = d
 * result: x ? a = c : b = d
 */
static inline int
applies_bcond_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e0) && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_IS_INVERTED_NODE (e0)
                == BTOR_IS_INVERTED_NODE (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_eq (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_eq_exp (btor,
                         BTOR_COND_INVERT_NODE (e0, real_e0->e[1]),
                         BTOR_COND_INVERT_NODE (e1, real_e1->e[1]));
  right  = rewrite_eq_exp (btor,
                          BTOR_COND_INVERT_NODE (e0, real_e0->e[2]),
                          BTOR_COND_INVERT_NODE (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, left);
  btor_release_exp (btor, right);
  return result;
}

/* match:  a * b + a * c
 * result: a * (b + c)
 */
static inline int
applies_add_mul_distrib (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && BTOR_IS_MUL_NODE (e0) && BTOR_IS_MUL_NODE (e1)
         && (e0->e[0] == e1->e[0] || e0->e[0] == e1->e[1]
             || e0->e[1] == e1->e[0] || e0->e[1] == e1->e[1]);
}

static inline BtorNode *
apply_add_mul_distrib (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_mul_distrib (btor, e0, e1));

  BtorNode *add, *mul, *result;

  BTOR_INC_REC_RW_CALL (btor);
  if (e0->e[0] == e1->e[0])
  {
    add = rewrite_add_exp (btor, e0->e[1], e1->e[1]);
    mul = e0->e[0];
  }
  else if (e0->e[0] == e1->e[1])
  {
    add = rewrite_add_exp (btor, e0->e[1], e1->e[0]);
    mul = e0->e[0];
  }
  else if (e0->e[1] == e1->e[0])
  {
    add = rewrite_add_exp (btor, e0->e[0], e1->e[1]);
    mul = e0->e[1];
  }
  else
  {
    assert (e0->e[1] == e1->e[1]);
    add = rewrite_add_exp (btor, e0->e[0], e1->e[0]);
    mul = e0->e[1];
  }

  result = rewrite_mul_exp (btor, mul, add);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, add);
  return result;
}

/* TODO
 *
 *
 */
static inline int
applies_distrib_add_mul_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int result;
  BtorNode *tmp = 0;

  result = btor->options.rewrite_level.val > 2 && !BTOR_IS_INVERTED_NODE (e0)
           && !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_MUL_NODE (e0)
           && BTOR_IS_ADD_NODE (e1)
           && applies_add_mul_distrib (btor, e1->e[0], e1->e[1])
           && (tmp = apply_add_mul_distrib (btor, e1->e[0], e1->e[1]))
           && tmp == e0;
  if (tmp) btor_release_exp (btor, tmp);
  return result;
}

static inline BtorNode *
apply_distrib_add_mul_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_distrib_add_mul_eq (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_true_exp (btor);
}

/* match:  a :: b = c
 * u: len(c)-1
 * l: len(c)-len(a)+1
 * result: a[u:l] = c[u:l] AND (a::b)[l:0] = c[l:0]
 *
 * push eq down over concats
 */
static inline int
applies_concat_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_REAL_ADDR_NODE (e0)->kind == BTOR_CONCAT_NODE;
}

static inline BtorNode *
apply_concat_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_concat_eq (btor, e0, e1));

  int upper, lower;
  BtorNode *real_e0, *tmp1, *tmp2, *tmp3, *tmp4, *result, *eq1, *eq2;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);

  BTOR_INC_REC_RW_CALL (btor);
  upper = btor_get_exp_width (btor, real_e0) - 1;
  lower = upper - btor_get_exp_width (btor, real_e0->e[0]) + 1;

  tmp1 = rewrite_slice_exp (btor, e0, upper, lower);
  tmp2 = rewrite_slice_exp (btor, e1, upper, lower);
  lower--;
  tmp3 = rewrite_slice_exp (btor, e0, lower, 0);
  tmp4 = rewrite_slice_exp (btor, e1, lower, 0);

  /* creating two slices on e1 does not really improve the situation here,
   * hence only create a result if a slice on e1 yields a result different
   * from a slice (through further rewriting) */
  if (!(BTOR_IS_SLICE_NODE (BTOR_REAL_ADDR_NODE (tmp2))
        && BTOR_IS_SLICE_NODE (BTOR_REAL_ADDR_NODE (tmp4))))
  {
    eq1    = rewrite_eq_exp (btor, tmp1, tmp2);
    eq2    = rewrite_eq_exp (btor, tmp3, tmp4);
    result = rewrite_and_exp (btor, eq1, eq2);
    btor_release_exp (btor, eq1);
    btor_release_exp (btor, eq2);
  }
  else
    result = 0;

  btor_release_exp (btor, tmp1);
  btor_release_exp (btor, tmp2);
  btor_release_exp (btor, tmp3);
  btor_release_exp (btor, tmp4);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

static inline int
applies_zero_eq_and_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e1;
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && is_const_zero_exp (btor, e0) && BTOR_IS_AND_NODE (real_e1)
         && (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e1->e[0]))
             || BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e1->e[1])));
}

static inline BtorNode *
apply_zero_eq_and_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  int len, upper, lower;
  BtorNode *result, *real_e1, *masked, *zero, *slice;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  if (is_bit_mask (real_e1->e[0], &upper, &lower))
    masked = real_e1->e[1];
  else if (is_bit_mask (real_e1->e[1], &upper, &lower))
    masked = real_e1->e[0];
  else
    return 0;

  len = upper - lower + 1;

  BTOR_INC_REC_RW_CALL (btor);
  zero   = btor_zero_exp (btor, len);
  slice  = rewrite_slice_exp (btor, masked, upper, lower);
  result = rewrite_eq_exp (btor, zero, slice);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, zero);
  btor_release_exp (btor, slice);
  return result;
}

/* ULT rules */

/* match:  a < a
 * result: false
 */
static inline int
applies_false_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return e0 == e1;
}

static inline BtorNode *
apply_false_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_false_ult (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_false_exp (btor);
}

/* match:  a < b, where len(a) = 1
 * result: !a AND b
 */
static inline int
applies_bool_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_get_exp_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_ult (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, BTOR_INVERT_NODE (e0), e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (a::b) < (a::c)
 * result: b < c
 */
static inline int
applies_concat_upper_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && BTOR_IS_CONCAT_NODE (e0) && e0->kind == e1->kind
         && e0->e[0] == e1->e[0];
}

static inline BtorNode *
apply_concat_upper_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_concat_upper_ult (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_ult_exp (btor, e0->e[1], e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (b::a) < (c::a)
 * result: b < c
 */
static inline int
applies_concat_lower_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && BTOR_IS_CONCAT_NODE (e0) && e0->kind == e1->kind
         && e0->e[1] == e1->e[1];
}

static inline BtorNode *
apply_concat_lower_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_concat_lower_ult (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_ult_exp (btor, e0->e[0], e1->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  (x ? a : b) < (x : c : d), where either a = c or b = d
 * result: x ? a < c : b < d
 */
static inline int
applies_bcond_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e0) && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_IS_INVERTED_NODE (e0)
                == BTOR_IS_INVERTED_NODE (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_ult (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_ult_exp (btor,
                          BTOR_COND_INVERT_NODE (e0, real_e0->e[1]),
                          BTOR_COND_INVERT_NODE (e1, real_e1->e[1]));
  right  = rewrite_ult_exp (btor,
                           BTOR_COND_INVERT_NODE (e0, real_e0->e[2]),
                           BTOR_COND_INVERT_NODE (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, left);
  btor_release_exp (btor, right);
  return result;
}

/* AND rules */

/* match:  a & a
 * result: a
 */
static inline int
applies_idem1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return e0 == e1;
}

static inline BtorNode *
apply_idem1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_idem1_and (btor, e0, e1));
  (void) e1;
  return btor_copy_exp (btor, e0);
}

/* match:  a & ~a
 * result: 0
 */
static inline int
applies_contr1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return BTOR_INVERT_NODE (e0) == e1;
}

static inline BtorNode *
apply_contr1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr1_and (btor, e0, e1));
  (void) e1;
  return btor_zero_exp (btor, btor_get_exp_width (btor, e0));
}

/* match: a & b & c & d, where a = ~c OR a = ~d OR b = ~c OR b = ~d
 * result: false
 *
 * second rule of contradiction
 */
static inline int
applies_contr2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e1))
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && (e0->e[0] == BTOR_INVERT_NODE (e1->e[0])
             || e0->e[0] == BTOR_INVERT_NODE (e1->e[1])
             || e0->e[1] == BTOR_INVERT_NODE (e1->e[0])
             || e0->e[1] == BTOR_INVERT_NODE (e1->e[1]));
}

static inline BtorNode *
apply_contr2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr2_and (btor, e0, e1));
  (void) e1;
  return btor_zero_exp (btor, btor_get_exp_width (btor, e0));
}

/* match: a & b & c & d, where a = c or b = c
 * result: a & b & d
 *
 * symmetric rule of idempotency
 */
static inline int
applies_idem2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e1))
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && (real_e0->e[0] == real_e1->e[0] || real_e0->e[1] == real_e1->e[0]);
}

static inline BtorNode *
apply_idem2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_idem2_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, BTOR_REAL_ADDR_NODE (e1)->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: a & b & c & d, where a = d OR b = d
 * result: a & b & c
 *
 * use commutativity
 */
static inline int
applies_comm_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e1))
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && (real_e0->e[0] == real_e1->e[1] || real_e0->e[1] == real_e1->e[1]);
}

static inline BtorNode *
apply_comm_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_comm_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, BTOR_REAL_ADDR_NODE (e1)->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: a & b & ~(c & d), where a = c OR a = d OR b = c OR b = d
 * result: a & b
 */
static inline int
applies_subsum1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e1))
         && !BTOR_IS_INVERTED_NODE (e0) && BTOR_IS_INVERTED_NODE (e1)
         && (real_e0->e[0] == BTOR_INVERT_NODE (real_e1->e[0])
             || real_e0->e[0]
                    == BTOR_INVERT_NODE (
                           real_e1->e[1]
                           || real_e0->e[1] == BTOR_INVERT_NODE (real_e1->e[0])
                           || real_e0->e[1]
                                  == BTOR_INVERT_NODE (real_e1->e[1])));
}

static inline BtorNode *
apply_subsum1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subsum1_and (btor, e0, e1));
  (void) e1;
  return btor_copy_exp (btor, e0);
}

/* match: a & b & ~(c & d), where a = c OR b = c
 * result: a & b & ~d
 *
 * symmetric rule of substitution
 */
static inline int
applies_subst1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_AND_NODE (real_e1) && !BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_INVERTED_NODE (e1)
         && (real_e1->e[0] == real_e0->e[1] || real_e1->e[0] == real_e0->e[0]);
}

static inline BtorNode *
apply_subst1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst1_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, e0, BTOR_INVERT_NODE (BTOR_REAL_ADDR_NODE (e1)->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: a & b & ~(c & d), where a = d OR b = d
 * result: a & b & ~c
 *
 * symmetric rule of substitution
 */
static inline int
applies_subst2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_AND_NODE (real_e1) && !BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_INVERTED_NODE (e1)
         && (real_e1->e[1] == real_e0->e[1] || real_e1->e[1] == real_e0->e[0]);
}

static inline BtorNode *
apply_subst2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst2_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, e0, BTOR_INVERT_NODE (BTOR_REAL_ADDR_NODE (e1)->e[0]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: a XNOR b, where len(a) = 1
 * result: a = b
 */
static inline int
applies_bool_xnor_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_AND_NODE (real_e1) && BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_INVERTED_NODE (e1)
         && btor_get_exp_width (btor, real_e0) == 1
         && BTOR_IS_INVERTED_NODE (real_e0->e[0])
                != BTOR_IS_INVERTED_NODE (real_e0->e[1])
         && BTOR_IS_INVERTED_NODE (real_e1->e[0])
                != BTOR_IS_INVERTED_NODE (real_e1->e[1])
         && ((real_e0->e[0] == BTOR_INVERT_NODE (real_e1->e[0])
              && real_e0->e[1] == BTOR_INVERT_NODE (real_e1->e[1]))
             || (real_e0->e[0] == BTOR_INVERT_NODE (real_e1->e[1])
                 && real_e0->e[1] == BTOR_INVERT_NODE (real_e1->e[0])));
}

static inline BtorNode *
apply_bool_xnor_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_xnor_and (btor, e0, e1));
  (void) e1;

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result =
      rewrite_eq_exp (btor,
                      BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e0)->e[0]),
                      BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (e0)->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: ~(a & b) & ~(c & d), where (a = c AND b = ~d) OR (a = d AND b = ~c)
 * result: ~a
 *
 * rule of resolution
 */
static inline int
applies_resol1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_AND_NODE (real_e1) && BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_INVERTED_NODE (e1)
         && ((real_e0->e[0] == real_e1->e[0]
              && real_e0->e[1] == BTOR_INVERT_NODE (real_e1->e[1]))
             || (real_e0->e[0] == real_e1->e[1]
                 && real_e0->e[1] == BTOR_INVERT_NODE (real_e1->e[0])));
}

static inline BtorNode *
apply_resol1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_resol1_and (btor, e0, e1));
  (void) e1;
  return BTOR_INVERT_NODE (
      btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (e0)->e[0]));
}

/* match: ~(a & b) & ~(c & d), where (~a = c AND b = d) OR (a = d AND ~b = c)
 * result: ~a
 *
 * rule of resolution
 */
static inline int
applies_resol2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_AND_NODE (real_e1) && BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_INVERTED_NODE (e1)
         && ((real_e1->e[1] == real_e0->e[1]
              && real_e1->e[0] == BTOR_INVERT_NODE (real_e0->e[0]))
             || (real_e1->e[1] == real_e0->e[0]
                 && real_e1->e[0] == BTOR_INVERT_NODE (real_e0->e[1])));
}

static inline BtorNode *
apply_resol2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_resol2_and (btor, e0, e1));
  (void) e0;
  return BTOR_INVERT_NODE (
      btor_copy_exp (btor, BTOR_REAL_ADDR_NODE (e1)->e[1]));
}

/* match: ~(a & b) & c, where a == ~c OR b == ~c
 * result: c
 *
 * first rule of subsumption
 */
static inline int
applies_subsum2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return BTOR_IS_AND_NODE (real_e0) && BTOR_IS_INVERTED_NODE (e0)
         && (real_e0->e[0] == BTOR_INVERT_NODE (e1)
             || real_e0->e[1] == BTOR_INVERT_NODE (e1));
}

static inline BtorNode *
apply_subsum2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subsum2_and (btor, e0, e1));
  (void) e0;
  return btor_copy_exp (btor, e1);
}

/* match: ~(a & b) & c, where b = c
 * result: ~a & c
 *
 * asymmetric rule of substitution
 */
static inline int
applies_subst3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_INVERTED_NODE (e0) && real_e0->e[1] == e1;
}

static inline BtorNode *
apply_subst3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst3_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, BTOR_INVERT_NODE (BTOR_REAL_ADDR_NODE (e0)->e[0]), e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: ~(a & b) & c, where a = c
 * result: ~b & c
 *
 * asymmetric rule of substitution
 */
static inline int
applies_subst4_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && BTOR_IS_INVERTED_NODE (e0) && real_e0->e[0] == e1;
}

static inline BtorNode *
apply_subst4_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst4_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, BTOR_INVERT_NODE (BTOR_REAL_ADDR_NODE (e0)->e[1]), e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: a & b & c, where a = ~c OR b = ~c
 * result: 0
 *
 * first rule of contradiction
 */
static inline int
applies_contr3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e0)
         && (e0->e[0] == BTOR_INVERT_NODE (e1)
             || e0->e[1] == BTOR_INVERT_NODE (e1));
}

static inline BtorNode *
apply_contr3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr3_and (btor, e0, e1));
  (void) e1;
  return btor_zero_exp (btor, btor_get_exp_width (btor, e0));
}

/* match: a & b & c, where a = c OR b = c
 * result: a
 *
 * asymmetric rule of idempotency
 */
static inline int
applies_idem3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e0) && (e0->e[0] == e1 || e0->e[1] == e1);
}

static inline BtorNode *
apply_idem3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_idem3_and (btor, e0, e1));
  (void) e1;
  return btor_copy_exp (btor, e0);
}

/* match: a & b & c, where a and c are constants
 * result: d & b, where d is a new constant obtained from a & c
 */
static inline int
applies_const1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1))
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0->e[0]));
}

static inline BtorNode *
apply_const1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const1_and (btor, e0, e1));
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0->e[1])));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e1, e0->e[0]);
  result = rewrite_and_exp (btor, tmp, e0->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: a & b & c, where b and c are constants
 * result: d & a, where d is a new constant obtained from b & c
 */
static inline int
applies_const2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1))
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0->e[1]));
}

static inline BtorNode *
apply_const2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const2_and (btor, e0, e1));
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0->e[0])));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e1, e0->e[1]);
  result = rewrite_and_exp (btor, tmp, e0->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: (a < b) & (b < a)
 * result: false
 */
static inline int
applies_ult_false_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_ULT_NODE (BTOR_REAL_ADDR_NODE (e1))
         && !BTOR_IS_INVERTED_NODE (e0) && !BTOR_IS_INVERTED_NODE (e1)
         && e0->e[0] == e1->e[1] && e0->e[1] == e1->e[0];
}

static inline BtorNode *
apply_ult_false_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_ult_false_and (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_false_exp (btor);
}

/* match: ~(a < b) & ~(b < a)
 * result: a = b
 */
static inline int
applies_ult_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_ULT_NODE (real_e0)
         && BTOR_IS_ULT_NODE (real_e1) && BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_INVERTED_NODE (e1) && real_e0->e[0] == real_e1->e[1]
         && real_e0->e[1] == real_e1->e[0];
}

static inline BtorNode *
apply_ult_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_ult_and (btor, e0, e1));
  (void) e1;

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (
      btor, BTOR_REAL_ADDR_NODE (e0)->e[0], BTOR_REAL_ADDR_NODE (e0)->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 *
 * recursively find contradicting ands
 */
static inline int
applies_contr_rec_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int calls = 0;
  return find_and_contradiction_exp (btor, e0, e0, e1, &calls)
         || find_and_contradiction_exp (btor, e1, e0, e1, &calls);
}

static inline BtorNode *
apply_contr_rec_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr_rec_and (btor, e0, e1));
  (void) e1;
  return btor_zero_exp (btor, btor_get_exp_width (btor, e0));
}

/* match:  (0::a) & (b::0)
 * result: 0
 *
 * match:  (0::a) & (b::1)
 * result: 0::a
 *
 * match: (1::a) & (b::1)
 * result: b::a
 */
static inline int
applies_concat_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int result;
  BtorNode *real_e0, *real_e1, *e00, *e01, *e10, *e11;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  result = btor->rec_rw_calls < BTOR_REC_RW_BOUND
           && BTOR_IS_CONCAT_NODE (real_e0) && BTOR_IS_CONCAT_NODE (real_e1)
           && BTOR_REAL_ADDR_NODE (real_e0->e[0])->sort_id
                  == BTOR_REAL_ADDR_NODE (real_e1->e[0])->sort_id;

  if (!result) return result;

  e00 = BTOR_COND_INVERT_NODE (e0, real_e0->e[0]);
  e01 = BTOR_COND_INVERT_NODE (e0, real_e0->e[1]);
  e10 = BTOR_COND_INVERT_NODE (e1, real_e1->e[0]);
  e11 = BTOR_COND_INVERT_NODE (e1, real_e1->e[1]);
  return ((is_const_zero_or_ones_exp (btor, e00)
           && is_const_zero_or_ones_exp (btor, e11))
          || (is_const_zero_or_ones_exp (btor, e01)
              && is_const_zero_or_ones_exp (btor, e10)));
}

static inline BtorNode *
apply_concat_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_concat_and (btor, e0, e1));

  BtorNode *real_e0, *real_e1, *e00, *e01, *e10, *e11, *left, *right, *result;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  e00     = BTOR_COND_INVERT_NODE (e0, real_e0->e[0]);
  e01     = BTOR_COND_INVERT_NODE (e0, real_e0->e[1]);
  e10     = BTOR_COND_INVERT_NODE (e1, real_e1->e[0]);
  e11     = BTOR_COND_INVERT_NODE (e1, real_e1->e[1]);

  BTOR_INC_REC_RW_CALL (btor);
  left   = btor_and_exp (btor, e00, e10);
  right  = btor_and_exp (btor, e01, e11);
  result = rewrite_concat_exp (btor, left, right);
  btor_release_exp (btor, right);
  btor_release_exp (btor, left);
  BTOR_DEC_REC_RW_CALL (btor);

  return result;
}

#if 0
/* match:
 * result: 
 */
static inline int
applies_and (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && !BTOR_IS_INVERTED_NODE (e0)
	 && BTOR_IS_BV_COND_NODE (e0);
}

static inline BtorNode * 
apply_and (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_and (btor, e0, e1));

}

// TODO (ma): uses shallow substitute, which does not really work
  if (!BTOR_IS_INVERTED_NODE (e0) &&
      e0->kind == BTOR_BEQ_NODE &&
      btor->options.rewrite_level.val > 2 &&
      btor->rec_rw_calls < BTOR_REC_RW_BOUND)
    {
      BtorNode * e1_simp = condrewrite (btor, e1, e0);
      if (e1_simp != e1) 
	{
	  BTOR_INC_REC_RW_CALL (btor);
	  result = rewrite_and_exp (btor, e0, e1_simp);
	  BTOR_DEC_REC_RW_CALL (btor);
	}
      else
	result = 0;
      btor_release_exp (btor, e1_simp);
      if (result)
	{
	  assert (!normalized);
	  return result;
	}
    }

  if (!BTOR_IS_INVERTED_NODE (e1) &&
      e1->kind == BTOR_BEQ_NODE &&
      btor->options.rewrite_level.val > 2 &&
      btor->rec_rw_calls < BTOR_REC_RW_BOUND)
    {
      BtorNode * e0_simp = condrewrite (btor, e0, e1);
      if (e0_simp != e0) 
	{
	  BTOR_INC_REC_RW_CALL (btor);
	  result = rewrite_and_exp (btor, e0_simp, e1);
	  BTOR_DEC_REC_RW_CALL (btor);
	}
      else
	result = 0;
      btor_release_exp (btor, e0_simp);
      if (result)
	{
	  assert (!normalized);
	  return result;
	}
    }
#endif

/* ADD rules */

/* match:  a + b, where len(a) = 1
 * result: a XOR b
 */
static inline int
applies_bool_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_get_exp_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_add (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = btor_xor_exp (btor, e0, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a - b OR -a + b, where a = b
 * result: 0
 */
static inline int
applies_neg_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_ADD_NODE (e1)
         && ((e0 == BTOR_INVERT_NODE (e1->e[0])
              && is_const_one_exp (btor, e1->e[1]))
             || (e0 == BTOR_INVERT_NODE (e1->e[1])
                 && is_const_one_exp (btor, e1->e[0])));
}

static inline BtorNode *
apply_neg_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_neg_add (btor, e0, e1));
  (void) e1;
  return btor_zero_exp (btor, btor_get_exp_width (btor, e0));
}

/* match: 0 + b
 * result: b
 */
static inline int
applies_zero_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return is_const_zero_exp (btor, e0);
}

static inline BtorNode *
apply_zero_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_zero_add (btor, e0, e1));
  (void) e0;
  return btor_copy_exp (btor, e1);
}

/* match: c0 + (c1 + b), where c0 and c1 are constants
 * result: c + b, where c is a new constant from c0 + c1
 *
 * recursion is no problem here, as one call leads to
 * folding of constants, and the other call can not
 * trigger the same kind of recursion anymore.
 */
static inline int
applies_const_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_ADD_NODE (e1)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[0]));
}

static inline BtorNode *
apply_const_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_lhs_add (btor, e0, e1));
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[1])));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_add_exp (btor, e0, e1->e[0]);
  result = rewrite_add_exp (btor, tmp, e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: c0 + (b + c1), where c0 and c1 are constants
 * result: c + b, where c is a new constant from c0 + c1
 *
 * recursion is no problem here, as one call leads to
 * folding of constants, and the other call can not
 * trigger the same kind of recursion anymore.
 */
static inline int
applies_const_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_ADD_NODE (e1)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[1]));
}

static inline BtorNode *
apply_const_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_rhs_add (btor, e0, e1));
  assert (!BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[0])));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_add_exp (btor, e0, e1->e[1]);
  result = rewrite_add_exp (btor, tmp, e1->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

#if 0
  // TODO: problematic as long we do not do 'addneg normalization'
  //
  // e0 + e1 == ~(e00 + e01) + e1
  //         == (-(e00 + e01) -1) + e1
  //         == - e00 - e01 - 1 + e1
  //         == (~e00 + 1) + (~e01 + 1) - 1 + e1
  //         == ((~e00 + ~e01) + 1) + e1
  //
  if (btor->options.rewrite_level.val > 2 &&
      BTOR_IS_INVERTED_NODE (e0) &&
      btor->rec_rw_calls < BTOR_REC_RW_BOUND &&
      (temp = BTOR_REAL_ADDR_NODE (e0))->kind == BTOR_ADD_NODE)
    {
      BtorNode * e00 = temp->e[0];
      BtorNode * e01 = temp->e[1];
      BtorNode * one, * sum;
      BTOR_INC_REC_RW_CALL (btor);
      one = btor_one_exp (btor, btor_get_exp_width (btor, temp));
      temp = btor_add_exp (btor,
        BTOR_INVERT_NODE (e00), BTOR_INVERT_NODE (e01));
      sum = btor_add_exp (btor, temp, one);
      result = btor_add_exp (btor, sum, e1);
      BTOR_DEC_REC_RW_CALL (btor);
      btor_release_exp (btor, sum);
      btor_release_exp (btor, temp);
      btor_release_exp (btor, one);
      return result;
    }

  // TODO: problematic as long we do not do 'addneg normalization'
  //
  // e0 + e1 == e0 + ~(e10 + e11)
  //         == e0 + (-(e10 + e11) -1)
  //         == e0 - e10 - e11 - 1
  //         == e0 + (~e10 + 1) + (~e11 + 1) - 1
  //         == e0 + ((~e10 + ~e11) + 1)
  //
  if (btor->options.rewrite_level.val > 2 &&
      BTOR_IS_INVERTED_NODE (e1) &&
      btor->rec_rw_calls < BTOR_REC_RW_BOUND &&
      (temp = BTOR_REAL_ADDR_NODE (e1))->kind == BTOR_ADD_NODE)
    {
      BtorNode * e10 = temp->e[0];
      BtorNode * e11 = temp->e[1];
      BtorNode * one, * sum;
      BTOR_INC_REC_RW_CALL (btor);
      one = btor_one_exp (btor, btor_get_exp_width (btor, temp));
      temp = btor_add_exp (btor, 
        BTOR_INVERT_NODE (e10), BTOR_INVERT_NODE (e11));
      sum = btor_add_exp (btor, temp, one);
      result = btor_add_exp (btor, e0, sum);
      BTOR_DEC_REC_RW_CALL (btor);
      btor_release_exp (btor, sum);
      btor_release_exp (btor, temp);
      btor_release_exp (btor, one);
      return result;
    }
#endif

/* match:  ~(c * a) + b
 * result: ((-c) * a - 1) + b
 */
static inline int
applies_const_neg_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_MUL_NODE (real_e0)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e0->e[0]));
}

static inline BtorNode *
apply_const_neg_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_neg_lhs_add (btor, e0, e1));

  BtorNode *result, *real_e0, *e00, *e01, *n00, *n01, *one, *sum, *tmp;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  e00     = real_e0->e[0];
  e01     = real_e0->e[1];

  BTOR_INC_REC_RW_CALL (btor);
  n00    = btor_neg_exp (btor, e00);
  n01    = btor_copy_exp (btor, e01);
  one    = btor_one_exp (btor, btor_get_exp_width (btor, real_e0));
  tmp    = rewrite_mul_exp (btor, n00, n01);
  sum    = btor_sub_exp (btor, tmp, one);
  result = rewrite_add_exp (btor, sum, e1);
  btor_release_exp (btor, sum);
  btor_release_exp (btor, tmp);
  btor_release_exp (btor, one);
  btor_release_exp (btor, n00);
  btor_release_exp (btor, n01);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  ~(a * c) + b
 * result: (a * (-c) - 1) + b
 */
static inline int
applies_const_neg_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_INVERTED_NODE (e0)
         && BTOR_IS_MUL_NODE (real_e0)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e0->e[1]));
}

static inline BtorNode *
apply_const_neg_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_neg_rhs_add (btor, e0, e1));

  BtorNode *result, *real_e0, *e00, *e01, *n00, *n01, *one, *sum, *tmp;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  e00     = real_e0->e[0];
  e01     = real_e0->e[1];

  BTOR_INC_REC_RW_CALL (btor);
  n00    = btor_copy_exp (btor, e00);
  n01    = btor_neg_exp (btor, e01);
  one    = btor_one_exp (btor, btor_get_exp_width (btor, real_e0));
  tmp    = rewrite_mul_exp (btor, n00, n01);
  sum    = btor_sub_exp (btor, tmp, one);
  result = rewrite_add_exp (btor, sum, e1);
  btor_release_exp (btor, sum);
  btor_release_exp (btor, tmp);
  btor_release_exp (btor, one);
  btor_release_exp (btor, n00);
  btor_release_exp (btor, n01);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a + a
 * result: 2 * a
 */
static inline int
applies_mult_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && e0 == e1
         && btor_get_exp_width (btor, e0) >= 2;
}

static inline BtorNode *
apply_mult_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_mult_add (btor, e0, e1));
  (void) e1;

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = btor_int_exp (btor, 2, btor_get_exp_width (btor, e0));
  result = rewrite_mul_exp (btor, e0, tmp);
  btor_release_exp (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a + ~a
 * result: -1
 */
static inline int
applies_not_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return BTOR_REAL_ADDR_NODE (e0) == BTOR_REAL_ADDR_NODE (e1) && e0 != e1;
}

static inline BtorNode *
apply_not_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_not_add (btor, e0, e1));
  (void) e1;
  return btor_ones_exp (btor, btor_get_exp_width (btor, e0));
}

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/* match:  (x ? a : b) + (x : c : d), where either a = c or b = d
 * result: x ? a + c : b + d
 */
static inline int
applies_bcond_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e0) && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_IS_INVERTED_NODE (e0)
                == BTOR_IS_INVERTED_NODE (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_add (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_add_exp (btor,
                          BTOR_COND_INVERT_NODE (e0, real_e0->e[1]),
                          BTOR_COND_INVERT_NODE (e1, real_e1->e[1]));
  right  = rewrite_add_exp (btor,
                           BTOR_COND_INVERT_NODE (e0, real_e0->e[2]),
                           BTOR_COND_INVERT_NODE (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, left);
  btor_release_exp (btor, right);
  return result;
}

/* MUL rules */

/* match:  a * b, wher len(a) = 1
 * result: a & b
 */
static inline int
applies_bool_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_get_exp_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_mul (btor, e0, e1));

  BtorNode *result;
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: c0 * (c1 * b), where c0 and c1 are constants
 * result: c * b, where c is a new constant from c0 * c1
 */
static inline int
applies_const_lhs_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_MUL_NODE (e1)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[0]));
}

static inline BtorNode *
apply_const_lhs_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_lhs_mul (btor, e0, e1));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_mul_exp (btor, e0, e1->e[0]);
  result = rewrite_mul_exp (btor, tmp, e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: c0 * (b * c1), where c0 and c1 are constants
 * result: c * b, where c is a new constant from c0 * c1
 */
static inline int
applies_const_rhs_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_MUL_NODE (e1)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[1]));
}

static inline BtorNode *
apply_const_rhs_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_rhs_mul (btor, e0, e1));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_mul_exp (btor, e0, e1->e[1]);
  result = rewrite_mul_exp (btor, tmp, e1->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: c0 * (a + c1)
 * result: c0 * a + c, where c is a new constant from c0 * c1
 */
static inline int
applies_const_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_IS_INVERTED_NODE (e1) && BTOR_IS_ADD_NODE (e1)
         && (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[0]))
             || BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1->e[1])));
}

static inline BtorNode *
apply_const_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_mul (btor, e0, e1));

  BtorNode *result, *left, *right;

  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_mul_exp (btor, e0, e1->e[0]);
  right  = rewrite_mul_exp (btor, e0, e1->e[1]);
  result = rewrite_add_exp (btor, left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, left);
  btor_release_exp (btor, right);
  return result;
}

#if 0
  // TODO: why should we disable this?
  //
  if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
    {
      if (is_const_ones_exp (btor, e0))
	result = e1;
      else
      if (is_const_ones_exp (btor, e1))
	result = e0;
      else
	result = 0;
	
      if (result)
	{
	  int len = btor_get_exp_width (btor, result);
	  BtorNode * tmp, * one = btor_one_exp (btor, len);
	  BTOR_INC_REC_RW_CALL (btor);
	  tmp = btor_add_exp (btor, BTOR_INVERT_NODE (result), one);
	  BTOR_DEC_REC_RW_CALL (btor);
	  btor_release_exp (btor, one);
	  result = tmp;
	  goto HAVE_RESULT_BUT_MIGHT_NEED_TO_RELEASE_SOMETHING;
	}
    }
#endif

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/* match:  (x ? a : b) * (x : c : d), where either a = c or b = d
 * result: x ? a * c : b * d
 */
static inline int
applies_bcond_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e0) && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_IS_INVERTED_NODE (e0)
                == BTOR_IS_INVERTED_NODE (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_mul (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_mul_exp (btor,
                          BTOR_COND_INVERT_NODE (e0, real_e0->e[1]),
                          BTOR_COND_INVERT_NODE (e1, real_e1->e[1]));
  right  = rewrite_mul_exp (btor,
                           BTOR_COND_INVERT_NODE (e0, real_e0->e[2]),
                           BTOR_COND_INVERT_NODE (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, left);
  btor_release_exp (btor, right);
  return result;
}

/* UDIV rules */

/* match: a / b, where len(a) = 1
 * result: ~(~a & b)
 */
static inline int
applies_bool_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_get_exp_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_udiv (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = BTOR_INVERT_NODE (rewrite_and_exp (btor, BTOR_INVERT_NODE (e0), e1));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a / 2^n
 * result: 0 :: a[len(a)-1:n]
 */
static inline int
applies_power2_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && !BTOR_IS_INVERTED_NODE (e1)
         && BTOR_IS_BV_CONST_NODE (e1)
         && btor_is_power_of_two_const (btor_const_get_bits (e1)) > 0;
}

static inline BtorNode *
apply_power2_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_power2_udiv (btor, e0, e1));

  unsigned l, n;
  BtorNode *slice, *pad, *result;

  n = btor_is_power_of_two_const (btor_const_get_bits (e1));
  l = btor_get_exp_width (btor, e0);
  assert (l > n);

  BTOR_INC_REC_RW_CALL (btor);
  slice  = rewrite_slice_exp (btor, e0, l - 1, n);
  pad    = btor_zero_exp (btor, n);
  result = rewrite_concat_exp (btor, pad, slice);
  BTOR_DEC_REC_RW_CALL (btor);
  assert (btor_get_exp_width (btor, result) == l);
  btor_release_exp (btor, pad);
  btor_release_exp (btor, slice);
  return result;
}

/* match: a / a
 * result: 1, if a != 0 and UINT_MAX otherwise
 */
static inline int
applies_one_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && e0 == e1;
}

static inline BtorNode *
apply_one_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_one_udiv (btor, e0, e1));
  (void) e1;

  BtorNode *result, *tmp1, *tmp2, *tmp3, *eq, *real_e0;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = btor_zero_exp (btor, btor_get_exp_width (btor, real_e0));
  tmp2   = btor_one_exp (btor, btor_get_exp_width (btor, real_e0));
  tmp3   = btor_ones_exp (btor, btor_get_exp_width (btor, real_e0));
  eq     = rewrite_eq_exp (btor, e0, tmp1);
  result = rewrite_cond_exp (btor, eq, tmp3, tmp2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, eq);
  btor_release_exp (btor, tmp1);
  btor_release_exp (btor, tmp2);
  btor_release_exp (btor, tmp3);
  return result;
}

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/* match:  (x ? a : b) / (x : c : d), where either a = c or b = d
 * result: x ? a / c : b / d
 */
static inline int
applies_bcond_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e0) && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_IS_INVERTED_NODE (e0)
                == BTOR_IS_INVERTED_NODE (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_udiv (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_udiv_exp (btor,
                           BTOR_COND_INVERT_NODE (e0, real_e0->e[1]),
                           BTOR_COND_INVERT_NODE (e1, real_e1->e[1]));
  right  = rewrite_udiv_exp (btor,
                            BTOR_COND_INVERT_NODE (e0, real_e0->e[2]),
                            BTOR_COND_INVERT_NODE (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, left);
  btor_release_exp (btor, right);
  return result;
}

/* UREM rules */

/* match:  a % b, where len(a) = 1
 * result: a & ~b
 */
static inline int
applies_bool_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_get_exp_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_urem (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, BTOR_INVERT_NODE (e1));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a % a
 * result: 0
 */
static inline int
applies_zero_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return e0 == e1;
}

static inline BtorNode *
apply_zero_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_zero_urem (btor, e0, e1));
  (void) e1;
  return btor_zero_exp (btor, btor_get_exp_width (btor, e0));
}

/* CONCAT rules */

/* match:  (a::c0)::c1
 * result: a::c, where c is a new constant obtained from c0::c1
 */
static inline int
applies_const_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1))
         && BTOR_IS_CONCAT_NODE (real_e0)
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (real_e0)->e[1]);
}

static inline BtorNode *
apply_const_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_concat (btor, e0, e1));

  BtorNode *result, *tmp, *real_e0;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);

  BTOR_INC_REC_RW_CALL (btor);
  tmp =
      rewrite_concat_exp (btor, BTOR_COND_INVERT_NODE (e0, real_e0->e[1]), e1);
  result =
      rewrite_concat_exp (btor, BTOR_COND_INVERT_NODE (e0, real_e0->e[0]), tmp);
  btor_release_exp (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match:  a[u1:l1]::a[u2:l2], where l1 = u2 + 1
 * result: a[u1:l2]
 */
static inline int
applies_slice_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->options.rewrite_level.val > 0
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_INVERTED_NODE (e0) == BTOR_IS_INVERTED_NODE (e1)
         && BTOR_IS_SLICE_NODE (real_e0) && BTOR_IS_SLICE_NODE (real_e1)
         && real_e0->e[0] == real_e1->e[0]
         && btor_slice_get_lower (real_e0)
                == btor_slice_get_upper (real_e1) + 1;
}

static inline BtorNode *
apply_slice_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_slice_concat (btor, e0, e1));

  BtorNode *result, *real_e0;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (btor,
                              real_e0->e[0],
                              btor_slice_get_upper (real_e0),
                              btor_slice_get_lower (e1));
  BTOR_DEC_REC_RW_CALL (btor);
  result = BTOR_COND_INVERT_NODE (e0, result);
  return result;
}

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor->options.rewrite_level.val > 2 &&
      !BTOR_IS_INVERTED_NODE (e0) &&
      e0->kind == BTOR_BCOND_NODE &&
      (btor_concat_simplifiable (e0->e[1]) ||
       btor_concat_simplifiable (e0->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_concat_exp (btor, e0->e[1], e1);
      e = btor_concat_exp (btor, e0->e[2], e1);
      result = btor_cond_exp (btor, e0->e[0], t, e);
      btor_release_exp (btor, e);
      btor_release_exp (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor->options.rewrite_level.val > 2 &&
      BTOR_IS_INVERTED_NODE (e0) &&
      (real_e0 = BTOR_REAL_ADDR_NODE (e0))->kind == BTOR_BCOND_NODE &&
      (btor_concat_simplifiable (real_e0->e[1]) ||
       btor_concat_simplifiable (real_e0->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_concat_exp (btor, BTOR_INVERT_NODE (real_e0->e[1]), e1);
      e = btor_concat_exp (btor, BTOR_INVERT_NODE (real_e0->e[2]), e1);
      result = btor_cond_exp (btor, real_e0->e[0], t, e);
      btor_release_exp (btor, e);
      btor_release_exp (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor->options.rewrite_level.val > 2 &&
      !BTOR_IS_INVERTED_NODE (e1) &&
      e1->kind == BTOR_BCOND_NODE &&
      (btor_concat_simplifiable (e1->e[1]) ||
       btor_concat_simplifiable (e1->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_concat_exp (btor, e0, e1->e[1]);
      e = btor_concat_exp (btor, e0, e1->e[2]);
      result = btor_cond_exp (btor, e1->e[0], t, e);
      btor_release_exp (btor, e);
      btor_release_exp (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor->options.rewrite_level.val > 2 &&
      BTOR_IS_INVERTED_NODE (e1) &&
      (real_e1 = BTOR_REAL_ADDR_NODE (e1))->kind == BTOR_BCOND_NODE &&
      (btor_concat_simplifiable (real_e1->e[1]) ||
       btor_concat_simplifiable (real_e1->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_concat_exp (btor, e0, BTOR_INVERT_NODE (real_e1->e[1]));
      e = btor_concat_exp (btor, e0, BTOR_INVERT_NODE (real_e1->e[2]));
      result = btor_cond_exp (btor, real_e1->e[0], t, e);
      btor_release_exp (btor, e);
      btor_release_exp (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

/* match: (a & b)::c
 * result: (a::c) & (b::c)
 */
static inline int
applies_and_lhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_e0;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e0)
         && (concat_simplifiable (real_e0->e[0])
             || concat_simplifiable (real_e0->e[1]));
}

static inline BtorNode *
apply_and_lhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_lhs_concat (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  BTOR_INC_REC_RW_CALL (btor);
  left =
      rewrite_concat_exp (btor, real_e0->e[0], BTOR_COND_INVERT_NODE (e0, e1));
  right =
      rewrite_concat_exp (btor, real_e0->e[1], BTOR_COND_INVERT_NODE (e0, e1));
  result = btor_and_exp (btor, left, right);
  result = BTOR_COND_INVERT_NODE (e0, result);
  btor_release_exp (btor, right);
  btor_release_exp (btor, left);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: a::(b & c)
 * result: (a::b) & (a::c)
 */
static inline int
applies_and_rhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  BtorNode *real_e1;
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && BTOR_IS_AND_NODE (real_e1)
         && (concat_simplifiable (real_e1->e[0])
             || concat_simplifiable (real_e1->e[1]));
}

static inline BtorNode *
apply_and_rhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_rhs_concat (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e1;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left =
      rewrite_concat_exp (btor, BTOR_COND_INVERT_NODE (e1, e0), real_e1->e[0]);
  right =
      rewrite_concat_exp (btor, BTOR_COND_INVERT_NODE (e1, e0), real_e1->e[1]);
  result = btor_and_exp (btor, left, right);
  result = BTOR_COND_INVERT_NODE (e1, result);
  btor_release_exp (btor, right);
  btor_release_exp (btor, left);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* SLL rules */

/* match:  a << c, where c is a constant
 * result: a[len(a)-val(c)-1:0]::0
 */
static inline int
applies_const_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1))
         && btor_get_exp_width (btor, e1) <= 32;
}

static inline BtorNode *
apply_const_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_sll (btor, e0, e1));

  unsigned shiftlen;
  char *bits, *len;
  BtorNode *result, *real_e0, *real_e1, *pad, *slice;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  if (is_const_zero_exp (btor, e1)) return btor_copy_exp (btor, e0);

  bits = btor_strdup (btor->mm, btor_const_get_bits (real_e1));
  if (BTOR_IS_INVERTED_NODE (e1)) btor_invert_const (btor->mm, bits);
  len = btor_const_to_decimal (btor->mm, bits);

  shiftlen = atoi (len);
  btor_freestr (btor->mm, bits);
  btor_freestr (btor->mm, len);

  assert (shiftlen > 0);
  assert (shiftlen < btor_get_exp_width (btor, real_e0));
  BTOR_INC_REC_RW_CALL (btor);
  pad   = btor_zero_exp (btor, shiftlen);
  slice = rewrite_slice_exp (
      btor, e0, btor_get_exp_width (btor, real_e0) - shiftlen - 1, 0);
  result = rewrite_concat_exp (btor, slice, pad);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, pad);
  btor_release_exp (btor, slice);
  assert (BTOR_REAL_ADDR_NODE (result)->sort_id == real_e0->sort_id);
  return result;
}

/* SRL rules */

/* match:  a >> c, where c is a constant
 * result: 0::a[len(a)-1:val(c)]
 */
static inline int
applies_const_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1))
         && btor_get_exp_width (btor, e1) <= 32;
}

static inline BtorNode *
apply_const_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_srl (btor, e0, e1));

  unsigned shiftlen;
  char *bits, *len;
  BtorNode *result, *real_e0, *real_e1, *pad, *slice;

  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  if (is_const_zero_exp (btor, e1)) return btor_copy_exp (btor, e0);

  bits = btor_strdup (btor->mm, btor_const_get_bits (real_e1));
  if (BTOR_IS_INVERTED_NODE (e1)) btor_invert_const (btor->mm, bits);
  len = btor_const_to_decimal (btor->mm, bits);

  shiftlen = atoi (len);
  btor_freestr (btor->mm, bits);
  btor_freestr (btor->mm, len);

  assert (shiftlen > 0);
  assert (shiftlen < btor_get_exp_width (btor, real_e0));
  BTOR_INC_REC_RW_CALL (btor);
  pad   = btor_zero_exp (btor, shiftlen);
  slice = rewrite_slice_exp (
      btor, e0, btor_get_exp_width (btor, real_e0) - 1, shiftlen);
  result = rewrite_concat_exp (btor, pad, slice);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, pad);
  btor_release_exp (btor, slice);
  assert (BTOR_REAL_ADDR_NODE (result)->sort_id == real_e0->sort_id);
  return result;
}

/* APPLY rules */

/* match:  (\lambda x . t)(a), where term t does not contain param x
 * result: t
 */
static inline int
applies_const_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (e0))
         && !BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (e0))->parameterized;
}

static inline BtorNode *
apply_const_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_lambda_apply (btor, e0, e1));
  (void) e1;
  return btor_copy_exp (btor, BTOR_LAMBDA_GET_BODY (BTOR_REAL_ADDR_NODE (e0)));
}

/* match:  (\lambda x . x)(a)
 * result: a
 */
static inline int
applies_param_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_PARAM_NODE (
                BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (e0)));
}

static inline BtorNode *
apply_param_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_param_lambda_apply (btor, e0, e1));

  BtorNode *result, *body;

  body = BTOR_LAMBDA_GET_BODY (e0);
  btor_assign_args (btor, e0, e1);
  result = btor_copy_exp (
      btor, btor_param_cur_assignment (BTOR_REAL_ADDR_NODE (body)));
  btor_unassign_params (btor, e0);
  result = BTOR_COND_INVERT_NODE (body, result);
  return result;
}

/* match:  (\lambda x . f(x))(a)
 * result: f(a)
 */
static inline int
applies_apply_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_body;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_APPLY_NODE (
                (real_body = BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (e0))))
         && !real_body->e[0]->parameterized;
}

static inline BtorNode *
apply_apply_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_apply_apply (btor, e0, e1));

  BtorNode *result, *real_body, *body;

  body      = BTOR_LAMBDA_GET_BODY (e0);
  real_body = BTOR_REAL_ADDR_NODE (body);
  BTOR_INC_REC_RW_CALL (btor);
  btor_assign_args (btor, e0, e1);
  e1 = btor_beta_reduce_bounded (btor, real_body->e[1], 1);
  btor_unassign_params (btor, e0);
  e0 = btor_simplify_exp (btor, real_body->e[0]);
  assert (BTOR_IS_FUN_NODE (e0));
  assert (BTOR_IS_ARGS_NODE (e1));
  result = rewrite_apply_exp (btor, e0, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, e1);
  result = BTOR_COND_INVERT_NODE (body, result);
  return result;
}

/*
 *
 * propagate apply over parameterized bv conditionals
 */
static inline int
applies_prop_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return BTOR_IS_LAMBDA_NODE (BTOR_REAL_ADDR_NODE (e0))
         && BTOR_IS_BV_COND_NODE (
                BTOR_REAL_ADDR_NODE (BTOR_LAMBDA_GET_BODY (e0)));
  ;
}

static inline BtorNode *
apply_prop_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_prop_apply (btor, e0, e1));

  BtorNode *result, *cur_fun, *next_fun, *cur_args, *e_cond, *array, *args;
  BtorNode *beta_cond, *cur_cond, *real_cur_cond;
  BtorNode *cur_branch, *real_cur_branch;
  BtorNode *index, *write_index, *value;
  int propagations, apply_propagations, done, inv_result;
  int inv_result_tmp;

  done               = 0;
  result             = 0;
  propagations       = 0;
  apply_propagations = 0;
  inv_result         = 0;
  inv_result_tmp     = 0;

  cur_fun  = e0;
  cur_args = btor_copy_exp (btor, e1);

  /* try to propagate apply over bv conditionals were conditions evaluate to
   * true if beta reduced with 'cur_args'. */
  cur_cond = BTOR_IS_LAMBDA_NODE (cur_fun) ? BTOR_LAMBDA_GET_BODY (cur_fun) : 0;
  while (!done && BTOR_IS_LAMBDA_NODE (cur_fun) && !cur_fun->parameterized
         && !cur_args->parameterized
         && (real_cur_cond = BTOR_REAL_ADDR_NODE (cur_cond))
         && BTOR_IS_BV_COND_NODE (real_cur_cond)
         /* if the condition is not parameterized the check was already done
          * while creating 'cur_cond' */
         && BTOR_REAL_ADDR_NODE (real_cur_cond->e[0])->parameterized
         && propagations++ < BTOR_APPLY_PROPAGATION_LIMIT)
  {
    assert (cur_cond);
    assert (BTOR_IS_REGULAR_NODE (cur_fun));
    assert (BTOR_IS_REGULAR_NODE (cur_args));
    assert (!result);

    next_fun = 0;
    /* optimization for lambdas representing array writes */
    if (is_write_exp (cur_fun, &array, &write_index, &value))
    {
      index = cur_args->e[0];
      /* found value at 'index' */
      if (write_index == index)
      {
        result = btor_copy_exp (btor, value);
        done   = 1;
      }
      /* propagate down to 'array' */
      else if (is_always_unequal (btor, write_index, index))
      {
        next_fun = array;
        apply_propagations++;
      }
      else
        goto REWRITE_APPLY_GENERAL_CASE;
    }
    /* more general case: any lambda with bv cond as body */
    else
    {
    REWRITE_APPLY_GENERAL_CASE:
      e_cond = real_cur_cond->e[0];

      if (!BTOR_REAL_ADDR_NODE (e_cond)->parameterized) break;

      /* 'inv_result_tmp' indicates if the result obtained from the
       * current propagation path needs to be inverted. in case we really
       * find a result, 'inv_result' will be inverted w.r.t.
       * 'inv_result_tmp'. */
      if (BTOR_IS_INVERTED_NODE (cur_cond)) inv_result_tmp = !inv_result_tmp;

      btor_assign_args (btor, cur_fun, cur_args);
      beta_cond = btor_beta_reduce_bounded (btor, e_cond, 1);
      /* condition of bv cond is either true or false */
      if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (beta_cond)))
      {
        if (is_true_cond (beta_cond))
          cur_branch = real_cur_cond->e[1];
        else
          cur_branch = real_cur_cond->e[2];

        real_cur_branch = BTOR_REAL_ADDR_NODE (cur_branch);
        /* branch not parameterized, we found a result */
        if (!real_cur_branch->parameterized)
        {
          result = btor_copy_exp (btor, real_cur_branch);
          done   = 1;
          goto HAVE_RESULT_CHECK_INVERTED;
        }
        else if (BTOR_IS_PARAM_NODE (real_cur_branch))
        {
          if ((value = btor_param_cur_assignment (real_cur_branch)))
            result = btor_copy_exp (btor, value);
          else
            result = btor_copy_exp (btor, real_cur_branch);
          done = 1;
          goto HAVE_RESULT_CHECK_INVERTED;
        }
        /* propagate down to next function */
        else if (BTOR_IS_APPLY_NODE (real_cur_branch))
        {
          args = btor_beta_reduce_bounded (btor, real_cur_branch->e[1], 1);
          assert (BTOR_IS_REGULAR_NODE (args));
          assert (BTOR_IS_ARGS_NODE (args));
          /* nested lambda */
          if (real_cur_branch->e[0]->parameterized)
          {
            btor_assign_args (btor, real_cur_branch->e[0], args);
            result = btor_beta_reduce_bounded (btor, real_cur_branch->e[0], 1);
            btor_unassign_params (btor, real_cur_branch->e[0]);
            assert (!BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (result)));

            /* propagate down to 'next_fun' */
            if (BTOR_IS_APPLY_NODE (BTOR_REAL_ADDR_NODE (result)))
            {
              next_fun = BTOR_REAL_ADDR_NODE (result)->e[0];
              /* result is not needed here as it may be further
               * rewritten */
              btor_release_exp (btor, result);
              result = 0;
            }
            else
              done = 1;
          }
          /* propagate down to 'next_fun' */
          else
          {
            next_fun = real_cur_branch->e[0];
            assert (BTOR_IS_FUN_NODE (next_fun));
          }

          /* set arguments for new functin application */
          btor_release_exp (btor, cur_args);
          cur_args = args;

        HAVE_RESULT_CHECK_INVERTED:
          assert (result || next_fun);
          assert (!result || !next_fun);
          assert (!done || result);
          /* at this point we already have a result, which is either
           * a value obtained by beta reducing 'cur_fun' or a
           * function application on 'next_fun' with 'cur_args'.
           * in the latter case, we try to further rewrite the function
           * application. */

          /* if 'cur_branch' is inverted we need to invert the result */
          if (BTOR_IS_INVERTED_NODE (cur_branch))
            inv_result_tmp = !inv_result_tmp;

          /* we got a result, we can savely set 'inv_result' */
          if (inv_result_tmp)
          {
            inv_result     = !inv_result;
            inv_result_tmp = 0;
          }
          apply_propagations++;
        }
        /* check if we can further propagate down along a conditional */
        else if (BTOR_IS_BV_COND_NODE (real_cur_branch))
        {
          cur_cond = cur_branch;
        }
        /* cur_branch is some other parameterized term that we don't
         * expand */
        // TODO (ma): try to expand more parameterized terms?
        else
          goto REWRITE_APPLY_NO_RESULT_DONE;
      }
      else
      {
      REWRITE_APPLY_NO_RESULT_DONE:
        assert (!result);
        done = 1;
      }
      btor_unassign_params (btor, cur_fun);
      btor_release_exp (btor, beta_cond);
    }

    if (next_fun)
    {
      cur_fun = next_fun;
      cur_cond =
          BTOR_IS_LAMBDA_NODE (cur_fun) ? BTOR_LAMBDA_GET_BODY (cur_fun) : 0;
    }
    assert (!result || done);
  }

  /* check if apply was propagated down to 'cur_fun' */
  if (!result && cur_fun != e0)
    result = btor_apply_exp_node (btor, cur_fun, cur_args);

  btor_release_exp (btor, cur_args);

  if (result && inv_result) result = BTOR_INVERT_NODE (result);

  btor->stats.apply_props_construct += apply_propagations;
  return result;
}

/* LAMBDA rules */

#if 0 
// TODO (ma): this rule cannot be applied yet as it may produce lambdas with
//            different sorts
/* match: (\lambda j . (\lambda k . t)(j))
 * result: \lambda k . t
 */
static inline int
applies_lambda_lambda (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return !BTOR_IS_INVERTED_NODE (e1)
	 && BTOR_IS_APPLY_NODE (e1)
	 && !e1->e[0]->parameterized
	 && e1->e[1]->arity == 1
	 && e1->e[1]->e[0] == e0;
}

static inline BtorNode *
apply_lambda_lambda (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_copy_exp (btor, e1->e[0]);
}
#endif

/* COND rules */

/* match: c ? a : a
 * result: a
 */
static inline int
applies_equal_branches_cond (Btor *btor,
                             BtorNode *e0,
                             BtorNode *e1,
                             BtorNode *e2)
{
  (void) btor;
  (void) e0;
  return e1 == e2;
}

static inline BtorNode *
apply_equal_branches_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_equal_branches_cond (btor, e0, e1, e2));
  (void) e0;
  (void) e2;
  return btor_copy_exp (btor, e1);
}

/* match: c ? a : b, where c is a constant
 * result: a if c is true, and b otherwise
 */
static inline int
applies_const_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (BTOR_IS_REGULAR_NODE (e0));
  (void) btor;
  (void) e1;
  (void) e2;
  return BTOR_IS_BV_CONST_NODE (e0);
}

static inline BtorNode *
apply_const_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_const_cond (btor, e0, e1, e2));
  if (btor_const_get_bits (e0)[0] == '1') return btor_copy_exp (btor, e1);
  return btor_copy_exp (btor, e2);
}

/* match: c0 ? (c0 ? a : b) : c
 * result: c0 ? a : c
 */
static inline int
applies_cond_if_dom_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e2;
  BtorNode *real_e1;
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e1) && real_e1->e[0] == e0;
}

static inline BtorNode *
apply_cond_if_dom_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_cond_if_dom_cond (btor, e0, e1, e2));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_cond_exp (
      btor, e0, BTOR_COND_INVERT_NODE (e1, BTOR_REAL_ADDR_NODE (e1)->e[1]), e2);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: c0 ? (c1 ? a : b) : a
 * result: c0 AND ~c1 ? a : b
 */
static inline int
applies_cond_if_merge_if_cond (Btor *btor,
                               BtorNode *e0,
                               BtorNode *e1,
                               BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e1;
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_COND_INVERT_NODE (e1, real_e1->e[1]) == e2;
}

static inline BtorNode *
apply_cond_if_merge_if_cond (Btor *btor,
                             BtorNode *e0,
                             BtorNode *e1,
                             BtorNode *e2)
{
  assert (applies_cond_if_merge_if_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e10, *e12, *real_e1;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  e10     = real_e1->e[0];
  e12     = BTOR_COND_INVERT_NODE (e1, real_e1->e[2]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e0, BTOR_INVERT_NODE (e10));
  result = rewrite_cond_exp (btor, tmp, e12, e2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: c0 ? (c1 ? b : a) : a
 * result: c0 AND c1 ? b : a
 */
static inline int
applies_cond_if_merge_else_cond (Btor *btor,
                                 BtorNode *e0,
                                 BtorNode *e1,
                                 BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e1;
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e1)
         && BTOR_COND_INVERT_NODE (e1, real_e1->e[2]) == e2;
}

static inline BtorNode *
apply_cond_if_merge_else_cond (Btor *btor,
                               BtorNode *e0,
                               BtorNode *e1,
                               BtorNode *e2)
{
  assert (applies_cond_if_merge_else_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e10, *e11, *real_e1;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  e10     = real_e1->e[0];
  e11     = BTOR_COND_INVERT_NODE (e1, real_e1->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e0, e10);
  result = rewrite_cond_exp (btor, tmp, e11, e2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: c0 ? a : (c0 ? b : c)
 * result: c0 ? a : c
 */
static inline int
applies_cond_else_dom_cond (Btor *btor,
                            BtorNode *e0,
                            BtorNode *e1,
                            BtorNode *e2)
{
  (void) e1;
  BtorNode *real_e2;
  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e2) && real_e2->e[0] == e0;
}

static inline BtorNode *
apply_cond_else_dom_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_cond_else_dom_cond (btor, e0, e1, e2));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_cond_exp (
      btor, e0, e1, BTOR_COND_INVERT_NODE (e2, BTOR_REAL_ADDR_NODE (e2)->e[2]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* match: c0 ? a : (c1 ? a : b)
 * result: ~c0 AND ~c1 ? b : a
 */
static inline int
applies_cond_else_merge_if_cond (Btor *btor,
                                 BtorNode *e0,
                                 BtorNode *e1,
                                 BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e2;
  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e2)
         && BTOR_COND_INVERT_NODE (e2, real_e2->e[1]) == e1;
}

static inline BtorNode *
apply_cond_else_merge_if_cond (Btor *btor,
                               BtorNode *e0,
                               BtorNode *e1,
                               BtorNode *e2)
{
  assert (applies_cond_else_merge_if_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e20, *e22, *real_e2;

  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  e20     = real_e2->e[0];
  e22     = BTOR_COND_INVERT_NODE (e2, real_e2->e[2]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp = rewrite_and_exp (btor, BTOR_INVERT_NODE (e0), BTOR_INVERT_NODE (e20));
  result = rewrite_cond_exp (btor, tmp, e22, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match: c0 ? a : (c1 ? b : a)
 * result: ~c0 AND c1 ? b : a
 */
static inline int
applies_cond_else_merge_else_cond (Btor *btor,
                                   BtorNode *e0,
                                   BtorNode *e1,
                                   BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e2;
  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && BTOR_IS_BV_COND_NODE (real_e2)
         && BTOR_COND_INVERT_NODE (e2, real_e2->e[2]) == e1;
}

static inline BtorNode *
apply_cond_else_merge_else_cond (Btor *btor,
                                 BtorNode *e0,
                                 BtorNode *e1,
                                 BtorNode *e2)
{
  assert (applies_cond_else_merge_else_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e20, *e21, *real_e2;

  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  e20     = real_e2->e[0];
  e21     = BTOR_COND_INVERT_NODE (e2, real_e2->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, BTOR_INVERT_NODE (e0), e20);
  result = rewrite_cond_exp (btor, tmp, e21, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  c ? a : b, where len(a) = 1
 * result: (~c OR a) AND (c OR b)
 */
static inline int
applies_bool_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  (void) e2;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_get_exp_width (btor, e1) == 1;
}

static inline BtorNode *
apply_bool_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_bool_cond (btor, e0, e1, e2));

  BtorNode *tmp1, *tmp2, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = btor_or_exp (btor, BTOR_INVERT_NODE (e0), e1);
  tmp2   = btor_or_exp (btor, e0, e2);
  result = rewrite_and_exp (btor, tmp1, tmp2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp1);
  btor_release_exp (btor, tmp2);
  return result;
}

/* match:  c ? (a + 1) : a
 * match:  c ? (1 + a) : a
 * result: a + 0::c
 */
static inline int
applies_add_if_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && !BTOR_IS_INVERTED_NODE (e1)
         && BTOR_IS_ADD_NODE (e1)
         && ((e1->e[0] == e2 && is_const_one_exp (btor, e1->e[1]))
             || (e1->e[1] == e2 && is_const_one_exp (btor, e1->e[0])));
}

static inline BtorNode *
apply_add_if_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_add_if_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = btor_uext_exp (btor, e0, btor_get_exp_width (btor, e1) - 1);
  result = rewrite_add_exp (btor, e2, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  c ? a : (a + 1)
 * match:  c ? a : (1 + a)
 * result: a + 0::c
 */
static inline int
applies_add_else_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && !BTOR_IS_INVERTED_NODE (e2)
         && BTOR_IS_ADD_NODE (e2)
         && ((e2->e[0] == e1 && is_const_one_exp (btor, e2->e[1]))
             || (e2->e[1] == e1 && is_const_one_exp (btor, e2->e[0])));
}

static inline BtorNode *
apply_add_else_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_add_else_cond (btor, e0, e1, e2));
  (void) e2;

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp = btor_uext_exp (
      btor, BTOR_INVERT_NODE (e0), btor_get_exp_width (btor, e1) - 1);
  result = rewrite_add_exp (btor, e1, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  c ? (a::b) : (a::d)
 * result: a :: (c ? b : d)
 *
 * match:  c ? (a::b) : (d::b)
 * result: (c ? a : d) :: b
 */
static inline int
applies_concat_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  int result;
  BtorNode *real_e1, *real_e2, *e10, *e11, *e20, *e21;

  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  result  = btor->options.rewrite_level.val > 2
           && btor->rec_rw_calls < BTOR_REC_RW_BOUND
           && BTOR_IS_CONCAT_NODE (real_e1) && BTOR_IS_CONCAT_NODE (real_e2);

  if (!result) return result;

  e10 = BTOR_COND_INVERT_NODE (e1, real_e1->e[0]);
  e11 = BTOR_COND_INVERT_NODE (e1, real_e1->e[1]);
  e20 = BTOR_COND_INVERT_NODE (e2, real_e2->e[0]);
  e21 = BTOR_COND_INVERT_NODE (e2, real_e2->e[1]);
  return (e10 == e20 || e11 == e21);
}

static inline BtorNode *
apply_concat_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_concat_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp1, *tmp2, *real_e1, *real_e2, *e10, *e11, *e20, *e21;
  real_e1 = BTOR_REAL_ADDR_NODE (e1);
  real_e2 = BTOR_REAL_ADDR_NODE (e2);
  e10     = BTOR_COND_INVERT_NODE (e1, real_e1->e[0]);
  e11     = BTOR_COND_INVERT_NODE (e1, real_e1->e[1]);
  e20     = BTOR_COND_INVERT_NODE (e2, real_e2->e[0]);
  e21     = BTOR_COND_INVERT_NODE (e2, real_e2->e[1]);

  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = rewrite_cond_exp (btor, e0, e10, e20);
  tmp2   = rewrite_cond_exp (btor, e0, e11, e21);
  result = rewrite_concat_exp (btor, tmp1, tmp2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp1);
  btor_release_exp (btor, tmp2);
  return result;
}

/* match:  c ? a OP b : a OP d, where OP is either +, &, *, /, %
 * result: a OP (c ? b : d)
 */
static inline int
applies_op_lhs_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e1) && !BTOR_IS_INVERTED_NODE (e2)
         && e1->kind == e2->kind
         && (BTOR_IS_ADD_NODE (e1) || BTOR_IS_AND_NODE (e1)
             || BTOR_IS_MUL_NODE (e1) || BTOR_IS_UDIV_NODE (e1)
             || BTOR_IS_UREM_NODE (e1))
         && e1->e[0] == e2->e[0];
}

static inline BtorNode *
apply_op_lhs_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_op_lhs_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_cond_exp (btor, e0, e1->e[1], e2->e[1]);
  result = btor_rewrite_binary_exp (btor, e1->kind, e1->e[0], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  c ? a OP b : d OP b, where OP is either +, &, *, /, %
 * result: (c ? a : d) OP b
 */
static inline int
applies_op_rhs_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e1) && !BTOR_IS_INVERTED_NODE (e2)
         && e1->kind == e2->kind
         && (BTOR_IS_ADD_NODE (e1) || BTOR_IS_AND_NODE (e1)
             || BTOR_IS_MUL_NODE (e1) || BTOR_IS_UDIV_NODE (e1)
             || BTOR_IS_UREM_NODE (e1))
         && e1->e[1] == e2->e[1];
}

static inline BtorNode *
apply_op_rhs_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_op_rhs_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_cond_exp (btor, e0, e1->e[0], e2->e[0]);
  result = btor_rewrite_binary_exp (btor, e1->kind, tmp, e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  c ? a OP b : d OP a, where OP is either +, &, *
 * result: a OP (c ? b : d)
 */
static inline int
applies_comm_op_1_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e1) && !BTOR_IS_INVERTED_NODE (e2)
         && e1->kind == e2->kind
         && (BTOR_IS_ADD_NODE (e1) || BTOR_IS_AND_NODE (e1)
             || BTOR_IS_MUL_NODE (e1))
         && e1->e[0] == e2->e[1];
}

static inline BtorNode *
apply_comm_op_1_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_comm_op_1_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_cond_exp (btor, e0, e1->e[1], e2->e[0]);
  result = btor_rewrite_binary_exp (btor, e1->kind, e1->e[0], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

/* match:  c ? a OP b : b OP d, where OP is either +, &, *
 * result: b OP (c ? a : d)
 */
static inline int
applies_comm_op_2_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->options.rewrite_level.val > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !BTOR_IS_INVERTED_NODE (e1) && !BTOR_IS_INVERTED_NODE (e2)
         && e1->kind == e2->kind
         && (BTOR_IS_ADD_NODE (e1) || BTOR_IS_AND_NODE (e1)
             || BTOR_IS_MUL_NODE (e1))
         && e1->e[1] == e2->e[0];
}

static inline BtorNode *
apply_comm_op_2_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_comm_op_2_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_cond_exp (btor, e0, e1->e[0], e2->e[1]);
  result = btor_rewrite_binary_exp (btor, e1->kind, e1->e[1], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_release_exp (btor, tmp);
  return result;
}

#if 0
/* match:
 * result:
 */
static inline int
applies_cond (Btor * btor, BtorNode * e0, BtorNode * e1, BtorNode * e2)
{
}

static inline BtorNode * 
apply_cond (Btor * btor, BtorNode * e0, BtorNode * e1, BtorNode * e2)
{
  assert (applies_cond (btor, e0, e1, e2));

}
#endif

/* -------------------------------------------------------------------------- */
/* normalizers */

static void
normalize_bin_comm_ass_exp (Btor *btor,
                            BtorNode *e0,
                            BtorNode *e1,
                            BtorNode **e0_norm,
                            BtorNode **e1_norm)
{
  assert (btor);
  assert (btor->options.rewrite_level.val > 2);
  assert (e0);
  assert (e1);
  assert (!BTOR_REAL_ADDR_NODE (e0)->simplified);
  assert (!BTOR_REAL_ADDR_NODE (e1)->simplified);
  assert (e0_norm);
  assert (e1_norm);
  assert (!BTOR_IS_INVERTED_NODE (e0));
  assert (!BTOR_IS_INVERTED_NODE (e1));
  assert (BTOR_IS_ADD_NODE (e0) || BTOR_IS_AND_NODE (e0)
          || BTOR_IS_MUL_NODE (e0));
  assert (e0->kind == e1->kind);

  int i;
  BtorNodeKind kind;
  BtorNode *cur, *result, *temp, *common;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorPtrHashTable *left, *right, *comm;
  BtorPtrHashBucket *b;
  BtorHashTableIterator it;

  mm    = btor->mm;
  kind  = e0->kind;
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
    if (!BTOR_IS_INVERTED_NODE (cur) && cur->kind == kind)
    {
      BTOR_PUSH_STACK (mm, stack, cur->e[1]);
      BTOR_PUSH_STACK (mm, stack, cur->e[0]);
    }
    else
    {
      b = btor_find_in_ptr_hash_table (left, cur);
      if (!b)
        btor_insert_in_ptr_hash_table (left, cur)->data.asInt = 1;
      else
        b->data.asInt++;
    }
  } while (!BTOR_EMPTY_STACK (stack));

  BTOR_PUSH_STACK (mm, stack, e1);
  do
  {
    cur = BTOR_POP_STACK (stack);
    if (!BTOR_IS_INVERTED_NODE (cur) && cur->kind == kind)
    {
      BTOR_PUSH_STACK (mm, stack, cur->e[1]);
      BTOR_PUSH_STACK (mm, stack, cur->e[0]);
    }
    else
    {
      b = btor_find_in_ptr_hash_table (left, cur);
      if (b)
      {
        /* we found one common operand */

        /* remove operand from left */
        if (b->data.asInt > 1)
          b->data.asInt--;
        else
        {
          assert (b->data.asInt == 1);
          btor_remove_from_ptr_hash_table (left, cur, 0, 0);
        }

        /* insert into common table */
        b = btor_find_in_ptr_hash_table (comm, cur);
        if (!b)
          btor_insert_in_ptr_hash_table (comm, cur)->data.asInt = 1;
        else
          b->data.asInt++;
      }
      else
      {
        /* operand is not common */
        b = btor_find_in_ptr_hash_table (right, cur);
        if (!b)
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

  if (kind == BTOR_AND_NODE)
    btor->stats.ands_normalized++;
  else if (kind == BTOR_ADD_NODE)
    btor->stats.adds_normalized++;
  else
  {
    assert (kind == BTOR_MUL_NODE);
    btor->stats.muls_normalized++;
  }

  assert (comm->count >= 2u);

  /* normalize common nodes */
  BTOR_INIT_STACK (stack);
  b = comm->first;
  while (b)
  {
    cur = b->key;
    for (i = 0; i < b->data.asInt; i++) BTOR_PUSH_STACK (mm, stack, cur);
    b = b->next;
  }

  qsort (
      stack.start, BTOR_COUNT_STACK (stack), sizeof (BtorNode *), cmp_node_id);

  common = btor_copy_exp (btor, BTOR_PEEK_STACK (stack, 0));
  for (i = 1; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur  = BTOR_PEEK_STACK (stack, i);
    temp = btor_rewrite_binary_exp (btor, kind, common, cur);
    btor_release_exp (btor, common);
    common = temp;
  }
  BTOR_RELEASE_STACK (mm, stack);

#if 0
  /* normalize left side */
  result = btor_copy_exp (btor, common);
  init_node_hash_table_iterator (&it, left);
  while (has_next_node_hash_table_iterator (&it))
    {
      b = it.bucket;
      cur = next_node_hash_table_iterator (&it);
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
  init_node_hash_table_iterator (&it, right);
  while (has_next_node_hash_table_iterator (&it))
    {
      b = it.bucket;
      cur = next_node_hash_table_iterator (&it);
      for (i = 0; i < b->data.asInt; i++)
	{
	  temp = fptr (btor, result, cur);
	  btor_release_exp (btor, result);
	  result = temp;
	}
    }
  *e1_norm = result;
#else
  /* Bubble up common part.
   */
  result = 0;
  init_node_hash_table_iterator (&it, left);
  while (has_next_node_hash_table_iterator (&it))
  {
    b   = it.bucket;
    cur = next_node_hash_table_iterator (&it);
    for (i = 0; i < b->data.asInt; i++)
    {
      if (result)
      {
        temp = btor_rewrite_binary_exp (btor, kind, result, cur);
        btor_release_exp (btor, result);
        result = temp;
      }
      else
        result = btor_copy_exp (btor, cur);
    }
  }

  if (result)
  {
    temp = btor_rewrite_binary_exp (btor, kind, common, result);
    btor_release_exp (btor, result);
    result = temp;
  }
  else
    result = btor_copy_exp (btor, common);

  *e0_norm = result;

  result = 0;
  init_node_hash_table_iterator (&it, right);
  while (has_next_node_hash_table_iterator (&it))
  {
    b   = it.bucket;
    cur = next_node_hash_table_iterator (&it);
    for (i = 0; i < b->data.asInt; i++)
    {
      if (result)
      {
        temp = btor_rewrite_binary_exp (btor, kind, result, cur);
        btor_release_exp (btor, result);
        result = temp;
      }
      else
        result = btor_copy_exp (btor, cur);
    }
  }

  if (result)
  {
    temp = btor_rewrite_binary_exp (btor, kind, common, result);
    btor_release_exp (btor, result);
    result = temp;
  }
  else
    result = btor_copy_exp (btor, common);

  *e1_norm = result;
#endif

  /* clean up */
  btor_release_exp (btor, common);
  btor_delete_ptr_hash_table (left);
  btor_delete_ptr_hash_table (right);
  btor_delete_ptr_hash_table (comm);
}

// TODO (ma): what does this do?
static BtorNode *
find_top_add (Btor *btor, BtorNode *e)
{
  BtorNode *res;
  if (BTOR_IS_INVERTED_NODE (e)) e = BTOR_REAL_ADDR_NODE (e);
  if (e->kind == BTOR_ADD_NODE) return e;
  if (btor->rec_rw_calls >= BTOR_REC_RW_BOUND) return 0;
  res = 0;
  if (e->kind == BTOR_SLICE_NODE)
  {
    BTOR_INC_REC_RW_CALL (btor);
    res = find_top_add (btor, e->e[0]);
    BTOR_DEC_REC_RW_CALL (btor);
  }

  // TODO handle more operators ... (here first)

  return res;
}

// TODO (ma): what does this do?
static BtorNode *
rebuild_top_add (Btor *btor, BtorNode *e, BtorNode *c, BtorNode *r)
{
  assert (!BTOR_IS_INVERTED_NODE (c));

  BtorNode *res, *tmp;

  if (BTOR_IS_INVERTED_NODE (e))
  {
    tmp = rebuild_top_add (btor, BTOR_REAL_ADDR_NODE (e), c, r);
    res = BTOR_INVERT_NODE (tmp);
  }
  else if (e == c)
    res = btor_copy_exp (btor, r);
  else
  {
    // TODO handle more operators ... (then here)
    //
    assert (e->kind == BTOR_SLICE_NODE);
    tmp = rebuild_top_add (btor, e->e[0], c, r);
    res = rewrite_slice_exp (
        btor, tmp, btor_slice_get_upper (e), btor_slice_get_lower (e));
    btor_release_exp (btor, tmp);
  }
  return res;
}

static inline void
normalize_adds_muls_ands (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1, *real_e0, *real_e1, *e0_norm, *e1_norm;

  e0      = *left;
  e1      = *right;
  real_e0 = BTOR_REAL_ADDR_NODE (e0);
  real_e1 = BTOR_REAL_ADDR_NODE (e1);

  if (btor->options.rewrite_level.val > 2 && real_e0->kind == real_e1->kind
      && (BTOR_IS_ADD_NODE (real_e0) || BTOR_IS_MUL_NODE (real_e0)
          || BTOR_IS_AND_NODE (real_e0)))
  {
    normalize_bin_comm_ass_exp (btor, real_e0, real_e1, &e0_norm, &e1_norm);
    e0_norm = BTOR_COND_INVERT_NODE (e0, e0_norm);
    e1_norm = BTOR_COND_INVERT_NODE (e1, e1_norm);
    btor_release_exp (btor, e0);
    btor_release_exp (btor, e1);
    *left  = e0_norm;
    *right = e1_norm;
  }
}

static inline void
normalize_eq (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1, *tmp1, *tmp2, *c0, *c1, *n0, *n1, *add;

  e0 = *left;
  e1 = *right;

  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (BTOR_IS_INVERTED_NODE (e0) && BTOR_IS_INVERTED_NODE (e1))
  {
    e0 = BTOR_INVERT_NODE (e0);
    e1 = BTOR_INVERT_NODE (e1);
  }

  if (btor->options.rewrite_level.val > 1)
  {
    if (BTOR_IS_INVERTED_NODE (e0)
        && BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (e0)))
    {
      e0 = BTOR_INVERT_NODE (e0);
      e1 = BTOR_INVERT_NODE (e1);
    }
    else if (BTOR_IS_INVERTED_NODE (e1)
             && BTOR_IS_BV_VAR_NODE (BTOR_REAL_ADDR_NODE (e1))
             && (BTOR_IS_INVERTED_NODE (e0) || !BTOR_IS_BV_VAR_NODE (e1)))
    {
      tmp1 = BTOR_INVERT_NODE (e0);
      e0   = BTOR_INVERT_NODE (e1);
      e1   = tmp1;
    }
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e0, &e1);

  // TODO (ma): what does this do?
  if (btor->options.rewrite_level.val > 2 && (c0 = find_top_add (btor, e0))
      && (c1 = find_top_add (btor, e1)) && c0->sort_id == c1->sort_id)
  {
    normalize_bin_comm_ass_exp (btor, c0, c1, &n0, &n1);
    tmp1 = rebuild_top_add (btor, e0, c0, n0);
    tmp2 = rebuild_top_add (btor, e1, c1, n1);
    btor_release_exp (btor, n0);
    btor_release_exp (btor, n1);
    btor_release_exp (btor, e0);
    btor_release_exp (btor, e1);
    e0 = tmp1;
    e1 = tmp2;
  }

  // TODO (ma): check if this is also applicable to mul nodes and maybe others?
  /* match: c0 = c1 + b
   * result: c0 - c1 = b
   *
   * also handles negated adds:
   *
   * c0 = ~(c1 + b) -> ~c0 = c1 + b
   */
  if (btor->options.rewrite_level.val > 2
      && ((BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (e0))
           && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1)))
          || (BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (e1))
              && BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0)))))
  {
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e0))
        && BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (e1)))
    {
      c0  = e0;
      add = e1;
    }
    else
    {
      assert (BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (e0)));
      assert (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (e1)));
      c0  = e1;
      add = e0;
    }

    /* c0 = ~(c1 + b) -> ~c0 = c1 + b */
    c0  = BTOR_COND_INVERT_NODE (add, c0);
    add = BTOR_COND_INVERT_NODE (add, add);

    c1 = tmp1 = 0;
    assert (BTOR_IS_REGULAR_NODE (add));
    if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (add->e[0])))
    {
      c1   = add->e[0];
      tmp1 = add->e[1];
    }
    else if (BTOR_IS_BV_CONST_NODE (BTOR_REAL_ADDR_NODE (add->e[1])))
    {
      c1   = add->e[1];
      tmp1 = add->e[0];
    }

    if (tmp1)
    {
      assert (c0);
      assert (c1);
      n0 = btor_copy_exp (btor, tmp1);
      n1 = btor_sub_exp (btor, c0, c1);
      btor_release_exp (btor, e0);
      btor_release_exp (btor, e1);
      e0 = n0;
      e1 = n1;
    }
  }

  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (BTOR_IS_INVERTED_NODE (e0) && BTOR_IS_INVERTED_NODE (e1))
  {
    e0 = BTOR_INVERT_NODE (e0);
    e1 = BTOR_INVERT_NODE (e1);
  }

  *left  = e0;
  *right = e1;
}

static void
normalize_ult (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1, *tmp;

  e0 = *left;
  e1 = *right;

  /* ~a < ~b  is the same as  b < a */
  if (BTOR_IS_INVERTED_NODE (e0) && BTOR_IS_INVERTED_NODE (e1))
  {
    tmp = BTOR_REAL_ADDR_NODE (e1);
    e1  = BTOR_REAL_ADDR_NODE (e0);
    e0  = tmp;
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_and (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and muls on demand */
  if (BTOR_IS_MUL_NODE (BTOR_REAL_ADDR_NODE (e0))
      || BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (e1)))
    normalize_adds_muls_ands (btor, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_add (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize muls and ands on demand */
  if (BTOR_IS_MUL_NODE (BTOR_REAL_ADDR_NODE (e0))
      || BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0)))
    normalize_adds_muls_ands (btor, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_mul (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and ands on demand */
  if (BTOR_IS_ADD_NODE (BTOR_REAL_ADDR_NODE (e0))
      || BTOR_IS_AND_NODE (BTOR_REAL_ADDR_NODE (e0)))
    normalize_adds_muls_ands (btor, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_udiv (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_urem (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_concat (Btor *btor, BtorNode **left, BtorNode **right)
{
  int i;
  BtorMemMgr *mm;
  BtorNode *e0, *e1, *cur, *real_cur, *tmp, *concat;
  BtorNodePtrStack stack, po_stack;

  mm = btor->mm;
  e0 = *left;
  e1 = *right;

  /* normalize concats --> left-associative */
  if (btor->options.rewrite_level.val > 2
      && btor->rec_rw_calls < BTOR_REC_RW_BOUND
      && BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (e1)))
  {
    BTOR_INIT_STACK (po_stack);
    BTOR_PUSH_STACK (mm, po_stack, e0);

    BTOR_INIT_STACK (stack);
    BTOR_PUSH_STACK (mm, stack, e1);
    do
    {
      cur      = BTOR_POP_STACK (stack);
      real_cur = BTOR_REAL_ADDR_NODE (cur);
      if (BTOR_IS_CONCAT_NODE (real_cur))
      {
        BTOR_PUSH_STACK (
            mm, stack, BTOR_COND_INVERT_NODE (cur, real_cur->e[1]));
        BTOR_PUSH_STACK (
            mm, stack, BTOR_COND_INVERT_NODE (cur, real_cur->e[0]));
      }
      else
        BTOR_PUSH_STACK (mm, po_stack, cur);
    } while (!BTOR_EMPTY_STACK (stack));

    BTOR_INC_REC_RW_CALL (btor);
    assert (BTOR_COUNT_STACK (po_stack) >= 3);
    cur    = BTOR_PEEK_STACK (po_stack, 0);
    tmp    = BTOR_PEEK_STACK (po_stack, 1);
    concat = rewrite_concat_exp (btor, cur, tmp);

    for (i = 2; i < BTOR_COUNT_STACK (po_stack) - 1; i++)
    {
      cur = BTOR_PEEK_STACK (po_stack, i);
      assert (!BTOR_IS_CONCAT_NODE (BTOR_REAL_ADDR_NODE (cur)));
      tmp = rewrite_concat_exp (btor, concat, cur);
      btor_release_exp (btor, concat);
      concat = tmp;
    }
    BTOR_DEC_REC_RW_CALL (btor);

    btor_release_exp (btor, e0);
    btor_release_exp (btor, e1);
    e0 = concat;
    e1 = btor_copy_exp (btor, BTOR_TOP_STACK (po_stack));

    BTOR_RELEASE_STACK (mm, stack);
    BTOR_RELEASE_STACK (mm, po_stack);
  }

  *left  = e0;
  *right = e1;
}

static inline void
normalize_cond (Btor *btor, BtorNode **cond, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1, *e2, *tmp;

  e0 = *cond;
  e1 = *left;
  e2 = *right;

  /* normalization: ~e0 ? e1 : e2 is the same as e0 ? e2: e1 */
  if (BTOR_IS_INVERTED_NODE (e0))
  {
    e0  = BTOR_INVERT_NODE (e0);
    tmp = e1;
    e1  = e2;
    e2  = tmp;
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e1, &e2);

  *cond  = e0;
  *left  = e1;
  *right = e2;
}

/* -------------------------------------------------------------------------- */
/* term rewriting functions */

static BtorNode *
rewrite_slice_exp (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  BtorNode *result = 0;

  exp = btor_simplify_exp (btor, exp);
  assert (btor_precond_slice_exp_dbg (btor, exp, upper, lower));

  ADD_RW_RULE (full_slice, exp, upper, lower);
  ADD_RW_RULE (const_slice, exp, upper, lower);
  ADD_RW_RULE (slice_slice, exp, upper, lower);
  ADD_RW_RULE (concat_lower_slice, exp, upper, lower);
  ADD_RW_RULE (concat_upper_slice, exp, upper, lower);
  ADD_RW_RULE (concat_rec_upper_slice, exp, upper, lower);
  ADD_RW_RULE (concat_rec_lower_slice, exp, upper, lower);
  ADD_RW_RULE (concat_rec_slice, exp, upper, lower);
  ADD_RW_RULE (and_slice, exp, upper, lower);
  ADD_RW_RULE (bcond_slice, exp, upper, lower);
  ADD_RW_RULE (zero_lower_slice, exp, upper, lower);

  assert (!result);
  result = btor_slice_exp_node (btor, exp, upper, lower);
DONE:
  assert (result);
  return result;
}

static BtorNode *
rewrite_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int swap_ops = 0;
  BtorNode *tmp, *result = 0;
  BtorNodeKind kind;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_eq_exp_dbg (btor, e0, e1));

  kind = BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (e0)) ? BTOR_FEQ_NODE
                                                     : BTOR_BEQ_NODE;

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_eq (btor, &e0, &e1);

  ADD_RW_RULE (const_binary_exp, kind, e0, e1);
  /* We do not rewrite eq in the boolean case, as we cannot extract the
   * resulting XNOR on top level again and would therefore loose substitutions.
   *
   * Additionally, we do not rewrite eq in the boolean case, as we rewrite
   * a != b to a = ~b and substitute.
   */
  ADD_RW_RULE (true_eq, e0, e1);
  ADD_RW_RULE (false_eq, e0, e1);
  ADD_RW_RULE (bcond_eq, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, kind, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, kind, e0, e1);
SWAP_OPERANDS:
  ADD_RW_RULE (add_left_eq, e0, e1);
  ADD_RW_RULE (add_right_eq, e0, e1);
  ADD_RW_RULE (add_add_1_eq, e0, e1);
  ADD_RW_RULE (add_add_2_eq, e0, e1);
  ADD_RW_RULE (add_add_3_eq, e0, e1);
  ADD_RW_RULE (add_add_4_eq, e0, e1);
  ADD_RW_RULE (bcond_uneq_if_eq, e0, e1);
  ADD_RW_RULE (bcond_uneq_else_eq, e0, e1);
  ADD_RW_RULE (bcond_if_eq, e0, e1);
  ADD_RW_RULE (bcond_else_eq, e0, e1);
  ADD_RW_RULE (distrib_add_mul_eq, e0, e1);
  ADD_RW_RULE (concat_eq, e0, e1);
  //  ADD_RW_RULE (zero_eq_and_eq, e0, e1);

  assert (!result);

  /* no result so far, swap operands */
  if (!swap_ops)
  {
    tmp      = e0;
    e0       = e1;
    e1       = tmp;
    swap_ops = 1;
    goto SWAP_OPERANDS;
  }

  result = btor_eq_exp_node (btor, e1, e0);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_ult (btor, &e0, &e1);

  ADD_RW_RULE (const_binary_exp, BTOR_ULT_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_ULT_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_ULT_NODE, e0, e1);
  ADD_RW_RULE (false_ult, e0, e1);
  ADD_RW_RULE (bool_ult, e0, e1);
  ADD_RW_RULE (concat_upper_ult, e0, e1);
  ADD_RW_RULE (concat_lower_ult, e0, e1);
  ADD_RW_RULE (bcond_ult, e0, e1);

  assert (!result);
  result = btor_ult_exp_node (btor, e0, e1);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int swap_ops = 0;
  BtorNode *tmp, *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_and (btor, &e0, &e1);

  ADD_RW_RULE (const_binary_exp, BTOR_AND_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_AND_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_AND_NODE, e0, e1);
  ADD_RW_RULE (idem1_and, e0, e1);
  ADD_RW_RULE (contr1_and, e0, e1);
  ADD_RW_RULE (contr2_and, e0, e1);
  ADD_RW_RULE (idem2_and, e0, e1);
  ADD_RW_RULE (comm_and, e0, e1);
  ADD_RW_RULE (bool_xnor_and, e0, e1);
  ADD_RW_RULE (resol1_and, e0, e1);
  ADD_RW_RULE (resol2_and, e0, e1);
  ADD_RW_RULE (ult_false_and, e0, e1);
  ADD_RW_RULE (ult_and, e0, e1);
  ADD_RW_RULE (contr_rec_and, e0, e1);
SWAP_OPERANDS:
  ADD_RW_RULE (subsum1_and, e0, e1);
  ADD_RW_RULE (subst1_and, e0, e1);
  ADD_RW_RULE (subst2_and, e0, e1);
  ADD_RW_RULE (subsum2_and, e0, e1);
  ADD_RW_RULE (subst3_and, e0, e1);
  ADD_RW_RULE (subst4_and, e0, e1);
  ADD_RW_RULE (contr3_and, e0, e1);
  ADD_RW_RULE (idem3_and, e0, e1);
  ADD_RW_RULE (const1_and, e0, e1);
  ADD_RW_RULE (const2_and, e0, e1);
  ADD_RW_RULE (concat_and, e0, e1);

  assert (!result);

  /* no result so far, swap operands */
  if (!swap_ops)
  {
    tmp      = e0;
    e0       = e1;
    e1       = tmp;
    swap_ops = 1;
    goto SWAP_OPERANDS;
  }

  result = btor_and_exp_node (btor, e1, e0);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int swap_ops = 0;
  BtorNode *tmp, *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_add (btor, &e0, &e1);

  ADD_RW_RULE (const_binary_exp, BTOR_ADD_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_ADD_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_ADD_NODE, e0, e1);
  ADD_RW_RULE (bool_add, e0, e1);
  ADD_RW_RULE (mult_add, e0, e1);
  ADD_RW_RULE (not_add, e0, e1);
  ADD_RW_RULE (bcond_add, e0, e1);
SWAP_OPERANDS:
  ADD_RW_RULE (neg_add, e0, e1);
  ADD_RW_RULE (zero_add, e0, e1);
  ADD_RW_RULE (const_lhs_add, e0, e1);
  ADD_RW_RULE (const_rhs_add, e0, e1);
  ADD_RW_RULE (const_neg_lhs_add, e0, e1);
  ADD_RW_RULE (const_neg_rhs_add, e0, e1);

  assert (!result);

  /* no result so far, swap operands */
  if (!swap_ops)
  {
    tmp      = e0;
    e0       = e1;
    e1       = tmp;
    swap_ops = 1;
    goto SWAP_OPERANDS;
  }

  result = btor_add_exp_node (btor, e1, e0);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  int swap_ops = 0;
  BtorNode *tmp, *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_mul (btor, &e0, &e1);

  ADD_RW_RULE (const_binary_exp, BTOR_MUL_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_MUL_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_MUL_NODE, e0, e1);
  ADD_RW_RULE (bool_mul, e0, e1);
// TODO (ma): this increases mul nodes in the general case, needs restriction
//  ADD_RW_RULE (bcond_mul, e0, e1);
SWAP_OPERANDS:
  ADD_RW_RULE (const_lhs_mul, e0, e1);
  ADD_RW_RULE (const_rhs_mul, e0, e1);
  ADD_RW_RULE (const_mul, e0, e1);

  assert (!result);

  /* no result so far, swap operands */
  if (!swap_ops)
  {
    tmp      = e0;
    e0       = e1;
    e1       = tmp;
    swap_ops = 1;
    goto SWAP_OPERANDS;
  }

  result = btor_mul_exp_node (btor, e1, e0);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_udiv (btor, &e0, &e1);

  // TODO what about non powers of 2, like divisor 3, which means that
  // some upper bits are 0 ...

  ADD_RW_RULE (const_binary_exp, BTOR_UDIV_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_UDIV_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_UDIV_NODE, e0, e1);
  ADD_RW_RULE (bool_udiv, e0, e1);
  ADD_RW_RULE (power2_udiv, e0, e1);
  ADD_RW_RULE (one_udiv, e0, e1);
  ADD_RW_RULE (bcond_udiv, e0, e1);

  assert (!result);
  result = btor_udiv_exp_node (btor, e0, e1);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_regular_binary_bv_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_urem (btor, &e0, &e1);

  // TODO do optimize for powers of two even AIGs do it as well !!!

  // TODO what about non powers of 2, like modulo 3, which means that
  // all but the last two bits are zero

  ADD_RW_RULE (const_binary_exp, BTOR_UREM_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_UREM_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_UREM_NODE, e0, e1);
  ADD_RW_RULE (bool_urem, e0, e1);
  ADD_RW_RULE (zero_urem, e0, e1);

  assert (!result);
  result = btor_urem_exp_node (btor, e0, e1);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_concat_exp_dbg (btor, e0, e1));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  normalize_concat (btor, &e0, &e1);

  ADD_RW_RULE (const_binary_exp, BTOR_CONCAT_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_CONCAT_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_CONCAT_NODE, e0, e1);
  ADD_RW_RULE (const_concat, e0, e1);
  ADD_RW_RULE (slice_concat, e0, e1);
  ADD_RW_RULE (and_lhs_concat, e0, e1);
  ADD_RW_RULE (and_rhs_concat, e0, e1);

  assert (!result);
  result = btor_concat_exp_node (btor, e0, e1);
DONE:
  assert (result);
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  return result;
}

static BtorNode *
rewrite_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  ADD_RW_RULE (const_binary_exp, BTOR_SLL_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_SLL_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_SLL_NODE, e0, e1);
  ADD_RW_RULE (const_sll, e0, e1);

  assert (!result);
  result = btor_sll_exp_node (btor, e0, e1);
DONE:
  assert (result);
  return result;
}

static BtorNode *
rewrite_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_shift_exp_dbg (btor, e0, e1));

  ADD_RW_RULE (const_binary_exp, BTOR_SRL_NODE, e0, e1);
  ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_SRL_NODE, e0, e1);
  ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_SRL_NODE, e0, e1);
  ADD_RW_RULE (const_srl, e0, e1);

  assert (!result);
  result = btor_srl_exp_node (btor, e0, e1);
DONE:
  assert (result);
  return result;
}

static BtorNode *
rewrite_apply_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_precond_apply_exp_dbg (btor, e0, e1));

  ADD_RW_RULE (const_lambda_apply, e0, e1);
  ADD_RW_RULE (param_lambda_apply, e0, e1);
  ADD_RW_RULE (apply_apply, e0, e1);
  ADD_RW_RULE (prop_apply, e0, e1);

  assert (!result);
  result = btor_apply_exp_node (btor, e0, e1);
DONE:
  assert (result);
  return result;
}

static BtorNode *
rewrite_lambda_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);

  // FIXME: this rule may yield lambdas with differents sorts (in case of
  // curried
  //        lambdas)
  //  ADD_RW_RULE (lambda_lambda, e0, e1);

  assert (!result);
  result = btor_lambda_exp_node (btor, e0, e1);
  // DONE:
  assert (result);
  return result;
}

static BtorNode *
rewrite_cond_exp (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  e2 = btor_simplify_exp (btor, e2);
  assert (btor_precond_cond_exp_dbg (btor, e0, e1, e2));

  e0 = btor_copy_exp (btor, e0);
  e1 = btor_copy_exp (btor, e1);
  e2 = btor_copy_exp (btor, e2);
  normalize_cond (btor, &e0, &e1, &e2);
  assert (BTOR_IS_REGULAR_NODE (e0));

  ADD_RW_RULE (equal_branches_cond, e0, e1, e2);
  ADD_RW_RULE (const_cond, e0, e1, e2);
  ADD_RW_RULE (cond_if_dom_cond, e0, e1, e2);
  ADD_RW_RULE (cond_if_merge_if_cond, e0, e1, e2);
  ADD_RW_RULE (cond_if_merge_else_cond, e0, e1, e2);
  ADD_RW_RULE (cond_else_dom_cond, e0, e1, e2);
  ADD_RW_RULE (cond_else_merge_if_cond, e0, e1, e2);
  ADD_RW_RULE (cond_else_merge_else_cond, e0, e1, e2);
  ADD_RW_RULE (bool_cond, e0, e1, e2);
  ADD_RW_RULE (add_if_cond, e0, e1, e2);
  ADD_RW_RULE (add_else_cond, e0, e1, e2);
  ADD_RW_RULE (concat_cond, e0, e1, e2);
  ADD_RW_RULE (op_lhs_cond, e0, e1, e2);
  ADD_RW_RULE (op_rhs_cond, e0, e1, e2);
  ADD_RW_RULE (comm_op_1_cond, e0, e1, e2);
  ADD_RW_RULE (comm_op_2_cond, e0, e1, e2);

  assert (!result);
  result = btor_cond_exp_node (btor, e0, e1, e2);
DONE:
  btor_release_exp (btor, e0);
  btor_release_exp (btor, e1);
  btor_release_exp (btor, e2);
  assert (result);
  return result;
}

/* -------------------------------------------------------------------------- */
/* api function */

BtorNode *
btor_rewrite_slice_exp (Btor *btor,
                        BtorNode *exp,
                        uint32_t upper,
                        uint32_t lower)
{
  assert (btor);
  assert (btor->options.rewrite_level.val > 0);

  return rewrite_slice_exp (btor, exp, upper, lower);
}

BtorNode *
btor_rewrite_binary_exp (Btor *btor,
                         BtorNodeKind kind,
                         BtorNode *e0,
                         BtorNode *e1)
{
  assert (btor);
  assert (kind);
  assert (e0);
  assert (e1);
  assert (btor->options.rewrite_level.val > 0);

  switch (kind)
  {
    case BTOR_FEQ_NODE:
    case BTOR_BEQ_NODE: return rewrite_eq_exp (btor, e0, e1);

    case BTOR_ULT_NODE: return rewrite_ult_exp (btor, e0, e1);

    case BTOR_AND_NODE: return rewrite_and_exp (btor, e0, e1);

    case BTOR_ADD_NODE: return rewrite_add_exp (btor, e0, e1);

    case BTOR_MUL_NODE: return rewrite_mul_exp (btor, e0, e1);

    case BTOR_UDIV_NODE: return rewrite_udiv_exp (btor, e0, e1);

    case BTOR_UREM_NODE: return rewrite_urem_exp (btor, e0, e1);

    case BTOR_CONCAT_NODE: return rewrite_concat_exp (btor, e0, e1);

    case BTOR_SLL_NODE: return rewrite_sll_exp (btor, e0, e1);

    case BTOR_SRL_NODE: return rewrite_srl_exp (btor, e0, e1);

    case BTOR_APPLY_NODE: return rewrite_apply_exp (btor, e0, e1);

    default:
      assert (kind == BTOR_LAMBDA_NODE);
      return rewrite_lambda_exp (btor, e0, e1);
  }

  return 0;
}

BtorNode *
btor_rewrite_ternary_exp (
    Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (btor);
  assert (kind);
  assert (kind == BTOR_BCOND_NODE);
  assert (e0);
  assert (e1);
  assert (e2);
  assert (btor->options.rewrite_level.val > 0);
  (void) kind;

  return rewrite_cond_exp (btor, e0, e1, e2);
}
