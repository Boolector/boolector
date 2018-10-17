/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2017 Armin Biere.
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *  Copyright (C) 2014-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbeta.h"
#include "btorbv.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorexp.h"
#include "btorlog.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

#include "btorrewrite.h"

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
#ifndef NDEBUG
#define ADD_RW_RULE(rw_rule, ...)                                              \
  if (applies_##rw_rule (btor, __VA_ARGS__))                                   \
  {                                                                            \
    assert (!result);                                                          \
    result = apply_##rw_rule (btor, __VA_ARGS__);                              \
    if (result)                                                                \
    {                                                                          \
      if (btor->stats.rw_rules_applied)                                        \
      {                                                                        \
        BtorPtrHashBucket *b =                                                 \
            btor_hashptr_table_get (btor->stats.rw_rules_applied, #rw_rule);   \
        if (!b)                                                                \
          b = btor_hashptr_table_add (btor->stats.rw_rules_applied, #rw_rule); \
        b->data.as_int += 1;                                                   \
      }                                                                        \
      goto DONE;                                                               \
    }                                                                          \
  }
#else
#define ADD_RW_RULE(rw_rule, ...)                 \
  if (applies_##rw_rule (btor, __VA_ARGS__))      \
  {                                               \
    assert (!result);                             \
    result = apply_##rw_rule (btor, __VA_ARGS__); \
    if (result) goto DONE;                        \
  }
#endif
//{fprintf (stderr, "apply: %s (%s)\n", #rw_rule, __FUNCTION__);

/* -------------------------------------------------------------------------- */
/* rewrite cache */

static BtorNode *
check_rw_cache (
    Btor *btor, BtorNodeKind kind, int32_t id0, int32_t id1, int32_t id2)
{
  BtorNode *result = 0;

  int32_t cached_result_id =
      btor_rw_cache_get (btor->rw_cache, kind, id0, id1, id2);
  if (cached_result_id)
  {
    result = btor_node_get_by_id (btor, cached_result_id);
    if (result)
    {
      btor->rw_cache->num_get++;
      result = btor_node_copy (
          btor, btor_pointer_chase_simplified_exp (btor, result));
    }
  }
  return result;
}

/* -------------------------------------------------------------------------- */
/* util functions */

static bool
is_const_zero_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  bool result;

  exp = btor_simplify_exp (btor, exp);

  if (!btor_node_is_bv_const (exp)) return false;

  if (btor_node_is_inverted (exp))
    result = btor_bv_is_ones (btor_node_bv_const_get_bits (exp));
  else
    result = btor_bv_is_zero (btor_node_bv_const_get_bits (exp));

  return result;
}

#if 0
static bool
is_const_ones_exp (Btor * btor, BtorNode * exp)
{
  assert (btor);
  assert (exp);

  bool result;

  exp = btor_simplify_exp (btor, exp);

  if (!btor_node_is_bv_const (exp))
    return false;

  if (btor_node_is_inverted (exp))
    result = btor_is_zero_const (btor_node_bv_const_get_bits (exp));
  else
    result = btor_is_ones_const (btor_node_bv_const_get_bits (exp));

  return result;
}
#endif

static bool
is_bv_const_zero_or_ones_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  bool result;
  BtorBitVector *bits;

  exp = btor_simplify_exp (btor, exp);

  if (!btor_node_is_bv_const (exp)) return false;

  bits   = btor_node_bv_const_get_bits (exp);
  result = btor_bv_is_zero (bits) || btor_bv_is_ones (bits);

  return result;
}

static bool
is_odd_bv_const_exp (BtorNode *exp)
{
  BtorBitVector *bits;

  if (!btor_node_is_bv_const (exp)) return false;
  if (btor_node_is_inverted (exp)) return false;

  bits = btor_node_bv_const_get_bits (exp);
  return btor_bv_get_bit (bits, 0) == 1;
}

static bool
is_xor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  BtorNode *e0, *e1, *e0_0, *e0_1, *e1_0, *e1_1;

  exp = btor_simplify_exp (btor, exp);
  (void) btor;

  if (btor_node_real_addr (exp)->kind != BTOR_BV_AND_NODE) return false;

  e0 = btor_node_real_addr (exp)->e[0];
  if (!(btor_node_is_inverted (e0)
        && btor_node_real_addr (e0)->kind == BTOR_BV_AND_NODE))
    return false;

  e1 = btor_node_real_addr (exp)->e[1];
  if (!(btor_node_is_inverted (e1)
        && btor_node_real_addr (e1)->kind == BTOR_BV_AND_NODE))
    return false;

  e0_0 = btor_node_real_addr (e0)->e[0];
  e0_1 = btor_node_real_addr (e0)->e[1];
  e1_0 = btor_node_real_addr (e1)->e[0];
  e1_1 = btor_node_real_addr (e1)->e[1];

  /* we assume that the children of commutative operators are sorted by id */
  /* are children of e0 the same children as of e1 (ignoring sign) ? */
  /* if not we terminate with false */
  if (btor_node_real_addr (e0_0) != btor_node_real_addr (e1_0)) return false;
  if (btor_node_real_addr (e0_1) != btor_node_real_addr (e1_1)) return false;

  /* we check for two cases */
  /* first case: !(!a && !b) && !(a && b) */
  if (!btor_node_is_inverted (exp))
  {
    if (btor_node_is_inverted (e0_0) == btor_node_is_inverted (e0_1)
        && btor_node_is_inverted (e1_0) == btor_node_is_inverted (e1_1)
        && btor_node_is_inverted (e0_0) != btor_node_is_inverted (e1_0))
      return true;
  }
  /* second case: !((!a && b) && !(a && !b)) */
  else
  {
    if (btor_node_is_inverted (e0_0) != btor_node_is_inverted (e1_0)
        && btor_node_is_inverted (e0_1) != btor_node_is_inverted (e1_1)
        && btor_node_is_inverted (e0_0) != btor_node_is_inverted (e0_1))
      return true;
  }
  return false;
}

static bool
is_xnor_exp (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  exp = btor_simplify_exp (btor, exp);
  return is_xor_exp (btor, btor_node_invert (exp));
}

static bool
slice_simplifiable (BtorNode *exp)
{
  exp = btor_node_real_addr (exp);
  return btor_node_is_bv_var (exp) || btor_node_is_bv_const (exp)
         || btor_node_is_bv_slice (exp);
}

static bool
is_always_unequal (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  BtorNode *e0_const = 0, *e0_node = 0, *e1_const = 0, *e1_node = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor);
  assert (e0);
  assert (e1);
  /* we need this so that a + 0 is rewritten to a,
   * and constants are normalized (all inverted constants are odd) */
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0);

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  if (!real_e0 || !real_e1) return 0;

  if (btor_node_is_fun (real_e0))
  {
    assert (btor_node_is_fun (real_e1));
    return false;
  }

  assert (!btor_node_is_fun (real_e1));

  if (e0 == btor_node_invert (e1)) return true;

  if (btor_node_is_bv_const (real_e0) && btor_node_is_bv_const (real_e1)
      && e0 != e1)
    return true;

  if (btor_node_is_bv_add (real_e0))
  {
    if (btor_node_is_bv_const (real_e0->e[0]))
    {
      e0_const = real_e0->e[0];
      e0_node  = real_e0->e[1];
    }
    else if (btor_node_is_bv_const (real_e0->e[1]))
    {
      e0_const = real_e0->e[1];
      e0_node  = real_e0->e[0];
    }

    if (e0_const && !is_const_zero_exp (btor, e0_const)
        && btor_node_cond_invert (e0, e0_node) == e1)
      return true;
  }

  if (btor_node_is_bv_add (real_e1))
  {
    if (btor_node_is_bv_const (real_e1->e[0]))
    {
      e1_const = real_e1->e[0];
      e1_node  = real_e1->e[1];
    }
    else if (btor_node_is_bv_const (real_e1->e[1]))
    {
      e1_const = real_e1->e[1];
      e1_node  = real_e1->e[0];
    }

    if (e1_const && !is_const_zero_exp (btor, e1_const)
        && btor_node_cond_invert (e1, e1_node) == e1)
      return true;
  }

  if (e0_const && e1_const
      && btor_node_is_inverted (e0) == btor_node_is_inverted (e1))
  {
    return e0_node == e1_node && e0_const != e1_const;
  }

  return false;
}

static int32_t
cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return btor_node_real_addr (a)->id - btor_node_real_addr (b)->id;
}

static bool
find_and_contradiction_exp (
    Btor *btor, BtorNode *exp, BtorNode *e0, BtorNode *e1, uint32_t *calls)
{
  assert (btor);
  assert (exp);
  assert (e0);
  assert (e1);
  assert (calls);
  (void) btor;

  if (*calls >= BTOR_FIND_AND_NODE_CONTRADICTION_LIMIT) return false;

  if (!btor_node_is_inverted (exp) && exp->kind == BTOR_BV_AND_NODE)
  {
    if (exp->e[0] == btor_node_invert (e0) || exp->e[0] == btor_node_invert (e1)
        || exp->e[1] == btor_node_invert (e0)
        || exp->e[1] == btor_node_invert (e1))
      return true;
    *calls += 1;
    return find_and_contradiction_exp (btor, exp->e[0], e0, e1, calls)
           || find_and_contradiction_exp (btor, exp->e[1], e0, e1, calls);
  }
  return false;
}

static bool
is_concat_simplifiable (BtorNode *exp)
{
  return btor_node_is_bv_var (exp) || btor_node_is_bv_const (exp);
}

static bool
is_write_exp (BtorNode *exp,
              BtorNode **array,
              BtorNode **index,
              BtorNode **value)
{
  assert (exp);
  assert (btor_node_is_regular (exp));

  BtorNode *param, *body, *eq, *app;

  if (!btor_node_is_lambda (exp)
      || btor_node_fun_get_arity (exp->btor, exp) > 1)
    return false;

  param = exp->e[0];
  body  = btor_node_binder_get_body (exp);

  if (btor_node_is_inverted (body) || !btor_node_is_bv_cond (body))
    return false;

  /* check condition */
  eq = body->e[0];
  if (btor_node_is_inverted (eq) || !btor_node_is_bv_eq (eq)
      || !eq->parameterized || (eq->e[0] != param && eq->e[1] != param))
    return false;

  /* check value */
  if (btor_node_real_addr (body->e[1])->parameterized) return false;

  /* check apply on unmodified array */
  app = body->e[2];
  if (btor_node_is_inverted (app) || !btor_node_is_apply (app)
      || btor_node_args_get_arity (app->btor, app->e[1]) > 1
      || app->e[1]->e[0] != param)
    return false;

  if (array) *array = app->e[0];
  if (index) *index = eq->e[1] == param ? eq->e[0] : eq->e[1];
  if (value) *value = body->e[1];
  return true;
}

static bool
is_true_cond (BtorNode *cond)
{
  assert (cond);
  assert (btor_node_bv_get_width (btor_node_real_addr (cond)->btor, cond) == 1);

  if (btor_node_is_inverted (cond)
      && !btor_bv_get_bit (btor_node_bv_const_get_bits (cond), 0))
    return true;
  else if (!btor_node_is_inverted (cond)
           && btor_bv_get_bit (btor_node_bv_const_get_bits (cond), 0))
    return true;

  return false;
}

#if 0
static bool
is_bit_mask (BtorNode * exp, uint32_t * upper, uint32_t * lower)
{
  uint32_t i, len, inv, bit;
  int32_t first, last;
  BtorBitVector *bits;
  BtorNode *real_exp;

  real_exp = btor_node_real_addr (exp);

  *upper = 0; *lower = 0;
  first = -1; last = -1;

  if (!btor_node_is_bv_const (real_exp))
    return false;

  bits = btor_node_bv_const_get_bits (real_exp);
  inv = btor_node_is_inverted (exp);
  len = btor_node_bv_get_width (real_exp->btor, real_exp);
  for (i = 0; i < len; i++)
    {
      bit = btor_bv_get_bit (bits, i);
      if (inv) bit ^= 1;

      if (bit && first == -1)
	first = i;
      else if (!bit && first > -1 && last == -1)
	last = i - 1;

      if (bit && last > -1)
	return false;
    }
  if (last == -1)
    last = len - 1;

  *upper = last;
  *lower = first;
  return true;
}
#endif

static bool
is_urem_exp (Btor *btor,
             BtorNode *e0,
             BtorNode *e1,
             BtorNode **res_e0,
             BtorNode **res_e1)
{
  BtorNode *mul, *udiv, *x, *y;

  if (btor_node_is_neg (btor, e0, &mul))
    x = e1;
  else if (btor_node_is_neg (btor, e1, &mul))
    x = e0;
  else
    return false;

  if (btor_node_is_inverted (mul) || !btor_node_is_bv_mul (mul)) return false;

  if (!btor_node_is_inverted (mul->e[0]) && btor_node_is_bv_udiv (mul->e[0]))
  {
    udiv = mul->e[0];
    y    = mul->e[0];
  }
  else if (!btor_node_is_inverted (mul->e[1])
           && btor_node_is_bv_udiv (mul->e[1]))
  {
    udiv = mul->e[1];
    y    = mul->e[0];
  }
  else
    return false;

  if (udiv->e[0] == x && udiv->e[1] == y)
  {
    if (res_e0) *res_e0 = x;
    if (res_e1) *res_e1 = y;
    return true;
  }
  return false;
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
static BtorNode *rewrite_forall_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_exists_exp (Btor *, BtorNode *, BtorNode *);
static BtorNode *rewrite_cond_exp (Btor *, BtorNode *, BtorNode *, BtorNode *);

/* -------------------------------------------------------------------------- */
/* const term rewriting                                                       */
/* -------------------------------------------------------------------------- */

/*
 * match:  binary op with two constants
 * result: constant
 */
static inline bool
applies_const_binary_exp (Btor *btor,
                          BtorNodeKind kind,
                          BtorNode *e0,
                          BtorNode *e1)
{
  (void) btor;
  (void) kind;
  return btor_node_is_bv_const (e0) && btor_node_is_bv_const (e1);
}

static inline BtorNode *
apply_const_binary_exp (Btor *btor,
                        BtorNodeKind kind,
                        BtorNode *e0,
                        BtorNode *e1)
{
  assert (applies_const_binary_exp (btor, kind, e0, e1));

  bool invert_b0, invert_b1;
  BtorBitVector *b0, *b1, *bresult;
  BtorMemMgr *mm;
  BtorNode *result, *real_e0, *real_e1;

  mm      = btor->mm;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  invert_b0 = btor_node_is_inverted (e0);
  invert_b1 = btor_node_is_inverted (e1);
  b0        = btor_node_bv_const_get_bits (real_e0);
  b1        = btor_node_bv_const_get_bits (real_e1);
  if (invert_b0) b0 = btor_bv_not (mm, b0);
  if (invert_b1) b1 = btor_bv_not (mm, b1);

  switch (kind)
  {
    case BTOR_BV_AND_NODE: bresult = btor_bv_and (mm, b0, b1); break;
    case BTOR_BV_EQ_NODE: bresult = btor_bv_eq (mm, b0, b1); break;
    case BTOR_BV_ADD_NODE: bresult = btor_bv_add (mm, b0, b1); break;
    case BTOR_BV_MUL_NODE: bresult = btor_bv_mul (mm, b0, b1); break;
    case BTOR_BV_ULT_NODE: bresult = btor_bv_ult (mm, b0, b1); break;
    case BTOR_BV_UDIV_NODE: bresult = btor_bv_udiv (mm, b0, b1); break;
    case BTOR_BV_UREM_NODE: bresult = btor_bv_urem (mm, b0, b1); break;
    case BTOR_BV_SLL_NODE: bresult = btor_bv_sll (mm, b0, b1); break;
    case BTOR_BV_SRL_NODE: bresult = btor_bv_srl (mm, b0, b1); break;
    default:
      assert (kind == BTOR_BV_CONCAT_NODE);
      bresult = btor_bv_concat (mm, b0, b1);
      break;
  }
  if (invert_b0) btor_bv_free (mm, b0);
  if (invert_b1) btor_bv_free (mm, b1);
  result = btor_exp_bv_const (btor, bresult);
  btor_bv_free (mm, bresult);
  return result;
}

/*
 * match:  binary op with one constant
 * result: constant
 */
static inline bool
applies_special_const_lhs_binary_exp (Btor *btor,
                                      BtorNodeKind kind,
                                      BtorNode *e0,
                                      BtorNode *e1)
{
  (void) btor;
  (void) kind;
  return btor_node_is_bv_const (e0) && !btor_node_is_bv_const (e1);
}

static inline BtorNode *
apply_special_const_lhs_binary_exp (Btor *btor,
                                    BtorNodeKind kind,
                                    BtorNode *e0,
                                    BtorNode *e1)
{
  assert (applies_special_const_lhs_binary_exp (btor, kind, e0, e1));

  char tmpstr[2] = {'\0', '\0'}, *bvstr;
  uint32_t pos, len, width_e0;
  bool invert_b0;
  BtorBitVector *b0, *bv;
  BtorMemMgr *mm;
  BtorSpecialConstBitVector sc;
  BtorNode *result = 0, *real_e0, *real_e1, *left, *right, *tmp1, *tmp2, *tmp3;
  BtorNode *tmp4, *eq;
  BtorNodePtrStack stack;
  BtorSortId sort;

  mm        = btor->mm;
  real_e0   = btor_node_real_addr (e0);
  real_e1   = btor_node_real_addr (e1);
  invert_b0 = btor_node_is_inverted (e0);
  b0        = btor_node_bv_const_get_bits (real_e0);
  width_e0  = btor_node_bv_get_width (btor, real_e0);

  if (invert_b0) b0 = btor_bv_not (mm, b0);
  sc = btor_bv_is_special_const (b0);
  if (invert_b0) btor_bv_free (mm, b0);

  switch (sc)
  {
    case BTOR_SPECIAL_CONST_BV_ZERO:
      switch (kind)
      {
        case BTOR_BV_EQ_NODE:
          if (width_e0 == 1)
            result = btor_exp_bv_not (btor, e1);
          else if (is_xor_exp (btor, e1)) /* 0 == (a ^ b)  -->  a = b */
          {
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              result = rewrite_eq_exp (
                  btor,
                  btor_node_real_addr (
                      btor_node_real_addr (btor_node_real_addr (e1)->e[0])
                          ->e[0]),
                  btor_node_real_addr (
                      btor_node_real_addr (btor_node_real_addr (e1)->e[0])
                          ->e[1]));
              BTOR_DEC_REC_RW_CALL (btor);
            }
          }
          else if (btor_node_is_inverted (e1)
                   && real_e1->kind == BTOR_BV_AND_NODE)
          { /* 0 == a | b  -->  a == 0 && b == 0 */
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              left =
                  rewrite_eq_exp (btor, btor_node_invert (real_e1->e[0]), e0);
              right =
                  rewrite_eq_exp (btor, btor_node_invert (real_e1->e[1]), e0);
              result = rewrite_and_exp (btor, left, right);
              BTOR_DEC_REC_RW_CALL (btor);
              btor_node_release (btor, left);
              btor_node_release (btor, right);
            }
          }
          break;
        case BTOR_BV_ULT_NODE: /* 0 < a --> a != 0 */
          result = btor_node_invert (rewrite_eq_exp (btor, e0, e1));
          break;
        case BTOR_BV_ADD_NODE: result = btor_node_copy (btor, e1); break;
        case BTOR_BV_MUL_NODE:
        case BTOR_BV_SLL_NODE:
        case BTOR_BV_SRL_NODE:
        case BTOR_BV_UREM_NODE:
        case BTOR_BV_AND_NODE:
          result = btor_exp_bv_zero (btor, btor_node_get_sort_id (real_e0));
          break;
        case BTOR_BV_UDIV_NODE:
          tmp2   = btor_exp_bv_zero (btor, btor_node_get_sort_id (real_e0));
          tmp4   = btor_exp_bv_ones (btor, btor_node_get_sort_id (real_e0));
          eq     = rewrite_eq_exp (btor, e1, tmp2);
          result = rewrite_cond_exp (btor, eq, tmp4, tmp2);
          btor_node_release (btor, tmp2);
          btor_node_release (btor, eq);
          btor_node_release (btor, tmp4);
          break;
        default: break;
      }
      break;
    case BTOR_SPECIAL_CONST_BV_ONE_ONES:
      assert (width_e0 == 1);
      if (kind == BTOR_BV_AND_NODE || kind == BTOR_BV_EQ_NODE
          || kind == BTOR_BV_MUL_NODE)
        result = btor_node_copy (btor, e1);
      else if (kind == BTOR_BV_ULT_NODE)
        result = btor_exp_false (btor);
      break;
    case BTOR_SPECIAL_CONST_BV_ONE:
      if (kind == BTOR_BV_MUL_NODE) result = btor_node_copy (btor, e1);
      break;
    case BTOR_SPECIAL_CONST_BV_ONES:
      if (kind == BTOR_BV_EQ_NODE)
      {
        if (is_xnor_exp (btor, e1)) /* 1+ == (a XNOR b)  -->  a = b */
        {
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            result = rewrite_eq_exp (
                btor,
                btor_node_real_addr (
                    btor_node_real_addr (btor_node_real_addr (e1)->e[0])->e[0]),
                btor_node_real_addr (
                    btor_node_real_addr (btor_node_real_addr (e1)->e[0])
                        ->e[1]));
            BTOR_DEC_REC_RW_CALL (btor);
          }
        }
        else if (!btor_node_is_inverted (e1) && e1->kind == BTOR_BV_AND_NODE)
        { /* 1+ == a & b  -->  a == 1+ && b == 1+ */
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            left   = rewrite_eq_exp (btor, e1->e[0], e0);
            right  = rewrite_eq_exp (btor, e1->e[1], e0);
            result = rewrite_and_exp (btor, left, right);
            BTOR_DEC_REC_RW_CALL (btor);
            btor_node_release (btor, left);
            btor_node_release (btor, right);
          }
        }
      }
      else if (kind == BTOR_BV_AND_NODE)
        result = btor_node_copy (btor, e1);
      else if (kind == BTOR_BV_ULT_NODE) /* UNSIGNED_MAX < x */
        result = btor_exp_false (btor);
      else if (kind == BTOR_BV_MUL_NODE)
        result = btor_exp_bv_neg (btor, e1);
      break;
    default:
      assert (sc == BTOR_SPECIAL_CONST_BV_NONE);
      if (kind == BTOR_BV_EQ_NODE && real_e1->kind == BTOR_BV_AND_NODE
          && btor->rec_rw_calls < BTOR_REC_RW_BOUND)
      {
        BTOR_INC_REC_RW_CALL (btor);
        BTOR_INIT_STACK (btor->mm, stack);
        if (btor_node_is_inverted (e0))
          bv = btor_bv_not (btor->mm, btor_node_bv_const_get_bits (real_e0));
        else
          bv = btor_bv_copy (btor->mm, btor_node_bv_const_get_bits (real_e0));

        pos = 0;
        /* const == a | b */
        if (btor_node_is_inverted (e1))
        {
          while (pos < width_e0)
          {
            bvstr     = btor_bv_to_char (btor->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn (bvstr + pos, tmpstr);
            btor_mem_freestr (btor->mm, bvstr);
            tmp1 = rewrite_slice_exp (btor,
                                      btor_node_invert (real_e1->e[0]),
                                      width_e0 - 1 - pos,
                                      width_e0 - pos - len);
            tmp2 = rewrite_slice_exp (btor,
                                      btor_node_invert (real_e1->e[1]),
                                      width_e0 - 1 - pos,
                                      width_e0 - pos - len);
            sort = btor_sort_bv (btor, len);
            if (tmpstr[0] == '0')
            {
              tmp3 = btor_exp_bv_zero (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_node_release (btor, tmp3);
            }
            else
            {
              assert (tmpstr[0] == '1');
              tmp3 = btor_exp_bv_or (btor, tmp1, tmp2);
              tmp4 = btor_exp_bv_ones (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_node_release (btor, tmp3);
              btor_node_release (btor, tmp4);
            }
            btor_sort_release (btor, sort);
            btor_node_release (btor, tmp1);
            btor_node_release (btor, tmp2);
            pos += len;
          }
        }
        else
        {
          assert (!btor_node_is_inverted (e1));
          /* const == a & b */
          while (pos < width_e0)
          {
            bvstr     = btor_bv_to_char (btor->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn (bvstr + pos, tmpstr);
            btor_mem_freestr (btor->mm, bvstr);
            tmp1 = rewrite_slice_exp (
                btor, e1->e[0], width_e0 - 1 - pos, width_e0 - pos - len);
            tmp2 = rewrite_slice_exp (
                btor, e1->e[1], width_e0 - 1 - pos, width_e0 - pos - len);
            sort = btor_sort_bv (btor, len);
            if (tmpstr[0] == '1')
            {
              tmp3 = btor_exp_bv_ones (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_node_release (btor, tmp3);
            }
            else
            {
              assert (tmpstr[0] == '0');
              tmp3 = rewrite_and_exp (btor, tmp1, tmp2);
              tmp4 = btor_exp_bv_zero (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_node_release (btor, tmp3);
              btor_node_release (btor, tmp4);
            }
            btor_sort_release (btor, sort);
            btor_node_release (btor, tmp1);
            btor_node_release (btor, tmp2);
            pos += len;
          }
        }

        result = btor_exp_true (btor);
        assert (!BTOR_EMPTY_STACK (stack));
        do
        {
          tmp1 = BTOR_POP_STACK (stack);
          tmp2 = rewrite_and_exp (btor, result, tmp1);
          btor_node_release (btor, result);
          result = tmp2;
          btor_node_release (btor, tmp1);
        } while (!BTOR_EMPTY_STACK (stack));
        btor_bv_free (btor->mm, bv);
        BTOR_RELEASE_STACK (stack);
        BTOR_DEC_REC_RW_CALL (btor);
      }
      break;
  }

  return result;
}

/*
 * match:  binary op with one constant
 * result: constant
 */
static inline bool
applies_special_const_rhs_binary_exp (Btor *btor,
                                      BtorNodeKind kind,
                                      BtorNode *e0,
                                      BtorNode *e1)
{
  (void) btor;
  (void) kind;
  return !btor_node_is_bv_const (e0) && btor_node_is_bv_const (e1);
}

static inline BtorNode *
apply_special_const_rhs_binary_exp (Btor *btor,
                                    BtorNodeKind kind,
                                    BtorNode *e0,
                                    BtorNode *e1)
{
  assert (applies_special_const_rhs_binary_exp (btor, kind, e0, e1));

  char tmpstr[2] = {'\0', '\0'}, *bvstr;
  uint32_t pos, len, width_e0, width_e1;
  bool invert_b1;
  BtorBitVector *b1, *bv;
  BtorMemMgr *mm;
  BtorSpecialConstBitVector sc;
  BtorNode *result = 0, *real_e0, *real_e1, *left, *right, *tmp1, *tmp2, *tmp3;
  BtorNode *tmp4;
  BtorNodePtrStack stack;
  BtorSortId sort;

  mm        = btor->mm;
  real_e0   = btor_node_real_addr (e0);
  real_e1   = btor_node_real_addr (e1);
  invert_b1 = btor_node_is_inverted (e1);
  b1        = btor_node_bv_const_get_bits (real_e1);
  width_e0  = btor_node_bv_get_width (btor, real_e0);
  width_e1  = btor_node_bv_get_width (btor, real_e1);

  if (invert_b1) b1 = btor_bv_not (mm, b1);
  sc = btor_bv_is_special_const (b1);
  if (invert_b1) btor_bv_free (mm, b1);

  switch (sc)
  {
    case BTOR_SPECIAL_CONST_BV_ZERO:
      switch (kind)
      {
        case BTOR_BV_EQ_NODE:
          if (width_e0 == 1)
            result = btor_exp_bv_not (btor, e0);
          else if (is_xor_exp (btor, e0)) /* (a ^ b) == 0 -->  a = b */
          {
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              result = rewrite_eq_exp (
                  btor,
                  btor_node_real_addr (
                      btor_node_real_addr (btor_node_real_addr (e0)->e[0])
                          ->e[0]),
                  btor_node_real_addr (
                      btor_node_real_addr (btor_node_real_addr (e0)->e[0])
                          ->e[1]));
              BTOR_DEC_REC_RW_CALL (btor);
            }
          }
          else if (btor_node_is_inverted (e0)
                   && real_e0->kind == BTOR_BV_AND_NODE)
          { /*  a | b == 0  -->  a == 0 && b == 0 */
            if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
            {
              BTOR_INC_REC_RW_CALL (btor);
              left =
                  rewrite_eq_exp (btor, btor_node_invert (real_e0->e[0]), e1);
              right =
                  rewrite_eq_exp (btor, btor_node_invert (real_e0->e[1]), e1);
              result = rewrite_and_exp (btor, left, right);
              BTOR_DEC_REC_RW_CALL (btor);
              btor_node_release (btor, left);
              btor_node_release (btor, right);
            }
          }
          break;
        case BTOR_BV_SLL_NODE:
        case BTOR_BV_SRL_NODE:
        case BTOR_BV_UREM_NODE:
        case BTOR_BV_ADD_NODE: result = btor_node_copy (btor, e0); break;
        case BTOR_BV_MUL_NODE:
        case BTOR_BV_AND_NODE:
          result = btor_exp_bv_zero (btor, btor_node_get_sort_id (real_e0));
          break;
        case BTOR_BV_ULT_NODE: /* x < 0 */
          result = btor_exp_false (btor);
          break;
        case BTOR_BV_UDIV_NODE:
          result = btor_exp_bv_ones (btor, btor_node_get_sort_id (real_e0));
          break;
        default: break;
      }
      break;
    case BTOR_SPECIAL_CONST_BV_ONE_ONES:
      assert (width_e1 == 1);
      if (kind == BTOR_BV_AND_NODE || kind == BTOR_BV_EQ_NODE
          || kind == BTOR_BV_MUL_NODE || kind == BTOR_BV_UDIV_NODE)
        result = btor_node_copy (btor, e0);
      break;
    case BTOR_SPECIAL_CONST_BV_ONE:
      if (kind == BTOR_BV_MUL_NODE || kind == BTOR_BV_UDIV_NODE)
        result = btor_node_copy (btor, e0);
      else if (kind == BTOR_BV_UREM_NODE)
        result = btor_exp_bv_zero (btor, btor_node_get_sort_id (real_e0));
      else if (kind == BTOR_BV_ULT_NODE)
      {
        BTOR_INC_REC_RW_CALL (btor);
        tmp1   = btor_exp_bv_zero (btor, btor_node_get_sort_id (real_e0));
        result = rewrite_eq_exp (btor, e0, tmp1);
        btor_node_release (btor, tmp1);
        BTOR_DEC_REC_RW_CALL (btor);
      }
      break;
    case BTOR_SPECIAL_CONST_BV_ONES:
      if (kind == BTOR_BV_EQ_NODE)
      {
        if (is_xnor_exp (btor, e0)) /* (a XNOR b) == 1 -->  a = b */
        {
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            result = rewrite_eq_exp (
                btor,
                btor_node_real_addr (
                    btor_node_real_addr (btor_node_real_addr (e0)->e[0])->e[0]),
                btor_node_real_addr (
                    btor_node_real_addr (btor_node_real_addr (e0)->e[0])
                        ->e[1]));
            BTOR_DEC_REC_RW_CALL (btor);
          }
        }
        else if (!btor_node_is_inverted (e0) && e0->kind == BTOR_BV_AND_NODE)
        {
          /* a & b == 1+ -->  a == 1+ && b == 1+ */
          if (btor->rec_rw_calls < BTOR_REC_RW_BOUND)
          {
            BTOR_INC_REC_RW_CALL (btor);
            left   = rewrite_eq_exp (btor, e0->e[0], e1);
            right  = rewrite_eq_exp (btor, e0->e[1], e1);
            result = rewrite_and_exp (btor, left, right);
            BTOR_DEC_REC_RW_CALL (btor);
            btor_node_release (btor, left);
            btor_node_release (btor, right);
          }
        }
      }
      else if (kind == BTOR_BV_AND_NODE)
        result = btor_node_copy (btor, e0);
      else if (kind == BTOR_BV_ULT_NODE)
      {
        BTOR_INC_REC_RW_CALL (btor);
        result = btor_node_invert (rewrite_eq_exp (btor, e0, e1));
        BTOR_DEC_REC_RW_CALL (btor);
      }
      else if (kind == BTOR_BV_MUL_NODE)
        result = btor_exp_bv_neg (btor, e0);
      break;
    default:
      assert (sc == BTOR_SPECIAL_CONST_BV_NONE);
      if (kind == BTOR_BV_EQ_NODE && real_e0->kind == BTOR_BV_AND_NODE
          && btor->rec_rw_calls < BTOR_REC_RW_BOUND)
      {
        BTOR_INC_REC_RW_CALL (btor);
        BTOR_INIT_STACK (btor->mm, stack);
        if (btor_node_is_inverted (e1))
          bv = btor_bv_not (btor->mm, btor_node_bv_const_get_bits (real_e1));
        else
          bv = btor_bv_copy (btor->mm, btor_node_bv_const_get_bits (real_e1));

        pos = 0;
        /* a | b == const */
        if (btor_node_is_inverted (e0))
        {
          while (pos < width_e1)
          {
            bvstr     = btor_bv_to_char (btor->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn (bvstr + pos, tmpstr);
            btor_mem_freestr (btor->mm, bvstr);
            tmp1 = rewrite_slice_exp (btor,
                                      btor_node_invert (real_e0->e[0]),
                                      width_e1 - 1 - pos,
                                      width_e1 - pos - len);
            tmp2 = rewrite_slice_exp (btor,
                                      btor_node_invert (real_e0->e[1]),
                                      width_e1 - 1 - pos,
                                      width_e1 - pos - len);
            sort = btor_sort_bv (btor, len);
            if (tmpstr[0] == '0')
            {
              tmp3 = btor_exp_bv_zero (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_node_release (btor, tmp3);
            }
            else
            {
              assert (tmpstr[0] == '1');
              tmp3 = btor_exp_bv_or (btor, tmp1, tmp2);
              tmp4 = btor_exp_bv_ones (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_node_release (btor, tmp3);
              btor_node_release (btor, tmp4);
            }
            btor_sort_release (btor, sort);
            btor_node_release (btor, tmp1);
            btor_node_release (btor, tmp2);
            pos += len;
          }
        }
        else
        {
          assert (!btor_node_is_inverted (e0));
          /* a & b == const */
          while (pos < width_e1)
          {
            bvstr     = btor_bv_to_char (btor->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn (bvstr + pos, tmpstr);
            btor_mem_freestr (btor->mm, bvstr);
            tmp1 = rewrite_slice_exp (
                btor, e0->e[0], width_e1 - 1 - pos, width_e1 - pos - len);
            tmp2 = rewrite_slice_exp (
                btor, e0->e[1], width_e1 - 1 - pos, width_e1 - pos - len);
            sort = btor_sort_bv (btor, len);
            if (tmpstr[0] == '1')
            {
              tmp3 = btor_exp_bv_ones (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp1, tmp3));
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp2, tmp3));
              btor_node_release (btor, tmp3);
            }
            else
            {
              assert (tmpstr[0] == '0');
              tmp3 = rewrite_and_exp (btor, tmp1, tmp2);
              tmp4 = btor_exp_bv_zero (btor, sort);
              BTOR_PUSH_STACK (stack, rewrite_eq_exp (btor, tmp3, tmp4));
              btor_node_release (btor, tmp3);
              btor_node_release (btor, tmp4);
            }
            btor_sort_release (btor, sort);
            btor_node_release (btor, tmp1);
            btor_node_release (btor, tmp2);
            pos += len;
          }
        }

        result = btor_exp_true (btor);
        assert (!BTOR_EMPTY_STACK (stack));
        do
        {
          tmp1 = BTOR_POP_STACK (stack);
          tmp2 = rewrite_and_exp (btor, result, tmp1);
          btor_node_release (btor, result);
          result = tmp2;
          btor_node_release (btor, tmp1);
        } while (!BTOR_EMPTY_STACK (stack));
        btor_bv_free (btor->mm, bv);
        BTOR_RELEASE_STACK (stack);
        BTOR_DEC_REC_RW_CALL (btor);
      }
      break;
  }

  return result;
}

/* -------------------------------------------------------------------------- */
/* linear term rewriting                                                      */
/* -------------------------------------------------------------------------- */

/* Can we rewrite 'term' as 'factor*lhs + rhs' where 'lhs' is a variable,
 * and 'factor' is odd?  We check whether this is possible but do not use
 * more than 'bound' recursive calls.  */
static bool
rewrite_linear_term_bounded (Btor *btor,
                             BtorNode *term,
                             BtorBitVector **factor_ptr,
                             BtorNode **lhs_ptr,
                             BtorNode **rhs_ptr,
                             uint32_t *bound_ptr)
{
  BtorNode *tmp, *other;
  BtorBitVector *factor;

  if (*bound_ptr <= 0) return false;

  *bound_ptr -= 1;

  if (btor_node_is_inverted (term))
  {
    /* term = ~subterm
     *      = -1 - subterm
     *      = -1 - (factor * lhs + rhs)
     *      = (-factor) * lhs + (-1 -rhs)
     *      = (-factor) * lhs + ~rhs
     */
    if (!rewrite_linear_term_bounded (btor,
                                      btor_node_invert (term),
                                      &factor,
                                      lhs_ptr,
                                      rhs_ptr,
                                      bound_ptr))
      return false;

    *rhs_ptr    = btor_node_invert (*rhs_ptr);
    *factor_ptr = btor_bv_neg (btor->mm, factor);
    btor_bv_free (btor->mm, factor);
  }
  else if (term->kind == BTOR_BV_ADD_NODE)
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
      return false;

    *rhs_ptr = rewrite_add_exp (btor, other, tmp);
    btor_node_release (btor, tmp);
  }
  else if (term->kind == BTOR_BV_MUL_NODE)
  {
    if (is_odd_bv_const_exp (term->e[0]))
    {
      if (!rewrite_linear_term_bounded (
              btor, term->e[1], &factor, lhs_ptr, &tmp, bound_ptr))
        return false;

      /* term = e0 * e1
       *      = e0 * (factor * lhs + rhs)
       *      = (e0 * factor) * lhs + e0 * rhs
       *      = (other * factor) * lhs + other * rhs
       */
      other = term->e[0];
    }
    else if (is_odd_bv_const_exp (term->e[1]))
    {
      if (!rewrite_linear_term_bounded (
              btor, term->e[0], &factor, lhs_ptr, &tmp, bound_ptr))
        return false;

      /* term = e0 * e1
       *      = (factor * lhs + rhs) * e1
       *      = (e1 * factor) * lhs + e1 * rhs
       *      = (other * factor) * lhs + other * rhs
       */
      other = term->e[1];
    }
    else
      return false;

    assert (!btor_node_is_inverted (other));
    *factor_ptr =
        btor_bv_mul (btor->mm, btor_node_bv_const_get_bits (other), factor);
    btor_bv_free (btor->mm, factor);
    *rhs_ptr = rewrite_mul_exp (btor, other, tmp);
    btor_node_release (btor, tmp);
  }
  else if (term->kind == BTOR_VAR_NODE)
  {
    *lhs_ptr    = btor_node_copy (btor, term);
    *rhs_ptr    = btor_exp_bv_zero (btor, btor_node_get_sort_id (term));
    *factor_ptr = btor_bv_one (btor->mm, btor_node_bv_get_width (btor, term));
  }
  else
    return false;

  return true;
}

bool
btor_rewrite_linear_term (Btor *btor,
                          BtorNode *term,
                          BtorBitVector **fp,
                          BtorNode **lp,
                          BtorNode **rp)
{
  uint32_t bound = 100;
  bool res;
  res = rewrite_linear_term_bounded (btor, term, fp, lp, rp, &bound);
  if (res) btor->stats.linear_equations++;
  return res;
}

/* -------------------------------------------------------------------------- */
/* rewriting rules                                                            */
/* -------------------------------------------------------------------------- */

/*
 * for each rule we define two functions:
 *   static inline bool
 *   applies_<rw_rule> (Btor * btor, ...)
 *   {
 *   }
 *
 *   static inline BtorNode *
 *   apply_<rw_rule> (Btor * btor, ...)
 *   {
 *     assert (applies_<rw_rule> (...));
 *   }
 *
 * where the first one determines if <rw_rule> is applicable, and the second
 * one applies the rule.
 *
 * for adding rw rules to a rewrite function use the ADD_RW_RULE macro.
 */


/* SLICE rules                                                                */
/* -------------------------------------------------------------------------- */

/*
 * match:  exp[len(exp) - 1:0]
 * result: exp
 */
static inline bool
applies_full_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) btor;
  return btor_node_bv_get_width (btor, exp) == upper - lower + 1;
}

static inline BtorNode *
apply_full_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_full_slice (btor, exp, upper, lower));
  (void) btor;
  (void) upper;
  (void) lower;
  return btor_node_copy (btor, exp);
}

/*
 * match: exp[upper:lower], where exp is a constant
 * result: constant
 */
static inline bool
applies_const_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) btor;
  (void) upper;
  (void) lower;
  return btor_node_is_bv_const (exp);
}

static inline BtorNode *
apply_const_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_const_slice (btor, exp, upper, lower));

  BtorBitVector *bits;
  BtorNode *result;

  bits =
      btor_bv_slice (btor->mm, btor_node_bv_const_get_bits (exp), upper, lower);
  result = btor_exp_bv_const (btor, bits);
  result = btor_node_cond_invert (exp, result);
  btor_bv_free (btor->mm, bits);
  return result;
}

/*
 * match:  (exp[u:l])[upper:lower]
 * result: exp[l+upper:l+lower]
 */
static inline bool
applies_slice_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_slice (exp);
}

static inline BtorNode *
apply_slice_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_slice_slice (btor, exp, upper, lower));

  BtorNode *result, *real_exp;

  real_exp = btor_node_real_addr (exp);
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (btor,
                              btor_node_cond_invert (exp, real_exp->e[0]),
                              btor_node_bv_slice_get_lower (real_exp) + upper,
                              btor_node_bv_slice_get_lower (real_exp) + lower);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: (a::b)[len(b)-1:0]
 * result: b
 */
static inline bool
applies_concat_lower_slice (Btor *btor,
                            BtorNode *exp,
                            uint32_t upper,
                            uint32_t lower)
{
  (void) btor;
  return btor_node_is_bv_concat (exp) && lower == 0
         && btor_node_bv_get_width (btor, btor_node_real_addr (exp)->e[1])
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

  result = btor_node_cond_invert (exp, btor_node_real_addr (exp)->e[1]);
  return btor_node_copy (btor, result);
}

/*
 * match: (a::b)[len(a)+len(b)-1:len(b)]
 * result: a
 */
static inline bool
applies_concat_upper_slice (Btor *btor,
                            BtorNode *exp,
                            uint32_t upper,
                            uint32_t lower)
{
  return btor_node_is_bv_concat (exp)
         && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) < 3
         && upper == btor_node_bv_get_width (btor, exp) - 1
         && btor_node_bv_get_width (btor, btor_node_real_addr (exp)->e[0])
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

  result = btor_node_cond_invert (exp, btor_node_real_addr (exp)->e[0]);
  return btor_node_copy (btor, result);
}

/*
 * match:  (a::b)[upper:lower], where lower >= len(b)
 * result: a[upper-len(b):lower-len(b)]
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline bool
applies_concat_rec_upper_slice (Btor *btor,
                                BtorNode *exp,
                                uint32_t upper,
                                uint32_t lower)
{
  (void) upper;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_concat (exp)
         && lower >= btor_node_bv_get_width (btor,
                                             btor_node_real_addr (exp)->e[1]);
}

static inline BtorNode *
apply_concat_rec_upper_slice (Btor *btor,
                              BtorNode *exp,
                              uint32_t upper,
                              uint32_t lower)
{
  assert (applies_concat_rec_upper_slice (btor, exp, upper, lower));

  uint32_t len;
  BtorNode *result, *real_exp;

  real_exp = btor_node_real_addr (exp);
  len      = btor_node_bv_get_width (btor, real_exp->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (btor,
                              btor_node_cond_invert (exp, real_exp->e[0]),
                              upper - len,
                              lower - len);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  (a::b)[upper:lower], where upper < len(b)
 * result: b[upper:lower]
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline bool
applies_concat_rec_lower_slice (Btor *btor,
                                BtorNode *exp,
                                uint32_t upper,
                                uint32_t lower)
{
  (void) lower;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_concat (exp)
         && upper < btor_node_bv_get_width (btor,
                                            btor_node_real_addr (exp)->e[1]);
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
      btor_node_cond_invert (exp, btor_node_real_addr (exp)->e[1]),
      upper,
      lower);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  (a::b)[upper:lower], where lower = 0 and upper >= len(b)
 * result: a[upper-len(b):0]::b
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline bool
applies_concat_rec_slice (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  return btor_node_is_bv_concat (exp)
         && btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && lower == 0
         && upper >= btor_node_bv_get_width (btor,
                                             btor_node_real_addr (exp)->e[1]);
}

static inline BtorNode *
apply_concat_rec_slice (Btor *btor,
                        BtorNode *exp,
                        uint32_t upper,
                        uint32_t lower)
{
  assert (applies_concat_rec_slice (btor, exp, upper, lower));
  (void) lower;

  uint32_t len;
  BtorNode *result, *real_exp, *tmp;

  real_exp = btor_node_real_addr (exp);
  len      = btor_node_bv_get_width (btor, real_exp->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp = rewrite_slice_exp (
      btor, btor_node_cond_invert (exp, real_exp->e[0]), upper - len, 0);
  result = rewrite_concat_exp (
      btor, tmp, btor_node_cond_invert (exp, real_exp->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  (a & b)[upper:lower]
 * result: a[upper:lower] & b[upper:lower]
 */
static inline bool
applies_and_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (exp)
         && (slice_simplifiable (btor_node_real_addr (exp)->e[0])
             || slice_simplifiable (btor_node_real_addr (exp)->e[1]));
}

static inline BtorNode *
apply_and_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_and_slice (btor, exp, upper, lower));

  BtorNode *result, *left, *right, *real_exp;

  real_exp = btor_node_real_addr (exp);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_slice_exp (btor, real_exp->e[0], upper, lower);
  right  = rewrite_slice_exp (btor, real_exp->e[1], upper, lower);
  result = btor_exp_bv_and (btor, left, right);
  btor_node_release (btor, right);
  btor_node_release (btor, left);
  result = btor_node_cond_invert (exp, result);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  (c ? a : b)[upper:lower]
 * result: c ? a[upper:lower] : b[upper:lower]
 */
static inline bool
applies_bcond_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) >= 3
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_cond (exp)
         && (slice_simplifiable (btor_node_real_addr (exp)->e[1])
             || slice_simplifiable (btor_node_real_addr (exp)->e[2]));
}

static inline BtorNode *
apply_bcond_slice (Btor *btor, BtorNode *exp, uint32_t upper, uint32_t lower)
{
  assert (applies_bcond_slice (btor, exp, upper, lower));

  BtorNode *t, *e, *result, *real_exp;

  real_exp = btor_node_real_addr (exp);
  BTOR_INC_REC_RW_CALL (btor);
  t      = rewrite_slice_exp (btor, real_exp->e[1], upper, lower);
  e      = rewrite_slice_exp (btor, real_exp->e[2], upper, lower);
  result = rewrite_cond_exp (btor, real_exp->e[0], t, e);
  btor_node_release (btor, e);
  btor_node_release (btor, t);
  result = btor_node_cond_invert (exp, result);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

static inline bool
applies_zero_lower_slice (Btor *btor,
                          BtorNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  (void) upper;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && lower == 0
         && upper < btor_node_bv_get_width (btor, exp) / 2
         && (btor_node_is_bv_mul (exp) || btor_node_is_bv_add (exp));
  //	     || btor_node_is_bv_and (exp));
}

static inline BtorNode *
apply_zero_lower_slice (Btor *btor,
                        BtorNode *exp,
                        uint32_t upper,
                        uint32_t lower)
{
  BtorNode *result, *real_exp, *tmp1, *tmp2;

  real_exp = btor_node_real_addr (exp);
  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = rewrite_slice_exp (btor, real_exp->e[0], upper, lower);
  tmp2   = rewrite_slice_exp (btor, real_exp->e[1], upper, lower);
  result = btor_rewrite_binary_exp (btor, real_exp->kind, tmp1, tmp2);
  result = btor_node_cond_invert (exp, result);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp1);
  btor_node_release (btor, tmp2);
  return result;
}

/* EQ rules                                                                   */
/* -------------------------------------------------------------------------- */

/*
 * match:  a = a
 * result: true
 */
static inline bool
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
  return btor_exp_true (btor);
}

/*
 * match:  a = b, where a != b
 * result: false
 */
static inline bool
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
  return btor_exp_false (btor);
}

/*
 * match:  a + b = a
 * result: b = 0
 *
 * This rule does not lead to less substitutions. 'a' cannot
 * be substituted as the occurrence check would fail
 */
static inline bool
applies_add_left_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && e0->kind == BTOR_BV_ADD_NODE
         && e0->e[0] == e1;
}

static inline BtorNode *
apply_add_left_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_left_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, tmp, e0->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  b + a = a
 * result: b = 0
 *
 * This rule does not lead to less substitutions. 'a' cannot
 * be substituted as the occurrence check would fail
 */
static inline bool
applies_add_right_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && e0->kind == BTOR_BV_ADD_NODE
         && e0->e[1] == e1;
}

static inline BtorNode *
apply_add_right_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_add_right_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, tmp, e0->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  a + b = a + c
 * result: b = c
 */
static inline bool
applies_add_add_1_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && e0->kind == BTOR_BV_ADD_NODE && e1->kind == BTOR_BV_ADD_NODE
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

/*
 * match:  a + b = c + a
 * result: b = c
 */
static inline bool
applies_add_add_2_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && e0->kind == BTOR_BV_ADD_NODE && e1->kind == BTOR_BV_ADD_NODE
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

/*
 * match:  b + a = a + c
 * result: b = c
 */
static inline bool
applies_add_add_3_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && e0->kind == BTOR_BV_ADD_NODE && e1->kind == BTOR_BV_ADD_NODE
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

/*
 * match:  b + a = c + a
 * result: b = c
 */
static inline bool
applies_add_add_4_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && e0->kind == BTOR_BV_ADD_NODE && e1->kind == BTOR_BV_ADD_NODE
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

/*
 * match:  t = a - b   (t = a + ~b + 1)
 * result: t + b = a
 */
static inline bool
applies_sub_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_regular (e1)
         && btor_node_is_bv_add (e1)
         && ((btor_node_is_regular (e1->e[0])
              && btor_node_is_neg (btor, e1->e[0], 0))
             || (btor_node_is_regular (e1->e[1])
                 && btor_node_is_neg (btor, e1->e[1], 0)));
}

static inline BtorNode *
apply_sub_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_sub_eq (btor, e0, e1));

  BtorNode *result;
  BtorNode *neg = 0, *other;

  if (btor_node_is_neg (btor, e1->e[0], &neg))
    other = e1->e[1];
  else
  {
    btor_node_is_neg (btor, e1->e[1], &neg);
    other = e1->e[0];
  }
  assert (neg);

  BTOR_INC_REC_RW_CALL (btor);
  BtorNode *lhs = rewrite_add_exp (btor, e0, neg);
  result        = rewrite_eq_exp (btor, lhs, other);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, lhs);
  return result;
}

#if 0
/*
 * match:  a & b = ~a & ~b
 * result: a = ~b
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_1_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
	 && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && !btor_node_is_inverted (e0)
	 && !btor_node_is_inverted (e1)
	 && e0->kind == BTOR_BV_AND_NODE
	 && e1->kind == BTOR_BV_AND_NODE
	 && e0->e[0] == btor_node_invert (e1->e[0])
	 && e0->e[1] == btor_node_invert (e1->e[1])
	 && btor_node_is_inverted (e0->e[0]) ==
	    btor_node_is_inverted (e0->e[1]);
}

static inline BtorNode * 
apply_and_and_1_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_and_and_1_eq (btor, e0, e1));
  assert (btor_node_is_inverted (e1->e[0]) == btor_node_is_inverted (e1->e[1]));
  (void) e1;

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[0], btor_node_invert (e0->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  ~a & b = a & ~b
 * result: a = b
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_2_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
	 && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && !btor_node_is_inverted (e0)
	 && !btor_node_is_inverted (e1)
	 && e0->kind == BTOR_BV_AND_NODE
	 && e1->kind == BTOR_BV_AND_NODE
	 && e0->e[0] == btor_node_invert (e1->e[0])
	 && e0->e[1] == btor_node_invert (e1->e[1])
	 && btor_node_is_inverted (e0->e[0]) !=
	    btor_node_is_inverted (e0->e[1]);
}

static inline BtorNode * 
apply_and_and_2_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_and_and_2_eq (btor, e0, e1));
  assert (btor_node_is_inverted (e1->e[0]) != btor_node_is_inverted (e1->e[1]));
  (void) e1;

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, btor_node_real_addr (e0->e[0]),
				btor_node_real_addr (e0->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a & b = a & ~b
 * result: a = 0
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_3_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
	 && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && !btor_node_is_inverted (e0)
	 && !btor_node_is_inverted (e1)
	 && e0->kind == BTOR_BV_AND_NODE
	 && e1->kind == BTOR_BV_AND_NODE
	 && e0->e[0] == e1->e[0] 
	 && e0->e[1] == btor_node_invert (e1->e[1]);
}

static inline BtorNode * 
apply_and_and_3_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_and_and_3_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[0], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  a & b = ~a & b
 * result: b = 0
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_4_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
	 && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && !btor_node_is_inverted (e0)
	 && !btor_node_is_inverted (e1)
	 && e0->kind == BTOR_BV_AND_NODE
	 && e1->kind == BTOR_BV_AND_NODE
	 && e0->e[0] == btor_node_invert (e1->e[0]) 
	 && e0->e[1] == e1->e[1];
}

static inline BtorNode * 
apply_and_and_4_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_and_and_4_eq (btor, e0, e1));
  (void) e1;

  BtorNode *tmp, *result;

  tmp = btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_eq_exp (btor, e0->e[1], tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}
#endif

/*
 * match:  b ? a : t = d, where a != d
 * result: !b AND d = t
 */
static inline bool
applies_bcond_uneq_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && btor_node_is_bv_cond (e0)
         && is_always_unequal (btor, e0->e[1], e1);
}

static inline BtorNode *
apply_bcond_uneq_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_uneq_if_eq (btor, e0, e1));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_eq_exp (btor, e0->e[2], e1);
  result = rewrite_and_exp (btor, btor_node_invert (e0->e[0]), tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  b ? a : t = d, where t != d
 * result: b AND a = t
 */
static inline bool
applies_bcond_uneq_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && btor_node_is_bv_cond (e0)
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
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  a = b ? a : c
 * result: b OR a = c
 *
 * match:  a = ~(b ? a : c)
 * result: !b AND a = ~c
 */
static inline bool
applies_bcond_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_cond (e1)
         && btor_node_real_addr (e1)->e[1] == e0;
}

static inline BtorNode *
apply_bcond_if_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_if_eq (btor, e0, e1));

  BtorNode *tmp, *result, *real_e1;

  real_e1 = btor_node_real_addr (e1);

  BTOR_INC_REC_RW_CALL (btor);
  if (btor_node_is_inverted (e1))
  {
    tmp    = rewrite_eq_exp (btor, btor_node_invert (real_e1->e[2]), e0);
    result = rewrite_and_exp (btor, btor_node_invert (real_e1->e[0]), tmp);
  }
  else
  {
    tmp    = rewrite_eq_exp (btor, real_e1->e[2], e0);
    result = btor_exp_bv_or (btor, real_e1->e[0], tmp);
  }
  btor_node_release (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a = b ? c : a
 * result: !b OR a = c
 *
 * match:  a = ~(b ? c : a)
 * result: b AND a = ~c
 */
static inline bool
applies_bcond_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_cond (e1)
         && btor_node_real_addr (e1)->e[2] == e0;
}

static inline BtorNode *
apply_bcond_else_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_else_eq (btor, e0, e1));

  BtorNode *tmp, *result, *real_e1;

  real_e1 = btor_node_real_addr (e1);

  BTOR_INC_REC_RW_CALL (btor);
  if (btor_node_is_inverted (e1))
  {
    tmp    = rewrite_eq_exp (btor, btor_node_invert (real_e1->e[1]), e0);
    result = rewrite_and_exp (btor, real_e1->e[0], tmp);
  }
  else
  {
    tmp    = rewrite_eq_exp (btor, real_e1->e[1], e0);
    result = btor_exp_bv_or (btor, btor_node_invert (real_e1->e[0]), tmp);
  }
  btor_node_release (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  (x ? a : b) = (x : c : d), where either a = c or b = d
 * result: x ? a = c : b = d
 */
static inline bool
applies_bcond_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_cond (real_e0) && btor_node_is_bv_cond (real_e1)
         && btor_node_is_inverted (e0)
                == btor_node_is_inverted (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_eq (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_eq_exp (btor,
                         btor_node_cond_invert (e0, real_e0->e[1]),
                         btor_node_cond_invert (e1, real_e1->e[1]));
  right  = rewrite_eq_exp (btor,
                          btor_node_cond_invert (e0, real_e0->e[2]),
                          btor_node_cond_invert (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, left);
  btor_node_release (btor, right);
  return result;
}

/*
 * match:  a * b + a * c
 * result: a * (b + c)
 */
static inline bool
applies_add_mul_distrib (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && btor_node_is_bv_mul (e0) && btor_node_is_bv_mul (e1)
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
  btor_node_release (btor, add);
  return result;
}

/*
 * match:  a * (b + c) = a * b + a * c
 * result: true
 */
static inline bool
applies_distrib_add_mul_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  bool result;
  BtorNode *tmp = 0;

  result = btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
           && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
           && btor_node_is_bv_mul (e0) && btor_node_is_bv_add (e1)
           && applies_add_mul_distrib (btor, e1->e[0], e1->e[1])
           && (tmp = apply_add_mul_distrib (btor, e1->e[0], e1->e[1]))
           && tmp == e0;
  if (tmp) btor_node_release (btor, tmp);
  return result;
}

static inline BtorNode *
apply_distrib_add_mul_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_distrib_add_mul_eq (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_exp_true (btor);
}

/*
 * match:  a :: b = c
 * result: a[u:l] = c[u:l] AND (a::b)[l:0] = c[l:0]
 * with: u: len(c)-1
 *       l: len(c)-len(a)+1
 *
 * push eq down over concats
 */
static inline bool
applies_concat_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_real_addr (e0)->kind == BTOR_BV_CONCAT_NODE;
}

static inline BtorNode *
apply_concat_eq (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_concat_eq (btor, e0, e1));

  uint32_t upper, lower;
  BtorNode *real_e0, *tmp1, *tmp2, *tmp3, *tmp4, *result, *eq1, *eq2;

  real_e0 = btor_node_real_addr (e0);

  BTOR_INC_REC_RW_CALL (btor);
  upper = btor_node_bv_get_width (btor, real_e0) - 1;
  lower = upper - btor_node_bv_get_width (btor, real_e0->e[0]) + 1;

  tmp1 = rewrite_slice_exp (btor, e0, upper, lower);
  tmp2 = rewrite_slice_exp (btor, e1, upper, lower);
  lower--;
  tmp3 = rewrite_slice_exp (btor, e0, lower, 0);
  tmp4 = rewrite_slice_exp (btor, e1, lower, 0);

  /* creating two slices on e1 does not really improve the situation here,
   * hence only create a result if a slice on e1 yields a result different
   * from a slice (through further rewriting) */
  if (!(btor_node_is_bv_slice (tmp2) && btor_node_is_bv_slice (tmp4)))
  {
    eq1    = rewrite_eq_exp (btor, tmp1, tmp2);
    eq2    = rewrite_eq_exp (btor, tmp3, tmp4);
    result = rewrite_and_exp (btor, eq1, eq2);
    btor_node_release (btor, eq1);
    btor_node_release (btor, eq2);
  }
  else
    result = 0;

  btor_node_release (btor, tmp1);
  btor_node_release (btor, tmp2);
  btor_node_release (btor, tmp3);
  btor_node_release (btor, tmp4);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

#if 0
static inline bool
applies_zero_eq_and_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  BtorNode *real_e1;
  real_e1 = btor_node_real_addr (e1);
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
	 && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && is_const_zero_exp (btor, e0)
	 && btor_node_is_bv_and (real_e1)
	 && (btor_node_is_bv_const (real_e1->e[0])
	     || btor_node_is_bv_const (real_e1->e[1]));
}

static inline BtorNode *
apply_zero_eq_and_eq (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  (void) e0;
  uint32_t len, upper, lower;
  BtorNode *result, *real_e1, *masked, *zero, *slice; 
  BtorSortId sort;

  real_e1 = btor_node_real_addr (e1);

  if (is_bit_mask (real_e1->e[0], &upper, &lower))
    masked = real_e1->e[1];
  else if (is_bit_mask (real_e1->e[1], &upper, &lower))
    masked = real_e1->e[0];
  else
    return 0;

  len = upper - lower + 1;

  BTOR_INC_REC_RW_CALL (btor);
  sort = btor_sort_bv (btor, len);
  zero = btor_exp_bv_zero (btor, sort);
  btor_sort_release (btor, sort);
  slice = rewrite_slice_exp (btor, masked, upper, lower);
  result = rewrite_eq_exp (btor, zero, slice);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, zero);
  btor_node_release (btor, slice);
  return result;
}
#endif


/* ULT rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a < a
 * result: false
 */
static inline bool
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
  return btor_exp_false (btor);
}

/*
 * match:  a < b, where len(a) = 1
 * result: !a AND b
 */
static inline bool
applies_bool_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_bv_get_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_ult (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, btor_node_invert (e0), e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  (a::b) < (a::c)
 * result: b < c
 */
static inline bool
applies_concat_upper_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && btor_node_is_bv_concat (e0) && e0->kind == e1->kind
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

/*
 * match:  (b::a) < (c::a)
 * result: b < c
 */
static inline bool
applies_concat_lower_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && btor_node_is_bv_concat (e0) && e0->kind == e1->kind
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

/*
 * match:  (x ? a : b) < (x : c : d), where either a = c or b = d
 * result: x ? a < c : b < d
 */
static inline bool
applies_bcond_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_cond (real_e0) && btor_node_is_bv_cond (real_e1)
         && btor_node_is_inverted (e0)
                == btor_node_is_inverted (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_ult (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_ult (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_ult_exp (btor,
                          btor_node_cond_invert (e0, real_e0->e[1]),
                          btor_node_cond_invert (e1, real_e1->e[1]));
  right  = rewrite_ult_exp (btor,
                           btor_node_cond_invert (e0, real_e0->e[2]),
                           btor_node_cond_invert (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, left);
  btor_node_release (btor, right);
  return result;
}


/* AND rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a & a
 * result: a
 */
static inline bool
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
  return btor_node_copy (btor, e0);
}

/*
 * match:  a & ~a
 * result: 0
 */
static inline bool
applies_contr1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return btor_node_invert (e0) == e1;
}

static inline BtorNode *
apply_contr1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr1_and (btor, e0, e1));
  (void) e1;
  return btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
}

/*
 * match: a & b & c & d, where a = ~c OR a = ~d OR b = ~c OR b = ~d
 * result: false
 *
 * second rule of contradiction
 */
static inline bool
applies_contr2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return btor_node_is_bv_and (e0) && btor_node_is_bv_and (e1)
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && (e0->e[0] == btor_node_invert (e1->e[0])
             || e0->e[0] == btor_node_invert (e1->e[1])
             || e0->e[1] == btor_node_invert (e1->e[0])
             || e0->e[1] == btor_node_invert (e1->e[1]));
}

static inline BtorNode *
apply_contr2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr2_and (btor, e0, e1));
  (void) e1;
  return btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
}

/*
 * match: a & b & c & d, where a = c or b = c
 * result: a & b & d
 *
 * symmetric rule of idempotency
 */
static inline bool
applies_idem2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (e0)
         && btor_node_is_bv_and (e1) && !btor_node_is_inverted (e0)
         && !btor_node_is_inverted (e1)
         && (real_e0->e[0] == real_e1->e[0] || real_e0->e[1] == real_e1->e[0]);
}

static inline BtorNode *
apply_idem2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_idem2_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, btor_node_real_addr (e1)->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: a & b & c & d, where a = d OR b = d
 * result: a & b & c
 *
 * use commutativity
 */
static inline bool
applies_comm_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (e0)
         && btor_node_is_bv_and (e1) && !btor_node_is_inverted (e0)
         && !btor_node_is_inverted (e1)
         && (real_e0->e[0] == real_e1->e[1] || real_e0->e[1] == real_e1->e[1]);
}

static inline BtorNode *
apply_comm_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_comm_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, btor_node_real_addr (e1)->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: a & b & ~(c & d), where a = c OR a = d OR b = c OR b = d
 * result: a & b
 */
static inline bool
applies_subsum1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor_node_is_bv_and (e0) && btor_node_is_bv_and (e1)
         && !btor_node_is_inverted (e0) && btor_node_is_inverted (e1)
         && (real_e0->e[0] == btor_node_invert (real_e1->e[0])
             || real_e0->e[0] == btor_node_invert (real_e1->e[1])
             || real_e0->e[1] == btor_node_invert (real_e1->e[0])
             || real_e0->e[1] == btor_node_invert (real_e1->e[1]));
}

static inline BtorNode *
apply_subsum1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subsum1_and (btor, e0, e1));
  (void) e1;
  return btor_node_copy (btor, e0);
}

/*
 * match: a & b & ~(c & d), where a = c OR b = c
 * result: a & b & ~d
 *
 * symmetric rule of substitution
 */
static inline bool
applies_subst1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_bv_and (real_e1) && !btor_node_is_inverted (e0)
         && btor_node_is_inverted (e1)
         && (real_e1->e[0] == real_e0->e[1] || real_e1->e[0] == real_e0->e[0]);
}

static inline BtorNode *
apply_subst1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst1_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, e0, btor_node_invert (btor_node_real_addr (e1)->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: a & b & ~(c & d), where a = d OR b = d
 * result: a & b & ~c
 *
 * symmetric rule of substitution
 */
static inline bool
applies_subst2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_bv_and (real_e1) && !btor_node_is_inverted (e0)
         && btor_node_is_inverted (e1)
         && (real_e1->e[1] == real_e0->e[1] || real_e1->e[1] == real_e0->e[0]);
}

static inline BtorNode *
apply_subst2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst2_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, e0, btor_node_invert (btor_node_real_addr (e1)->e[0]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: a XNOR b, where len(a) = 1
 * result: a = b
 */
static inline bool
applies_bool_xnor_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_bv_and (real_e1) && btor_node_is_inverted (e0)
         && btor_node_is_inverted (e1)
         && btor_node_bv_get_width (btor, real_e0) == 1
         && btor_node_is_inverted (real_e0->e[0])
                != btor_node_is_inverted (real_e0->e[1])
         && btor_node_is_inverted (real_e1->e[0])
                != btor_node_is_inverted (real_e1->e[1])
         && ((real_e0->e[0] == btor_node_invert (real_e1->e[0])
              && real_e0->e[1] == btor_node_invert (real_e1->e[1]))
             || (real_e0->e[0] == btor_node_invert (real_e1->e[1])
                 && real_e0->e[1] == btor_node_invert (real_e1->e[0])));
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
                      btor_node_real_addr (btor_node_real_addr (e0)->e[0]),
                      btor_node_real_addr (btor_node_real_addr (e0)->e[1]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: ~(a & b) & ~(c & d), where (a = c AND b = ~d) OR (a = d AND b = ~c)
 * result: ~a
 *
 * rule of resolution
 */
static inline bool
applies_resol1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_bv_and (real_e1) && btor_node_is_inverted (e0)
         && btor_node_is_inverted (e1)
         && ((real_e0->e[0] == real_e1->e[0]
              && real_e0->e[1] == btor_node_invert (real_e1->e[1]))
             || (real_e0->e[0] == real_e1->e[1]
                 && real_e0->e[1] == btor_node_invert (real_e1->e[0])));
}

static inline BtorNode *
apply_resol1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_resol1_and (btor, e0, e1));
  (void) e1;
  return btor_node_invert (
      btor_node_copy (btor, btor_node_real_addr (e0)->e[0]));
}

/*
 * match: ~(a & b) & ~(c & d), where (~a = c AND b = d) OR (a = d AND ~b = c)
 * result: ~a
 *
 * rule of resolution
 */
static inline bool
applies_resol2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_bv_and (real_e1) && btor_node_is_inverted (e0)
         && btor_node_is_inverted (e1)
         && ((real_e1->e[1] == real_e0->e[1]
              && real_e1->e[0] == btor_node_invert (real_e0->e[0]))
             || (real_e1->e[1] == real_e0->e[0]
                 && real_e1->e[0] == btor_node_invert (real_e0->e[1])));
}

static inline BtorNode *
apply_resol2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_resol2_and (btor, e0, e1));
  (void) e0;
  return btor_node_invert (
      btor_node_copy (btor, btor_node_real_addr (e1)->e[1]));
}

/*
 * match: ~(a & b) & c, where a == ~c OR b == ~c
 * result: c
 *
 * first rule of subsumption
 */
static inline bool
applies_subsum2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor_node_is_bv_and (real_e0) && btor_node_is_inverted (e0)
         && (real_e0->e[0] == btor_node_invert (e1)
             || real_e0->e[1] == btor_node_invert (e1));
}

static inline BtorNode *
apply_subsum2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subsum2_and (btor, e0, e1));
  (void) e0;
  return btor_node_copy (btor, e1);
}

/*
 * match: ~(a & b) & c, where b = c
 * result: ~a & c
 *
 * asymmetric rule of substitution
 */
static inline bool
applies_subst3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_inverted (e0) && real_e0->e[1] == e1;
}

static inline BtorNode *
apply_subst3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst3_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, btor_node_invert (btor_node_real_addr (e0)->e[0]), e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: ~(a & b) & c, where a = c
 * result: ~b & c
 *
 * asymmetric rule of substitution
 */
static inline bool
applies_subst4_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (real_e0)
         && btor_node_is_inverted (e0) && real_e0->e[0] == e1;
}

static inline BtorNode *
apply_subst4_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_subst4_and (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (
      btor, btor_node_invert (btor_node_real_addr (e0)->e[1]), e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: a & b & c, where a = ~c OR b = ~c
 * result: 0
 *
 * first rule of contradiction
 */
static inline bool
applies_contr3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return btor_node_is_bv_and (e0) && !btor_node_is_inverted (e0)
         && (e0->e[0] == btor_node_invert (e1)
             || e0->e[1] == btor_node_invert (e1));
}

static inline BtorNode *
apply_contr3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr3_and (btor, e0, e1));
  (void) e1;
  return btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
}

/*
 * match: a & b & c, where a = c OR b = c
 * result: a
 *
 * asymmetric rule of idempotency
 */
static inline bool
applies_idem3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return btor_node_is_bv_and (e0) && !btor_node_is_inverted (e0)
         && (e0->e[0] == e1 || e0->e[1] == e1);
}

static inline BtorNode *
apply_idem3_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_idem3_and (btor, e0, e1));
  (void) e1;
  return btor_node_copy (btor, e0);
}

/*
 * match: a & b & c, where a and c are constants
 * result: d & b, where d is a new constant obtained from a & c
 */
static inline bool
applies_const1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (e0)
         && !btor_node_is_inverted (e0) && btor_node_is_bv_const (e1)
         && btor_node_is_bv_const (e0->e[0]);
}

static inline BtorNode *
apply_const1_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const1_and (btor, e0, e1));
  assert (!btor_node_is_bv_const (e0->e[1]));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e1, e0->e[0]);
  result = rewrite_and_exp (btor, tmp, e0->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: a & b & c, where b and c are constants
 * result: d & a, where d is a new constant obtained from b & c
 */
static inline bool
applies_const2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_and (e0)
         && !btor_node_is_inverted (e0) && btor_node_is_bv_const (e1)
         && btor_node_is_bv_const (e0->e[1]);
}

static inline BtorNode *
apply_const2_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const2_and (btor, e0, e1));
  assert (!btor_node_is_bv_const (e0->e[0]));

  BtorNode *tmp, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e1, e0->e[1]);
  result = rewrite_and_exp (btor, tmp, e0->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: (a < b) & (b < a)
 * result: false
 */
static inline bool
applies_ult_false_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return btor_node_is_bv_ult (e0) && btor_node_is_bv_ult (e1)
         && !btor_node_is_inverted (e0) && !btor_node_is_inverted (e1)
         && e0->e[0] == e1->e[1] && e0->e[1] == e1->e[0];
}

static inline BtorNode *
apply_ult_false_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_ult_false_and (btor, e0, e1));
  (void) e0;
  (void) e1;
  return btor_exp_false (btor);
}

/*
 * match: ~(a < b) & ~(b < a)
 * result: a = b
 */
static inline bool
applies_ult_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_ult (real_e0)
         && btor_node_is_bv_ult (real_e1) && btor_node_is_inverted (e0)
         && btor_node_is_inverted (e1) && real_e0->e[0] == real_e1->e[1]
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
      btor, btor_node_real_addr (e0)->e[0], btor_node_real_addr (e0)->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * recursively find contradicting ands
 */
static inline bool
applies_contr_rec_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  uint32_t calls = 0;
  return find_and_contradiction_exp (btor, e0, e0, e1, &calls)
         || find_and_contradiction_exp (btor, e1, e0, e1, &calls);
}

static inline BtorNode *
apply_contr_rec_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_contr_rec_and (btor, e0, e1));
  (void) e1;
  return btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
}

/*
 * match:  (0::a) & (b::0)
 * result: 0
 *
 * match:  (0::a) & (b::1)
 * result: 0::a
 *
 * match: (1::a) & (b::1)
 * result: b::a
 */
static inline bool
applies_concat_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  bool result;
  BtorNode *real_e0, *real_e1, *e00, *e01, *e10, *e11;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  result = btor->rec_rw_calls < BTOR_REC_RW_BOUND
           && btor_node_is_bv_concat (real_e0)
           && btor_node_is_bv_concat (real_e1)
           && btor_node_get_sort_id (real_e0->e[0])
                  == btor_node_get_sort_id (real_e1->e[0]);

  if (!result) return result;

  e00 = btor_node_cond_invert (e0, real_e0->e[0]);
  e01 = btor_node_cond_invert (e0, real_e0->e[1]);
  e10 = btor_node_cond_invert (e1, real_e1->e[0]);
  e11 = btor_node_cond_invert (e1, real_e1->e[1]);
  return ((is_bv_const_zero_or_ones_exp (btor, e00)
           && is_bv_const_zero_or_ones_exp (btor, e11))
          || (is_bv_const_zero_or_ones_exp (btor, e01)
              && is_bv_const_zero_or_ones_exp (btor, e10)));
}

static inline BtorNode *
apply_concat_and (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_concat_and (btor, e0, e1));

  BtorNode *real_e0, *real_e1, *e00, *e01, *e10, *e11, *left, *right, *result;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  e00     = btor_node_cond_invert (e0, real_e0->e[0]);
  e01     = btor_node_cond_invert (e0, real_e0->e[1]);
  e10     = btor_node_cond_invert (e1, real_e1->e[0]);
  e11     = btor_node_cond_invert (e1, real_e1->e[1]);

  BTOR_INC_REC_RW_CALL (btor);
  left   = btor_exp_bv_and (btor, e00, e10);
  right  = btor_exp_bv_and (btor, e01, e11);
  result = rewrite_concat_exp (btor, left, right);
  btor_node_release (btor, right);
  btor_node_release (btor, left);
  BTOR_DEC_REC_RW_CALL (btor);

  return result;
}

#if 0
/*
 * match:
 * result:
 */
static inline bool
applies_and (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && !btor_node_is_inverted (e0)
	 && btor_node_is_bv_cond (e0);
}

static inline BtorNode * 
apply_and (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_and (btor, e0, e1));

}

// TODO (ma): uses shallow substitute, which does not really work
  if (!btor_node_is_inverted (e0) &&
      e0->kind == BTOR_BV_EQ_NODE &&
      btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
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
      btor_node_release (btor, e1_simp);
      if (result)
	{
	  assert (!normalized);
	  return result;
	}
    }

  if (!btor_node_is_inverted (e1) &&
      e1->kind == BTOR_BV_EQ_NODE &&
      btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
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
      btor_node_release (btor, e0_simp);
      if (result)
	{
	  assert (!normalized);
	  return result;
	}
    }
#endif


/* ADD rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a + b, where len(a) = 1
 * result: a XOR b
 */
static inline bool
applies_bool_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_bv_get_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_add (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = btor_exp_bv_xor (btor, e0, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a - b OR -a + b, where a = b
 * result: 0
 */
static inline bool
applies_neg_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return !btor_node_is_inverted (e1) && btor_node_is_bv_add (e1)
         && ((e0 == btor_node_invert (e1->e[0])
              && btor_node_is_bv_const_one (btor, e1->e[1]))
             || (e0 == btor_node_invert (e1->e[1])
                 && btor_node_is_bv_const_one (btor, e1->e[0])));
}

static inline BtorNode *
apply_neg_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_neg_add (btor, e0, e1));
  (void) e1;
  return btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
}

/*
 * match: 0 + b
 * result: b
 */
static inline bool
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
  return btor_node_copy (btor, e1);
}

/*
 * match: c0 + (c1 + b), where c0 and c1 are constants
 * result: c + b, where c is a new constant from c0 + c1
 *
 * recursion is no problem here, as one call leads to
 * folding of constants, and the other call can not
 * trigger the same kind of recursion anymore.
 */
static inline bool
applies_const_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e0)
         && !btor_node_is_inverted (e1) && btor_node_is_bv_add (e1)
         && btor_node_is_bv_const (e1->e[0]);
}

static inline BtorNode *
apply_const_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_lhs_add (btor, e0, e1));
  assert (!btor_node_is_bv_const (e1->e[1]));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_add_exp (btor, e0, e1->e[0]);
  result = rewrite_add_exp (btor, tmp, e1->e[1]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: c0 + (b + c1), where c0 and c1 are constants
 * result: c + b, where c is a new constant from c0 + c1
 *
 * recursion is no problem here, as one call leads to
 * folding of constants, and the other call can not
 * trigger the same kind of recursion anymore.
 */
static inline bool
applies_const_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e0)
         && !btor_node_is_inverted (e1) && btor_node_is_bv_add (e1)
         && btor_node_is_bv_const (e1->e[1]);
}

static inline BtorNode *
apply_const_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_rhs_add (btor, e0, e1));
  assert (!btor_node_is_bv_const (e1->e[0]));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_add_exp (btor, e0, e1->e[1]);
  result = rewrite_add_exp (btor, tmp, e1->e[0]);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
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
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
      btor_node_is_inverted (e0) &&
      btor->rec_rw_calls < BTOR_REC_RW_BOUND &&
      (temp = btor_node_real_addr (e0))->kind == BTOR_BV_ADD_NODE)
    {
      BtorNode * e00 = temp->e[0];
      BtorNode * e01 = temp->e[1];
      BtorNode * one, * sum;
      BTOR_INC_REC_RW_CALL (btor);
      one = btor_exp_bv_one (btor, btor_node_get_sort_id (temp));
      temp = btor_exp_bv_add (btor,
        btor_node_invert (e00), btor_node_invert (e01));
      sum = btor_exp_bv_add (btor, temp, one);
      result = btor_exp_bv_add (btor, sum, e1);
      BTOR_DEC_REC_RW_CALL (btor);
      btor_node_release (btor, sum);
      btor_node_release (btor, temp);
      btor_node_release (btor, one);
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
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
      btor_node_is_inverted (e1) &&
      btor->rec_rw_calls < BTOR_REC_RW_BOUND &&
      (temp = btor_node_real_addr (e1))->kind == BTOR_BV_ADD_NODE)
    {
      BtorNode * e10 = temp->e[0];
      BtorNode * e11 = temp->e[1];
      BtorNode * one, * sum;
      BTOR_INC_REC_RW_CALL (btor);
      one = btor_exp_bv_one (btor, btor_node_get_sort_id (temp));
      temp = btor_exp_bv_add (btor, 
        btor_node_invert (e10), btor_node_invert (e11));
      sum = btor_exp_bv_add (btor, temp, one);
      result = btor_exp_bv_add (btor, e0, sum);
      BTOR_DEC_REC_RW_CALL (btor);
      btor_node_release (btor, sum);
      btor_node_release (btor, temp);
      btor_node_release (btor, one);
      return result;
    }
#endif

/*
 * match:  ~(c * a) + b
 * result: ((-c) * a - 1) + b
 */
static inline bool
applies_const_neg_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_inverted (e0)
         && btor_node_is_bv_mul (real_e0)
         && btor_node_is_bv_const (real_e0->e[0]);
}

static inline BtorNode *
apply_const_neg_lhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_neg_lhs_add (btor, e0, e1));

  BtorNode *result, *real_e0, *e00, *e01, *n00, *n01, *one, *sum, *tmp;

  real_e0 = btor_node_real_addr (e0);
  e00     = real_e0->e[0];
  e01     = real_e0->e[1];

  BTOR_INC_REC_RW_CALL (btor);
  n00    = btor_exp_bv_neg (btor, e00);
  n01    = btor_node_copy (btor, e01);
  one    = btor_exp_bv_one (btor, btor_node_get_sort_id (real_e0));
  tmp    = rewrite_mul_exp (btor, n00, n01);
  sum    = btor_exp_bv_sub (btor, tmp, one);
  result = rewrite_add_exp (btor, sum, e1);
  btor_node_release (btor, sum);
  btor_node_release (btor, tmp);
  btor_node_release (btor, one);
  btor_node_release (btor, n00);
  btor_node_release (btor, n01);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  ~(a * c) + b
 * result: (a * (-c) - 1) + b
 */
static inline bool
applies_const_neg_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_inverted (e0)
         && btor_node_is_bv_mul (real_e0)
         && btor_node_is_bv_const (real_e0->e[1]);
}

static inline BtorNode *
apply_const_neg_rhs_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_neg_rhs_add (btor, e0, e1));

  BtorNode *result, *real_e0, *e00, *e01, *n00, *n01, *one, *sum, *tmp;

  real_e0 = btor_node_real_addr (e0);
  e00     = real_e0->e[0];
  e01     = real_e0->e[1];

  BTOR_INC_REC_RW_CALL (btor);
  n00    = btor_node_copy (btor, e00);
  n01    = btor_exp_bv_neg (btor, e01);
  one    = btor_exp_bv_one (btor, btor_node_get_sort_id (real_e0));
  tmp    = rewrite_mul_exp (btor, n00, n01);
  sum    = btor_exp_bv_sub (btor, tmp, one);
  result = rewrite_add_exp (btor, sum, e1);
  btor_node_release (btor, sum);
  btor_node_release (btor, tmp);
  btor_node_release (btor, one);
  btor_node_release (btor, n00);
  btor_node_release (btor, n01);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a + a
 * result: 2 * a
 */
static inline bool
applies_mult_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && e0 == e1
         && btor_node_bv_get_width (btor, e0) >= 2;
}

static inline BtorNode *
apply_mult_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_mult_add (btor, e0, e1));
  (void) e1;

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = btor_exp_bv_int (btor, 2, btor_node_get_sort_id (e0));
  result = rewrite_mul_exp (btor, e0, tmp);
  btor_node_release (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a + ~a
 * result: -1
 */
static inline bool
applies_not_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  return btor_node_real_addr (e0) == btor_node_real_addr (e1) && e0 != e1;
}

static inline BtorNode *
apply_not_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_not_add (btor, e0, e1));
  (void) e1;
  return btor_exp_bv_ones (btor, btor_node_get_sort_id (e0));
}

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/*
 * match:  (x ? a : b) + (x : c : d), where either a = c or b = d
 * result: x ? a + c : b + d
 */
static inline bool
applies_bcond_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_cond (real_e0) && btor_node_is_bv_cond (real_e1)
         && btor_node_is_inverted (e0)
                == btor_node_is_inverted (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_add (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_add_exp (btor,
                          btor_node_cond_invert (e0, real_e0->e[1]),
                          btor_node_cond_invert (e1, real_e1->e[1]));
  right  = rewrite_add_exp (btor,
                           btor_node_cond_invert (e0, real_e0->e[2]),
                           btor_node_cond_invert (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, left);
  btor_node_release (btor, right);
  return result;
}

static inline bool
applies_urem_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return is_urem_exp (btor, e0, e1, 0, 0);
}

static inline BtorNode *
apply_urem_add (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_urem_add (btor, e0, e1));

  BtorNode *x, *y;
  is_urem_exp (btor, e0, e1, &x, &y);
  return rewrite_urem_exp (btor, x, y);
}


/* MUL rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a * b, wher len(a) = 1
 * result: a & b
 */
static inline bool
applies_bool_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_bv_get_width (btor, e0) == 1;
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

/*
 * match: c0 * (c1 * b), where c0 and c1 are constants
 * result: c * b, where c is a new constant from c0 * c1
 */
static inline bool
applies_const_lhs_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e0)
         && !btor_node_is_inverted (e1) && btor_node_is_bv_mul (e1)
         && btor_node_is_bv_const (e1->e[0]);
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
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: c0 * (b * c1), where c0 and c1 are constants
 * result: c * b, where c is a new constant from c0 * c1
 */
static inline bool
applies_const_rhs_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e0)
         && !btor_node_is_inverted (e1) && btor_node_is_bv_mul (e1)
         && btor_node_is_bv_const (e1->e[1]);
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
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: c0 * (a + c1)
 * result: c0 * a + c, where c is a new constant from c0 * c1
 */
static inline bool
applies_const_mul (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e0)
         && !btor_node_is_inverted (e1) && btor_node_is_bv_add (e1)
         && (btor_node_is_bv_const (e1->e[0])
             || btor_node_is_bv_const (e1->e[1]));
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
  btor_node_release (btor, left);
  btor_node_release (btor, right);
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
	  BtorNode * tmp, * one = btor_exp_bv_one (btor, btor_node_get_sort_id (result));
	  BTOR_INC_REC_RW_CALL (btor);
	  tmp = btor_exp_bv_add (btor, btor_node_invert (result), one);
	  BTOR_DEC_REC_RW_CALL (btor);
	  btor_node_release (btor, one);
	  result = tmp;
	  goto HAVE_RESULT_BUT_MIGHT_NEED_TO_RELEASE_SOMETHING;
	}
    }
#endif

#if 0
// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/* match:  (x ? a : b) * (x : c : d), where either a = c or b = d
 * result: x ? a * c : b * d 
 */
static inline bool
applies_bcond_mul (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
	 && btor_node_is_bv_cond (real_e0)
	 && btor_node_is_bv_cond (real_e1)
	 && btor_node_is_inverted (e0) == btor_node_is_inverted (e1) // TODO: needed?
	 && real_e0->e[0] == real_e1->e[0]
	 && (real_e0->e[1] == real_e1->e[1]
	     || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode * 
apply_bcond_mul (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  assert (applies_bcond_mul (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left = rewrite_mul_exp (btor,
			  btor_node_cond_invert (e0, real_e0->e[1]),
			  btor_node_cond_invert (e1, real_e1->e[1]));
  right = rewrite_mul_exp (btor,
			   btor_node_cond_invert (e0, real_e0->e[2]),
			   btor_node_cond_invert (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, left);
  btor_node_release (btor, right);
  return result;
}
#endif


/* UDIV rules                                                                 */
/* -------------------------------------------------------------------------- */

/*
 * match: a / b, where len(a) = 1
 * result: ~(~a & b)
 */
static inline bool
applies_bool_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_bv_get_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_udiv (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = btor_node_invert (rewrite_and_exp (btor, btor_node_invert (e0), e1));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a / 2^n
 * result: 0 :: a[len(a)-1:n]
 */
static inline bool
applies_power2_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && !btor_node_is_inverted (e1)
         && btor_node_is_bv_const (e1)
         && btor_bv_power_of_two (btor_node_bv_const_get_bits (e1)) > 0;
}

static inline BtorNode *
apply_power2_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_power2_udiv (btor, e0, e1));

  uint32_t l, n;
  BtorNode *slice, *pad, *result;
  BtorSortId sort;

  n = btor_bv_power_of_two (btor_node_bv_const_get_bits (e1));
  l = btor_node_bv_get_width (btor, e0);
  assert (l > n);

  BTOR_INC_REC_RW_CALL (btor);
  slice = rewrite_slice_exp (btor, e0, l - 1, n);
  sort  = btor_sort_bv (btor, n);
  pad   = btor_exp_bv_zero (btor, sort);
  btor_sort_release (btor, sort);
  result = rewrite_concat_exp (btor, pad, slice);
  BTOR_DEC_REC_RW_CALL (btor);
  assert (btor_node_bv_get_width (btor, result) == l);
  btor_node_release (btor, pad);
  btor_node_release (btor, slice);
  return result;
}

/*
 * match: a / a
 * result: 1, if a != 0 and UINT32_MAX otherwise
 */
static inline bool
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

  real_e0 = btor_node_real_addr (e0);
  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = btor_exp_bv_zero (btor, btor_node_get_sort_id (real_e0));
  tmp2   = btor_exp_bv_one (btor, btor_node_get_sort_id (real_e0));
  tmp3   = btor_exp_bv_ones (btor, btor_node_get_sort_id (real_e0));
  eq     = rewrite_eq_exp (btor, e0, tmp1);
  result = rewrite_cond_exp (btor, eq, tmp3, tmp2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, eq);
  btor_node_release (btor, tmp1);
  btor_node_release (btor, tmp2);
  btor_node_release (btor, tmp3);
  return result;
}

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/*
 * match:  (x ? a : b) / (x : c : d), where either a = c or b = d
 * result: x ? a / c : b / d
 */
static inline bool
applies_bcond_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_cond (real_e0) && btor_node_is_bv_cond (real_e1)
         && btor_node_is_inverted (e0)
                == btor_node_is_inverted (e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BtorNode *
apply_bcond_udiv (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bcond_udiv (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left   = rewrite_udiv_exp (btor,
                           btor_node_cond_invert (e0, real_e0->e[1]),
                           btor_node_cond_invert (e1, real_e1->e[1]));
  right  = rewrite_udiv_exp (btor,
                            btor_node_cond_invert (e0, real_e0->e[2]),
                            btor_node_cond_invert (e1, real_e1->e[2]));
  result = rewrite_cond_exp (btor, real_e0->e[0], left, right);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, left);
  btor_node_release (btor, right);
  return result;
}

/* UREM rules                                                                 */
/* -------------------------------------------------------------------------- */

/*
 * match:  a % b, where len(a) = 1
 * result: a & ~b
 */
static inline bool
applies_bool_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_bv_get_width (btor, e0) == 1;
}

static inline BtorNode *
apply_bool_urem (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_bool_urem (btor, e0, e1));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_and_exp (btor, e0, btor_node_invert (e1));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a % a
 * result: 0
 */
static inline bool
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
  return btor_exp_bv_zero (btor, btor_node_get_sort_id (e0));
}

/* CONCAT rules                                                               */
/* -------------------------------------------------------------------------- */

/*
 * match:  (a::c0)::c1
 * result: a::c, where c is a new constant obtained from c0::c1
 */
static inline bool
applies_const_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e1)
         && btor_node_is_bv_concat (real_e0)
         && btor_node_is_bv_const (real_e0->e[1]);
}

static inline BtorNode *
apply_const_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_concat (btor, e0, e1));

  BtorNode *result, *tmp, *real_e0;

  real_e0 = btor_node_real_addr (e0);

  BTOR_INC_REC_RW_CALL (btor);
  tmp =
      rewrite_concat_exp (btor, btor_node_cond_invert (e0, real_e0->e[1]), e1);
  result =
      rewrite_concat_exp (btor, btor_node_cond_invert (e0, real_e0->e[0]), tmp);
  btor_node_release (btor, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match:  a[u1:l1]::a[u2:l2], where l1 = u2 + 1
 * result: a[u1:l2]
 */
static inline bool
applies_slice_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *real_e0, *real_e1;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_inverted (e0) == btor_node_is_inverted (e1)
         && btor_node_is_bv_slice (real_e0) && btor_node_is_bv_slice (real_e1)
         && real_e0->e[0] == real_e1->e[0]
         && btor_node_bv_slice_get_lower (real_e0)
                == btor_node_bv_slice_get_upper (real_e1) + 1;
}

static inline BtorNode *
apply_slice_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_slice_concat (btor, e0, e1));

  BtorNode *result, *real_e0;

  real_e0 = btor_node_real_addr (e0);
  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_slice_exp (btor,
                              real_e0->e[0],
                              btor_node_bv_slice_get_upper (real_e0),
                              btor_node_bv_slice_get_lower (e1));
  BTOR_DEC_REC_RW_CALL (btor);
  result = btor_node_cond_invert (e0, result);
  return result;
}

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
      !btor_node_is_inverted (e0) &&
      e0->kind == BTOR_BCOND_NODE &&
      (btor_is_concat_simplifiable (e0->e[1]) ||
       btor_is_concat_simplifiable (e0->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_exp_bv_concat (btor, e0->e[1], e1);
      e = btor_exp_bv_concat (btor, e0->e[2], e1);
      result = btor_exp_cond (btor, e0->e[0], t, e);
      btor_node_release (btor, e);
      btor_node_release (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
      btor_node_is_inverted (e0) &&
      (real_e0 = btor_node_real_addr (e0))->kind == BTOR_BCOND_NODE &&
      (btor_is_concat_simplifiable (real_e0->e[1]) ||
       btor_is_concat_simplifiable (real_e0->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_exp_bv_concat (btor, btor_node_invert (real_e0->e[1]), e1);
      e = btor_exp_bv_concat (btor, btor_node_invert (real_e0->e[2]), e1);
      result = btor_exp_cond (btor, real_e0->e[0], t, e);
      btor_node_release (btor, e);
      btor_node_release (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
      !btor_node_is_inverted (e1) &&
      e1->kind == BTOR_BCOND_NODE &&
      (btor_is_concat_simplifiable (e1->e[1]) ||
       btor_is_concat_simplifiable (e1->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_exp_bv_concat (btor, e0, e1->e[1]);
      e = btor_exp_bv_concat (btor, e0, e1->e[2]);
      result = btor_exp_cond (btor, e1->e[0], t, e);
      btor_node_release (btor, e);
      btor_node_release (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2 &&
      btor_node_is_inverted (e1) &&
      (real_e1 = btor_node_real_addr (e1))->kind == BTOR_BCOND_NODE &&
      (btor_is_concat_simplifiable (real_e1->e[1]) ||
       btor_is_concat_simplifiable (real_e1->e[2])))
    {
      BTOR_INC_REC_RW_CALL (btor);
      t = btor_exp_bv_concat (btor, e0, btor_node_invert (real_e1->e[1]));
      e = btor_exp_bv_concat (btor, e0, btor_node_invert (real_e1->e[2]));
      result = btor_exp_cond (btor, real_e1->e[0], t, e);
      btor_node_release (btor, e);
      btor_node_release (btor, t);
      BTOR_DEC_REC_RW_CALL (btor);
      return result;
    }
#endif

/*
 * match: (a & b)::c
 * result: (a::c) & (b::c)
 */
static inline bool
applies_and_lhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_e0;
  real_e0 = btor_node_real_addr (e0);
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_and (real_e0)
         && (is_concat_simplifiable (real_e0->e[0])
             || is_concat_simplifiable (real_e0->e[1]));
}

static inline BtorNode *
apply_and_lhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_lhs_concat (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e0;

  real_e0 = btor_node_real_addr (e0);
  BTOR_INC_REC_RW_CALL (btor);
  left =
      rewrite_concat_exp (btor, real_e0->e[0], btor_node_cond_invert (e0, e1));
  right =
      rewrite_concat_exp (btor, real_e0->e[1], btor_node_cond_invert (e0, e1));
  result = btor_exp_bv_and (btor, left, right);
  result = btor_node_cond_invert (e0, result);
  btor_node_release (btor, right);
  btor_node_release (btor, left);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: a::(b & c)
 * result: (a::b) & (a::c)
 */
static inline bool
applies_and_rhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  BtorNode *real_e1;
  real_e1 = btor_node_real_addr (e1);
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_is_bv_and (real_e1)
         && (is_concat_simplifiable (real_e1->e[0])
             || is_concat_simplifiable (real_e1->e[1]));
}

static inline BtorNode *
apply_and_rhs_concat (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_and_rhs_concat (btor, e0, e1));

  BtorNode *result, *left, *right, *real_e1;

  real_e1 = btor_node_real_addr (e1);
  BTOR_INC_REC_RW_CALL (btor);
  left =
      rewrite_concat_exp (btor, btor_node_cond_invert (e1, e0), real_e1->e[0]);
  right =
      rewrite_concat_exp (btor, btor_node_cond_invert (e1, e0), real_e1->e[1]);
  result = btor_exp_bv_and (btor, left, right);
  result = btor_node_cond_invert (e1, result);
  btor_node_release (btor, right);
  btor_node_release (btor, left);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/* SLL rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a << c, where c is a constant
 * result: a[len(a)-val(c)-1:0]::0
 */
static inline bool
applies_const_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e1)
         && btor_node_bv_get_width (btor, e1) <= 32;
}

static inline BtorNode *
apply_const_sll (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_sll (btor, e0, e1));

  uint32_t shiftlen;
  BtorBitVector *bits;
  BtorNode *result, *real_e0, *real_e1, *pad, *slice;
  BtorSortId sort;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  if (is_const_zero_exp (btor, e1)) return btor_node_copy (btor, e0);

  bits = btor_node_bv_const_get_bits (real_e1);
  if (btor_node_is_inverted (e1)) bits = btor_bv_not (btor->mm, bits);
  shiftlen = (uint32_t) btor_bv_to_uint64 (bits);
  if (btor_node_is_inverted (e1)) btor_bv_free (btor->mm, bits);
  assert (shiftlen > 0);
  assert (shiftlen < btor_node_bv_get_width (btor, real_e0));
  BTOR_INC_REC_RW_CALL (btor);
  sort = btor_sort_bv (btor, shiftlen);
  pad  = btor_exp_bv_zero (btor, sort);
  btor_sort_release (btor, sort);
  slice = rewrite_slice_exp (
      btor, e0, btor_node_bv_get_width (btor, real_e0) - shiftlen - 1, 0);
  result = rewrite_concat_exp (btor, slice, pad);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, pad);
  btor_node_release (btor, slice);
  assert (btor_node_get_sort_id (result) == btor_node_get_sort_id (real_e0));
  return result;
}

/* SRL rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a >> c, where c is a constant
 * result: 0::a[len(a)-1:val(c)]
 */
static inline bool
applies_const_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_const (e1)
         && btor_node_bv_get_width (btor, e1) <= 32;
}

static inline BtorNode *
apply_const_srl (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_srl (btor, e0, e1));

  uint32_t shiftlen;
  BtorBitVector *bits;
  BtorNode *result, *real_e0, *real_e1, *pad, *slice;
  BtorSortId sort;

  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  if (is_const_zero_exp (btor, e1)) return btor_node_copy (btor, e0);

  bits = btor_node_bv_const_get_bits (real_e1);
  if (btor_node_is_inverted (e1)) bits = btor_bv_not (btor->mm, bits);
  shiftlen = (uint32_t) btor_bv_to_uint64 (bits);
  if (btor_node_is_inverted (e1)) btor_bv_free (btor->mm, bits);
  assert (shiftlen > 0);
  assert (shiftlen < btor_node_bv_get_width (btor, real_e0));
  BTOR_INC_REC_RW_CALL (btor);
  sort = btor_sort_bv (btor, shiftlen);
  pad  = btor_exp_bv_zero (btor, sort);
  btor_sort_release (btor, sort);
  slice = rewrite_slice_exp (
      btor, e0, btor_node_bv_get_width (btor, real_e0) - 1, shiftlen);
  result = rewrite_concat_exp (btor, pad, slice);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, pad);
  btor_node_release (btor, slice);
  assert (btor_node_get_sort_id (result) == btor_node_get_sort_id (real_e0));
  return result;
}

/* APPLY rules                                                                */
/* -------------------------------------------------------------------------- */

/*
 * match:  (\lambda x . t)(a), where term t does not contain param x
 * result: t
 */
static inline bool
applies_const_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return btor_node_is_lambda (e0)
         && !btor_node_real_addr (btor_node_binder_get_body (e0))
                 ->parameterized;
}

static inline BtorNode *
apply_const_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_const_lambda_apply (btor, e0, e1));
  (void) e1;
  return btor_node_copy (btor,
                         btor_node_binder_get_body (btor_node_real_addr (e0)));
}

/*
 * match:  (\lambda x . x)(a)
 * result: a
 */
static inline bool
applies_param_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return btor_node_is_lambda (e0) && !e0->parameterized
         && btor_node_is_param (btor_node_binder_get_body (e0));
}

static inline BtorNode *
apply_param_lambda_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_param_lambda_apply (btor, e0, e1));

  BtorNode *result, *body;

  body = btor_node_binder_get_body (e0);
  btor_beta_assign_args (btor, e0, e1);
  result = btor_node_copy (
      btor, btor_node_param_get_assigned_exp (btor_node_real_addr (body)));
  btor_beta_unassign_params (btor, e0);
  result = btor_node_cond_invert (body, result);
  return result;
}

/*
 * match:  (\lambda x . f(x))(a)
 * result: f(a)
 */
static inline bool
applies_apply_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) e1;
  BtorNode *real_body;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_lambda (e0)
         && btor_node_is_apply ((real_body = btor_node_real_addr (
                                     btor_node_binder_get_body (e0))))
         && !real_body->e[0]->parameterized;
}

static inline BtorNode *
apply_apply_apply (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_apply_apply (btor, e0, e1));

  BtorNode *result, *real_body, *body;

  body      = btor_node_binder_get_body (e0);
  real_body = btor_node_real_addr (body);
  BTOR_INC_REC_RW_CALL (btor);
  btor_beta_assign_args (btor, e0, e1);
  e1 = btor_beta_reduce_bounded (btor, real_body->e[1], 1);
  btor_beta_unassign_params (btor, e0);
  e0 = btor_simplify_exp (btor, real_body->e[0]);
  assert (btor_node_is_fun (e0));
  assert (btor_node_is_args (e1));
  result = rewrite_apply_exp (btor, e0, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, e1);
  result = btor_node_cond_invert (body, result);
  return result;
}

/*
 * propagate apply over parameterized bv conditionals
 */
static inline bool
applies_prop_apply_lambda (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return btor_node_is_lambda (e0)
         && btor_node_is_bv_cond (btor_node_binder_get_body (e0));
  ;
}

static inline BtorNode *
apply_prop_apply_lambda (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_prop_apply_lambda (btor, e0, e1));

  BtorNode *result, *cur_fun, *next_fun, *cur_args, *e_cond, *array, *args;
  BtorNode *beta_cond, *cur_cond, *real_cur_cond;
  BtorNode *cur_branch, *real_cur_branch;
  BtorNode *index, *write_index, *value;
  bool done, inv_result_tmp;
  uint32_t propagations, apply_propagations, inv_result;

  done               = 0;
  result             = 0;
  propagations       = 0;
  apply_propagations = 0;
  inv_result         = 0;
  inv_result_tmp     = false;

  cur_fun  = e0;
  cur_args = btor_node_copy (btor, e1);

  /* try to propagate apply over bv conditionals were conditions evaluate to
   * true if beta reduced with 'cur_args'. */
  cur_cond =
      btor_node_is_lambda (cur_fun) ? btor_node_binder_get_body (cur_fun) : 0;
  while (!done && btor_node_is_lambda (cur_fun) && !cur_fun->parameterized
         && !cur_args->parameterized
         && (real_cur_cond = btor_node_real_addr (cur_cond))
         && btor_node_is_bv_cond (real_cur_cond)
         /* if the condition is not parameterized the check was already done
          * while creating 'cur_cond' */
         && btor_node_real_addr (real_cur_cond->e[0])->parameterized
         && propagations++ < BTOR_APPLY_PROPAGATION_LIMIT)
  {
    assert (cur_cond);
    assert (btor_node_is_regular (cur_fun));
    assert (btor_node_is_regular (cur_args));
    assert (!result);

    next_fun = 0;
    /* optimization for lambdas representing array writes */
    if (is_write_exp (cur_fun, &array, &write_index, &value))
    {
      index = cur_args->e[0];
      /* found value at 'index' */
      if (write_index == index)
      {
        result = btor_node_copy (btor, value);
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

      if (!btor_node_real_addr (e_cond)->parameterized) break;

      /* 'inv_result_tmp' indicates if the result obtained from the
       * current propagation path needs to be inverted. in case we really
       * find a result, 'inv_result' will be inverted w.r.t.
       * 'inv_result_tmp'. */
      if (btor_node_is_inverted (cur_cond)) inv_result_tmp = !inv_result_tmp;

      btor_beta_assign_args (btor, cur_fun, cur_args);
      beta_cond = btor_beta_reduce_bounded (btor, e_cond, 1);
      /* condition of bv cond is either true or false */
      if (btor_node_is_bv_const (beta_cond))
      {
        if (is_true_cond (beta_cond))
          cur_branch = real_cur_cond->e[1];
        else
          cur_branch = real_cur_cond->e[2];

        real_cur_branch = btor_node_real_addr (cur_branch);
        /* branch not parameterized, we found a result */
        if (!real_cur_branch->parameterized)
        {
          result = btor_node_copy (btor, real_cur_branch);
          done   = 1;
          goto HAVE_RESULT_CHECK_INVERTED;
        }
        else if (btor_node_is_param (real_cur_branch))
        {
          if ((value = btor_node_param_get_assigned_exp (real_cur_branch)))
            result = btor_node_copy (btor, value);
          else
            result = btor_node_copy (btor, real_cur_branch);
          done = 1;
          goto HAVE_RESULT_CHECK_INVERTED;
        }
        /* propagate down to next function */
        else if (btor_node_is_apply (real_cur_branch))
        {
          args = btor_beta_reduce_bounded (btor, real_cur_branch->e[1], 1);
          assert (btor_node_is_regular (args));
          assert (btor_node_is_args (args));
          /* nested lambda */
          if (btor_node_is_lambda (real_cur_branch->e[0])
              && real_cur_branch->e[0]->parameterized)
          {
            btor_beta_assign_args (btor, real_cur_branch->e[0], args);
            result = btor_beta_reduce_bounded (btor, real_cur_branch->e[0], 1);
            btor_beta_unassign_params (btor, real_cur_branch->e[0]);
            assert (!btor_node_is_fun (result));

            /* propagate down to 'next_fun' */
            if (btor_node_is_apply (result))
            {
              next_fun = btor_node_real_addr (result)->e[0];
              btor_node_release (btor, args);
              args = btor_node_copy (btor, btor_node_real_addr (result)->e[1]);
              /* result is not needed here as it may be further
               * rewritten */
              btor_node_release (btor, result);
              result = 0;
            }
            else
              done = 1;
          }
          /* beta reduce parameterized condition and select branch */
          else if (btor_node_is_fun_cond (real_cur_branch->e[0])
                   && real_cur_branch->e[0]->parameterized)
          {
            assert (real_cur_branch->e[0]->e[0]->parameterized);
            assert (!real_cur_branch->e[0]->e[1]->parameterized);
            assert (!real_cur_branch->e[0]->e[2]->parameterized);
            result =
                btor_beta_reduce_bounded (btor, real_cur_branch->e[0]->e[0], 1);

            if (btor_node_is_bv_const (result))
            {
              if (result == btor->true_exp)
                next_fun = real_cur_branch->e[0]->e[1];
              else
                next_fun = real_cur_branch->e[0]->e[2];
            }
            btor_node_release (btor, result);
            result = 0;
            /* no branch can be selected, we are done */
            if (!next_fun)
            {
              btor_node_release (btor, args);
              goto REWRITE_APPLY_NO_RESULT_DONE;
            }
          }
          /* propagate down to 'next_fun' */
          else
          {
            next_fun = real_cur_branch->e[0];
            assert (btor_node_is_fun (next_fun));
          }

          /* set arguments for new functin application */
          btor_node_release (btor, cur_args);
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
          if (btor_node_is_inverted (cur_branch))
            inv_result_tmp = !inv_result_tmp;

          /* we got a result, we can savely set 'inv_result' */
          if (inv_result_tmp)
          {
            inv_result     = !inv_result;
            inv_result_tmp = false;
          }
          apply_propagations++;
        }
        /* check if we can further propagate down along a conditional */
        else if (btor_node_is_bv_cond (real_cur_branch))
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
      btor_beta_unassign_params (btor, cur_fun);
      btor_node_release (btor, beta_cond);
    }

    if (next_fun)
    {
      cur_fun  = next_fun;
      cur_cond = btor_node_is_lambda (cur_fun)
                     ? btor_node_binder_get_body (cur_fun)
                     : 0;
    }
    assert (!result || done);
  }

  /* check if apply was propagated down to 'cur_fun' */
  if (!result && cur_fun != e0)
    result = btor_node_create_apply (btor, cur_fun, cur_args);

  btor_node_release (btor, cur_args);

  if (result && inv_result) result = btor_node_invert (result);

  btor->stats.prop_apply_lambda += apply_propagations;
  return result;
}

/*
 * TODO description
 */
static inline bool
applies_prop_apply_update (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  (void) btor;
  (void) e1;
  return btor_node_is_update (e0);
}

static inline BtorNode *
apply_prop_apply_update (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  assert (applies_prop_apply_update (btor, e0, e1));

  uint32_t propagations = 0, num_eq;
  bool prop_down;
  BtorNode *cur, *args, *value, *a1, *a2, *result = 0, *eq;
  BtorArgsIterator it1, it2;

  cur = e0;
  while (btor_node_is_update (cur))
  {
    args  = cur->e[1];
    value = cur->e[2];

    if (e1 == args)
    {
      propagations++;
      result = btor_node_copy (btor, value);
      break;
    }

    prop_down = false;
    num_eq    = 0;
    assert (e1->sort_id == args->sort_id);
    btor_iter_args_init (&it1, e1);
    btor_iter_args_init (&it2, args);
    while (btor_iter_args_has_next (&it1))
    {
      assert (btor_iter_args_has_next (&it2));
      a1 = btor_iter_args_next (&it1);
      a2 = btor_iter_args_next (&it2);

      if (is_always_unequal (btor, a1, a2))
      {
        prop_down = true;
        break;
      }

      BTOR_INC_REC_RW_CALL (btor);
      eq = rewrite_eq_exp (btor, a1, a2);
      BTOR_DEC_REC_RW_CALL (btor);
      if (eq == btor_node_invert (btor->true_exp))
      {
        btor_node_release (btor, eq);
        prop_down = true;
        break;
      }
      else if (eq == btor->true_exp)
      {
        num_eq++;
      }
      btor_node_release (btor, eq);
    }

    if (num_eq == btor_node_args_get_arity (btor, args))
    {
      propagations++;
      result = btor_node_copy (btor, value);
      break;
    }

    if (prop_down)
    {
      propagations++;
      cur = cur->e[0];
    }
    else
      break;
  }

  /* propagated until 'cur', create apply on 'cur' */
  if (!result)
  {
    BTOR_INC_REC_RW_CALL (btor);
    result = btor_node_create_apply (btor, cur, e1);
    BTOR_DEC_REC_RW_CALL (btor);
  }
  btor->stats.prop_apply_update += propagations;
  return result;
}

/* LAMBDA rules */

#if 0 
// TODO (ma): this rule cannot be applied yet as it may produce lambdas with
//            different sorts
/*
 * match: (\lambda j . (\lambda k . t)(j))
 * result: \lambda k . t
 */
static inline bool
applies_lambda_lambda (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return !btor_node_is_inverted (e1)
	 && btor_node_is_apply (e1)
	 && !e1->e[0]->parameterized
	 && e1->e[1]->arity == 1
	 && e1->e[1]->e[0] == e0;
}

static inline BtorNode *
apply_lambda_lambda (Btor * btor, BtorNode * e0, BtorNode * e1)
{
  return btor_node_copy (btor, e1->e[0]);
}
#endif


/* QUANTIFIER rules                                                           */
/* -------------------------------------------------------------------------- */

/*
 * TODO description
 */
static inline bool
applies_const_quantifier (Btor *btor, BtorNode *param, BtorNode *body)
{
  (void) btor;
  (void) param;
  return !btor_node_real_addr (body)->parameterized;
}

static inline BtorNode *
apply_const_quantifier (Btor *btor, BtorNode *param, BtorNode *body)
{
  assert (applies_const_quantifier (btor, param, body));
  (void) param;
  return btor_node_copy (btor, body);
}

/* FORALL rules                                                               */
/* -------------------------------------------------------------------------- */

#if 0

/*
 * match:  (\forall x . t) where x does not occur in t
 * result: t
 */
static inline bool
applies_param_free_forall (Btor * btor, BtorNode * param, BtorNode * body)
{ 
  (void) btor;
  (void) body;
  return param->parents == 0;
}

static inline BtorNode *
apply_param_free_forall (Btor * btor, BtorNode * param, BtorNode * body)
{
  assert (applies_param_free_forall (btor, param, body));
  (void) param;
  return btor_node_copy (btor, body);
}

#endif

/*
 * match: \forall x . x = t    if x \not \in vars(t)
 * match: \forall x . x != t    if x \not \in vars(t)
 * result: false
 */
static inline bool
applies_eq_forall (Btor *btor, BtorNode *param, BtorNode *body)
{
  (void) btor;
  (void) body;
  BtorNode *real_body;
  real_body = btor_node_real_addr (body);
  return btor_node_is_bv_eq (body)
         && param->parents == 1  // only parent is body
         && ((real_body->e[0] == param
              && !btor_node_real_addr (real_body->e[1])->quantifier_below)
             || (real_body->e[1] == param
                 && !btor_node_real_addr (real_body->e[0])->quantifier_below));
}

static inline BtorNode *
apply_eq_forall (Btor *btor, BtorNode *param, BtorNode *body)
{
  assert (applies_eq_forall (btor, param, body));
  (void) param;
  (void) body;
  return btor_exp_false (btor);
}

#if 0

/* EXISTS rules                                                               */
/* -------------------------------------------------------------------------- */

/*
 * match:  (\exists x . t) where x does not occur in t
 * result: t
 */
static inline bool
applies_param_free_exists (Btor * btor, BtorNode * param, BtorNode * body)
{ 
  (void) btor;
  (void) body;
  return param->parents == 0;
}

static inline BtorNode *
apply_param_free_exists (Btor * btor, BtorNode * param, BtorNode * body)
{
  assert (applies_param_free_exists (btor, param, body));
  (void) param;
  return btor_node_copy (btor, body);
}

#endif

/*
 * match: \exists x . x = t    if x \not \in vars(t)
 * match: \exists x . x != t    if x \not \in vars(t)
 * result: true
 */
static inline bool
applies_eq_exists (Btor *btor, BtorNode *param, BtorNode *body)
{
  (void) btor;
  (void) body;
  BtorNode *real_body;
  real_body = btor_node_real_addr (body);
  return btor_node_is_bv_eq (body)
         && param->parents == 1  // only parent is body
         && ((real_body->e[0] == param
              && !btor_node_real_addr (real_body->e[1])->quantifier_below)
             || (real_body->e[1] == param
                 && !btor_node_real_addr (real_body->e[0])->quantifier_below));
}

static inline BtorNode *
apply_eq_exists (Btor *btor, BtorNode *param, BtorNode *body)
{
  assert (applies_eq_exists (btor, param, body));
  (void) param;
  (void) body;
  return btor_exp_true (btor);
}

/* COND rules                                                                 */
/* -------------------------------------------------------------------------- */

/*
 * match: c ? a : a
 * result: a
 */
static inline bool
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
  return btor_node_copy (btor, e1);
}

/*
 * match: c ? a : b, where c is a constant
 * result: a if c is true, and b otherwise
 */
static inline bool
applies_const_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) btor;
  (void) e1;
  (void) e2;
  return btor_node_is_bv_const (e0);
}

static inline BtorNode *
apply_const_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_const_cond (btor, e0, e1, e2));
  if (btor_bv_get_bit (btor_node_bv_const_get_bits (e0), 0))
    return btor_node_copy (btor, e1);
  return btor_node_copy (btor, e2);
}

/*
 * match: c0 ? (c0 ? a : b) : c
 * result: c0 ? a : c
 */
static inline bool
applies_cond_if_dom_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e2;
  BtorNode *real_e1;
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_cond (real_e1)
         && real_e1->e[0] == e0;
}

static inline BtorNode *
apply_cond_if_dom_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_cond_if_dom_cond (btor, e0, e1, e2));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_cond_exp (
      btor, e0, btor_node_cond_invert (e1, btor_node_real_addr (e1)->e[1]), e2);
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: c0 ? (c1 ? a : b) : a
 * result: c0 AND ~c1 ? b : a
 */
static inline bool
applies_cond_if_merge_if_cond (Btor *btor,
                               BtorNode *e0,
                               BtorNode *e1,
                               BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e1;
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_cond (real_e1)
         && btor_node_cond_invert (e1, real_e1->e[1]) == e2;
}

static inline BtorNode *
apply_cond_if_merge_if_cond (Btor *btor,
                             BtorNode *e0,
                             BtorNode *e1,
                             BtorNode *e2)
{
  assert (applies_cond_if_merge_if_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e10, *e12, *real_e1;

  real_e1 = btor_node_real_addr (e1);
  e10     = real_e1->e[0];
  e12     = btor_node_cond_invert (e1, real_e1->e[2]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e0, btor_node_invert (e10));
  result = rewrite_cond_exp (btor, tmp, e12, e2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: c0 ? (c1 ? b : a) : a
 * result: c0 AND c1 ? b : a
 */
static inline bool
applies_cond_if_merge_else_cond (Btor *btor,
                                 BtorNode *e0,
                                 BtorNode *e1,
                                 BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e1;
  real_e1 = btor_node_real_addr (e1);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_cond (real_e1)
         && btor_node_cond_invert (e1, real_e1->e[2]) == e2;
}

static inline BtorNode *
apply_cond_if_merge_else_cond (Btor *btor,
                               BtorNode *e0,
                               BtorNode *e1,
                               BtorNode *e2)
{
  assert (applies_cond_if_merge_else_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e10, *e11, *real_e1;

  real_e1 = btor_node_real_addr (e1);
  e10     = real_e1->e[0];
  e11     = btor_node_cond_invert (e1, real_e1->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, e0, e10);
  result = rewrite_cond_exp (btor, tmp, e11, e2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: c0 ? a : (c0 ? b : c)
 * result: c0 ? a : c
 */
static inline bool
applies_cond_else_dom_cond (Btor *btor,
                            BtorNode *e0,
                            BtorNode *e1,
                            BtorNode *e2)
{
  (void) e1;
  BtorNode *real_e2;
  real_e2 = btor_node_real_addr (e2);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_cond (real_e2)
         && real_e2->e[0] == e0;
}

static inline BtorNode *
apply_cond_else_dom_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_cond_else_dom_cond (btor, e0, e1, e2));

  BtorNode *result;

  BTOR_INC_REC_RW_CALL (btor);
  result = rewrite_cond_exp (
      btor, e0, e1, btor_node_cond_invert (e2, btor_node_real_addr (e2)->e[2]));
  BTOR_DEC_REC_RW_CALL (btor);
  return result;
}

/*
 * match: c0 ? a : (c1 ? a : b)
 * result: ~c0 AND ~c1 ? b : a
 */
static inline bool
applies_cond_else_merge_if_cond (Btor *btor,
                                 BtorNode *e0,
                                 BtorNode *e1,
                                 BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e2;
  real_e2 = btor_node_real_addr (e2);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_cond (real_e2)
         && btor_node_cond_invert (e2, real_e2->e[1]) == e1;
}

static inline BtorNode *
apply_cond_else_merge_if_cond (Btor *btor,
                               BtorNode *e0,
                               BtorNode *e1,
                               BtorNode *e2)
{
  assert (applies_cond_else_merge_if_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e20, *e22, *real_e2;

  real_e2 = btor_node_real_addr (e2);
  e20     = real_e2->e[0];
  e22     = btor_node_cond_invert (e2, real_e2->e[2]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp = rewrite_and_exp (btor, btor_node_invert (e0), btor_node_invert (e20));
  result = rewrite_cond_exp (btor, tmp, e22, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match: c0 ? a : (c1 ? b : a)
 * result: ~c0 AND c1 ? b : a
 */
static inline bool
applies_cond_else_merge_else_cond (Btor *btor,
                                   BtorNode *e0,
                                   BtorNode *e1,
                                   BtorNode *e2)
{
  (void) e0;
  BtorNode *real_e2;
  real_e2 = btor_node_real_addr (e2);
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_cond (real_e2)
         && btor_node_cond_invert (e2, real_e2->e[2]) == e1;
}

static inline BtorNode *
apply_cond_else_merge_else_cond (Btor *btor,
                                 BtorNode *e0,
                                 BtorNode *e1,
                                 BtorNode *e2)
{
  assert (applies_cond_else_merge_else_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp, *e20, *e21, *real_e2;

  real_e2 = btor_node_real_addr (e2);
  e20     = real_e2->e[0];
  e21     = btor_node_cond_invert (e2, real_e2->e[1]);
  BTOR_INC_REC_RW_CALL (btor);
  tmp    = rewrite_and_exp (btor, btor_node_invert (e0), e20);
  result = rewrite_cond_exp (btor, tmp, e21, e1);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  c ? a : b, where len(a) = 1
 * result: (~c OR a) AND (c OR b)
 */
static inline bool
applies_bool_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  (void) e2;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && btor_node_bv_get_width (btor, e1) == 1;
}

static inline BtorNode *
apply_bool_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_bool_cond (btor, e0, e1, e2));

  BtorNode *tmp1, *tmp2, *result;

  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = btor_exp_bv_or (btor, btor_node_invert (e0), e1);
  tmp2   = btor_exp_bv_or (btor, e0, e2);
  result = rewrite_and_exp (btor, tmp1, tmp2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp1);
  btor_node_release (btor, tmp2);
  return result;
}

/*
 * match:  c ? (a + 1) : a
 * match:  c ? (1 + a) : a
 * result: a + 0::c
 */
static inline bool
applies_add_if_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && !btor_node_is_inverted (e1)
         && btor_node_is_bv_add (e1)
         && ((e1->e[0] == e2 && btor_node_is_bv_const_one (btor, e1->e[1]))
             || (e1->e[1] == e2 && btor_node_is_bv_const_one (btor, e1->e[0])));
}

static inline BtorNode *
apply_add_if_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_add_if_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp    = btor_exp_bv_uext (btor, e0, btor_node_bv_get_width (btor, e1) - 1);
  result = rewrite_add_exp (btor, e2, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  c ? a : (a + 1)
 * match:  c ? a : (1 + a)
 * result: a + 0::c
 */
static inline bool
applies_add_else_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor->rec_rw_calls < BTOR_REC_RW_BOUND && !btor_node_is_inverted (e2)
         && btor_node_is_bv_add (e2)
         && ((e2->e[0] == e1 && btor_node_is_bv_const_one (btor, e2->e[1]))
             || (e2->e[1] == e1 && btor_node_is_bv_const_one (btor, e2->e[0])));
}

static inline BtorNode *
apply_add_else_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_add_else_cond (btor, e0, e1, e2));
  (void) e2;

  BtorNode *result, *tmp;

  BTOR_INC_REC_RW_CALL (btor);
  tmp = btor_exp_bv_uext (
      btor, btor_node_invert (e0), btor_node_bv_get_width (btor, e1) - 1);
  result = rewrite_add_exp (btor, e1, tmp);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  c ? (a::b) : (a::d)
 * result: a :: (c ? b : d)
 *
 * match:  c ? (a::b) : (d::b)
 * result: (c ? a : d) :: b
 */
static inline bool
applies_concat_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  bool result;
  BtorNode *real_e1, *real_e2, *e10, *e11, *e20, *e21;

  real_e1 = btor_node_real_addr (e1);
  real_e2 = btor_node_real_addr (e2);
  result  = btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
           && btor->rec_rw_calls < BTOR_REC_RW_BOUND
           && btor_node_is_bv_concat (real_e1)
           && btor_node_is_bv_concat (real_e2);

  if (!result) return result;

  e10 = btor_node_cond_invert (e1, real_e1->e[0]);
  e11 = btor_node_cond_invert (e1, real_e1->e[1]);
  e20 = btor_node_cond_invert (e2, real_e2->e[0]);
  e21 = btor_node_cond_invert (e2, real_e2->e[1]);
  return (e10 == e20 || e11 == e21);
}

static inline BtorNode *
apply_concat_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (applies_concat_cond (btor, e0, e1, e2));

  BtorNode *result, *tmp1, *tmp2, *real_e1, *real_e2, *e10, *e11, *e20, *e21;
  real_e1 = btor_node_real_addr (e1);
  real_e2 = btor_node_real_addr (e2);
  e10     = btor_node_cond_invert (e1, real_e1->e[0]);
  e11     = btor_node_cond_invert (e1, real_e1->e[1]);
  e20     = btor_node_cond_invert (e2, real_e2->e[0]);
  e21     = btor_node_cond_invert (e2, real_e2->e[1]);

  BTOR_INC_REC_RW_CALL (btor);
  tmp1   = rewrite_cond_exp (btor, e0, e10, e20);
  tmp2   = rewrite_cond_exp (btor, e0, e11, e21);
  result = rewrite_concat_exp (btor, tmp1, tmp2);
  BTOR_DEC_REC_RW_CALL (btor);
  btor_node_release (btor, tmp1);
  btor_node_release (btor, tmp2);
  return result;
}

/*
 * match:  c ? a OP b : a OP d, where OP is either +, &, *, /, %
 * result: a OP (c ? b : d)
 */
static inline bool
applies_op_lhs_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e1) && !btor_node_is_inverted (e2)
         && e1->kind == e2->kind
         && (btor_node_is_bv_add (e1) || btor_node_is_bv_and (e1)
             || btor_node_is_bv_mul (e1) || btor_node_is_bv_udiv (e1)
             || btor_node_is_bv_urem (e1))
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
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  c ? a OP b : d OP b, where OP is either +, &, *, /, %
 * result: (c ? a : d) OP b
 */
static inline bool
applies_op_rhs_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e1) && !btor_node_is_inverted (e2)
         && e1->kind == e2->kind
         && (btor_node_is_bv_add (e1) || btor_node_is_bv_and (e1)
             || btor_node_is_bv_mul (e1) || btor_node_is_bv_udiv (e1)
             || btor_node_is_bv_urem (e1))
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
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  c ? a OP b : d OP a, where OP is either +, &, *
 * result: a OP (c ? b : d)
 */
static inline bool
applies_comm_op_1_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e1) && !btor_node_is_inverted (e2)
         && e1->kind == e2->kind
         && (btor_node_is_bv_add (e1) || btor_node_is_bv_and (e1)
             || btor_node_is_bv_mul (e1))
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
  btor_node_release (btor, tmp);
  return result;
}

/*
 * match:  c ? a OP b : b OP d, where OP is either +, &, *
 * result: b OP (c ? a : d)
 */
static inline bool
applies_comm_op_2_cond (Btor *btor, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  (void) e0;
  return btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
         && btor->rec_rw_calls < BTOR_REC_RW_BOUND
         && !btor_node_is_inverted (e1) && !btor_node_is_inverted (e2)
         && e1->kind == e2->kind
         && (btor_node_is_bv_add (e1) || btor_node_is_bv_and (e1)
             || btor_node_is_bv_mul (e1))
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
  btor_node_release (btor, tmp);
  return result;
}

#if 0
/*
 * match:
 * result:
 */
static inline bool
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
/* normalizers                                                                */
/* -------------------------------------------------------------------------- */

static void
normalize_bin_comm_ass_exp (Btor *btor,
                            BtorNode *e0,
                            BtorNode *e1,
                            BtorNode **e0_norm,
                            BtorNode **e1_norm)
{
  assert (btor);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2);
  assert (e0);
  assert (e1);
  assert (!btor_node_real_addr (e0)->simplified);
  assert (!btor_node_real_addr (e1)->simplified);
  assert (e0_norm);
  assert (e1_norm);
  assert (!btor_node_is_inverted (e0));
  assert (!btor_node_is_inverted (e1));
  assert (btor_node_is_bv_add (e0) || btor_node_is_bv_and (e0)
          || btor_node_is_bv_mul (e0));
  assert (e0->kind == e1->kind);

  size_t i;
  BtorNodeKind kind;
  BtorNode *cur, *result, *temp, *common;
  BtorNodePtrStack stack;
  BtorMemMgr *mm;
  BtorPtrHashTable *left, *right, *comm;
  BtorPtrHashBucket *b;
  BtorPtrHashTableIterator it;
  BtorIntHashTable *cache;

  mm    = btor->mm;
  kind  = e0->kind;
  left  = btor_hashptr_table_new (mm,
                                 (BtorHashPtr) btor_node_hash_by_id,
                                 (BtorCmpPtr) btor_node_compare_by_id);
  right = btor_hashptr_table_new (mm,
                                  (BtorHashPtr) btor_node_hash_by_id,
                                  (BtorCmpPtr) btor_node_compare_by_id);
  comm  = btor_hashptr_table_new (mm,
                                 (BtorHashPtr) btor_node_hash_by_id,
                                 (BtorCmpPtr) btor_node_compare_by_id);
  cache = btor_hashint_table_new (mm);

  if (!btor_opt_get (btor, BTOR_OPT_NORMALIZE))
    goto RETURN_NO_RESULT;

  BTOR_INIT_STACK (mm, stack);
  BTOR_PUSH_STACK (stack, e0);
  do
  {
    cur = BTOR_POP_STACK (stack);
    if (!btor_node_is_inverted (cur) && cur->kind == kind)
    {
      if (btor_hashint_table_contains (cache, cur->id))
      {
        BTOR_RELEASE_STACK (stack);
        goto RETURN_NO_RESULT;
      }
      btor_hashint_table_add (cache, cur->id);
      BTOR_PUSH_STACK (stack, cur->e[1]);
      BTOR_PUSH_STACK (stack, cur->e[0]);
    }
    else
    {
      b = btor_hashptr_table_get (left, cur);
      if (!b)
        btor_hashptr_table_add (left, cur)->data.as_int = 1;
      else
        b->data.as_int++;
    }
  } while (!BTOR_EMPTY_STACK (stack));
  btor_hashint_table_delete (cache);
  cache = btor_hashint_table_new (mm);

  BTOR_PUSH_STACK (stack, e1);
  do
  {
    cur = BTOR_POP_STACK (stack);
    if (!btor_node_is_inverted (cur) && cur->kind == kind)
    {
      if (btor_hashint_table_contains (cache, cur->id))
      {
        BTOR_RELEASE_STACK (stack);
        goto RETURN_NO_RESULT;
      }
      btor_hashint_table_add (cache, cur->id);
      BTOR_PUSH_STACK (stack, cur->e[1]);
      BTOR_PUSH_STACK (stack, cur->e[0]);
    }
    else
    {
      b = btor_hashptr_table_get (left, cur);
      if (b)
      {
        /* we found one common operand */

        /* remove operand from left */
        if (b->data.as_int > 1)
          b->data.as_int--;
        else
        {
          assert (b->data.as_int == 1);
          btor_hashptr_table_remove (left, cur, 0, 0);
        }

        /* insert into common table */
        b = btor_hashptr_table_get (comm, cur);
        if (!b)
          btor_hashptr_table_add (comm, cur)->data.as_int = 1;
        else
          b->data.as_int++;
      }
      else
      {
        /* operand is not common */
        b = btor_hashptr_table_get (right, cur);
        if (!b)
          btor_hashptr_table_add (right, cur)->data.as_int = 1;
        else
          b->data.as_int++;
      }
    }
  } while (!BTOR_EMPTY_STACK (stack));
  BTOR_RELEASE_STACK (stack);

  /* no operand or only one operand in common? leave everything as it is */
  if (comm->count < 2u)
  {
  RETURN_NO_RESULT:
    /* clean up */
    btor_hashptr_table_delete (left);
    btor_hashptr_table_delete (right);
    btor_hashptr_table_delete (comm);
    btor_hashint_table_delete (cache);
    *e0_norm = btor_node_copy (btor, e0);
    *e1_norm = btor_node_copy (btor, e1);
    return;
  }

  if (kind == BTOR_BV_AND_NODE)
    btor->stats.ands_normalized++;
  else if (kind == BTOR_BV_ADD_NODE)
    btor->stats.adds_normalized++;
  else
  {
    assert (kind == BTOR_BV_MUL_NODE);
    btor->stats.muls_normalized++;
  }

  assert (comm->count >= 2u);

  /* normalize common nodes */
  BTOR_INIT_STACK (mm, stack);
  b = comm->first;
  while (b)
  {
    cur = b->key;
    assert (b->data.as_int >= 0);
    for (i = 0; i < (size_t) b->data.as_int; i++) BTOR_PUSH_STACK (stack, cur);
    b = b->next;
  }

  qsort (
      stack.start, BTOR_COUNT_STACK (stack), sizeof (BtorNode *), cmp_node_id);

  common = btor_node_copy (btor, BTOR_PEEK_STACK (stack, 0));
  for (i = 1; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur  = BTOR_PEEK_STACK (stack, i);
    temp = btor_rewrite_binary_exp (btor, kind, common, cur);
    btor_node_release (btor, common);
    common = temp;
  }
  BTOR_RELEASE_STACK (stack);

#if 0
  /* normalize left side */
  result = btor_node_copy (btor, common);
  btor_iter_hashptr_init (&it, left);
  while (btor_iter_hashptr_has_next (&it))
    {
      b = it.bucket;
      cur = btor_iter_hashptr_next (&it);
      for (i = 0; i < b->data.as_int; i++)
	{
	  temp = fptr (btor, result, cur);
	  btor_node_release (btor, result);
	  result = temp;
	}
    }
  *e0_norm = result;

  /* normalize right side */
  result = btor_node_copy (btor, common);
  btor_iter_hashptr_init (&it, right);
  while (btor_iter_hashptr_has_next (&it))
    {
      b = it.bucket;
      cur = btor_iter_hashptr_next (&it);
      for (i = 0; i < b->data.as_int; i++)
	{
	  temp = fptr (btor, result, cur);
	  btor_node_release (btor, result);
	  result = temp;
	}
    }
  *e1_norm = result;
#else
  /* Bubble up common part.
   */
  result = 0;
  btor_iter_hashptr_init (&it, left);
  while (btor_iter_hashptr_has_next (&it))
  {
    b   = it.bucket;
    cur = btor_iter_hashptr_next (&it);
    assert (b->data.as_int >= 0);
    for (i = 0; i < (size_t) b->data.as_int; i++)
    {
      if (result)
      {
        temp = btor_rewrite_binary_exp (btor, kind, result, cur);
        btor_node_release (btor, result);
        result = temp;
      }
      else
        result = btor_node_copy (btor, cur);
    }
  }

  if (result)
  {
    temp = btor_rewrite_binary_exp (btor, kind, common, result);
    btor_node_release (btor, result);
    result = temp;
  }
  else
    result = btor_node_copy (btor, common);

  *e0_norm = result;

  result = 0;
  btor_iter_hashptr_init (&it, right);
  while (btor_iter_hashptr_has_next (&it))
  {
    b   = it.bucket;
    cur = btor_iter_hashptr_next (&it);
    assert (b->data.as_int >= 0);
    for (i = 0; i < (size_t) b->data.as_int; i++)
    {
      if (result)
      {
        temp = btor_rewrite_binary_exp (btor, kind, result, cur);
        btor_node_release (btor, result);
        result = temp;
      }
      else
        result = btor_node_copy (btor, cur);
    }
  }

  if (result)
  {
    temp = btor_rewrite_binary_exp (btor, kind, common, result);
    btor_node_release (btor, result);
    result = temp;
  }
  else
    result = btor_node_copy (btor, common);

  *e1_norm = result;
#endif

  /* clean up */
  btor_node_release (btor, common);
  btor_hashptr_table_delete (left);
  btor_hashptr_table_delete (right);
  btor_hashptr_table_delete (comm);
  btor_hashint_table_delete (cache);
}

// TODO (ma): what does this do?
static BtorNode *
find_top_add (Btor *btor, BtorNode *e)
{
  BtorNode *res;
  if (btor_node_is_inverted (e)) e = btor_node_real_addr (e);
  if (e->kind == BTOR_BV_ADD_NODE) return e;
  if (btor->rec_rw_calls >= BTOR_REC_RW_BOUND) return 0;
  res = 0;
  if (e->kind == BTOR_BV_SLICE_NODE)
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
  assert (!btor_node_is_inverted (c));

  BtorNode *res, *tmp;

  if (btor_node_is_inverted (e))
  {
    tmp = rebuild_top_add (btor, btor_node_real_addr (e), c, r);
    res = btor_node_invert (tmp);
  }
  else if (e == c)
    res = btor_node_copy (btor, r);
  else
  {
    // TODO handle more operators ... (then here)
    //
    assert (e->kind == BTOR_BV_SLICE_NODE);
    tmp = rebuild_top_add (btor, e->e[0], c, r);
    res = rewrite_slice_exp (btor,
                             tmp,
                             btor_node_bv_slice_get_upper (e),
                             btor_node_bv_slice_get_lower (e));
    btor_node_release (btor, tmp);
  }
  return res;
}

static void
normalize_adds_muls_ands (Btor *btor, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1, *real_e0, *real_e1, *e0_norm, *e1_norm;

  e0      = *left;
  e1      = *right;
  real_e0 = btor_node_real_addr (e0);
  real_e1 = btor_node_real_addr (e1);

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && real_e0->kind == real_e1->kind
      && ((btor_node_is_bv_add (real_e0)
           && btor_opt_get (btor, BTOR_OPT_NORMALIZE_ADD))
          || btor_node_is_bv_mul (real_e0) || btor_node_is_bv_and (real_e0)))
  {
    normalize_bin_comm_ass_exp (btor, real_e0, real_e1, &e0_norm, &e1_norm);
    e0_norm = btor_node_cond_invert (e0, e0_norm);
    e1_norm = btor_node_cond_invert (e1, e1_norm);
    btor_node_release (btor, e0);
    btor_node_release (btor, e1);
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
  if (btor_node_is_inverted (e0) && btor_node_is_inverted (e1))
  {
    e0 = btor_node_invert (e0);
    e1 = btor_node_invert (e1);
  }

  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 1)
  {
    if (btor_node_is_inverted (e0) && btor_node_is_bv_var (e0))
    {
      e0 = btor_node_invert (e0);
      e1 = btor_node_invert (e1);
    }
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e0, &e1);

  // TODO (ma): what does this do?
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && btor_opt_get (btor, BTOR_OPT_NORMALIZE_ADD)
      && (c0 = find_top_add (btor, e0)) && (c1 = find_top_add (btor, e1))
      && btor_node_get_sort_id (c0) == btor_node_get_sort_id (c1))
  {
    normalize_bin_comm_ass_exp (btor, c0, c1, &n0, &n1);
    tmp1 = rebuild_top_add (btor, e0, c0, n0);
    tmp2 = rebuild_top_add (btor, e1, c1, n1);
    btor_node_release (btor, n0);
    btor_node_release (btor, n1);
    btor_node_release (btor, e0);
    btor_node_release (btor, e1);
    e0 = tmp1;
    e1 = tmp2;
  }

  // TODO (ma): check if this is also applicable to mul nodes and maybe others?
  /*
   * match: c0 = c1 + b
   * result: c0 - c1 = b
   *
   * also handles negated adds:
   *
   * c0 = ~(c1 + b) -> ~c0 = c1 + b
   */
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && ((btor_node_is_bv_add (e0) && btor_node_is_bv_const (e1))
          || (btor_node_is_bv_add (e1) && btor_node_is_bv_const (e0))))
  {
    if (btor_node_is_bv_const (e0) && btor_node_is_bv_add (e1))
    {
      c0  = e0;
      add = e1;
    }
    else
    {
      assert (btor_node_is_bv_add (e0));
      assert (btor_node_is_bv_const (e1));
      c0  = e1;
      add = e0;
    }

    /* c0 = ~(c1 + b) -> ~c0 = c1 + b */
    c0  = btor_node_cond_invert (add, c0);
    add = btor_node_cond_invert (add, add);

    c1 = tmp1 = 0;
    assert (btor_node_is_regular (add));
    if (btor_node_is_bv_const (add->e[0]))
    {
      c1   = add->e[0];
      tmp1 = add->e[1];
    }
    else if (btor_node_is_bv_const (add->e[1]))
    {
      c1   = add->e[1];
      tmp1 = add->e[0];
    }

    if (tmp1)
    {
      assert (c0);
      assert (c1);
      n0 = btor_node_copy (btor, tmp1);
      n1 = btor_exp_bv_sub (btor, c0, c1);
      btor_node_release (btor, e0);
      btor_node_release (btor, e1);
      e0 = n0;
      e1 = n1;
    }
  }

  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (btor_node_is_inverted (e0) && btor_node_is_inverted (e1))
  {
    e0 = btor_node_invert (e0);
    e1 = btor_node_invert (e1);
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
  if (btor_node_is_inverted (e0) && btor_node_is_inverted (e1))
  {
    tmp = btor_node_real_addr (e1);
    e1  = btor_node_real_addr (e0);
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
  if (btor_node_is_bv_mul (e0) || btor_node_is_bv_add (e1))
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
  if (btor_node_is_bv_mul (e0) || btor_node_is_bv_and (e0))
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
  if (btor_node_is_bv_add (e0) || btor_node_is_bv_and (e0))
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
  uint32_t i;
  BtorMemMgr *mm;
  BtorNode *e0, *e1, *cur, *real_cur, *tmp, *concat;
  BtorNodePtrStack stack, po_stack;

  mm = btor->mm;
  e0 = *left;
  e1 = *right;

  /* normalize concats --> left-associative */
  if (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 2
      && btor->rec_rw_calls < BTOR_REC_RW_BOUND && btor_node_is_bv_concat (e1))
  {
    BTOR_INIT_STACK (mm, po_stack);
    BTOR_PUSH_STACK (po_stack, e0);

    BTOR_INIT_STACK (mm, stack);
    BTOR_PUSH_STACK (stack, e1);
    do
    {
      cur      = BTOR_POP_STACK (stack);
      real_cur = btor_node_real_addr (cur);
      if (btor_node_is_bv_concat (real_cur))
      {
        BTOR_PUSH_STACK (stack, btor_node_cond_invert (cur, real_cur->e[1]));
        BTOR_PUSH_STACK (stack, btor_node_cond_invert (cur, real_cur->e[0]));
      }
      else
        BTOR_PUSH_STACK (po_stack, cur);
    } while (!BTOR_EMPTY_STACK (stack));

    BTOR_INC_REC_RW_CALL (btor);
    assert (BTOR_COUNT_STACK (po_stack) >= 3);
    cur    = BTOR_PEEK_STACK (po_stack, 0);
    tmp    = BTOR_PEEK_STACK (po_stack, 1);
    concat = rewrite_concat_exp (btor, cur, tmp);

    for (i = 2; i < BTOR_COUNT_STACK (po_stack) - 1; i++)
    {
      cur = BTOR_PEEK_STACK (po_stack, i);
      assert (!btor_node_is_bv_concat (cur));
      tmp = rewrite_concat_exp (btor, concat, cur);
      btor_node_release (btor, concat);
      concat = tmp;
    }
    BTOR_DEC_REC_RW_CALL (btor);

    btor_node_release (btor, e0);
    btor_node_release (btor, e1);
    e0 = concat;
    e1 = btor_node_copy (btor, BTOR_TOP_STACK (po_stack));

    BTOR_RELEASE_STACK (stack);
    BTOR_RELEASE_STACK (po_stack);
  }

  *left  = e0;
  *right = e1;
}

static inline void
normalize_cond (Btor *btor, BtorNode **cond, BtorNode **left, BtorNode **right)
{
  BtorNode *e0, *e1, *e2;

  e0 = *cond;
  e1 = *left;
  e2 = *right;

  /* normalization: ~e0 ? e1 : e2 is the same as e0 ? e2: e1 */
  if (btor_node_is_inverted (e0))
  {
    e0 = btor_node_invert (e0);
    BTOR_SWAP (BtorNode *, e1, e2);
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands (btor, &e1, &e2);

  *cond  = e0;
  *left  = e1;
  *right = e2;
}

/* -------------------------------------------------------------------------- */
/* term rewriting functions                                                   */
/* -------------------------------------------------------------------------- */

static BtorNode *
rewrite_slice_exp (Btor *btor, BtorNode *e, uint32_t upper, uint32_t lower)
{
  BtorNode *result = 0;

  e = btor_simplify_exp (btor, e);
  assert (btor_dbg_precond_slice_exp (btor, e, upper, lower));

  result = check_rw_cache (
      btor, BTOR_BV_SLICE_NODE, btor_node_get_id (e), upper, lower);

  if (!result)
  {
    ADD_RW_RULE (full_slice, e, upper, lower);
    ADD_RW_RULE (const_slice, e, upper, lower);
    ADD_RW_RULE (slice_slice, e, upper, lower);
    ADD_RW_RULE (concat_lower_slice, e, upper, lower);
    ADD_RW_RULE (concat_upper_slice, e, upper, lower);
    ADD_RW_RULE (concat_rec_upper_slice, e, upper, lower);
    ADD_RW_RULE (concat_rec_lower_slice, e, upper, lower);
    ADD_RW_RULE (concat_rec_slice, e, upper, lower);
    ADD_RW_RULE (and_slice, e, upper, lower);
    ADD_RW_RULE (bcond_slice, e, upper, lower);
    ADD_RW_RULE (zero_lower_slice, e, upper, lower);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_slice (btor, e, upper, lower);
    }
    else
    {
    /* Note: The else branch is only active if we were able to use a rewrite
     * rule. */
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_SLICE_NODE,
                         btor_node_get_id (e),
                         upper,
                         lower,
                         btor_node_get_id (result));
    }
  }
  assert (result);
  return result;
}

static BtorNode *
rewrite_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  bool swap_ops = false;
  BtorNode *result = 0;
  BtorNodeKind kind;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_eq_exp (btor, e0, e1));
  kind = btor_node_is_fun (e0) ? BTOR_FUN_EQ_NODE : BTOR_BV_EQ_NODE;

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_eq (btor, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache (
      btor, kind, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE (const_binary_exp, kind, e0, e1);
      /* We do not rewrite eq in the boolean case, as we cannot extract the
       * resulting XNOR on top level again and would therefore lose
       * substitutions.
       *
       * Additionally, we do not rewrite eq in the boolean case, as we rewrite
       * a != b to a = ~b and substitute.
       */
      ADD_RW_RULE (true_eq, e0, e1);
      ADD_RW_RULE (false_eq, e0, e1);
      ADD_RW_RULE (bcond_eq, e0, e1);
      ADD_RW_RULE (special_const_lhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE (special_const_rhs_binary_exp, kind, e0, e1);
    }
    ADD_RW_RULE (add_left_eq, e0, e1);
    ADD_RW_RULE (add_right_eq, e0, e1);
    ADD_RW_RULE (add_add_1_eq, e0, e1);
    ADD_RW_RULE (add_add_2_eq, e0, e1);
    ADD_RW_RULE (add_add_3_eq, e0, e1);
    ADD_RW_RULE (add_add_4_eq, e0, e1);
    ADD_RW_RULE (sub_eq, e0, e1);
    ADD_RW_RULE (bcond_uneq_if_eq, e0, e1);
    ADD_RW_RULE (bcond_uneq_else_eq, e0, e1);
    ADD_RW_RULE (bcond_if_eq, e0, e1);
    ADD_RW_RULE (bcond_else_eq, e0, e1);
    ADD_RW_RULE (distrib_add_mul_eq, e0, e1);
    ADD_RW_RULE (concat_eq, e0, e1);
#if 0
    ADD_RW_RULE (zero_eq_and_eq, e0, e1);
#endif

    assert (!result);
    /* no result so far, swap operands */
    if (!swap_ops)
    {
      BTOR_SWAP (BtorNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = btor_node_create_eq (btor, e1, e0);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         kind,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_ult (btor, &e0, &e1);

  result = check_rw_cache (
      btor, BTOR_BV_ULT_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_binary_exp, BTOR_BV_ULT_NODE, e0, e1);
    ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_ULT_NODE, e0, e1);
    ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_ULT_NODE, e0, e1);
    ADD_RW_RULE (false_ult, e0, e1);
    ADD_RW_RULE (bool_ult, e0, e1);
    ADD_RW_RULE (concat_upper_ult, e0, e1);
    ADD_RW_RULE (concat_lower_ult, e0, e1);
    ADD_RW_RULE (bcond_ult, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_ult (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_ULT_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  bool swap_ops = false;
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_and (btor, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache (
      btor, BTOR_BV_AND_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE (const_binary_exp, BTOR_BV_AND_NODE, e0, e1);
      ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_AND_NODE, e0, e1);
      ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_AND_NODE, e0, e1);
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
    }
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
      BTOR_SWAP (BtorNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = btor_node_create_bv_and (btor, e1, e0);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_AND_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  bool swap_ops = false;
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_add (btor, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache (
      btor, BTOR_BV_ADD_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE (const_binary_exp, BTOR_BV_ADD_NODE, e0, e1);
      ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_ADD_NODE, e0, e1);
      ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_ADD_NODE, e0, e1);
      ADD_RW_RULE (bool_add, e0, e1);
      ADD_RW_RULE (mult_add, e0, e1);
      ADD_RW_RULE (not_add, e0, e1);
      ADD_RW_RULE (bcond_add, e0, e1);
      ADD_RW_RULE (urem_add, e0, e1);
    }
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
      BTOR_SWAP (BtorNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = btor_node_create_bv_add (btor, e1, e0);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_ADD_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  bool swap_ops = false;
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_mul (btor, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache (
      btor, BTOR_BV_MUL_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE (const_binary_exp, BTOR_BV_MUL_NODE, e0, e1);
      ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_MUL_NODE, e0, e1);
      ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_MUL_NODE, e0, e1);
      ADD_RW_RULE (bool_mul, e0, e1);
#if 0
      // TODO (ma): this increases mul nodes in the general case, needs restriction
      ADD_RW_RULE (bcond_mul, e0, e1);
#endif
    }
    ADD_RW_RULE (const_lhs_mul, e0, e1);
    ADD_RW_RULE (const_rhs_mul, e0, e1);
    ADD_RW_RULE (const_mul, e0, e1);

    assert (!result);

    /* no result so far, swap operands */
    if (!swap_ops)
    {
      BTOR_SWAP (BtorNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = btor_node_create_bv_mul (btor, e1, e0);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_MUL_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_udiv (btor, &e0, &e1);

  result = check_rw_cache (
      btor, BTOR_BV_UDIV_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    // TODO what about non powers of 2, like divisor 3, which means that
    // some upper bits are 0 ...

    ADD_RW_RULE (const_binary_exp, BTOR_BV_UDIV_NODE, e0, e1);
    ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_UDIV_NODE, e0, e1);
    ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_UDIV_NODE, e0, e1);
    ADD_RW_RULE (bool_udiv, e0, e1);
    ADD_RW_RULE (power2_udiv, e0, e1);
    ADD_RW_RULE (one_udiv, e0, e1);
    ADD_RW_RULE (bcond_udiv, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_udiv (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_UDIV_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_regular_binary_bv_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_urem (btor, &e0, &e1);

  result = check_rw_cache (
      btor, BTOR_BV_UREM_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    // TODO do optimize for powers of two even AIGs do it as well !!!

    // TODO what about non powers of 2, like modulo 3, which means that
    // all but the last two bits are zero

    ADD_RW_RULE (const_binary_exp, BTOR_BV_UREM_NODE, e0, e1);
    ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_UREM_NODE, e0, e1);
    ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_UREM_NODE, e0, e1);
    ADD_RW_RULE (bool_urem, e0, e1);
    ADD_RW_RULE (zero_urem, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_urem (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_UREM_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_concat_exp (btor, e0, e1));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  normalize_concat (btor, &e0, &e1);

  result = check_rw_cache (
      btor, BTOR_BV_CONCAT_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_binary_exp, BTOR_BV_CONCAT_NODE, e0, e1);
    ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_CONCAT_NODE, e0, e1);
    ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_CONCAT_NODE, e0, e1);
    ADD_RW_RULE (const_concat, e0, e1);
    ADD_RW_RULE (slice_concat, e0, e1);
    ADD_RW_RULE (and_lhs_concat, e0, e1);
    ADD_RW_RULE (and_rhs_concat, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_concat (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_CONCAT_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  assert (result);
  return result;
}

static BtorNode *
rewrite_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  result = check_rw_cache (
      btor, BTOR_BV_SLL_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_binary_exp, BTOR_BV_SLL_NODE, e0, e1);
    ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_SLL_NODE, e0, e1);
    ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_SLL_NODE, e0, e1);
    ADD_RW_RULE (const_sll, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_sll (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_SLL_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  assert (result);
  return result;
}

static BtorNode *
rewrite_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_shift_exp (btor, e0, e1));

  result = check_rw_cache (
      btor, BTOR_BV_SRL_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_binary_exp, BTOR_BV_SRL_NODE, e0, e1);
    ADD_RW_RULE (special_const_lhs_binary_exp, BTOR_BV_SRL_NODE, e0, e1);
    ADD_RW_RULE (special_const_rhs_binary_exp, BTOR_BV_SRL_NODE, e0, e1);
    ADD_RW_RULE (const_srl, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_bv_srl (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_BV_SRL_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  assert (result);
  return result;
}

static BtorNode *
rewrite_apply_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);
  assert (btor_dbg_precond_apply_exp (btor, e0, e1));

  result = check_rw_cache (
      btor, BTOR_APPLY_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_lambda_apply, e0, e1);
    ADD_RW_RULE (param_lambda_apply, e0, e1);
    ADD_RW_RULE (apply_apply, e0, e1);
    ADD_RW_RULE (prop_apply_lambda, e0, e1);
    ADD_RW_RULE (prop_apply_update, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_apply (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_APPLY_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  assert (result);
  return result;
}

static BtorNode *
rewrite_lambda_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);

  // Note: Rewrite caching not needed since no rules applied

  // FIXME: this rule may yield lambdas with differents sorts (in case of
  // curried
  //        lambdas)
  //  ADD_RW_RULE (lambda_lambda, e0, e1);

  assert (!result);
  result = btor_node_create_lambda (btor, e0, e1);
  // DONE:
  assert (result);
  return result;
}

static BtorNode *
rewrite_forall_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);

  result = check_rw_cache (
      btor, BTOR_FORALL_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_quantifier, e0, e1);
    ADD_RW_RULE (eq_forall, e0, e1);
    //  ADD_RW_RULE (param_free_forall, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_forall (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_FORALL_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

  assert (result);
  return result;
}

static BtorNode *
rewrite_exists_exp (Btor *btor, BtorNode *e0, BtorNode *e1)
{
  BtorNode *result = 0;

  e0 = btor_simplify_exp (btor, e0);
  e1 = btor_simplify_exp (btor, e1);

  result = check_rw_cache (
      btor, BTOR_EXISTS_NODE, btor_node_get_id (e0), btor_node_get_id (e1), 0);

  if (!result)
  {
    ADD_RW_RULE (const_quantifier, e0, e1);
    ADD_RW_RULE (eq_exists, e0, e1);
    //  ADD_RW_RULE (param_free_exists, e0, e1);

    assert (!result);
    if (!result)
    {
      result = btor_node_create_exists (btor, e0, e1);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_EXISTS_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         0,
                         btor_node_get_id (result));
    }
  }

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
  assert (btor_dbg_precond_cond_exp (btor, e0, e1, e2));

  e0 = btor_node_copy (btor, e0);
  e1 = btor_node_copy (btor, e1);
  e2 = btor_node_copy (btor, e2);
  normalize_cond (btor, &e0, &e1, &e2);
  assert (btor_node_is_regular (e0));

  result = check_rw_cache (btor,
                           BTOR_COND_NODE,
                           btor_node_get_id (e0),
                           btor_node_get_id (e1),
                           btor_node_get_id (e2));

  if (!result)
  {
    ADD_RW_RULE (equal_branches_cond, e0, e1, e2);
    ADD_RW_RULE (const_cond, e0, e1, e2);
    ADD_RW_RULE (cond_if_dom_cond, e0, e1, e2);
    ADD_RW_RULE (cond_if_merge_if_cond, e0, e1, e2);
    ADD_RW_RULE (cond_if_merge_else_cond, e0, e1, e2);
    ADD_RW_RULE (cond_else_dom_cond, e0, e1, e2);
    ADD_RW_RULE (cond_else_merge_if_cond, e0, e1, e2);
    ADD_RW_RULE (cond_else_merge_else_cond, e0, e1, e2);
    // TODO (ma): check if more rules can be applied for ite on bv and funs
    if (!btor_node_is_fun (e1))
    {
      ADD_RW_RULE (bool_cond, e0, e1, e2);
      ADD_RW_RULE (add_if_cond, e0, e1, e2);
      ADD_RW_RULE (add_else_cond, e0, e1, e2);
      ADD_RW_RULE (concat_cond, e0, e1, e2);
      ADD_RW_RULE (op_lhs_cond, e0, e1, e2);
      ADD_RW_RULE (op_rhs_cond, e0, e1, e2);
      ADD_RW_RULE (comm_op_1_cond, e0, e1, e2);
      ADD_RW_RULE (comm_op_2_cond, e0, e1, e2);
    }

    assert (!result);
    if (!result)
    {
      result = btor_node_create_cond (btor, e0, e1, e2);
    }
    else
    {
    DONE:
      btor_rw_cache_add (btor->rw_cache,
                         BTOR_COND_NODE,
                         btor_node_get_id (e0),
                         btor_node_get_id (e1),
                         btor_node_get_id (e2),
                         btor_node_get_id (result));
    }
  }
  btor_node_release (btor, e0);
  btor_node_release (btor, e1);
  btor_node_release (btor, e2);
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
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0);

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
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0);

  BtorNode *result;

  switch (kind)
  {
    case BTOR_FUN_EQ_NODE:
    case BTOR_BV_EQ_NODE: result = rewrite_eq_exp (btor, e0, e1); break;

    case BTOR_BV_ULT_NODE: result = rewrite_ult_exp (btor, e0, e1); break;

    case BTOR_BV_AND_NODE: result = rewrite_and_exp (btor, e0, e1); break;

    case BTOR_BV_ADD_NODE: result = rewrite_add_exp (btor, e0, e1); break;

    case BTOR_BV_MUL_NODE: result = rewrite_mul_exp (btor, e0, e1); break;

    case BTOR_BV_UDIV_NODE: result = rewrite_udiv_exp (btor, e0, e1); break;

    case BTOR_BV_UREM_NODE: result = rewrite_urem_exp (btor, e0, e1); break;

    case BTOR_BV_CONCAT_NODE: result = rewrite_concat_exp (btor, e0, e1); break;

    case BTOR_BV_SLL_NODE: result = rewrite_sll_exp (btor, e0, e1); break;

    case BTOR_BV_SRL_NODE: result = rewrite_srl_exp (btor, e0, e1); break;

    case BTOR_APPLY_NODE: result = rewrite_apply_exp (btor, e0, e1); break;

    case BTOR_FORALL_NODE: result = rewrite_forall_exp (btor, e0, e1); break;

    case BTOR_EXISTS_NODE: result = rewrite_exists_exp (btor, e0, e1); break;

    default:
      assert (kind == BTOR_LAMBDA_NODE);
      result = rewrite_lambda_exp (btor, e0, e1);
  }

  return result;
}

BtorNode *
btor_rewrite_ternary_exp (
    Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, BtorNode *e2)
{
  assert (btor);
  assert (kind);
  assert (kind == BTOR_COND_NODE);
  assert (e0);
  assert (e1);
  assert (e2);
  assert (btor_opt_get (btor, BTOR_OPT_REWRITE_LEVEL) > 0);
  (void) kind;

  return rewrite_cond_exp (btor, e0, e1, e2);
}
