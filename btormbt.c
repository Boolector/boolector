/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Christian Reisenberger.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolector.h"
#include "btorexp.h"

#include <assert.h>
#include <ctype.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/wait.h>
#include <unistd.h>

#define MAX_BITWIDTH 128 /* must be >= 2 */
#define MAX_INDEXWIDTH 8
#define MAX_MULDIVWIDTH 8
#define MIN_NPARAMS 1 /* must be >= 1 */
#define MAX_NPARAMS 5
#define MAX_NPARAMOPS 5
#define MAX_NNESTEDBFUNS 50

#define USAGE                                 \
  "usage: btormbt [-k][-q][-f][-a]\n"         \
  "\n"                                        \
  "where <option> is one of the following:\n" \
  "\n"                                        \
  "  -k | --keep-lines\n"                     \
  "  -q | --quiet\n"                          \
  "  -f | --first-bug-only\n"                 \
  "  -a | --always-fork\n"                    \
  "\n"                                        \
  "  -m <maxruns>\n"

static double start_time;

/*------------------------------------------------------------------------*/

#define NORM_VAL 1000.0f

#ifndef NDEBUG
#define DEBUG_MSG(msg, ARGS...)          \
  do                                     \
  {                                      \
    printf ("[btormbt] *** debug *** "); \
    printf (msg, ##ARGS);                \
    fflush (stdout);                     \
  } while (0)
#else
#define DEBUG_MSG(msg, ARGS...) \
  do                            \
  {                             \
  } while (0)
#endif

/* avoid compiler warnings for unused variables in DEBUG assertions */
#define UNUSED(expr) \
  do                 \
  {                  \
    (void) (expr);   \
  } while (0)

/*------------------------------------------------------------------------*/

typedef enum Op
{
  /* const */
  CONST,
  ZERO,
  FALSE,
  ONES,
  TRUE,
  ONE,
  UINT,
  INT,
  /* var, array */
  VAR,
  ARRAY,
  /* unary funs */
  NOT,
  NEG,
  SLICE,
  INC,
  DEC,
  UEXT,
  SEXT,
  /* boolean unary funs */
  REDOR,
  REDXOR,
  REDAND,
  /* boolean binary funs */
  EQ,
  NE,
  UADDO,
  SADDO,
  USUBO,
  SSUBO,
  UMULO,
  SMULO,
  SDIVO,
  ULT,
  SLT,
  ULTE,
  SLTE,
  UGT,
  SGT,
  UGTE,
  SGTE,
  IMPLIES,
  IFF,
  /* binary funs */
  XOR,
  XNOR,
  AND,
  NAND,
  OR,
  NOR,
  ADD,
  SUB,
  MUL,
  UDIV,
  SDIV,
  UREM,
  SREM,
  SMOD,
  SLL,
  SRL,
  SRA,
  ROL,
  ROR,
  CONCAT,
  /* ternary funs */
  COND,
  /* array funs */
  READ,
  WRITE,
  /* bv funs */
  APPLY
} Op;

typedef enum ExpType
{
  T_BO, /* Boolean */
  T_BV, /* bit vector */
  T_BB, /* Boolean or bit vector */
  T_ARR /* array */
} ExpType;

static int
is_unary_fun (Op op)
{
  return op >= NOT && op <= REDAND;
}

static int
is_boolean_unary_fun (Op op)
{
  return (op >= REDOR && op <= REDAND);
}

static int
is_binary_fun (Op op)
{
  return (op >= EQ && op <= CONCAT);
}

static int
is_boolean_binary_fun (Op op)
{
  return (op >= EQ && op <= IFF);
}

static int
is_ternary_fun (Op op)
{
  return op == COND;
}

static int
is_array_fun (Op op)
{
  return (op >= COND && op <= WRITE) || (op >= EQ && op <= NE);
}

// TODO get rid of
typedef struct Exp
{
  BtorNode *exp;
  int pars; /* number of parents */
  // TODO number of parents is not needed anymore in actual implentation could
  // be removed
  //-> but may not so trivial code adaptations
  // just use sexp-> marker for selected expressions in ExpStack
} Exp;

typedef struct ExpStack
{
  Exp *exps;
  int size, n, sexp, /* marker for selected expressions */
      initlayer;     /* marker for init layer */
} ExpStack;

typedef struct Data
{
  Btor *btor;
  int print, isinit;
  int inc, mgen;
  int nlits, ops, nops;
  /* probability distribution of variables, constants, arrays */
  float p_var, p_const, p_arr;
  /* propability distrbution of add and release operations */
  float p_addop, p_relop;
  /* probability distribution of functions (without macros and array
   * operations), array operations, macros, literals */
  float p_fun, p_afun, p_bfun, p_lit;
  /* probability distribution of assertions */
  float p_ass;
  /* target probability distribution for dynamic adaption */
  ExpStack bo, bv, arr;
  ExpStack *parambo, *parambv, *paramarr;

  int nass;       /* number of asserts / assumes todo in actual round */
  int nassert;    /* number of produced asserts in actual round */
  int nassume;    /* number of produced assumes in actual round */
  int totasserts; /* total asserts done save for printing */
  ExpStack cnf;
} Data;

void
es_push (ExpStack *es, BtorNode *exp)
{
  if (es->n == es->size)
  {
    es->size = es->size ? es->size * 2 : 2;
    es->exps = realloc (es->exps, es->size * sizeof *es->exps);
  }
  es->exps[es->n].exp  = exp;
  es->exps[es->n].pars = 0;
  es->n++;
}

static void
es_del (Data *data, ExpStack *es, int idx)
{
  int i;
  assert (idx >= 0 && idx < es->n);

  boolector_release (data->btor, es->exps[idx].exp);
  for (i = idx; i < es->n - 1; i++) es->exps[i] = es->exps[i + 1];
  es->n -= 1;
  if (idx < es->sexp) es->sexp -= 1;
}

static void
es_reset (Data *data, ExpStack *es)
{
  int i;

  for (i = 0; i < es->n; i++) boolector_release (data->btor, es->exps[i].exp);
  es->n = 0;
}

void
es_release (Data *data, ExpStack *es)
{
  int i;

  for (i = 0; i < es->n; i++) boolector_release (data->btor, es->exps[i].exp);
  es->n = 0;
  free (es->exps);
}

BtorNode *
es_get (ExpStack *es, int idx)
{
  assert (idx >= 0 && idx < es->n);
  return es->exps[idx].exp;
}

/*------------------------------------------------------------------------*/

/**
 * initialize probability distribution of literals
 * parameter: ratio var:const:arr (e.g. 3:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_lits (Data *data, float ratio_var, float ratio_const, float ratio_arr)
{
  float sum;

  sum = ratio_var + ratio_const + ratio_arr;

  assert (sum > 0);

  data->p_var   = (ratio_var * NORM_VAL) / sum;
  data->p_const = (ratio_const * NORM_VAL) / sum;
  data->p_arr   = (ratio_arr * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add operation
 * parameter: ratio fun:afun:lit (e.g. 1:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_addop (Data *data,
               float ratio_fun,
               float ratio_afun,
               float ratio_bfun,
               float ratio_lit)
{
  float sum;

  sum = ratio_fun + ratio_afun + ratio_lit;

  assert (sum > 0);

  data->p_fun  = (ratio_fun * NORM_VAL) / sum;
  data->p_afun = (ratio_afun * NORM_VAL) / sum;
  data->p_bfun = (ratio_bfun * NORM_VAL) / sum;
  data->p_lit  = (ratio_lit * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add/release op
 * parameter: ratio addop:relop (e.g. 1:0)
 * normalized to NORM_VAL
 */
static void
init_pd_op (Data *data, float ratio_addop, float ratio_relop)
{
  float sum;

  sum = ratio_addop + ratio_relop;

  assert (sum > 0);

  data->p_addop = (ratio_addop * NORM_VAL) / sum;
  data->p_relop = (ratio_relop * NORM_VAL) / sum;
}

typedef struct RNG
{
  unsigned z, w;
} RNG;

typedef void *(*State) (Data *, unsigned rand);

typedef struct Env
{
  int seed, quiet, alwaysfork, round, bugs, first, forked, print;
  int terminal;
  RNG rng;
} Env;

static RNG
initrng (unsigned seed)
{
  RNG res;
  res.z = seed * 1000632769u;
  res.w = seed * 2019164533u;
  return res;
}

static unsigned
nextrand (RNG *rng)
{
  rng->z = 36969 * (rng->z & 65535) + (rng->z >> 16);
  rng->w = 18000 * (rng->w & 65535) + (rng->w >> 16);
  return (rng->z << 16) + rng->w; /* 32-bit result */
}

static int
pick (RNG *rng_ptr, unsigned from, unsigned to)
{
  unsigned tmp = nextrand (rng_ptr);
  int res;
  assert (from <= to && to < UINT_MAX);
  tmp %= to - from + 1;
  tmp += from;
  res = tmp;
  return res;
}

static Env env;

/*------------------------------------------------------------------------*/

/* returns power of 2 val nearest to i and its log2, minimum of pow2 = 2*/
/* used for log2 operators */
static void
nextpow2 (int val, int *pow2, int *log2)
{
  *pow2 = 2;
  *log2 = 1;
  val   = val >> 2;
  while (val)
  {
    val   = val >> 1;
    *pow2 = *pow2 << 1;
    (*log2)++;
  }
}

/* Change node e with width ew to width tow.
 * Note: param ew prevents too many boolector_get_width calls. */
static BtorNode *
modifybv (Data *data, RNG *rng, BtorNode *e, int ew, int tow, int is_param)
{
  int tmp;
  ExpStack *es;

  assert (tow > 0 && ew > 0);

  if (tow > 1)
    es = is_param ? data->parambv : &data->bv;
  else
    es = is_param ? data->parambo : &data->bo;

  if (tow < ew)
  {
    tmp = pick (rng, 0, ew - tow);
    e   = boolector_slice (data->btor, e, tmp + tow - 1, tmp);
    es_push (es, e);
    es->exps[es->n - 1].pars++;
  }
  else if (tow > ew)
  {
    tmp = boolector_get_width (data->btor, e);
    e   = (pick (rng, 0, 1) ? boolector_uext (data->btor, e, tow - ew)
                          : boolector_sext (data->btor, e, tow - ew));
    es_push (es, e);
    es->exps[es->n - 1].pars++;
  }

  assert (tow == boolector_get_width (data->btor, e));
  return e;
}

static void
make_var (Data *data, RNG *rng, ExpType type)
{
  int width;
  if (type == T_BO)
    width = 1;
  else if (type == T_BV)
    width = pick (rng, 2, MAX_BITWIDTH);
  else
    width = pick (rng, 1, MAX_BITWIDTH);

  if (width == 1)
    es_push (&data->bo, boolector_var (data->btor, width, NULL));
  else
    es_push (&data->bv, boolector_var (data->btor, width, NULL));
}

static void
make_const (Data *data, RNG *rng)
{
  int width, val, i;
  ExpStack *es;

  width = 0;

  val = 0;

  Op op = pick (rng, CONST, INT);
  if (op != TRUE && op != FALSE)
  {
    width = pick (rng, 1, MAX_BITWIDTH);
    if (width == 1)
      es = &data->bo;
    else
      es = &data->bv;
  }
  else
  {
    es = &data->bo;
  }
  if (op == UINT || op == INT)
  {
    if (width < 32)
      val = (1 << width) - 1;
    else
      val = UINT_MAX - 1; /* UINT_MAX leads to divison by 0 in pick */
    val = pick (rng, 0, val);
  }
  switch (op)
  {
    case CONST:
    {
      char *buff = malloc (width + 1); /* generate random binary string */
      for (i = 0; i < width; i++) buff[i] = pick (rng, 0, 1) ? '1' : '0';
      buff[width] = '\0';
      es_push (es, boolector_const (data->btor, buff));
      free (buff);
      break;
    }
    case ZERO: es_push (es, boolector_zero (data->btor, width)); break;
    case FALSE: es_push (es, boolector_false (data->btor)); break;
    case ONES: es_push (es, boolector_ones (data->btor, width)); break;
    case TRUE: es_push (es, boolector_true (data->btor)); break;
    case ONE: es_push (es, boolector_one (data->btor, width)); break;
    case UINT:
      es_push (es, boolector_unsigned_int (data->btor, val, width));
      break;
    case INT: es_push (es, boolector_int (data->btor, val, width)); break;
    default: assert (0);
  }
}

static void
make_arr (Data *data, RNG *rng)
{
  int ew = pick (rng, 1, MAX_BITWIDTH);
  int iw = pick (rng, 1, MAX_INDEXWIDTH);

  es_push (&data->arr, boolector_array (data->btor, ew, iw, NULL));
}

/* randomly select variables from bo within the range ifrom - ito */
static BtorNode *
make_clause (Data *data, RNG *rng, int ifrom, int ito)
{
  int i, idx;
  BtorNode *e0, *e1;
  ExpStack *es;

  es = &data->bo;
  e0 = NULL;
  /* make clause with 3 literals */
  for (i = 0; i < 3; i++)
  {
    idx = pick (rng, ifrom, ito);
    if (e0 == NULL)
    {
      e0 = es->exps[idx].exp;
      if (pick (rng, 0, 1))
      {
        e0 = boolector_not (data->btor, e0);
        es_push (&data->cnf, e0);
      }
    }
    else
    {
      e1 = es->exps[idx].exp;
      if (pick (rng, 0, 1))
      {
        e1 = boolector_not (data->btor, e1);
        es_push (&data->cnf, e1);
      }
      e0 = boolector_or (data->btor, e0, e1);
      es_push (&data->cnf, e0);
    }
  }
  return e0;
}

static void
unary_fun (Data *data, RNG *rng, Op op, BtorNode *e0, int is_param)
{
  int tmp0, tmp1, e0w, rw;
  ExpStack *es;

  tmp0 = 0;
  tmp1 = 0;

  assert (is_unary_fun (op));
  e0w = boolector_get_width (data->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  /* set default result width */
  if (is_boolean_unary_fun (op))
    rw = 1;
  else
    rw = e0w;

  if (op == SLICE)
  {
    tmp0 = pick (rng, 0, e0w - 1);
    tmp1 = pick (rng, 0, tmp0);
    rw   = tmp0 - tmp1 + 1; /* update resulting width */
  }
  else if (op == UEXT || op == SEXT)
  {
    tmp0 = pick (rng, 0, MAX_BITWIDTH - e0w);
    rw   = e0w + tmp0;
  }

  assert (rw > 0);
  if (rw == 1)
    es = is_param ? data->parambo : &data->bo;
  else
    es = is_param ? data->parambv : &data->bv;

  switch (op)
  {
    case NOT: es_push (es, boolector_not (data->btor, e0)); break;
    case NEG: es_push (es, boolector_neg (data->btor, e0)); break;
    case SLICE:
      es_push (es, boolector_slice (data->btor, e0, tmp0, tmp1));
      break;
    case INC: es_push (es, boolector_inc (data->btor, e0)); break;
    case DEC: es_push (es, boolector_dec (data->btor, e0)); break;
    case UEXT: es_push (es, boolector_uext (data->btor, e0, tmp0)); break;
    case SEXT: es_push (es, boolector_sext (data->btor, e0, tmp0)); break;
    case REDOR: es_push (es, boolector_redor (data->btor, e0)); break;
    case REDXOR: es_push (es, boolector_redxor (data->btor, e0)); break;
    case REDAND: es_push (es, boolector_redand (data->btor, e0)); break;
    default: assert (0);
  }
}

static void
binary_fun (
    Data *data, RNG *rng, Op op, BtorNode *e0, BtorNode *e1, int is_param)
{
  int tmp0, tmp1, e0w, e1w, rw;
  ExpStack *es;

  assert (is_binary_fun (op));
  e0w = boolector_get_width (data->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  e1w = boolector_get_width (data->btor, e1);
  assert (e1w <= MAX_BITWIDTH);

  /* set default result width */
  if (is_boolean_binary_fun (op))
    rw = 1;
  else
    rw = e0w;

  if ((op >= XOR && op <= SMOD) || (op >= EQ && op <= SGTE))
  {
    /* modify e1w equal to e0w, guarded mul and div */
    if ((op >= UMULO && op <= SDIVO) || (op >= MUL && op <= SMOD))
    {
      if (e0w > MAX_MULDIVWIDTH)
      {
        e0  = modifybv (data, rng, e0, e0w, MAX_MULDIVWIDTH, is_param);
        e0w = MAX_MULDIVWIDTH;
        if (op >= MUL && op <= SMOD)
        {
          rw = e0w;
        }
      }
    }
    e1  = modifybv (data, rng, e1, e1w, e0w, is_param);
    e1w = e0w;
  }
  else if (op >= SLL && op <= ROR)
  {
    /* modify width of e0 power of 2 and e1 log2(e0) */
    nextpow2 (e0w, &tmp0, &tmp1);
    e0  = modifybv (data, rng, e0, e0w, tmp0, is_param);
    e1  = modifybv (data, rng, e1, e1w, tmp1, is_param);
    e0w = tmp0;
    e1w = tmp1;
    rw  = e0w;
  }
  else if (op == CONCAT)
  {
    if (e0w + e1w > MAX_BITWIDTH)
    {
      // printf("concat modify\n ")
      if (e0w > 1)
      {
        e0  = modifybv (data, rng, e0, e0w, e0w / 2, is_param);
        e0w = e0w / 2;
      }
      if (e1w > 1)
      {
        e1  = modifybv (data, rng, e1, e1w, e1w / 2, is_param);
        e1w = e1w / 2;
      }
    }
    /* set e0w to select right exp stack */
    rw = e0w + e1w;
  }

  if (rw == 1)
    es = is_param ? data->parambo : &data->bo;
  else
    es = is_param ? data->parambv : &data->bv;

  switch (op)
  {
    case XOR: es_push (es, boolector_xor (data->btor, e0, e1)); break;
    case XNOR: es_push (es, boolector_xnor (data->btor, e0, e1)); break;
    case AND: es_push (es, boolector_and (data->btor, e0, e1)); break;
    case NAND: es_push (es, boolector_nand (data->btor, e0, e1)); break;
    case OR: es_push (es, boolector_or (data->btor, e0, e1)); break;
    case NOR: es_push (es, boolector_nor (data->btor, e0, e1)); break;
    case ADD: es_push (es, boolector_add (data->btor, e0, e1)); break;
    case SUB: es_push (es, boolector_sub (data->btor, e0, e1)); break;
    case MUL: es_push (es, boolector_mul (data->btor, e0, e1)); break;
    case UDIV: es_push (es, boolector_udiv (data->btor, e0, e1)); break;
    case SDIV: es_push (es, boolector_sdiv (data->btor, e0, e1)); break;
    case UREM: es_push (es, boolector_urem (data->btor, e0, e1)); break;
    case SREM: es_push (es, boolector_srem (data->btor, e0, e1)); break;
    case SMOD: es_push (es, boolector_smod (data->btor, e0, e1)); break;
    case SLL: es_push (es, boolector_sll (data->btor, e0, e1)); break;
    case SRL: es_push (es, boolector_srl (data->btor, e0, e1)); break;
    case SRA: es_push (es, boolector_sra (data->btor, e0, e1)); break;
    case ROL: es_push (es, boolector_rol (data->btor, e0, e1)); break;
    case ROR: es_push (es, boolector_ror (data->btor, e0, e1)); break;
    case CONCAT: es_push (es, boolector_concat (data->btor, e0, e1)); break;
    case EQ: es_push (es, boolector_eq (data->btor, e0, e1)); break;
    case NE: es_push (es, boolector_ne (data->btor, e0, e1)); break;
    case UADDO: es_push (es, boolector_uaddo (data->btor, e0, e1)); break;
    case SADDO: es_push (es, boolector_saddo (data->btor, e0, e1)); break;
    case USUBO: es_push (es, boolector_usubo (data->btor, e0, e1)); break;
    case SSUBO: es_push (es, boolector_ssubo (data->btor, e0, e1)); break;
    case UMULO: es_push (es, boolector_umulo (data->btor, e0, e1)); break;
    case SMULO: es_push (es, boolector_smulo (data->btor, e0, e1)); break;
    case SDIVO: es_push (es, boolector_sdivo (data->btor, e0, e1)); break;
    case ULT: es_push (es, boolector_ult (data->btor, e0, e1)); break;
    case SLT: es_push (es, boolector_slt (data->btor, e0, e1)); break;
    case ULTE: es_push (es, boolector_ulte (data->btor, e0, e1)); break;
    case SLTE: es_push (es, boolector_slte (data->btor, e0, e1)); break;
    case UGT: es_push (es, boolector_ugt (data->btor, e0, e1)); break;
    case SGT: es_push (es, boolector_sgt (data->btor, e0, e1)); break;
    case UGTE: es_push (es, boolector_ugte (data->btor, e0, e1)); break;
    case SGTE: es_push (es, boolector_sgte (data->btor, e0, e1)); break;
    case IMPLIES: es_push (es, boolector_implies (data->btor, e0, e1)); break;
    default:
      assert (op == IFF);
      es_push (es, boolector_iff (data->btor, e0, e1));
  }
}

static void
ternary_fun (Data *data,
             RNG *rng,
             Op op,
             BtorNode *e0,
             BtorNode *e1,
             BtorNode *e2,
             int is_param)
{
  assert (is_ternary_fun (op));
  assert (boolector_get_width (data->btor, e0) == 1);

  int e1w, e2w;
  ExpStack *es;

  e1w = boolector_get_width (data->btor, e1);
  assert (e1w <= MAX_BITWIDTH);
  e2w = boolector_get_width (data->btor, e2);
  assert (e2w <= MAX_BITWIDTH);

  /* bitvectors must have same bit width */
  e2  = modifybv (data, rng, e2, e2w, e1w, is_param);
  e2w = e1w;

  if (e1w == 1)
    es = is_param ? data->parambo : &data->bo;
  else
    es = is_param ? data->parambv : &data->bv;

  es_push (es, boolector_cond (data->btor, e0, e1, e2));
}

/* calling convention:
 * if op ==
 *          READ:  bolector_read (btor, e0(arr), e1(bv))
 *          WRITE: bolector_write(btor, e0(arr), e1(bv), e2(bv))
 *          EQ:    bolector_eq   (btor, e0(arr), e1(arr))
 *          NEQ:   bolector_neq  (btor, e0(arr), e1(arr))
 *          COND:  bolector_cond (btor, e2(bo),  e0(arr), e1(arr))
 *
 * if e0 && e1 are arrays they have to be the same size
 */
static void
afun (Data *data,
      RNG *rng,
      Op op,
      BtorNode *e0,
      BtorNode *e1,
      BtorNode *e2,
      int is_param)
{
  assert (e0);
  assert (e1);
  assert (boolector_is_array (data->btor, e0));

  int e0w, e0iw, e1w, e2w;
  ExpStack *es;

  int isarr = is_array_fun (op);
  UNUSED (isarr);
  assert (isarr);

  e0w = boolector_get_width (data->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  e0iw = boolector_get_index_width (data->btor, e0);
  assert (e0iw <= MAX_INDEXWIDTH);

  if (op >= READ && op <= WRITE)
  {
    e1w = boolector_get_width (data->btor, e1);
    assert (e1w <= MAX_BITWIDTH);

    e1  = modifybv (data, rng, e1, e1w, e0iw, is_param);
    e1w = e0iw;
    if (op == WRITE)
    {
      e2w = boolector_get_width (data->btor, e2);
      assert (e1w <= MAX_BITWIDTH);

      e2 = modifybv (data, rng, e2, e2w, e0w, is_param);
      es_push (is_param ? data->paramarr : &data->arr,
               boolector_write (data->btor, e0, e1, e2));
    }
    else
    {
      if (e0w == 1)
        es = is_param ? data->parambo : &data->bo;
      else
        es = is_param ? data->parambv : &data->bv;
      es_push (es, boolector_read (data->btor, e0, e1));
    }
  }
  else
  {
    assert (boolector_is_array (data->btor, e1));
    e1w = boolector_get_width (data->btor, e1);
    assert (e1w == e0w && e1w <= MAX_BITWIDTH);
    assert (boolector_get_index_width (data->btor, e1) == e0iw
            && boolector_get_index_width (data->btor, e1) <= MAX_INDEXWIDTH);

    if (op == EQ)
      es_push (is_param ? data->parambo : &data->bo,
               boolector_eq (data->btor, e0, e1));
    else if (op == NE)
      es_push (is_param ? data->parambo : &data->bo,
               boolector_ne (data->btor, e0, e1));
    else
    {
      assert (op == COND);
      es_push (is_param ? data->paramarr : &data->arr,
               boolector_cond (data->btor, e2, e0, e1));
    }
  }
}

/* Randomly select expression by given type, nodes with no parents (yet unused)
 * are preferred.
 */
static BtorNode *
selexp (Data *data, RNG *rng, ExpType type, int force_param, int *is_param)
{
  assert (force_param != 1 || (data->parambo && data->parambo->n)
          || (data->parambv && data->parambv->n)
          || (data->paramarr && data->paramarr->n));

  int rand, i, bw, idx = -1;
  ExpStack *es, *bo, *bv, *arr;
  BtorNode *exp, *e[3];

  /* choose between param. exps and non-param. exps with p = 0.5 */
  rand = pick (rng, 0, NORM_VAL - 1);

  if (force_param == -1 || (!data->parambo && !data->parambv && !data->paramarr)
      || (!data->parambo->n && !data->parambv->n && !data->paramarr->n)
      || (force_param == 0 && (rand < 0.5 * NORM_VAL)))
  // FIXME store p value in data
  {
    bo  = &data->bo;
    bv  = &data->bv;
    arr = &data->arr;
    if (is_param) *is_param = 0;
  }
  else
  {
    bo  = data->parambo;
    bv  = data->parambv;
    arr = data->paramarr;
    if (is_param) *is_param = 1;
  }

  switch (type)
  {
    case T_BO: es = bo; break;
    case T_BV: es = bv; break;
    case T_ARR: es = arr; break;
    default:
    {
      assert (type == T_BB);
      /* select target exp stack with prob. proportional to size */
      rand = pick (rng, 0, bo->n + bv->n - 1);
      es   = rand < bo->n ? bo : bv;
    }
  }

  if (es->n == 0)
  {
    assert (es == data->parambo || es == data->paramarr);
    assert (bv == data->parambv);
    if (es == data->parambo)
    {
      rand = pick (rng, 0, bv->n - 1);
      exp  = bv->exps[rand].exp;
      bw   = boolector_get_width (data->btor, exp) - 1;
      es_push (es, boolector_slice (data->btor, exp, bw, bw));
    }
    else
    {
      /* generate parameterized WRITE */
      e[0] = selexp (data, rng, T_ARR, -1, NULL);
      rand = pick (rng, 1, 2);
      for (i = 1; i < 3; i++)
        e[i] = selexp (data, rng, T_BV, rand == i ? 1 : 0, NULL);
      afun (data, rng, WRITE, e[0], e[1], e[2], 1);
    }
  }

  /* select first nodes without parents (not yet referenced) */
  while (es->sexp < es->n)
  {
    if (es->exps[es->sexp].pars <= 0)
    {
      idx = es->sexp++;
      break;
    }
    es->sexp++;
  }
  if (idx < 0)
  {
    /* select random literal */
    idx = pick (rng, 0, es->n - 1);
  }
  exp = es->exps[idx].exp;
  es->exps[idx].pars++;
  return exp;
}

/* Search and select array expression with element width eew
 * and index width eiw.  If no suitable expression is found,
 * create new array/parameterized WRITE eew->eiw.
 */
static BtorNode *
selarrexp (
    Data *data, RNG *rng, BtorNode *exp, int eew, int eiw, int force_param)
{
  int i, rand, idx, sel_eew, sel_eiw;
  ExpStack *es;
  BtorNode *sel_e, *e[3];

  /* choose between param. exps and non-param. exps with p = 0.5 */
  rand = pick (rng, 0, NORM_VAL - 1);
  if (force_param == -1 || (!data->parambo && !data->parambv && !data->paramarr)
      || (!data->parambo->n && !data->parambv->n && !data->paramarr->n)
      || (force_param == 0 && (rand < 0.5 * NORM_VAL)))
    // FIXME store p value in data
    es = &data->arr;
  else
    es = data->paramarr;

  assert (es->n);
  /* random search start idx */
  idx = i = pick (rng, 0, es->n - 1);
  do
  {
    sel_e   = es->exps[i].exp;
    sel_eew = boolector_get_width (data->btor, sel_e);
    sel_eiw = boolector_get_index_width (data->btor, sel_e);
    if (sel_eew == eew && sel_eiw == eiw && sel_e != exp)
    {
      es->exps[i].pars++;
      return sel_e;
    }
    i = (i + 1) % es->n;
  } while (idx != i);

  /* no suitable array exp found */
  if (force_param == 1)
  {
    /* generate parameterized WRITE */
    e[0] = selarrexp (data, rng, NULL, eew, eiw, -1);
    rand = pick (rng, 1, 2);
    for (i = 1; i < 3; i++)
      e[i] = selexp (data, rng, T_BV, rand == i ? 1 : 0, NULL);
    afun (data, rng, WRITE, e[0], e[1], e[2], 1);
    sel_e = data->paramarr->exps[data->paramarr->n - 1].exp;
  }
  else
  {
    sel_e = boolector_array (data->btor, eew, eiw, NULL);
    es_push (es, sel_e);
  }
  es->exps[es->n - 1].pars++;
  return sel_e;
}
/* Generate parameterized unary/binary/ternary operation. */
static void
param_fun (Data *data, RNG *rng, int op_from, int op_to)
{
  int i, rand;
  BtorNode *e[3];
  Op op;

  assert (op_from >= NOT && op_from <= COND);
  assert (op_to >= NOT && op_to <= COND);

  op = pick (rng, op_from, op_to);
  if (is_unary_fun (op))
  {
    e[0] = selexp (data, rng, T_BB, 1, NULL);
    unary_fun (data, rng, op, e[0], 1);
  }
  else if (is_binary_fun (op))
  {
    rand = pick (rng, 0, 1);
    for (i = 0; i < 2; i++)
      e[i] = selexp (data,
                     rng,
                     ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB),
                     i == rand ? 1 : 0,
                     NULL);
    binary_fun (data, rng, op, e[0], e[1], 1);
  }
  else
  {
    assert (is_ternary_fun (op));
    rand = pick (rng, 0, 2);
    for (i = 0; i < 3; i++)
      e[i] = selexp (data, rng, i == 0 ? T_BO : T_BB, i == rand ? 1 : 0, NULL);
    ternary_fun (data, rng, op, e[0], e[1], e[2], 1);
  }
}

/* Generate parameterized operations on arrays.
 * Force array expressions with non-parameterized arrays via parameter
 * force_arrnparr (mostly needed for initializing the paramarr stack).
 * Note that this forces either a WRITE or COND expression. */
static void
param_afun (Data *data, RNG *rng, int force_arrnparr)
{
  int i, rand, eiw, eew;
  BtorNode *e[3];
  Op op;

  /* force array exp with non-parameterized arrays? */
  rand = force_arrnparr ? -1 : pick (rng, 0, 1);
  e[0] = selexp (data, rng, T_ARR, rand, NULL);
  eew  = boolector_get_width (data->btor, e[0]);
  eiw  = boolector_get_index_width (data->btor, e[0]);

  /* choose READ/WRITE with p = 0.666, else EQ/NE/COND */
  if (pick (rng, 0, 2))
  {
    /* force WRITE if array exp with non-parameterized arrays forced */
    op = rand == -1 ? WRITE : pick (rng, READ, WRITE);
    if (op == WRITE)
    {
      rand = pick (rng, 1, 2);
      for (i = 1; i < 3; i++)
        e[i] = selexp (data, rng, T_BV, rand == i ? 1 : 0, NULL);
    }
    else
      e[1] = selexp (data, rng, T_BV, 1, NULL);
  }
  else
  {
    /* force COND if array exp with non-parameterized arrays forced,
     * else distribute EQ, NE and COND evenly */
    op   = rand >= 0 && pick (rng, 0, 2) ? pick (rng, EQ, NE) : COND;
    e[1] = selarrexp (data, rng, e[0], eew, eiw, rand == -1 ? rand : rand ^ 1);
    if (op == COND) e[2] = selexp (data, rng, T_BO, rand < 0 ? 1 : 0, NULL);
  }
  afun (data, rng, op, e[0], e[1], e[2], 1);
}

static void
bfun (Data *data, unsigned r, int *nparams, int *width, int nlevel)
{
  int i, n, np, ip, w, nops, rand;
  ExpStack parambo, parambv, paramarr;
  BtorNode *tmp, *fun, **params, **args;
  RNG rng;

  rng = initrng (r);
  memset (&parambo, 0, sizeof (parambo));
  memset (&parambv, 0, sizeof (parambv));
  memset (&paramarr, 0, sizeof (paramarr));
  data->parambo  = &parambo;
  data->parambv  = &parambv;
  data->paramarr = &paramarr;

  /* choose function parameters */
  *width   = pick (&rng, 1, MAX_BITWIDTH);
  *nparams = pick (&rng, MIN_NPARAMS, MAX_NPARAMS);
  params   = malloc (sizeof (BtorNode *) * *nparams);
  for (i = 0; i < *nparams; i++)
  {
    tmp       = boolector_param (data->btor, *width, NULL);
    params[i] = tmp;
    es_push (*width == 1 ? data->parambo : data->parambv, tmp);
  }

  /* initialize stacks for non-bv parameterized expressions */
  if (data->parambv->n == 0)
  {
    assert (data->parambo->n);
    tmp = data->parambo->exps[pick (&rng, 0, data->parambo->n)].exp;
    assert (boolector_get_width (data->btor, tmp) == 1);
    modifybv (data, &rng, tmp, 1, pick (&rng, 2, MAX_BITWIDTH), 1);
  }
  assert (data->parambv->n);
  if (data->parambo->n == 0) param_fun (data, &rng, REDOR, IFF);
  assert (data->parambo->n);
  param_afun (data, &rng, 1);
  assert (data->paramarr->n);

  /* generate parameterized expressions */
  nops = pick (&rng, 0, MAX_NPARAMOPS);
  n    = 0;
  while (n++ < nops)
  {
  BFUN_PICK_FUN_TYPE:
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < data->p_fun)
      param_fun (data, &rng, NOT, COND);
    else if (rand < data->p_fun + data->p_afun)
      param_afun (data, &rng, 0);
    else
    {
      if (nlevel < MAX_NNESTEDBFUNS)
      {
        bfun (data, nextrand (&rng), &np, &w, nlevel + 1);
        data->parambo  = &parambo;
        data->parambv  = &parambv;
        data->paramarr = &paramarr;
      }
      else
        goto BFUN_PICK_FUN_TYPE;
    }
  }

  rand = pick (&rng, 0, parambv.n - 1);
  fun  = boolector_fun (data->btor, *nparams, params, parambv.exps[rand].exp);
  args = malloc (sizeof (BtorNode *) * *nparams);
  for (i = 0; i < *nparams; i++)
  {
    tmp     = selexp (data, &rng, T_BV, -1, &ip);
    args[i] = modifybv (
        data, &rng, tmp, boolector_get_width (data->btor, tmp), *width, ip);
  }
  es_push (&data->bv, boolector_apply (data->btor, *nparams, args, fun));

  /* cleanup */
  boolector_release (data->btor, fun);
  es_release (data, &parambo);
  data->parambo = NULL;
  es_release (data, &parambv);
  data->parambv = NULL;
  es_release (data, &paramarr);
  data->paramarr = NULL;
  free (params);
  free (args);
}

/*------------------------------------------------------------------------*/

/* states */
static void *_new (Data *, unsigned);
static void *_opt (Data *, unsigned);
static void *_init (Data *, unsigned);
static void *_main (Data *, unsigned);
static void *_addop (Data *, unsigned);
static void *_fun (Data *, unsigned);
static void *_afun (Data *, unsigned);
static void *_bfun (Data *, unsigned);
static void *_lit (Data *, unsigned);
static void *_relop (Data *, unsigned);
static void *_ass (Data *, unsigned);
static void *_sat (Data *, unsigned);
static void *_mgen (Data *, unsigned);
static void *_inc (Data *, unsigned);
static void *_relall (Data *, unsigned);
static void *_del (Data *, unsigned);

static void *
_new (Data *data, unsigned r)
{
  RNG rng = initrng (r);

  /* number of initial literals */
  data->nlits = pick (&rng, 5, 40);
  /* number of initial operations */
  data->nops = pick (&rng, 0, 100);

  init_pd_lits (data, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 2, 5));

  /* no delete operation at init */
  init_pd_op (data, 1, 0);
  /* no additional lits at init */
  init_pd_addop (
      data, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 0, 5), 0);

  if (data->print)
    printf (
        "[btormbt] init: pick %d ops (add:rel=%0.1f%%:%0.1f%%), %d lits, \n",
        data->nops,
        data->p_addop / 10,
        data->p_relop / 10,
        data->nlits);

  data->btor = boolector_new ();
  assert (data->btor);
  assert (data->btor->apitrace);
  return _opt;
}

static void *
_opt (Data *data, unsigned r)
{
  int rw;
  RNG rng = initrng (r);

  if (pick (&rng, 0, 1))
  {
    if (data->print)
      printf ("[btormbt] enable model generation \n"), fflush (stdout);
    boolector_enable_model_gen (data->btor);
    data->mgen = 1;
  }
  if (pick (&rng, 0, 1))
  {
    if (data->print)
      printf ("[btormbt] enable incremental usage \n"), fflush (stdout);
    boolector_enable_inc_usage (data->btor);
    data->inc = 1;
  }

  rw = pick (&rng, 0, 3);
  if (data->print)
    printf ("[btormbt] set rewrite level %d \n", rw), fflush (stdout);
  boolector_set_rewrite_level (data->btor, rw);

  return _init;
}

static void *
_init (Data *data, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  if (data->bo.n + data->bv.n + data->arr.n < data->nlits)
  {
    return _lit;
  }

  /* generate at least one bool-var, one bv-var and one arr;
   * to ensure nonempty expression stacks */
  if (data->bo.n < 1) make_var (data, &rng, T_BO);
  if (data->bv.n < 1) make_var (data, &rng, T_BV);
  if (data->arr.n < 1) make_arr (data, &rng);

  if (data->ops < data->nops)
  {
    data->ops++;
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < data->p_addop)
      return _addop;
    else
      return _relop;
  }

  if (data->print)
    printf (
        "[btormbt] after init: nexps: booleans %d, bitvectors %d, arrays %d \n",
        data->bo.n,
        data->bv.n,
        data->arr.n);

  data->bo.initlayer  = data->bo.n;
  data->bv.initlayer  = data->bv.n;
  data->arr.initlayer = data->arr.n;

  /* adapt paramters for main */
  data->ops  = 0; /* reset operation counter */
  data->nops = pick (&rng, 20, 200);
  data->nass = pick (&rng, 10, 70); /* how many assertions of nops */
  // TODO the more operation the higher and vice versa - or may ok like that

  init_pd_lits (data, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 0, 5));
  init_pd_op (data, pick (&rng, 1, 8), pick (&rng, 1, 3));
  init_pd_addop (data,
                 pick (&rng, 1, 10),
                 pick (&rng, 0, 5),
                 pick (&rng, 0, 5),
                 pick (&rng, 0, 3));

  if (data->print)
  {
    printf ("[btormbt] main: pick %d ops (add:rel=%0.1f%%:%0.1f%%)\n",
            data->nops,
            data->p_addop / 10,
            data->p_relop / 10);
    printf ("[btormbt]       make ~%d asserts/assumes \n", data->nass);
  }

  data->isinit = 1;
  return _main;
}

static void *
_main (Data *data, unsigned r)
{
  float rand;
  RNG rng = initrng (r);

  assert (data->bo.n > 0);
  assert (data->bv.n > 0);
  assert (data->arr.n > 0);

  /* main operations */
  if (data->ops < data->nops)
  {
    data->ops++;
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < data->nass * NORM_VAL / data->nops)
      return _ass;
    else
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < data->p_addop)
        return _addop;
      else
        return _relop;
    }
  }

  if (data->print)
    printf (
        "[btormbt] after main: nexps: booleans %d, bitvectors %d, arrays %d \n",
        data->bo.n,
        data->bv.n,
        data->arr.n);
  if (data->print)
    printf ("[btormbt] after main: number of asserts: %d, assumps: %d \n",
            data->totasserts,
            data->nassume);

  return _sat;
}

static void *
_addop (Data *data, unsigned r)
{
  int rand;
  void *next;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);

  if (rand < data->p_fun)
    next = _fun;
  else if (rand < data->p_fun + data->p_afun)
    next = _afun;
  else if (rand < data->p_fun + data->p_afun + data->p_bfun)
    next = _bfun;
  else
    next = _lit;

  return next;
}

static void *
_fun (Data *data, unsigned r)
{
  BtorNode *e0, *e1, *e2;
  RNG rng = initrng (r);

  Op op = pick (&rng, NOT, COND);

  if (is_unary_fun (op))
  {
    e0 = selexp (data, &rng, T_BB, 0, NULL);
    unary_fun (data, &rng, op, e0, 0);
  }
  else if (is_binary_fun (op))
  {
    e0 = selexp (
        data, &rng, ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB), 0, NULL);
    e1 = selexp (
        data, &rng, ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB), 0, NULL);
    binary_fun (data, &rng, op, e0, e1, 0);
  }
  else
  {
    assert (is_ternary_fun (op));
    e0 = selexp (data, &rng, T_BO, 0, NULL);
    e1 = selexp (data, &rng, T_BB, 0, NULL);
    e2 = selexp (data, &rng, T_BB, 0, NULL);
    ternary_fun (data, &rng, op, e0, e1, e2, 0);
  }
  return (data->isinit ? _main : _init);
}

static void *
_afun (Data *data, unsigned r)
{
  int e0w, e0iw;
  Op op;
  BtorNode *e0, *e1, *e2 = NULL;
  RNG rng = initrng (r);

  e0   = selexp (data, &rng, T_ARR, 0, NULL);
  e0w  = boolector_get_width (data->btor, e0);
  e0iw = boolector_get_index_width (data->btor, e0);

  /* use read/write with p=0.666 else EQ/NE/COND */
  // TODO may use p=0.5??
  if (pick (&rng, 0, 2))
  {
    op = pick (&rng, READ, WRITE);
    e1 = selexp (data, &rng, T_BV, 0, NULL);
    if (op == WRITE) e2 = selexp (data, &rng, T_BV, 0, NULL);
    afun (data, &rng, op, e0, e1, e2, 0);
  }
  else
  {
    /* select EQ/NE/COND with same propability */
    op = pick (&rng, 0, 2) ? pick (&rng, EQ, NE) : COND;
    e1 = selarrexp (data, &rng, e0, e0w, e0iw, 0);
    if (op == COND) e2 = selexp (data, &rng, T_BO, 0, NULL);
    afun (data, &rng, op, e0, e1, e2, 0);
  }

  return (data->isinit ? _main : _init);
}

static void *
_bfun (Data *data, unsigned r)
{
  assert (!data->parambo && !data->parambv && !data->paramarr);

  int nparams, width;

  bfun (data, r, &nparams, &width, 0);

  data->parambo = data->parambv = data->paramarr = NULL; /* cleanup */

  return (data->isinit ? _main : _init);
}

static void *
_lit (Data *data, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);
  if (rand < data->p_var)
    make_var (data, &rng, T_BB);
  else if (rand < data->p_const + data->p_var)
    make_const (data, &rng);
  else
    make_arr (data, &rng);

  return (data->isinit ? _main : _init);
}

static void *
_relop (Data *data, unsigned r)
{
  int idx, rand;
  ExpStack *es;
  RNG rng = initrng (r);

  /* select target exp stack with probabilty proportional to size */
  rand = pick (&rng, 0, data->bo.n + data->bv.n + data->arr.n - 1);
  if (rand < data->bo.n)
    es = &data->bo;
  else if (rand < data->bo.n + data->bv.n)
    es = &data->bv;
  else
    es = &data->arr;
  if (es->n > 1)
  {
    idx = pick (&rng, 0, es->n - 1);

    if (es == &data->bo)
      assert (boolector_get_width (data->btor, data->bo.exps[idx].exp) == 1);
    else if (es == &data->bv)
      assert (boolector_get_width (data->btor, data->bv.exps[idx].exp) > 1);
    else
      assert (boolector_is_array (data->btor, data->arr.exps[idx].exp));

    es_del (data, es, idx);
  }
  return (data->isinit ? _main : _init);
}

static void *
_ass (Data *data, unsigned r)
{
  int lower;
  RNG rng = initrng (r);
  BtorNode *cls;

  /* select from init layer with lower probability */
  lower = (data->bo.n > data->bo.initlayer && pick (&rng, 0, 4)
               ? data->bo.initlayer - 1
               : 0);
  cls   = make_clause (data, &rng, lower, data->bo.n - 1);

  if (data->inc && pick (&rng, 0, 4))
  {
    boolector_assume (data->btor, cls);
    data->nassume++;
  }
  else
  {
    boolector_assert (data->btor, cls);
    data->nassert++;
    data->totasserts++;
  }
  return _main;
}

static void *
_sat (Data *data, unsigned r)
{
  UNUSED (r);
  int res;

  if (data->print) printf ("[btormbt] call sat...\n");

  res = boolector_sat (data->btor);

  if (res == BOOLECTOR_UNSAT)
  {
    if (data->print) printf ("[btormbt] unsat\n");
  }
  else if (res == BOOLECTOR_SAT)
  {
    if (data->print) printf ("[btormbt] sat\n");
  }
  else
  {
    if (data->print) printf ("[btormbt]  sat call returned %d\n", res);
  }

  return data->mgen && res == BOOLECTOR_SAT ? _mgen : _inc;
}

static void *
_mgen (Data *data, unsigned r)
{
  UNUSED (r);
  int i, size = 0;
  char *bv = NULL, **indices = NULL, **values = NULL;

  assert (data->mgen);

  for (i = 0; i < data->bo.n; i++)
  {
    bv = boolector_bv_assignment (data->btor, data->bo.exps[i].exp);
    boolector_free_bv_assignment (data->btor, bv);
  }
  for (i = 0; i < data->bv.n; i++)
  {
    bv = boolector_bv_assignment (data->btor, data->bv.exps[i].exp);
    boolector_free_bv_assignment (data->btor, bv);
  }
  for (i = 0; i < data->arr.n; i++)
  {
    boolector_array_assignment (
        data->btor, data->arr.exps[i].exp, &indices, &values, &size);
    if (size > 0)
    {
      /*
         DEBUG_MSG("**Array %d\n", i);
         int j;
         for (j = 0; j < size; j++) {
         DEBUG_MSG("**[%s]=%s\n", indices[j], values[j]);
         }
       */
      boolector_free_array_assignment (data->btor, indices, values, size);
    }
  }
  return _inc;
}

static void *
_inc (Data *data, unsigned r)
{
  RNG rng = initrng (r);

  /* release cnf expressions */
  es_reset (data, &data->cnf);

  if (data->inc && pick (&rng, 0, 2))
  {
    data->inc++;
    data->ops     = 0; /* reset */
    data->nass    = data->nass - data->nassert;
    data->nassume = 0; /* reset */
    data->nassert = 0;
    data->nops    = pick (&rng, 0, 150);
    init_pd_lits (
        data, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 0, 5));
    init_pd_op (data, pick (&rng, 1, 5), pick (&rng, 1, 5));
    init_pd_addop (data,
                   pick (&rng, 1, 10),
                   pick (&rng, 0, 5),
                   pick (&rng, 1, 5),
                   pick (&rng, 0, 3));

    if (data->print)
      printf ("[btormbt] inc: pick %d ops(add:rel=%0.1f%%:%0.1f%%) \n",
              data->nops,
              data->p_addop / 10,
              data->p_relop / 10);

    return _main;
  }
  return _relall;
}

static void *
_relall (Data *data, unsigned r)
{
  UNUSED (r);
  int i;
  for (i = 0; i < data->bo.n; i++)
  {
    assert (boolector_get_width (data->btor, data->bo.exps[i].exp) == 1);
    boolector_release (data->btor, data->bo.exps[i].exp);
  }
  for (i = 0; i < data->bv.n; i++)
  {
    assert (boolector_get_width (data->btor, data->bv.exps[i].exp) > 1);
    boolector_release (data->btor, data->bv.exps[i].exp);
  }
  for (i = 0; i < data->arr.n; i++)
  {
    assert (boolector_is_array (data->btor, data->arr.exps[i].exp));
    boolector_release (data->btor, data->arr.exps[i].exp);
  }
  return _del;
}

static void *
_del (Data *data, unsigned r)
{
  UNUSED (r);
  boolector_delete (data->btor);
  if (data->print && data->inc)
    printf ("[btormbt] number of increments: %d \n", data->inc - 1);
  return 0;
}

static void
rantrav (Env *env)
{
  State state, next;
  unsigned rand;
  Data data;
  memset (&data, 0, sizeof data);

  data.print = !env->quiet;
  memset (&data.bo, 0, sizeof (data.bo));
  memset (&data.bv, 0, sizeof (data.bv));
  memset (&data.arr, 0, sizeof (data.arr));
  memset (&data.cnf, 0, sizeof (data.cnf));
  data.parambo = data.parambv = data.paramarr = NULL;

  env->rng.z = env->rng.w = env->seed;

  /* state loop */
  for (state = _new; state; state = next)
  {
    rand = nextrand (&env->rng);
    next = state (&data, rand);
  }

  /* Note: all btor exps have been previously released in _relall! */
  free (data.bv.exps);
  free (data.bo.exps);
  free (data.arr.exps);
  free (data.cnf.exps);
}

static int
run (Env *env, void (*process) (Env *))
{
  int res, status, saved1, saved2, null;
  pid_t id;
  env->forked++;
  fflush (stdout);
  if ((id = fork ()))
  {
#ifndef NDEBUG
    pid_t wid =
#endif
        wait (&status);
    assert (wid == id);
  }
  else
  {
#ifndef NDEBUG
    int tmp;
#endif
    saved1 = dup (1);
    saved2 = dup (2);
    null   = open ("/dev/null", O_WRONLY);
    close (1);
    close (2);
#ifndef NDEBUG
    tmp =
#endif
        dup (null);
    assert (tmp == 1);
#ifndef NDEBUG
    tmp =
#endif
        dup (null);
#ifndef NDEBUG
    assert (tmp == 2);
#endif
    process (env);
    close (null);
    close (2);
#ifndef NDEBUG
    tmp =
#endif
        dup (saved2);
#ifndef NDEBUG
    assert (tmp == 2);
    close (1);
#ifndef NDEBUG
    tmp =
#endif
        dup (saved1);
#ifdef NDEBUG
    assert (tmp == 1);
#endif
    UNUSED (tmp);
#endif
    exit (0);
  }
  if (WIFEXITED (status))
  {
    res = WEXITSTATUS (status);
    if (env->print) printf ("exit %d ", res);
  }
  else if (WIFSIGNALED (status))
  {
    if (env->print) printf ("signal");
    res = 1;
  }
  else
  {
    if (env->print) printf ("unknown");
    res = 1;
  }
  return res;
}

static void
erase (void)
{
  int i;
  fputc ('\r', stdout);
  for (i = 0; i < 80; i++) fputc (' ', stdout);
  fputc ('\r', stdout);
}

static int
isnumstr (const char *str)
{
  const char *p;
  for (p = str; *p; p++)
    if (!isdigit (*p)) return 0;
  return 1;
}

static void
die (const char *msg, ...)
{
  va_list ap;
  fputs ("*** lglmbt: ", stderr);
  va_start (ap, msg);
  vfprintf (stderr, msg, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static int
hashmac (void)
{
  FILE *file = fopen ("/sys/class/net/eth0/address", "r");
  int mac[6], res = 0;
  if (!file) return 0;
  if (fscanf (file,
              "%02x:%02x:%02x:%02x:%02x:%02x",
              mac + 0,
              mac + 1,
              mac + 2,
              mac + 3,
              mac + 4,
              mac + 5)
      == 6)
  {
    res = mac[5];
    res ^= mac[4] << 4;
    res ^= mac[3] << 8;
    res ^= mac[2] << 16;
    res ^= mac[1] << 20;
    res ^= mac[0] << 24;
  }
  fclose (file);
  return res;
}

static double
current_time (void)
{
  double res = 0;
  struct timeval tv;
  if (!gettimeofday (&tv, 0)) res = 1e-6 * tv.tv_usec, res += tv.tv_sec;
  return res;
}

static double
get_time ()
{
  return current_time () - start_time;
}

static double
average (double a, double b)
{
  return b ? a / b : 0;
}

static void
stats (void)
{
  double t = get_time ();
  printf ("[btormbt] finished after %.2f seconds\n", t);
  printf ("[btormbt] %d rounds = %.2f rounds per second\n",
          env.round,
          average (env.round, t));
  printf ("[btormbt] %d bugs = %.2f bugs per second\n",
          env.bugs,
          average (env.bugs, t));
}

static void
sighandler (int sig)
{
  fflush (stdout);
  fflush (stderr);
  printf ("*** btormbt: caught signal %d in round %d\n", sig, env.round);
  fflush (stdout);
  stats ();
  exit (1);
}

static void
setsighandlers (void)
{
  (void) signal (SIGINT, sighandler);
  (void) signal (SIGSEGV, sighandler);
  (void) signal (SIGABRT, sighandler);
  (void) signal (SIGTERM, sighandler);
}

int
main (int argc, char **argv)
{
  int i, max, mac, pid, prev, res;
  char name[100];
  char *aname, *cmd;

  start_time = current_time ();

  memset (&env, 0, sizeof env);
  max          = INT_MAX;
  prev         = 0;
  env.seed     = -1;
  env.terminal = isatty (1);

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("%s", USAGE);
      exit (0);
    }
    else if (!strcmp (argv[i], "-k") || !strcmp (argv[i], "--keep-lines"))
      env.terminal = 0;
    else if (!strcmp (argv[i], "-q") || !strcmp (argv[i], "--quiet"))
      env.quiet = 1;
    else if (!strcmp (argv[i], "-a") || !strcmp (argv[i], "--always-fork"))
      env.alwaysfork = 1;
    else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--first-bug-only"))
      env.first = 1;
    else if (!strcmp (argv[i], "-m"))
    {
      if (++i == argc) die ("argument to '-m' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument '%s' to '-m' not a number (try '-h')", argv[i]);
      max = atoi (argv[i]);
    }
    else if (!isnumstr (argv[i]))
    {
      die ("invalid command line option '%s' (try '-h')", argv[i]);
    }
    else
      env.seed = atoi (argv[i]);
  }

  if (!(aname = getenv ("BTORAPITRACE")))
  {
    sprintf (name, "/tmp/bug-%d-mbt.trace", getpid ());
    setenv ("BTORAPITRACE", name, 1);
  }
  env.print = !env.quiet;

  if (env.seed >= 0 && !env.alwaysfork)
  {
    rantrav (&env);
    printf ("\n");
  }
  else
  {
    mac = hashmac ();
    pid = getpid ();
    setsighandlers ();
    for (env.round = 0; env.round < max; env.round++)
    {
      if (!(prev & 1)) prev++;

      env.seed = mac;
      env.seed *= 123301093;
      env.seed += times (0);
      env.seed *= 223531513;
      env.seed += pid;
      env.seed *= 31752023;
      env.seed += prev;
      env.seed *= 43376579;
      prev = env.seed = abs (env.seed) >> 1;

      if (!env.quiet)
      {
        if (env.terminal) erase ();
        printf ("%d %d ", env.round, env.seed);
        fflush (stdout);
      }

      res = run (&env, rantrav);

      if (res > 0)
      {
        env.bugs++;
        env.bugs++;
        cmd = malloc (strlen (name) + 80);
        sprintf (cmd, "cp %s btormbt-bug-%d.trace", name, env.seed);

        if (system (cmd))
        {
          printf (" [btormbt] Error on copy command %s \n", cmd);
          exit (1);
        }

        free (cmd);
      }
      if (!env.quiet)
      {
        if (res || !env.terminal) printf ("\n");
        fflush (stdout);
      }
      if (res && env.first) break;
    }
  }
  if (!env.quiet)
  {
    if (env.terminal) erase ();
    printf ("forked %d\n", env.forked);
  }
  stats ();
  return 0;
}
