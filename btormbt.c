/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Christian Reisenberger.
 *  Copyright (C) 2013 Aina Niemetz.
 *  Copyright (C) 2013 Armin Biere.
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

// TODO externalize all parameters

#define NORM_VAL 1000.0f

#define MAX_BITWIDTH 128 /* must be >= 2 */
#define MAX_INDEXWIDTH 8
#define MAX_MULDIVWIDTH 8
#define MIN_NPARAMS 1 /* must be >= 1 */
#define MAX_NPARAMS 5
#define MAX_NPARAMOPS 5
#define MAX_NNESTEDBFUNS 50

#define BTORMBT_USAGE                         \
  "usage: btormbt [-k][-q][-f][-a]\n"         \
  "\n"                                        \
  "where <option> is one of the following:\n" \
  "\n"                                        \
  "  -k | --keep-lines\n"                     \
  "  -q | --quiet\n"                          \
  "  -f | --first-bug-only\n"                 \
  "  -a | --always-fork\n"                    \
  "  -e | --no-extensionality\n"              \
  "\n"                                        \
  "  -m <maxruns>\n"

#define BTORMBT_MIN(x, y) ((x) < (y) ? (x) : (y))

#define BTORMBT_LOG(c, btormbt, fmt, args...) \
  do                                          \
  {                                           \
    if ((c) && btormbt->print)                \
    {                                         \
      printf ("[btormbt] ");                  \
      printf (fmt, ##args);                   \
      fflush (stdout);                        \
    }                                         \
  } while (0)

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/
#define BTORMBT_DEBUG_MSG(msg, ARGS...)  \
  do                                     \
  {                                      \
    printf ("[btormbt] *** debug *** "); \
    printf (msg, ##ARGS);                \
    fflush (stdout);                     \
  } while (0)
#else
#define BTORMBT_DEBUG_MSG(msg, ARGS...) \
  do                                    \
  {                                     \
  } while (0)
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

/* avoid compiler warnings for unused variables in DEBUG assertions */
#define BTORMBT_UNUSED(expr) \
  do                         \
  {                          \
    (void) (expr);           \
  } while (0)

/*------------------------------------------------------------------------*/

typedef struct RNG
{
  unsigned z, w;
} RNG;

typedef struct Env
{
  int seed, quiet, alwaysfork, round, bugs, first, forked, print, noext;
  int ppid; /* parent pid */
  int terminal;
  RNG rng;
} Env;

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

typedef struct Exp
{
  BtorNode *exp;
  int pars; /* number of parents */
} Exp;

typedef struct ExpStack
{
  Exp *exps;
  int size, n, sexp, /* marker for selected expressions */
      initlayer;     /* marker for init layer */
} ExpStack;

typedef struct BtorMBT
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

  ExpStack bo, bv, arr, fun;
  ExpStack *parambo, *parambv, *paramarr;
  ExpStack cnf;

  int nass;       /* number of asserts / assumes todo in actual round */
  int nassert;    /* number of produced asserts in actual round */
  int nassume;    /* number of produced assumes in actual round */
  int totasserts; /* total asserts done save for printing */
} BtorMBT;

typedef void *(*State) (BtorMBT *, unsigned rand);

/*------------------------------------------------------------------------*/

static double start_time;
static Env env;

/*------------------------------------------------------------------------*/

void
es_push (ExpStack *es, BtorNode *exp)
{
  assert (es);
  assert (exp);

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
es_del (BtorMBT *btormbt, ExpStack *es, int idx)
{
  assert (es);
  assert (idx >= 0 && idx < es->n);

  int i;

  boolector_release (btormbt->btor, es->exps[idx].exp);
  for (i = idx; i < es->n - 1; i++) es->exps[i] = es->exps[i + 1];
  es->n -= 1;
  if (idx < es->sexp) es->sexp -= 1;
}

static void
es_reset (BtorMBT *btormbt, ExpStack *es)
{
  assert (es);

  int i;

  for (i = 0; i < es->n; i++)
    boolector_release (btormbt->btor, es->exps[i].exp);
  es->n = 0;
}

void
es_release (BtorMBT *btormbt, ExpStack *es)
{
  int i;

  if (es)
  {
    for (i = 0; i < es->n; i++)
      boolector_release (btormbt->btor, es->exps[i].exp);
    es->n         = 0;
    es->size      = 0;
    es->sexp      = 0;
    es->initlayer = 0;
    free (es->exps);
    es->exps = NULL;
  }
}

/*------------------------------------------------------------------------*/

/**
 * initialize probability distribution of literals
 * parameter: ratio var:const:arr (e.g. 3:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_lits (BtorMBT *btormbt,
              float ratio_var,
              float ratio_const,
              float ratio_arr)
{
  float sum;

  sum = ratio_var + ratio_const + ratio_arr;

  assert (sum > 0);

  btormbt->p_var   = (ratio_var * NORM_VAL) / sum;
  btormbt->p_const = (ratio_const * NORM_VAL) / sum;
  btormbt->p_arr   = (ratio_arr * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add operation
 * parameter: ratio fun:afun:lit (e.g. 1:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_addop (BtorMBT *btormbt,
               float ratio_fun,
               float ratio_afun,
               float ratio_bfun,
               float ratio_lit)
{
  float sum;

  sum = ratio_fun + ratio_afun + ratio_lit;

  assert (sum > 0);

  btormbt->p_fun  = (ratio_fun * NORM_VAL) / sum;
  btormbt->p_afun = (ratio_afun * NORM_VAL) / sum;
  btormbt->p_bfun = (ratio_bfun * NORM_VAL) / sum;
  btormbt->p_lit  = (ratio_lit * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add/release op
 * parameter: ratio addop:relop (e.g. 1:0)
 * normalized to NORM_VAL
 */
static void
init_pd_op (BtorMBT *btormbt, float ratio_addop, float ratio_relop)
{
  float sum;

  sum = ratio_addop + ratio_relop;

  assert (sum > 0);

  btormbt->p_addop = (ratio_addop * NORM_VAL) / sum;
  btormbt->p_relop = (ratio_relop * NORM_VAL) / sum;
}

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

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

#ifndef NDEBUG
static int
is_ternary_fun (Op op)
{
  return op == COND;
}
#endif

static int
is_array_fun (Op op)
{
  return (op >= COND && op <= WRITE) || (op >= EQ && op <= NE);
}

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
modifybv (
    BtorMBT *btormbt, RNG *rng, BtorNode *e, int ew, int tow, int is_param)
{
  int tmp;
  ExpStack *es;

  assert (tow > 0 && ew > 0);

  if (tow > 1)
    es = is_param ? btormbt->parambv : &btormbt->bv;
  else
    es = is_param ? btormbt->parambo : &btormbt->bo;

  if (tow < ew)
  {
    tmp = pick (rng, 0, ew - tow);
    e   = boolector_slice (btormbt->btor, e, tmp + tow - 1, tmp);
    es_push (es, e);
    es->exps[es->n - 1].pars++;
  }
  else if (tow > ew)
  {
    // TODO 'tmp' unused so remove?
#if 0
      tmp = boolector_get_width (btormbt->btor, e);
#endif
    e = (pick (rng, 0, 1) ? boolector_uext (btormbt->btor, e, tow - ew)
                          : boolector_sext (btormbt->btor, e, tow - ew));
    es_push (es, e);
    es->exps[es->n - 1].pars++;
  }

  assert (tow == boolector_get_width (btormbt->btor, e));
  return e;
}

static void
make_var (BtorMBT *btormbt, RNG *rng, ExpType type)
{
  int width;
  if (type == T_BO)
    width = 1;
  else if (type == T_BV)
    width = pick (rng, 2, MAX_BITWIDTH);
  else
    width = pick (rng, 1, MAX_BITWIDTH);

  if (width == 1)
    es_push (&btormbt->bo, boolector_var (btormbt->btor, width, NULL));
  else
    es_push (&btormbt->bv, boolector_var (btormbt->btor, width, NULL));
}

static void
make_const (BtorMBT *btormbt, RNG *rng)
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
      es = &btormbt->bo;
    else
      es = &btormbt->bv;
  }
  else
  {
    es = &btormbt->bo;
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
      es_push (es, boolector_const (btormbt->btor, buff));
      free (buff);
      break;
    }
    case ZERO: es_push (es, boolector_zero (btormbt->btor, width)); break;
    case FALSE: es_push (es, boolector_false (btormbt->btor)); break;
    case ONES: es_push (es, boolector_ones (btormbt->btor, width)); break;
    case TRUE: es_push (es, boolector_true (btormbt->btor)); break;
    case ONE: es_push (es, boolector_one (btormbt->btor, width)); break;
    case UINT:
      es_push (es, boolector_unsigned_int (btormbt->btor, val, width));
      break;
    case INT: es_push (es, boolector_int (btormbt->btor, val, width)); break;
    default: assert (0);
  }
}

static void
make_arr (BtorMBT *btormbt, RNG *rng)
{
  int ew = pick (rng, 1, MAX_BITWIDTH);
  int iw = pick (rng, 1, MAX_INDEXWIDTH);

  es_push (&btormbt->arr, boolector_array (btormbt->btor, ew, iw, NULL));
}

/* randomly select variables from bo within the range ifrom - ito */
static BtorNode *
make_clause (BtorMBT *btormbt, RNG *rng, int ifrom, int ito)
{
  int i, idx;
  BtorNode *e0, *e1;
  ExpStack *es;

  es = &btormbt->bo;
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
        e0 = boolector_not (btormbt->btor, e0);
        es_push (&btormbt->cnf, e0);
      }
    }
    else
    {
      e1 = es->exps[idx].exp;
      if (pick (rng, 0, 1))
      {
        e1 = boolector_not (btormbt->btor, e1);
        es_push (&btormbt->cnf, e1);
      }
      e0 = boolector_or (btormbt->btor, e0, e1);
      es_push (&btormbt->cnf, e0);
    }
  }
  return e0;
}

static void
unary_fun (BtorMBT *btormbt, RNG *rng, Op op, BtorNode *e0, int is_param)
{
  int tmp0, tmp1, e0w, rw;
  ExpStack *es;

  tmp0 = 0;
  tmp1 = 0;

  assert (is_unary_fun (op));
  e0w = boolector_get_width (btormbt->btor, e0);
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
    es = is_param ? btormbt->parambo : &btormbt->bo;
  else
    es = is_param ? btormbt->parambv : &btormbt->bv;

  switch (op)
  {
    case NOT: es_push (es, boolector_not (btormbt->btor, e0)); break;
    case NEG: es_push (es, boolector_neg (btormbt->btor, e0)); break;
    case SLICE:
      es_push (es, boolector_slice (btormbt->btor, e0, tmp0, tmp1));
      break;
    case INC: es_push (es, boolector_inc (btormbt->btor, e0)); break;
    case DEC: es_push (es, boolector_dec (btormbt->btor, e0)); break;
    case UEXT: es_push (es, boolector_uext (btormbt->btor, e0, tmp0)); break;
    case SEXT: es_push (es, boolector_sext (btormbt->btor, e0, tmp0)); break;
    case REDOR: es_push (es, boolector_redor (btormbt->btor, e0)); break;
    case REDXOR: es_push (es, boolector_redxor (btormbt->btor, e0)); break;
    case REDAND: es_push (es, boolector_redand (btormbt->btor, e0)); break;
    default: assert (0);
  }
}

static void
binary_fun (
    BtorMBT *btormbt, RNG *rng, Op op, BtorNode *e0, BtorNode *e1, int is_param)
{
  int tmp0, tmp1, e0w, e1w, rw;
  ExpStack *es;

  assert (is_binary_fun (op));
  e0w = boolector_get_width (btormbt->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  e1w = boolector_get_width (btormbt->btor, e1);
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
        e0  = modifybv (btormbt, rng, e0, e0w, MAX_MULDIVWIDTH, is_param);
        e0w = MAX_MULDIVWIDTH;
        if (op >= MUL && op <= SMOD)
        {
          rw = e0w;
        }
      }
    }
    e1  = modifybv (btormbt, rng, e1, e1w, e0w, is_param);
    e1w = e0w;
    (void) e1w;  // TODO remove since never used?
  }
  else if (op >= SLL && op <= ROR)
  {
    /* modify width of e0 power of 2 and e1 log2(e0) */
    nextpow2 (e0w, &tmp0, &tmp1);
    e0  = modifybv (btormbt, rng, e0, e0w, tmp0, is_param);
    e1  = modifybv (btormbt, rng, e1, e1w, tmp1, is_param);
    e0w = tmp0;
    e1w = tmp1;
    (void) e1w;  // TODO remove since never used?
    rw = e0w;
  }
  else if (op == CONCAT)
  {
    if (e0w + e1w > MAX_BITWIDTH)
    {
      // printf("concat modify\n ")
      if (e0w > 1)
      {
        e0  = modifybv (btormbt, rng, e0, e0w, e0w / 2, is_param);
        e0w = e0w / 2;
      }
      if (e1w > 1)
      {
        e1  = modifybv (btormbt, rng, e1, e1w, e1w / 2, is_param);
        e1w = e1w / 2;
      }
    }
    /* set e0w to select right exp stack */
    rw = e0w + e1w;
  }

  if (rw == 1)
    es = is_param ? btormbt->parambo : &btormbt->bo;
  else
    es = is_param ? btormbt->parambv : &btormbt->bv;

  switch (op)
  {
    case XOR: es_push (es, boolector_xor (btormbt->btor, e0, e1)); break;
    case XNOR: es_push (es, boolector_xnor (btormbt->btor, e0, e1)); break;
    case AND: es_push (es, boolector_and (btormbt->btor, e0, e1)); break;
    case NAND: es_push (es, boolector_nand (btormbt->btor, e0, e1)); break;
    case OR: es_push (es, boolector_or (btormbt->btor, e0, e1)); break;
    case NOR: es_push (es, boolector_nor (btormbt->btor, e0, e1)); break;
    case ADD: es_push (es, boolector_add (btormbt->btor, e0, e1)); break;
    case SUB: es_push (es, boolector_sub (btormbt->btor, e0, e1)); break;
    case MUL: es_push (es, boolector_mul (btormbt->btor, e0, e1)); break;
    case UDIV: es_push (es, boolector_udiv (btormbt->btor, e0, e1)); break;
    case SDIV: es_push (es, boolector_sdiv (btormbt->btor, e0, e1)); break;
    case UREM: es_push (es, boolector_urem (btormbt->btor, e0, e1)); break;
    case SREM: es_push (es, boolector_srem (btormbt->btor, e0, e1)); break;
    case SMOD: es_push (es, boolector_smod (btormbt->btor, e0, e1)); break;
    case SLL: es_push (es, boolector_sll (btormbt->btor, e0, e1)); break;
    case SRL: es_push (es, boolector_srl (btormbt->btor, e0, e1)); break;
    case SRA: es_push (es, boolector_sra (btormbt->btor, e0, e1)); break;
    case ROL: es_push (es, boolector_rol (btormbt->btor, e0, e1)); break;
    case ROR: es_push (es, boolector_ror (btormbt->btor, e0, e1)); break;
    case CONCAT: es_push (es, boolector_concat (btormbt->btor, e0, e1)); break;
    case EQ: es_push (es, boolector_eq (btormbt->btor, e0, e1)); break;
    case NE: es_push (es, boolector_ne (btormbt->btor, e0, e1)); break;
    case UADDO: es_push (es, boolector_uaddo (btormbt->btor, e0, e1)); break;
    case SADDO: es_push (es, boolector_saddo (btormbt->btor, e0, e1)); break;
    case USUBO: es_push (es, boolector_usubo (btormbt->btor, e0, e1)); break;
    case SSUBO: es_push (es, boolector_ssubo (btormbt->btor, e0, e1)); break;
    case UMULO: es_push (es, boolector_umulo (btormbt->btor, e0, e1)); break;
    case SMULO: es_push (es, boolector_smulo (btormbt->btor, e0, e1)); break;
    case SDIVO: es_push (es, boolector_sdivo (btormbt->btor, e0, e1)); break;
    case ULT: es_push (es, boolector_ult (btormbt->btor, e0, e1)); break;
    case SLT: es_push (es, boolector_slt (btormbt->btor, e0, e1)); break;
    case ULTE: es_push (es, boolector_ulte (btormbt->btor, e0, e1)); break;
    case SLTE: es_push (es, boolector_slte (btormbt->btor, e0, e1)); break;
    case UGT: es_push (es, boolector_ugt (btormbt->btor, e0, e1)); break;
    case SGT: es_push (es, boolector_sgt (btormbt->btor, e0, e1)); break;
    case UGTE: es_push (es, boolector_ugte (btormbt->btor, e0, e1)); break;
    case SGTE: es_push (es, boolector_sgte (btormbt->btor, e0, e1)); break;
    case IMPLIES:
      es_push (es, boolector_implies (btormbt->btor, e0, e1));
      break;
    default:
      assert (op == IFF);
      es_push (es, boolector_iff (btormbt->btor, e0, e1));
  }
}

static void
ternary_fun (BtorMBT *btormbt,
             RNG *rng,
             Op op,
             BtorNode *e0,
             BtorNode *e1,
             BtorNode *e2,
             int is_param)
{
  int e1w, e2w;
  ExpStack *es;

  (void) op;

  assert (is_ternary_fun (op));
  assert (boolector_get_width (btormbt->btor, e0) == 1);

  e1w = boolector_get_width (btormbt->btor, e1);
  assert (e1w <= MAX_BITWIDTH);
  e2w = boolector_get_width (btormbt->btor, e2);
  assert (e2w <= MAX_BITWIDTH);

  /* bitvectors must have same bit width */
  e2  = modifybv (btormbt, rng, e2, e2w, e1w, is_param);
  e2w = e1w;
  (void) e2w;  // TODO remove since 'e2w' never used?

  if (e1w == 1)
    es = is_param ? btormbt->parambo : &btormbt->bo;
  else
    es = is_param ? btormbt->parambv : &btormbt->bv;

  es_push (es, boolector_cond (btormbt->btor, e0, e1, e2));
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
afun (BtorMBT *btormbt,
      RNG *rng,
      Op op,
      BtorNode *e0,
      BtorNode *e1,
      BtorNode *e2,
      int is_param)
{
  assert (e0);
  assert (e1);
  assert (boolector_is_array (btormbt->btor, e0));

  int e0w, e0iw, e1w, e2w;
  ExpStack *es;

  int isarr = is_array_fun (op);
  BTORMBT_UNUSED (isarr);
  assert (isarr);

  e0w = boolector_get_width (btormbt->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  e0iw = boolector_get_index_width (btormbt->btor, e0);
  assert (e0iw <= MAX_INDEXWIDTH);

  if (op >= READ && op <= WRITE)
  {
    e1w = boolector_get_width (btormbt->btor, e1);
    assert (e1w <= MAX_BITWIDTH);

    e1  = modifybv (btormbt, rng, e1, e1w, e0iw, is_param);
    e1w = e0iw;
    if (op == WRITE)
    {
      e2w = boolector_get_width (btormbt->btor, e2);
      assert (e1w <= MAX_BITWIDTH);

      e2 = modifybv (btormbt, rng, e2, e2w, e0w, is_param);
      es_push (is_param ? btormbt->paramarr : &btormbt->arr,
               boolector_write (btormbt->btor, e0, e1, e2));
    }
    else
    {
      if (e0w == 1)
        es = is_param ? btormbt->parambo : &btormbt->bo;
      else
        es = is_param ? btormbt->parambv : &btormbt->bv;
      es_push (es, boolector_read (btormbt->btor, e0, e1));
    }
  }
  else
  {
    assert (boolector_is_array (btormbt->btor, e1));
    e1w = boolector_get_width (btormbt->btor, e1);
    assert (e1w == e0w && e1w <= MAX_BITWIDTH);
    assert (boolector_get_index_width (btormbt->btor, e1) == e0iw
            && boolector_get_index_width (btormbt->btor, e1) <= MAX_INDEXWIDTH);

    if (op == EQ)
      es_push (is_param ? btormbt->parambo : &btormbt->bo,
               boolector_eq (btormbt->btor, e0, e1));
    else if (op == NE)
      es_push (is_param ? btormbt->parambo : &btormbt->bo,
               boolector_ne (btormbt->btor, e0, e1));
    else
    {
      assert (op == COND);
      es_push (is_param ? btormbt->paramarr : &btormbt->arr,
               boolector_cond (btormbt->btor, e2, e0, e1));
    }
  }
}

/* Randomly select expression by given type, nodes with no parents (yet unused)
 * are preferred.
 */
static BtorNode *
selexp (
    BtorMBT *btormbt, RNG *rng, ExpType type, int force_param, int *is_param)
{
  assert (force_param != 1 || (btormbt->parambo && btormbt->parambo->n)
          || (btormbt->parambv && btormbt->parambv->n)
          || (btormbt->paramarr && btormbt->paramarr->n));

  int rand, i, bw, idx = -1;
  ExpStack *es, *bo, *bv, *arr;
  BtorNode *exp, *e[3];

  /* choose between param. exps and non-param. exps with p = 0.5 */
  rand = pick (rng, 0, NORM_VAL - 1);

  assert (btormbt->parambo);
  assert (btormbt->parambv);
  if (force_param == -1
      || (!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr)
      || (!btormbt->parambo->n && !btormbt->parambv->n && !btormbt->paramarr->n)
      || (force_param == 0 && (rand < 0.5 * NORM_VAL)))
  // FIXME store p value in btormbt
  {
    bo  = &btormbt->bo;
    bv  = &btormbt->bv;
    arr = &btormbt->arr;
    if (is_param) *is_param = 0;
  }
  else
  {
    bo  = btormbt->parambo;
    bv  = btormbt->parambv;
    arr = btormbt->paramarr;
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
    assert (es == btormbt->parambo || es == btormbt->paramarr);
    assert (bv == btormbt->parambv);
    if (es == btormbt->parambo)
    {
      rand = pick (rng, 0, bv->n - 1);
      exp  = bv->exps[rand].exp;
      bw   = boolector_get_width (btormbt->btor, exp) - 1;
      es_push (es, boolector_slice (btormbt->btor, exp, bw, bw));
    }
    else
    {
      /* generate parameterized WRITE */
      e[0] = selexp (btormbt, rng, T_ARR, -1, NULL);
      rand = pick (rng, 1, 2);
      for (i = 1; i < 3; i++)
        e[i] = selexp (btormbt, rng, T_BV, rand == i ? 1 : 0, NULL);
      afun (btormbt, rng, WRITE, e[0], e[1], e[2], 1);
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
    /* select random literal
     * select from initlayer with lower probability
     * - from range (initlayer - n) with p = 0.666
     * - from ragne (0 - n)         with p = 0.333 */
    idx = pick (rng,
                es->initlayer && es->n > es->initlayer && pick (rng, 0, 3)
                    ? es->initlayer - 1
                    : 0,
                es->n - 1);
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
selarrexp (BtorMBT *btormbt,
           RNG *rng,
           BtorNode *exp,
           int eew,
           int eiw,
           int force_param)
{
  int i, rand, idx, sel_eew, sel_eiw;
  ExpStack *es;
  BtorNode *sel_e, *e[3];

  /* choose between param. exps and non-param. exps with p = 0.5 */
  rand = pick (rng, 0, NORM_VAL - 1);
  assert (btormbt->parambo);
  assert (btormbt->parambv);
  if (force_param == -1
      || (!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr)
      || (!btormbt->parambo->n && !btormbt->parambv->n && !btormbt->paramarr->n)
      || (force_param == 0 && (rand < 0.5 * NORM_VAL)))
    // FIXME store p value in btormbt
    es = &btormbt->arr;
  else
    es = btormbt->paramarr;
  assert (es->n);

  /* random search start idx */
  idx = i = pick (rng, 0, es->n - 1);
  do
  {
    sel_e   = es->exps[i].exp;
    sel_eew = boolector_get_width (btormbt->btor, sel_e);
    sel_eiw = boolector_get_index_width (btormbt->btor, sel_e);
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
    e[0] = selarrexp (btormbt, rng, NULL, eew, eiw, -1);
    rand = pick (rng, 1, 2);
    for (i = 1; i < 3; i++)
      e[i] = selexp (btormbt, rng, T_BV, rand == i ? 1 : 0, NULL);
    afun (btormbt, rng, WRITE, e[0], e[1], e[2], 1);
    sel_e = btormbt->paramarr->exps[btormbt->paramarr->n - 1].exp;
  }
  else
  {
    sel_e = boolector_array (btormbt->btor, eew, eiw, NULL);
    es_push (es, sel_e);
  }
  es->exps[es->n - 1].pars++;
  return sel_e;
}

/* Generate parameterized unary/binary/ternary operation. */
static void
param_fun (BtorMBT *btormbt, RNG *rng, int op_from, int op_to)
{
  int i, rand;
  BtorNode *e[3];
  Op op;

  assert (op_from >= NOT && op_from <= COND);
  assert (op_to >= NOT && op_to <= COND);

  op = pick (rng, op_from, op_to);
  if (is_unary_fun (op))
  {
    e[0] = selexp (btormbt, rng, T_BB, 1, NULL);
    unary_fun (btormbt, rng, op, e[0], 1);
  }
  else if (is_binary_fun (op))
  {
    rand = pick (rng, 0, 1);
    for (i = 0; i < 2; i++)
      e[i] = selexp (btormbt,
                     rng,
                     ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB),
                     i == rand ? 1 : 0,
                     NULL);
    binary_fun (btormbt, rng, op, e[0], e[1], 1);
  }
  else
  {
    assert (is_ternary_fun (op));
    rand = pick (rng, 0, 2);
    for (i = 0; i < 3; i++)
      e[i] =
          selexp (btormbt, rng, i == 0 ? T_BO : T_BB, i == rand ? 1 : 0, NULL);
    ternary_fun (btormbt, rng, op, e[0], e[1], e[2], 1);
  }
}

/* Generate parameterized operations on arrays.
 * Force array expressions with non-parameterized arrays via parameter
 * force_arrnparr (mostly needed for initializing the paramarr stack).
 * Note that this forces either a WRITE or COND expression. */
static void
param_afun (BtorMBT *btormbt, RNG *rng, int force_arrnparr)
{
  int i, rand, eiw, eew;
  BtorNode *e[3];
  Op op;

  /* force array exp with non-parameterized arrays? */
  rand = force_arrnparr ? -1 : pick (rng, 0, 1);
  e[0] = selexp (btormbt, rng, T_ARR, rand, NULL);
  e[1] = e[2] = 0;
  eew         = boolector_get_width (btormbt->btor, e[0]);
  eiw         = boolector_get_index_width (btormbt->btor, e[0]);

  /* choose READ/WRITE with p = 0.666, else EQ/NE/COND */
  if (pick (rng, 0, 2))
  {
    /* force WRITE if array exp with non-parameterized arrays forced */
    op = rand == -1 ? WRITE : pick (rng, READ, WRITE);
    if (op == WRITE)
    {
      rand = pick (rng, 1, 2);
      for (i = 1; i < 3; i++)
        e[i] = selexp (btormbt, rng, T_BV, rand == i ? 1 : 0, NULL);
    }
    else
      e[1] = selexp (btormbt, rng, T_BV, 1, NULL);
  }
  else
  {
    /* force COND if array exp with non-parameterized arrays forced,
     * else distribute EQ, NE and COND evenly */
    op =
        rand >= 0 && pick (rng, 0, 2) && !env.noext ? pick (rng, EQ, NE) : COND;
    e[1] =
        selarrexp (btormbt, rng, e[0], eew, eiw, rand == -1 ? rand : rand ^ 1);
    if (op == COND) e[2] = selexp (btormbt, rng, T_BO, rand < 0 ? 1 : 0, NULL);
  }
  afun (btormbt, rng, op, e[0], e[1], e[2], 1);
}

static void
bfun (BtorMBT *btormbt, unsigned r, int *nparams, int *width, int nlevel)
{
  int i, n, np, ip, w, nops, rand;
  ExpStack parambo, parambv, paramarr;
  ExpStack *es, *tmpparambo, *tmpparambv, *tmpparamarr;
  BtorNode *tmp, *fun, **params, **args;
  RNG rng;

  rng = initrng (r);
  /* choose between apply on random existing function and apply on new
   * function with p = 0.5 */
  // FIXME externalise p
  if (btormbt->fun.n && pick (&rng, 0, 1)) /* use existing function */
  {
    rand     = pick (&rng, 0, btormbt->fun.n - 1);
    fun      = btormbt->fun.exps[rand].exp;
    *nparams = boolector_get_fun_arity (btormbt->btor, fun);
    assert (*nparams);
    *width = boolector_get_index_width (btormbt->btor, fun);
  }
  else /* generate new function */
  {
    tmpparambo  = btormbt->parambo;
    tmpparambv  = btormbt->parambv;
    tmpparamarr = btormbt->paramarr;

    memset (&parambo, 0, sizeof (parambo));
    memset (&parambv, 0, sizeof (parambv));
    memset (&paramarr, 0, sizeof (paramarr));
    btormbt->parambo  = &parambo;
    btormbt->parambv  = &parambv;
    btormbt->paramarr = &paramarr;

    /* choose function parameters */
    *width   = pick (&rng, 1, MAX_BITWIDTH);
    *nparams = pick (&rng, MIN_NPARAMS, MAX_NPARAMS);
    params   = malloc (sizeof (BtorNode *) * *nparams);
    for (i = 0; i < *nparams; i++)
    {
      tmp       = boolector_param (btormbt->btor, *width, NULL);
      params[i] = tmp;
      es_push (*width == 1 ? btormbt->parambo : btormbt->parambv, tmp);
    }

    /* initialize parameterized stacks to be non-empty */
    if (btormbt->parambv->n == 0)
    {
      assert (btormbt->parambo->n);
      rand = pick (&rng, 0, btormbt->parambo->n - 1);
      tmp  = btormbt->parambo->exps[rand].exp;
      assert (boolector_get_width (btormbt->btor, tmp) == 1);
      modifybv (btormbt, &rng, tmp, 1, pick (&rng, 2, MAX_BITWIDTH), 1);
    }
    assert (btormbt->parambv->n);
    if (btormbt->parambo->n == 0) param_fun (btormbt, &rng, REDOR, IFF);
    assert (btormbt->parambo->n);
    param_afun (btormbt, &rng, 1);
    assert (btormbt->paramarr->n);

    /* generate parameterized expressions */
    nops = pick (&rng, 0, MAX_NPARAMOPS);
    n    = 0;
    while (n++ < nops)
    {
    BFUN_PICK_FUN_TYPE:
      assert (parambo.n);
      assert (parambv.n);
      assert (paramarr.n);
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < btormbt->p_fun)
        param_fun (btormbt, &rng, NOT, COND);
      else if (rand < btormbt->p_fun + btormbt->p_afun)
        param_afun (btormbt, &rng, 0);
      else
      {
        if (nlevel < MAX_NNESTEDBFUNS)
        {
          bfun (btormbt, nextrand (&rng), &np, &w, nlevel + 1);
          btormbt->parambo  = &parambo;
          btormbt->parambv  = &parambv;
          btormbt->paramarr = &paramarr;
        }
        else
          goto BFUN_PICK_FUN_TYPE;
      }
    }

    /* pick exp from parambo/parambo with p = 0.5 if non-empty */
    es = parambo.n ? (parambv.n ? (pick (&rng, 0, 1) ? &parambo : &parambv)
                                : &parambo)
                   : &parambv;
    assert (es->n);
    rand = pick (&rng, 0, es->n - 1);
    fun  = boolector_fun (btormbt->btor, *nparams, params, es->exps[rand].exp);
    es_push (&btormbt->fun, fun);

    /* reset scope for arguments to apply node */
    btormbt->parambo  = tmpparambo;
    btormbt->parambv  = tmpparambv;
    btormbt->paramarr = tmpparamarr;

    /* cleanup */
    es_reset (btormbt, &parambo);
    es_reset (btormbt, &parambv);
    es_reset (btormbt, &paramarr);
    free (params);
  }

  /* generate apply expression with arguments within scope of apply */
  args = malloc (sizeof (BtorNode *) * *nparams);
  for (i = 0; i < *nparams; i++)
  {
    tmp     = selexp (btormbt, &rng, T_BV, 0, &ip);
    args[i] = modifybv (btormbt,
                        &rng,
                        tmp,
                        boolector_get_width (btormbt->btor, tmp),
                        *width,
                        ip);
  }

  tmp = boolector_apply (btormbt->btor, *nparams, args, fun);
  es_push (boolector_get_width (btormbt->btor, fun) == 1
               ? (BTOR_REAL_ADDR_NODE (tmp)->parameterized ? btormbt->parambo
                                                           : &btormbt->bo)
               : (BTOR_REAL_ADDR_NODE (tmp)->parameterized ? btormbt->parambv
                                                           : &btormbt->bv),
           tmp);

  free (args);
}

/*------------------------------------------------------------------------*/

/* states */
static void *_new (BtorMBT *, unsigned);
static void *_opt (BtorMBT *, unsigned);
static void *_init (BtorMBT *, unsigned);
static void *_main (BtorMBT *, unsigned);
static void *_addop (BtorMBT *, unsigned);
static void *_fun (BtorMBT *, unsigned);
static void *_afun (BtorMBT *, unsigned);
static void *_bfun (BtorMBT *, unsigned);
static void *_lit (BtorMBT *, unsigned);
static void *_relop (BtorMBT *, unsigned);
static void *_ass (BtorMBT *, unsigned);
static void *_sat (BtorMBT *, unsigned);
static void *_mgen (BtorMBT *, unsigned);
static void *_inc (BtorMBT *, unsigned);
static void *_del (BtorMBT *, unsigned);

static void *
_new (BtorMBT *btormbt, unsigned r)
{
  RNG rng = initrng (r);

  // FIXME externalise
  /* number of initial literals */
  // btormbt->nlits = pick (&rng, 5, 40);
  btormbt->nlits = pick (&rng, 3, 30);
  /* number of initial operations */
  // btormbt->nops = pick (&rng, 0, 100);
  btormbt->nops = pick (&rng, 0, 50);

  init_pd_lits (
      btormbt, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 2, 5));

  /* no delete operation at init */
  init_pd_op (btormbt, 1, 0);
  /* no additional lits at init */
  init_pd_addop (
      btormbt, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 0, 5), 0);

  BTORMBT_LOG (1,
               btormbt,
               "init: pick %d ops (add:rel=%0.1f%%:%0.1f%%), %d lits\n",
               btormbt->nops,
               btormbt->p_addop / 10,
               btormbt->p_relop / 10,
               btormbt->nlits);

  btormbt->btor = boolector_new ();
  assert (btormbt->btor);
  assert (btormbt->btor->apitrace);
  return _opt;
}

static void *
_opt (BtorMBT *btormbt, unsigned r)
{
  int rw;
  RNG rng = initrng (r);

  if (pick (&rng, 0, 1))
  {
    BTORMBT_LOG (1, btormbt, "[btormbt] enable model generation\n");
    boolector_enable_model_gen (btormbt->btor);
    btormbt->mgen = 1;
  }
  if (pick (&rng, 0, 1))
  {
    BTORMBT_LOG (1, btormbt, "[btormbt] enable incremental usage\n");
    boolector_enable_inc_usage (btormbt->btor);
    btormbt->inc = 1;
  }

  rw = pick (&rng, 0, 3);
  BTORMBT_LOG (1, btormbt, "[btormbt] set rewrite level %d \n", rw);
  boolector_set_rewrite_level (btormbt->btor, rw);

  return _init;
}

static void *
_init (BtorMBT *btormbt, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  if (btormbt->bo.n + btormbt->bv.n + btormbt->arr.n < btormbt->nlits)
  {
    return _lit;
  }

  /* generate at least one bool-var, one bv-var and one arr;
   * to ensure nonempty expression stacks */
  if (btormbt->bo.n < 1) make_var (btormbt, &rng, T_BO);
  if (btormbt->bv.n < 1) make_var (btormbt, &rng, T_BV);
  if (btormbt->arr.n < 1) make_arr (btormbt, &rng);

  if (btormbt->ops < btormbt->nops)
  {
    btormbt->ops++;
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < btormbt->p_addop)
      return _addop;
    else
      return _relop;
  }

  BTORMBT_LOG (
      1,
      btormbt,
      "[btormbt] after init: nexps: booleans %d, bitvectors %d, arrays %d \n",
      btormbt->bo.n,
      btormbt->bv.n,
      btormbt->arr.n);

  btormbt->bo.initlayer  = btormbt->bo.n;
  btormbt->bv.initlayer  = btormbt->bv.n;
  btormbt->arr.initlayer = btormbt->arr.n;

  // FIXME externalise
  /* adapt paramters for main */
  btormbt->ops = 0; /* reset operation counter */
  // btormbt->nops = pick (&rng, 20, 200);
  // btormbt->nass = pick (&rng, 10, 70);  /* how many assertions of nops */
  btormbt->nops = pick (&rng, 20, 100);
  /* how many operations should be assertions?
   * -> nops and nass should be in relation (the more ops, the more assertions)
   *    in order to keep the sat/unsat ration balanced */
  // TODO may improve?
  // btormbt->nass = pick (&rng, 10, 30);
  // does this find as many bugs??
  if (btormbt->nops < 50)
    btormbt->nass = BTORMBT_MIN (btormbt->nops, pick (&rng, 5, 25));
  else
    btormbt->nass = pick (&rng, 20, 30);

  //  FIXME externalise
  //  init_pd_lits (btormbt, pick (&rng, 1, 10), pick (&rng, 0, 5),
  //		pick (&rng, 0, 5));
  init_pd_lits (
      btormbt, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 0, 5));
  init_pd_op (btormbt, pick (&rng, 1, 8), pick (&rng, 1, 3));
  init_pd_addop (btormbt,
                 pick (&rng, 1, 10),
                 pick (&rng, 0, 5),
                 pick (&rng, 0, 5),
                 pick (&rng, 0, 3));

  BTORMBT_LOG (1,
               btormbt,
               "[btormbt] main: pick %d ops (add:rel=%0.1f%%:%0.1f%%)\n",
               btormbt->nops,
               btormbt->p_addop / 10,
               btormbt->p_relop / 10);
  BTORMBT_LOG (
      1, btormbt, "[btormbt]       make ~%d asserts/assumes \n", btormbt->nass);

  btormbt->isinit = 1;
  return _main;
}

static void *
_main (BtorMBT *btormbt, unsigned r)
{
  float rand;
  RNG rng = initrng (r);

  assert (btormbt->bo.n > 0);
  assert (btormbt->bv.n > 0);
  assert (btormbt->arr.n > 0);

  /* main operations */
  if (btormbt->ops < btormbt->nops)
  {
    btormbt->ops++;
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < btormbt->nass * NORM_VAL / btormbt->nops)
      return _ass;
    else
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < btormbt->p_addop)
        return _addop;
      else
        return _relop;
    }
  }

  BTORMBT_LOG (
      1,
      btormbt,
      "[btormbt] after main: nexps: booleans %d, bitvectors %d, arrays %d \n",
      btormbt->bo.n,
      btormbt->bv.n,
      btormbt->arr.n);
  BTORMBT_LOG (1,
               btormbt,
               "[btormbt] after main: number of asserts: %d, assumps: %d \n",
               btormbt->totasserts,
               btormbt->nassume);

  return _sat;
}

static void *
_addop (BtorMBT *btormbt, unsigned r)
{
  int rand;
  void *next;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);

  if (rand < btormbt->p_fun)
    next = _fun;
  else if (rand < btormbt->p_fun + btormbt->p_afun)
    next = _afun;
  else if (rand < btormbt->p_fun + btormbt->p_afun + btormbt->p_bfun)
    next = _bfun;
  else
    next = _lit;

  return next;
}

static void *
_fun (BtorMBT *btormbt, unsigned r)
{
  BtorNode *e0, *e1, *e2;
  RNG rng = initrng (r);

  Op op = pick (&rng, NOT, COND);

  if (is_unary_fun (op))
  {
    e0 = selexp (btormbt, &rng, T_BB, 0, NULL);
    unary_fun (btormbt, &rng, op, e0, 0);
  }
  else if (is_binary_fun (op))
  {
    e0 = selexp (
        btormbt, &rng, ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB), 0, NULL);
    e1 = selexp (
        btormbt, &rng, ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB), 0, NULL);
    binary_fun (btormbt, &rng, op, e0, e1, 0);
  }
  else
  {
    assert (is_ternary_fun (op));
    e0 = selexp (btormbt, &rng, T_BO, 0, NULL);
    e1 = selexp (btormbt, &rng, T_BB, 0, NULL);
    e2 = selexp (btormbt, &rng, T_BB, 0, NULL);
    ternary_fun (btormbt, &rng, op, e0, e1, e2, 0);
  }
  return (btormbt->isinit ? _main : _init);
}

static void *
_afun (BtorMBT *btormbt, unsigned r)
{
  int e0w, e0iw;
  Op op;
  BtorNode *e0, *e1, *e2 = NULL;
  RNG rng = initrng (r);

  e0   = selexp (btormbt, &rng, T_ARR, 0, NULL);
  e0w  = boolector_get_width (btormbt->btor, e0);
  e0iw = boolector_get_index_width (btormbt->btor, e0);

  /* use read/write with p=0.666 else EQ/NE/COND */
  // TODO may use p=0.5??
  if (pick (&rng, 0, 2))
  {
    op = pick (&rng, READ, WRITE);
    e1 = selexp (btormbt, &rng, T_BV, 0, NULL);
    if (op == WRITE) e2 = selexp (btormbt, &rng, T_BV, 0, NULL);
    afun (btormbt, &rng, op, e0, e1, e2, 0);
  }
  else
  {
    /* select EQ/NE/COND with same propability */
    op = pick (&rng, 0, 2) && !env.noext ? pick (&rng, EQ, NE) : COND;
    e1 = selarrexp (btormbt, &rng, e0, e0w, e0iw, 0);
    if (op == COND) e2 = selexp (btormbt, &rng, T_BO, 0, NULL);
    afun (btormbt, &rng, op, e0, e1, e2, 0);
  }

  return (btormbt->isinit ? _main : _init);
}

static void *
_bfun (BtorMBT *btormbt, unsigned r)
{
  assert (!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr);

  int nparams, width;

  bfun (btormbt, r, &nparams, &width, 0);

  btormbt->parambo = btormbt->parambv = btormbt->paramarr = NULL; /* cleanup */

  return (btormbt->isinit ? _main : _init);
}

static void *
_lit (BtorMBT *btormbt, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);
  if (rand < btormbt->p_var)
    make_var (btormbt, &rng, T_BB);
  else if (rand < btormbt->p_const + btormbt->p_var)
    make_const (btormbt, &rng);
  else
    make_arr (btormbt, &rng);

  return (btormbt->isinit ? _main : _init);
}

static void *
_relop (BtorMBT *btormbt, unsigned r)
{
  int idx, rand;
  ExpStack *es;
  RNG rng = initrng (r);

  /* select target exp stack with probabilty proportional to size */
  rand = pick (&rng, 0, btormbt->bo.n + btormbt->bv.n + btormbt->arr.n - 1);
  if (rand < btormbt->bo.n)
    es = &btormbt->bo;
  else if (rand < btormbt->bo.n + btormbt->bv.n)
    es = &btormbt->bv;
  else
    es = &btormbt->arr;
  if (es->n > 1)
  {
    idx = pick (&rng, 0, es->n - 1);

    if (es == &btormbt->bo)
      assert (boolector_get_width (btormbt->btor, btormbt->bo.exps[idx].exp)
              == 1);
    else if (es == &btormbt->bv)
      assert (boolector_get_width (btormbt->btor, btormbt->bv.exps[idx].exp)
              > 1);
    else
      assert (boolector_is_array (btormbt->btor, btormbt->arr.exps[idx].exp));

    es_del (btormbt, es, idx);
  }
  return (btormbt->isinit ? _main : _init);
}

static void *
_ass (BtorMBT *btormbt, unsigned r)
{
  int lower;
  RNG rng = initrng (r);
  BtorNode *cls;

  /* select from init layer with lower probability */
  lower = btormbt->bo.initlayer && btormbt->bo.n > btormbt->bo.initlayer
                  && pick (&rng, 0, 4)
              ? btormbt->bo.initlayer - 1
              : 0;
  cls = make_clause (btormbt, &rng, lower, btormbt->bo.n - 1);
  assert (!BTOR_REAL_ADDR_NODE (cls)->parameterized);

  if (btormbt->inc && pick (&rng, 0, 4))
  {
    boolector_assume (btormbt->btor, cls);
    btormbt->nassume++;
  }
  else
  {
    boolector_assert (btormbt->btor, cls);
    btormbt->nassert++;
    btormbt->totasserts++;
  }
  return _main;
}

static void *
_sat (BtorMBT *btormbt, unsigned r)
{
  BTORMBT_UNUSED (r);
  int res;

  BTORMBT_LOG (1, btormbt, "[btormbt] call sat...\n");

  res = boolector_sat (btormbt->btor);

  if (res == BOOLECTOR_UNSAT)
    BTORMBT_LOG (1, btormbt, "[btormbt] unsat\n");
  else if (res == BOOLECTOR_SAT)
    BTORMBT_LOG (1, btormbt, "[btormbt] sat\n");
  else
    BTORMBT_LOG (1, btormbt, "[btormbt]  sat call returned %d\n", res);

  return btormbt->mgen && res == BOOLECTOR_SAT ? _mgen : _inc;
}

static void *
_mgen (BtorMBT *btormbt, unsigned r)
{
  BTORMBT_UNUSED (r);
  int i, size = 0;
  char *bv = NULL, **indices = NULL, **values = NULL;

  assert (btormbt->mgen);

  for (i = 0; i < btormbt->bo.n; i++)
  {
    bv = boolector_bv_assignment (btormbt->btor, btormbt->bo.exps[i].exp);
    boolector_free_bv_assignment (btormbt->btor, bv);
  }
  for (i = 0; i < btormbt->bv.n; i++)
  {
    bv = boolector_bv_assignment (btormbt->btor, btormbt->bv.exps[i].exp);
    boolector_free_bv_assignment (btormbt->btor, bv);
  }
  for (i = 0; i < btormbt->arr.n; i++)
  {
    boolector_array_assignment (
        btormbt->btor, btormbt->arr.exps[i].exp, &indices, &values, &size);
    if (size > 0)
      boolector_free_array_assignment (btormbt->btor, indices, values, size);
  }
  return _inc;
}

static void *
_inc (BtorMBT *btormbt, unsigned r)
{
  RNG rng = initrng (r);

  /* release cnf expressions */
  es_reset (btormbt, &btormbt->cnf);

  // FIXME externalize
  if (btormbt->inc && pick (&rng, 0, 2))
  {
    btormbt->inc++;
    btormbt->ops     = 0; /* reset */
    btormbt->nass    = btormbt->nass - btormbt->nassert;
    btormbt->nassume = 0; /* reset */
    btormbt->nassert = 0;
    // btormbt->nops = pick (&rng, 0, 150);
    btormbt->nops = pick (&rng, 20, 50);
    init_pd_lits (
        btormbt, pick (&rng, 1, 10), pick (&rng, 0, 5), pick (&rng, 0, 5));
    init_pd_op (btormbt, pick (&rng, 1, 5), pick (&rng, 1, 5));
    init_pd_addop (btormbt,
                   pick (&rng, 1, 10),
                   pick (&rng, 0, 5),
                   pick (&rng, 1, 5),
                   pick (&rng, 0, 3));

    BTORMBT_LOG (1,
                 btormbt,
                 "[btormbt] inc: pick %d ops(add:rel=%0.1f%%:%0.1f%%) \n",
                 btormbt->nops,
                 btormbt->p_addop / 10,
                 btormbt->p_relop / 10);
    BTORMBT_LOG (btormbt->inc,
                 btormbt,
                 "[btormbt] number of increments: %d \n",
                 btormbt->inc - 1);

    return _main;
  }
  return _del;
}

static void *
_del (BtorMBT *btormbt, unsigned r)
{
  assert (btormbt->btor);

  BTORMBT_UNUSED (r);

  es_release (btormbt, &btormbt->bo);
  es_release (btormbt, &btormbt->bv);
  es_release (btormbt, &btormbt->arr);
  es_release (btormbt, &btormbt->fun);
  es_release (btormbt, &btormbt->cnf);

  boolector_delete (btormbt->btor);
  btormbt->btor = NULL;
  return 0;
}

static void
rantrav (Env *env)
{
  State state, next;
  unsigned rand;
  BtorMBT btormbt;
  memset (&btormbt, 0, sizeof btormbt);

  btormbt.print = !env->quiet;
  memset (&btormbt.bo, 0, sizeof (btormbt.bo));
  memset (&btormbt.bv, 0, sizeof (btormbt.bv));
  memset (&btormbt.arr, 0, sizeof (btormbt.arr));
  memset (&btormbt.fun, 0, sizeof (btormbt.fun));
  memset (&btormbt.cnf, 0, sizeof (btormbt.cnf));
  btormbt.parambo = btormbt.parambv = btormbt.paramarr = NULL;

  env->rng.z = env->rng.w = env->seed;

  /* state loop */
  for (state = _new; state; state = next)
  {
    rand = nextrand (&env->rng);
    next = state (&btormbt, rand);
  }
}

static int
run (Env *env, void (*process) (Env *))
{
  int res, status, saved1, saved2, null;
  pid_t id;
  (void) saved1;
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
#ifdef USE_PRAGMAS_TO_DISABLE_UNUSED_RESULT_WARNING
#pragma GCC diagnostic ignored "-Wunused-result"
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
#ifdef USE_PRAGMAS_TO_DISABLE_UNUSED_RESULT_WARNING
#pragma GCC diagnostic ignored "-Wunused-result"
#endif
#ifdef NDEBUG
    assert (tmp == 1);
#endif
    BTORMBT_UNUSED (tmp);
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
    if (env->print) printf ("signal %d", WTERMSIG (status));
    res = 1;
  }
  else
  {
    if (env->print) printf ("unknown");
    res = 1;
  }
  return res;
}

/*------------------------------------------------------------------------*/

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
  fputs ("*** btormbt: ", stderr);
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
  printf ("[btormbt] finished after %0.2f seconds\n", t);
  printf ("[btormbt] %d rounds = %0.2f rounds per second\n",
          env.round,
          average (env.round, t));
  printf ("[btormbt] %d bugs = %0.2f bugs per second\n",
          env.bugs,
          average (env.bugs, t));
}

#ifdef __GNUC__
#if __GNUC__ >= 4 && __GNUC_MAJOR__ >= 6
#define USE_PRAGMAS_TO_DISABLE_UNUSED_RESULT_WARNING
#endif
#endif

/* Note: - do not call non-reentrant function here, see:
 *         https://www.securecoding.cert.org/confluence/display/seccode/SIG30-C.+Call+only+asynchronous-safe+functions+within+signal+handlers
 *       - do not use printf here (causes segfault when SIGINT and valgrind) */
static void
sighandler (int sig)
{
  char str[100];

  sprintf (str, "*** btormbt: caught signal %d\n", sig);
#ifdef USE_PRAGMAS_TO_DISABLE_UNUSED_RESULT_WARNING
#pragma GCC diagnostic ignored "-Wunused-result"
#endif
  write (1, str, strlen (str));
#ifdef USE_PRAGMAS_TO_DISABLE_UNUSED_RESULT_WARNING
#pragma GCC diagnostic warning "-Wunused-result"
#endif
  /* Note: if _exit is used here (which is reentrant, in contrast to exit),
   *       atexit handler is not called. Hence, use exit here. */
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

static void
finish (void)
{
  fflush (stderr);
  fflush (stdout);
  if (env.ppid == getpid ()) stats ();
  fflush (stdout);
}

int
main (int argc, char **argv)
{
  int i, max, mac, pid, prev, res, seeded;
  char name[100];
  char *aname, *cmd;

  start_time = current_time ();

  memset (&env, 0, sizeof env);
  max          = INT_MAX;
  pid          = 0;
  prev         = 0;
  seeded       = 0;
  env.seed     = -1;
  env.terminal = isatty (1);

  atexit (finish);

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("%s", BTORMBT_USAGE);
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
    else if (!strcmp (argv[i], "-e")
             || !strcmp (argv[i], "--no-extensionality"))
      env.noext = 1;
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
    {
      env.seed = atoi (argv[i]);
      seeded   = 1;
    }
  }

  if (!(aname = getenv ("BTORAPITRACE")))
  {
    sprintf (name, "/tmp/bug-%d-mbt.trace", getpid ());
    setenv ("BTORAPITRACE", name, 1);
  }
  env.print = !env.quiet;

  env.ppid = getpid ();
  setsighandlers ();

  if (env.seed >= 0 && !env.alwaysfork)
  {
    rantrav (&env);
    printf ("\n");
  }
  else
  {
    mac = hashmac ();
    for (env.round = 0; env.round < max; env.round++)
    {
      if (!(prev & 1)) prev++;

      if (!seeded)
      {
        env.seed = mac;
        env.seed *= 123301093;
        env.seed += times (0);
        env.seed *= 223531513;
        env.seed += pid;
        env.seed *= 31752023;
        env.seed += prev;
        env.seed *= 43376579;
        prev = env.seed = abs (env.seed) >> 1;
      }

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

      if ((res && env.first) || seeded) break;
    }
  }
  if (!env.quiet)
  {
    if (env.terminal) erase ();
    printf ("forked %d\n", env.forked);
  }
  return 0;
}
