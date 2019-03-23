/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Christian Reisenberger.
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2018 Mathias Preiner.
 *  Copyright (C) 2013-2016 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolector.h"
#include "btorcore.h"
#include "btoropt.h"
#include "btorsort.h"
#include "utils/btormem.h"
#include "utils/btorrng.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BtorConstCharPtr, const char *);
BTOR_DECLARE_STACK (BtorCharPtrPtr, char **);
BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

/*------------------------------------------------------------------------*/

void boolector_print_value_smt2 (Btor *, BoolectorNode *, char *, FILE *);

/*------------------------------------------------------------------------*/

#define MIN_BITWIDTH 2   /* must be >= 2 */
#define MAX_BITWIDTH 128 /* must be >= 2 */
#define MIN_INDEXWIDTH 1
#define MAX_INDEXWIDTH 8
#define MIN_MULDIVWIDTH 1
#define MAX_MULDIVWIDTH 8

#define MIN_SORT_FUN_ARITY 2
#define MAX_SORT_FUN_ARITY 10

#define MIN_NPARAMS 1 /* must be >= 1 */
#define MAX_NPARAMS 5
#define MAX_NPARAMOPS 5
#define MAX_NNESTEDBFUNS 10

#define MIN_NLITS 3
#define MAX_NLITS 30

#define MIN_NVARS_INIT 1
#define MAX_NVARS_INIT 10
#define MIN_NVARS 1
#define MAX_NVARS 10
#define MIN_NVARS_INC 1
#define MAX_NVARS_INC 10
#define MIN_NCONSTS_INIT 0
#define MAX_NCONSTS_INIT 5
#define MIN_NCONSTS 0
#define MAX_NCONSTS 5
#define MIN_NCONSTS_INC 0
#define MAX_NCONSTS_INC 5
#define MIN_NARRS_INIT 2
#define MAX_NARRS_INIT 5
#define MIN_NARRS 0
#define MAX_NARRS 5
#define MIN_NARRS_INC 0
#define MAX_NARRS_INC 5
#define MIN_NADDOPFUNS_INIT 1
#define MAX_NADDOPFUNS_INIT 10
#define MIN_NADDOPFUNS 1
#define MAX_NADDOPFUNS 10
#define MIN_NADDOPFUNS_INC 1
#define MAX_NADDOPFUNS_INC 10
#define MIN_NADDOPUF_INIT 1
#define MAX_NADDOPUF_INIT 10
#define MIN_NADDOPUF 1
#define MAX_NADDOPUF 10
#define MIN_NADDOPUF_INC 1
#define MAX_NADDOPUF_INC 10
#define MIN_NADDOPAFUNS_INIT 0
#define MAX_NADDOPAFUNS_INIT 5
#define MIN_NADDOPAFUNS 0
#define MAX_NADDOPAFUNS 5
#define MIN_NADDOPAFUNS_INC 0
#define MAX_NADDOPAFUNS_INC 5
#define MIN_NADDOPBFUNS_INIT 0
#define MAX_NADDOPBFUNS_INIT 5
#define MIN_NADDOPBFUNS 0
#define MAX_NADDOPBFUNS 5
#define MIN_NADDOPBFUNS_INC 1
#define MAX_NADDOPBFUNS_INC 5
#define MIN_NADDOPLITS_INIT 0
#define MAX_NADDOPLITS_INIT 0
#define MIN_NADDOPLITS 0
#define MAX_NADDOPLITS 3
#define MIN_NADDOPLITS_INC 0
#define MAX_NADDOPLITS_INC 3

#define MIN_NOPS_INIT 0
#define MAX_NOPS_INIT 50
#define MIN_NOPS 20
#define MAX_NOPS 100
#define MIN_NOPS_INC 20
#define MAX_NOPS_INC 50
#define MIN_NADDOPS_INIT 1
#define MAX_NADDOPS_INIT 1
#define MIN_NADDOPS 1
#define MAX_NADDOPS 8
#define MIN_NADDOPS_INC 1
#define MAX_NADDOPS_INC 5
#define MIN_NRELOPS_INIT 0
#define MAX_NRELOPS_INIT 0
#define MIN_NRELOPS 1
#define MAX_NRELOPS 3
#define MIN_NRELOPS_INC 1
#define MAX_NRELOPS_INC 5

#define MAX_NOPS_LOWER 50
#define MIN_NASSERTS_LOWER 0
#define MAX_NASSERTS_LOWER 10
#define MIN_NASSERTS_UPPER 5
#define MAX_NASSERTS_UPPER 15

#define MIN_INC_CALLS 0
#define MAX_INC_CALLS 10

#define P_SORT_BV 500         // 0.5
#define P_SORT_FUN 500        // 0.5
#define P_SORT_FUN_UNARY 100  // 0.1
#define P_ASSUME 800          // 0.8
#define P_PARAM_EXP 500       // 0.5
#define P_PARAM_ARR_EXP 500   // 0.5
#define P_APPLY_FUN 500       // 0.5
#define P_APPLY_UF 500        // 0.5
#define P_RW 666              // 0.66
#define P_READ 500            // 0.5
#define P_COND 333            // 0.33
#define P_EQ 500              // 0.5
#define P_DUMP 100            // 0.1
#define P_PRINT_MODEL 100     // 0.1
#define P_MODEL_FORMAT 500    // 0.5

#define EXIT_OK 0
#define EXIT_ERROR 1
#define EXIT_TIMEOUT 2
#define EXIT_SIGNALED 3
#define EXIT_UNKNOWN 4

#define FORCE_SHADOW_NONE 0
#define FORCE_SHADOW_TRUE 1
#define FORCE_SHADOW_FALSE -1

/*------------------------------------------------------------------------*/

#define BTORMBT_STR(str) #str
#define BTORMBT_M2STR(m) BTORMBT_STR (m)

/*------------------------------------------------------------------------*/

#define BTORMBT_USAGE                                                          \
  "usage: mbt [<option>]\n"                                                    \
  "\n"                                                                         \
  "where <option> is one of the following:\n"                                  \
  "\n"                                                                         \
  "  -h, --help                  print this message and exit\n"                \
  "  -ha                         print all options\n"                          \
  "\n"                                                                         \
  "  -v                          be extra verbose\n"                           \
  "  -q                          be extra quiet (stats only)\n"                \
  "\n"                                                                         \
  "  -s <val>                    enable/disable shadow clone testing\n"        \
  "                              (0: disable, 1: enable)\n"                    \
  "  -o                          disable option fuzzing\n"                     \
  "  -f                          quit after first bug encountered\n"           \
  "  -m <maxruns>                quit after <maxruns> rounds\n"                \
  "  -t <seconds>                set time limit for calls to boolector\n"      \
  "  -O                          output directory for saving traces\n"         \
  "\n"                                                                         \
  "  --logic <logic>             generate <logic> formulas only, available\n"  \
  "                              logics are: QF_BV,QF_UFBV,QF_ABV, QF_AUFBV\n" \
  "                              (default: QF_AUFBV)\n"                        \
  "  -b <btoropt> <val>          set boolector option <btoropt> to <val>\n"

/*------------------------------------------------------------------------*/

#define BTORMBT_LOG(l, fmt, args...) \
  do                                 \
  {                                  \
    if (l <= g_btormbt->verbosity)   \
    {                                \
      printf ("[btormbt] ");         \
      printf (fmt, ##args);          \
      printf ("\n");                 \
    }                                \
  } while (0)

#define BTORMBT_LOG_STATUS(l, prefix)                                      \
  BTORMBT_LOG (l,                                                          \
               prefix " (%d): bool %" PRId64 ", bv %" PRId64               \
                      ", array %" PRId64 ", fun %" PRId64 ", uf %" PRId64, \
               g_btormbt->round.ops,                                       \
               BTOR_COUNT_STACK (g_btormbt->bo->exps),                     \
               BTOR_COUNT_STACK (g_btormbt->bv->exps),                     \
               BTOR_COUNT_STACK (g_btormbt->arr->exps),                    \
               BTOR_COUNT_STACK (g_btormbt->fun->exps),                    \
               BTOR_COUNT_STACK (g_btormbt->uf->exps));

/*------------------------------------------------------------------------*/

#define BTORMBT_MIN(x, y) ((x) < (y) ? (x) : (y))

/*------------------------------------------------------------------------*/

typedef enum BtorMBTOperator
{
  /* PARAM must be the first */
  PARAM,
  FUN,
  UF,
  /* const */
  CONST,
  ZERO,
  FALSE,
  ONES,
  MIN_SIGNED,
  MAX_SIGNED,
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
  REPEAT,
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
  APPLY,
  /* do not remove */
  BTORMBT_NUM_OPS
} BtorMBTOperator;

const char *const g_op2str[] = {
    "param", "fun",     "uf",    "const", "zero",  "false", "ones",   "true",
    "one",   "uint",    "int",   "var",   "array", "not",   "neg",    "repeat",
    "slice", "inc",     "dec",   "uext",  "sext",  "redor", "redxor", "redand",
    "eq",    "ne",      "uaddo", "saddo", "usubo", "ssubo", "umulo",  "smulo",
    "sdivo", "ult",     "slt",   "ulte",  "slte",  "ugt",   "sgt",    "ugte",
    "sgte",  "implies", "iff",   "xor",   "xnor",  "and",   "nand",   "or",
    "nor",   "add",     "sub",   "mul",   "udiv",  "sdiv",  "urem",   "srem",
    "smod",  "sll",     "srl",   "sra",   "rol",   "ror",   "concat", "cond",
    "read",  "write",   "apply",
};

static bool
is_unary_op (BtorMBTOperator op)
{
  return op >= NOT && op <= REDAND;
}

#if 0
// NOTE (ma): not required right now
static bool
is_boolean_unary_op (BtorMBTOperator op)
{
  return (op >= REDOR && op <= REDAND);
}
#endif

static bool
is_binary_op (BtorMBTOperator op)
{
  return (op >= EQ && op <= CONCAT);
}

#if 0
// NOTE (ma): not required right now
static bool
is_boolean_binary_op (BtorMBTOperator op)
{
  return (op >= EQ && op <= IFF);
}
#endif

#ifndef NDEBUG
static bool
is_ternary_op (BtorMBTOperator op)
{
  return op == COND;
}

static bool
is_array_op (BtorMBTOperator op)
{
  return (op >= COND && op <= WRITE) || (op >= EQ && op <= NE);
}
#endif

/*------------------------------------------------------------------------*/

typedef struct BtorMBT BtorMBT;

static void btormbt_release_node (BtorMBT *mbt, BoolectorNode *node);

struct BtorMBTBtorOpt
{
  BtorOption kind;
  char *name;
  char *shrt;
  uint32_t val;
  uint32_t min;
  uint32_t max;
  uint32_t dflt;
  const char *desc;

  bool is_engine_opt;
  uint32_t engine;

  bool forced_by_cl;
};

typedef struct BtorMBTBtorOpt BtorMBTBtorOpt;

BTOR_DECLARE_STACK (BtorMBTBtorOptPtr, BtorMBTBtorOpt *);

/*------------------------------------------------------------------------*/

enum BtorMBTExpType
{
  BTORMBT_BO_T, /* Boolean */
  BTORMBT_BV_T, /* bit vector */
  BTORMBT_BB_T, /* Boolean or bit vector */
  BTORMBT_ARR_T /* array */
};

typedef enum BtorMBTExpType BtorMBTExpType;

struct BtorMBTExp
{
  BoolectorNode *exp;
  uint32_t parents; /* number of parents */
};

typedef struct BtorMBTExp BtorMBTExp;

BTOR_DECLARE_STACK (BtorMBTExpPtr, BtorMBTExp *);

struct BtorMBTExpStack
{
  BtorMBTExpPtrStack exps;
  uint32_t last_pos_parents; /* position of last parents check */
  uint32_t init_layer_size;  /* size of initial layer */
};

typedef struct BtorMBTExpStack BtorMBTExpStack;

static BtorMBTExpStack *
btormbt_new_exp_stack (BtorMemMgr *mm)
{
  assert (mm);
  BtorMBTExpStack *res;

  BTOR_CNEW (mm, res);
  BTOR_INIT_STACK (mm, res->exps);
  return res;
}

static void
btormbt_push_exp_stack (BtorMemMgr *mm,
                        BtorMBTExpStack *expstack,
                        BoolectorNode *exp)
{
  assert (mm);
  assert (expstack);
  assert (exp);

  BtorMBTExp *e;

  BTOR_CNEW (mm, e);
  e->exp = exp;
  BTOR_PUSH_STACK (expstack->exps, e);
}

static BoolectorNode *
btormbt_pop_exp_stack (BtorMemMgr *mm, BtorMBTExpStack *expstack)
{
  assert (mm);
  assert (expstack);

  BtorMBTExp *e;
  BoolectorNode *exp;

  if (!BTOR_COUNT_STACK (expstack->exps)) return 0;
  e   = BTOR_POP_STACK (expstack->exps);
  exp = e->exp;
  BTOR_DELETE (mm, e);
  return exp;
}

static void
btormbt_del_exp_stack (BtorMemMgr *mm, BtorMBTExpStack *expstack, uint32_t idx)
{
  assert (expstack);
  assert (idx < BTOR_COUNT_STACK (expstack->exps));

  uint32_t i;

  BTOR_DELETE (mm, expstack->exps.start[idx]);
  for (i = idx; i < BTOR_COUNT_STACK (expstack->exps) - 1; i++)
    expstack->exps.start[i] = expstack->exps.start[i + 1];
  (void) BTOR_POP_STACK (expstack->exps);
  if (idx < expstack->last_pos_parents) expstack->last_pos_parents -= 1;
}

static void
btormbt_reset_exp_stack (BtorMemMgr *mm, BtorMBTExpStack *expstack)
{
  assert (expstack);

  uint32_t i;

  for (i = 0; i < BTOR_COUNT_STACK (expstack->exps); i++)
    BTOR_DELETE (mm, expstack->exps.start[i]);
  BTOR_RESET_STACK (expstack->exps);
  expstack->last_pos_parents = 0;
  expstack->init_layer_size  = 0;
}

static void
btormbt_release_exp_stack (BtorMemMgr *mm, BtorMBTExpStack *expstack)
{
  assert (expstack);

  BtorMBTExp *exp;

  if (!expstack) return;
  while (!BTOR_EMPTY_STACK (expstack->exps))
  {
    exp = BTOR_POP_STACK (expstack->exps);
    BTOR_DELETE (mm, exp);
  }
  BTOR_RELEASE_STACK (expstack->exps);
  BTOR_DELETE (mm, expstack);
}

#define RELEASE_EXP_STACK(stack, dorelease)                         \
  do                                                                \
  {                                                                 \
    uint32_t i;                                                     \
    if (dorelease)                                                  \
    {                                                               \
      for (i = 0; i < BTOR_COUNT_STACK (mbt->stack->exps); i++)     \
        btormbt_release_node (mbt, mbt->stack->exps.start[i]->exp); \
    }                                                               \
    btormbt_release_exp_stack (mbt->mm, mbt->stack);                \
    mbt->stack = 0;                                                 \
  } while (0)

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BoolectorSort, BoolectorSort);

static BoolectorSortStack *
btormbt_new_sort_stack (BtorMemMgr *mm)
{
  assert (mm);
  BoolectorSortStack *res;

  BTOR_CNEW (mm, res);
  BTOR_INIT_STACK (mm, *res);
  return res;
}

static void
btormbt_push_sort_stack (BoolectorSortStack *sortstack, BoolectorSort sort)
{
  assert (sortstack);
  assert (sort);

  BTOR_PUSH_STACK (*sortstack, sort);
}

static void
btormbt_release_sort_stack (BtorMemMgr *mm, BoolectorSortStack *sortstack)
{
  assert (sortstack);

  if (!sortstack) return;
  BTOR_RELEASE_STACK (*sortstack);
  BTOR_DELETE (mm, sortstack);
}

#define RELEASE_SORT_STACK(stack)                               \
  do                                                            \
  {                                                             \
    uint32_t i;                                                 \
    for (i = 0; i < BTOR_COUNT_STACK (*mbt->stack); i++)        \
      boolector_release_sort (mbt->btor, mbt->stack->start[i]); \
    btormbt_release_sort_stack (mbt->mm, mbt->stack);           \
    mbt->stack = 0;                                             \
  } while (0)

/*------------------------------------------------------------------------*/

struct BtorMBTStatistics
{
  /* total numbers for all rounds */
  uint32_t num_sat;
  uint32_t num_unsat;
  uint32_t num_inc;
  uint32_t num_shadow_clone;
  uint32_t num_clone;
  uint32_t num_simp;
  BtorMBTOperator num_ops[BTORMBT_NUM_OPS];

  /* avg. numbers per round */
};

typedef struct BtorMBTStatistics BtorMBTStatistics;

/*------------------------------------------------------------------------*/

enum BtorMBTLogic
{
  BTORMBT_LOGIC_QF_AUFBV = 0, /* default: all */
  BTORMBT_LOGIC_QF_BV,
  BTORMBT_LOGIC_QF_ABV,
  BTORMBT_LOGIC_QF_UFBV,
};

typedef enum BtorMBTLogic BtorMBTLogic;

/*------------------------------------------------------------------------*/

struct BtorMBTConfig
{
  uint32_t min;
  uint32_t max;
};

typedef struct BtorMBTConfig BtorMBTConfig;

struct BtorMBTNodeConfig
{
  uint32_t min; /* min number (without initial layer) */
  uint32_t max; /* max number (without initial layer) */
  struct
  {
    uint32_t min; /* min number of initial layer */
    uint32_t max; /* max number of initial layer */
  } init;
  struct
  {
    uint32_t min; /* min number in incremental step */
    uint32_t max; /* max number in incremental step */
  } inc;
};

typedef struct BtorMBTNodeConfig BtorMBTNodeConfig;

/*------------------------------------------------------------------------*/

struct BtorMBT
{
  BtorMemMgr *mm;

  Btor *btor;

  BtorMBTBtorOptPtrStack btor_opts; /* maintains all available boolector opts */

  double start_time;

  uint32_t seed;
  bool seeded;
  uint32_t rounds;
  uint32_t bugs;
  uint32_t forked;
  uint32_t ppid; /* parent pid */
  uint32_t verbosity;

  bool quiet;
  bool terminal;
  bool quit_after_first;
  bool ext;
  bool optfuzz;
  int32_t fshadow;
  int32_t flogic;
  bool is_flogic;
  char *out;
  bool create_funs;
  bool create_ufs;
  bool create_arrays;

  uint32_t max_rounds;

  BtorMBTConfig bw;
  BtorMBTConfig bw_index;
  BtorMBTConfig bw_muldiv;

  BtorMBTConfig sort_fun_arity;

  BtorMBTConfig inputs;
  BtorMBTNodeConfig vars;
  BtorMBTNodeConfig consts;
  BtorMBTNodeConfig arrays;

  /* add/release phase options */
  BtorMBTNodeConfig add_funs;
  BtorMBTNodeConfig add_uf;
  BtorMBTNodeConfig add_arrayops;
  BtorMBTNodeConfig add_bvops;
  BtorMBTNodeConfig add_inputs;
  BtorMBTNodeConfig ops;
  BtorMBTNodeConfig add_ops;
  BtorMBTNodeConfig release_ops;

  uint32_t max_ops_lower; /* lower bound for ops.max in current round
                             for determining round.max_ass */

  uint32_t min_asserts_lower; /* min number of assertions in a round
                                 for round.ops.max < max_ops_lower */
  uint32_t max_asserts_lower; /* max number of assertions in a round
                                 for round.ops.max < max_ops_lower */
  uint32_t min_asserts_upper; /* min number of assertions in a round
                                 for round.ops.max >= max_ops_lower */
  uint32_t max_asserts_upper; /* max number of assertions in a round
                                 for round.ops.max >= max_ops_lower */

  /* propability options */

  /* choose an existing bv sort over creating a new one */
  uint32_t p_sort_bv;
  /* choose an existing fun sort over creating a new one */
  uint32_t p_sort_fun;
  /* choose a unary fun sort */
  uint32_t p_sort_fun_unary;
  /* choose an assumption over an assertion in incremental mode */
  uint32_t p_assume;
  /* choose parameterized over non-parameterized expressions */
  uint32_t p_param_exp;
  /* choose parameterized over non-parameterized array expressions */
  uint32_t p_param_arr_exp;
  /* choose an apply on an existing over an apply on a new function */
  uint32_t p_apply_fun;
  /* choose an apply on an existing over an apply on a new UF */
  uint32_t p_apply_uf;
  /* choose read/write over eq/ne/cond */
  uint32_t p_rw;
  /* choose read over write */
  uint32_t p_read;
  /* choose cond over eq/ne */
  uint32_t p_cond;
  /* choose eq over ne */
  uint32_t p_eq;
  /* dump formula and exit */
  uint32_t p_dump;
  /* print the model after a sat call */
  uint32_t p_print_model;
  /* use btor over smt2 format when printing a model */
  uint32_t p_model_format;

  /* round counters */
  /* number of add ops wrt to number of release ops (initial layer) */
  uint32_t r_add_init;
  /* number of release ops wrt to number of add ops (initial layer) */
  uint32_t r_release_init;
  /* number of add ops wrt to number of release ops (after initial layer) */
  uint32_t r_add;
  /* number of release ops wrt to number of add ops (after initial layer) */
  uint32_t r_release;
  /* number of add ops wrt to number of release ops (reinit inc step) */
  uint32_t r_add_inc;
  /* number of release ops wrt to number of add ops (reinit inc step) */
  uint32_t r_release_inc;

  BtorMBTExpStack *assumptions;
  BtorMBTExpStack *bo, *bv, *arr, *fun, *uf;
  BtorMBTExpStack *parambo, *parambv, *paramarr, *paramfun;
  BoolectorSortStack *bv_sorts, *fun_sorts;

  struct
  {
    BtorMBTLogic logic;

    bool is_init;
    bool inc;
    bool mgen;
    bool dump;
    bool print_model;
    bool shadow;

    bool has_shadow;

    uint32_t ninc;
    uint32_t max_ninc;

    /* prob. distribution of variables, constants, arrays in current round */
    uint32_t p_var, p_const, p_array;
    /* prop. distrbution of add and release operations in current round */
    uint32_t p_add, p_release;
    /* prob. distribution of functions (without macros and array operations),
     * array operations, macros, inputs in current round */
    uint32_t p_bitvec_fun, p_bitvec_uf, p_array_op, p_bitvec_op, p_input;

    uint32_t ops;     /* number of operations in current round */
    uint32_t asserts; /* number of produced asserts in current round */
    uint32_t assumes; /* number of produced assumes in current round */

    uint32_t max_inputs; /* max number of inputs in current round */
    uint32_t max_ops;    /* max number of operations in current round */
    uint32_t max_ass;    /* max number of ass(erts|umes) in current round */

    uint32_t asserts_tot; /* total number of asserts in current round */
    uint32_t num_ite_fun;
    uint32_t num_eq_fun;

    BtorRNG rng;
  } round;
};

typedef void *(*BtorMBTState) (BtorMBT *);

static BtorMBT *
btormbt_new_btormbt (void)
{
  BtorOption opt;
  BtorMBT *mbt;
  BtorMemMgr *mm;
  Btor *tmpbtor;
  BtorMBTBtorOpt *btoropt;

  mm = btor_mem_mgr_new ();
  BTOR_CNEW (mm, mbt);
  mbt->mm = mm;

  BTOR_INIT_STACK (mm, mbt->btor_opts);

  /* retrieve all available boolector options */
  tmpbtor = boolector_new ();
  for (opt = boolector_first_opt (tmpbtor); opt < BTOR_OPT_NUM_OPTS;
       opt = boolector_next_opt (tmpbtor, opt))
  {
    BTOR_CNEW (mm, btoropt);
    btoropt->kind = opt;
    btoropt->name = btor_mem_strdup (mm, boolector_get_opt_lng (tmpbtor, opt));
    btoropt->shrt = btor_mem_strdup (mm, boolector_get_opt_shrt (tmpbtor, opt));
    btoropt->val  = boolector_get_opt (tmpbtor, opt);
    btoropt->min  = boolector_get_opt_min (tmpbtor, opt);
    btoropt->max  = boolector_get_opt_max (tmpbtor, opt);
    btoropt->dflt = boolector_get_opt_dflt (tmpbtor, opt);
    btoropt->desc = boolector_get_opt_desc (tmpbtor, opt);
    /* disabling incremental not supported */
    if (opt == BTOR_OPT_INCREMENTAL) btoropt->min = btoropt->max;
    /* check if opt is an engine opt */
    if (strchr (btoropt->name, ':'))
    {
      btoropt->is_engine_opt = true;
      if (strstr (btoropt->name, "fun:"))
        btoropt->engine = BTOR_ENGINE_FUN;
      else if (strstr (btoropt->name, "aigprop:"))
        btoropt->engine = BTOR_ENGINE_AIGPROP;
      else if (strstr (btoropt->name, "prop:"))
        btoropt->engine = BTOR_ENGINE_PROP;
      else if (strstr (btoropt->name, "quant:"))
        btoropt->engine = BTOR_ENGINE_QUANT;
      else
      {
        assert (strstr (btoropt->name, "sls:"));
        btoropt->engine = BTOR_ENGINE_SLS;
      }
    }
    /* check if opt was set (forced) via the command line */
    btoropt->forced_by_cl = false;
    BTOR_PUSH_STACK (mbt->btor_opts, btoropt);
  }
  boolector_delete (tmpbtor);

  mbt->optfuzz               = true;
  mbt->max_rounds            = UINT32_MAX;
  mbt->seed                  = -1;
  mbt->seeded                = false;
  mbt->terminal              = isatty (1) == 1;
  mbt->ext                   = false;
  mbt->create_funs           = true;
  mbt->create_ufs            = true;
  mbt->create_arrays         = true;
  mbt->bw.min                = MIN_BITWIDTH;
  mbt->bw.max                = MAX_BITWIDTH;
  mbt->bw_index.min          = MIN_INDEXWIDTH;
  mbt->bw_index.max          = MAX_INDEXWIDTH;
  mbt->bw_muldiv.min         = MIN_MULDIVWIDTH;
  mbt->bw_muldiv.max         = MAX_MULDIVWIDTH;
  mbt->sort_fun_arity.min    = MIN_SORT_FUN_ARITY;
  mbt->sort_fun_arity.max    = MAX_SORT_FUN_ARITY;
  mbt->inputs.min            = MIN_NLITS;
  mbt->inputs.max            = MAX_NLITS;
  mbt->vars.init.min         = MIN_NVARS_INIT;
  mbt->vars.init.max         = MAX_NVARS_INIT;
  mbt->vars.min              = MIN_NVARS;
  mbt->vars.max              = MAX_NVARS;
  mbt->vars.inc.min          = MIN_NVARS_INC;
  mbt->vars.inc.max          = MAX_NVARS_INC;
  mbt->consts.init.min       = MIN_NCONSTS_INIT;
  mbt->consts.init.max       = MAX_NCONSTS_INIT;
  mbt->consts.min            = MIN_NCONSTS;
  mbt->consts.max            = MAX_NCONSTS;
  mbt->consts.inc.min        = MIN_NCONSTS_INC;
  mbt->consts.inc.max        = MAX_NCONSTS_INC;
  mbt->arrays.init.min       = MIN_NARRS_INIT;
  mbt->arrays.init.max       = MAX_NARRS_INIT;
  mbt->arrays.min            = MIN_NARRS;
  mbt->arrays.max            = MAX_NARRS;
  mbt->arrays.inc.min        = MIN_NARRS_INC;
  mbt->arrays.inc.max        = MAX_NARRS_INC;
  mbt->add_funs.init.min     = MIN_NADDOPFUNS_INIT;
  mbt->add_funs.init.max     = MAX_NADDOPFUNS_INIT;
  mbt->add_funs.min          = MIN_NADDOPFUNS;
  mbt->add_funs.max          = MAX_NADDOPFUNS;
  mbt->add_funs.inc.min      = MIN_NADDOPFUNS_INC;
  mbt->add_funs.inc.max      = MAX_NADDOPFUNS_INC;
  mbt->add_uf.init.min       = MIN_NADDOPUF_INIT;
  mbt->add_uf.init.max       = MAX_NADDOPUF_INIT;
  mbt->add_uf.min            = MIN_NADDOPUF;
  mbt->add_uf.max            = MAX_NADDOPUF;
  mbt->add_uf.inc.min        = MIN_NADDOPUF_INC;
  mbt->add_uf.inc.max        = MAX_NADDOPUF_INC;
  mbt->add_arrayops.init.min = MIN_NADDOPAFUNS_INIT;
  mbt->add_arrayops.init.max = MAX_NADDOPAFUNS_INIT;
  mbt->add_arrayops.min      = MIN_NADDOPAFUNS;
  mbt->add_arrayops.max      = MAX_NADDOPAFUNS;
  mbt->add_arrayops.inc.min  = MIN_NADDOPAFUNS_INC;
  mbt->add_arrayops.inc.max  = MAX_NADDOPAFUNS_INC;
  mbt->add_bvops.init.min    = MIN_NADDOPBFUNS_INIT;
  mbt->add_bvops.init.max    = MAX_NADDOPBFUNS_INIT;
  mbt->add_bvops.min         = MIN_NADDOPBFUNS;
  mbt->add_bvops.max         = MAX_NADDOPBFUNS;
  mbt->add_bvops.inc.min     = MIN_NADDOPBFUNS_INC;
  mbt->add_bvops.inc.max     = MAX_NADDOPBFUNS_INC;
  mbt->add_inputs.init.min   = MIN_NADDOPLITS_INIT;
  mbt->add_inputs.init.max   = MAX_NADDOPLITS_INIT;
  mbt->add_inputs.min        = MIN_NADDOPLITS;
  mbt->add_inputs.max        = MAX_NADDOPLITS;
  mbt->add_inputs.inc.min    = MIN_NADDOPLITS_INC;
  mbt->add_inputs.inc.max    = MAX_NADDOPLITS_INC;
  mbt->ops.init.min          = MIN_NOPS_INIT;
  mbt->ops.init.max          = MAX_NOPS_INIT;
  mbt->ops.min               = MIN_NOPS;
  mbt->ops.max               = MAX_NOPS;
  mbt->ops.inc.min           = MIN_NOPS_INC;
  mbt->ops.inc.max           = MAX_NOPS_INC;
  mbt->add_ops.init.min      = MIN_NADDOPS_INIT;
  mbt->add_ops.init.max      = MAX_NADDOPS_INIT;
  mbt->add_ops.min           = MIN_NADDOPS;
  mbt->add_ops.max           = MAX_NADDOPS;
  mbt->add_ops.inc.min       = MIN_NADDOPS_INC;
  mbt->add_ops.inc.max       = MAX_NADDOPS_INC;
  mbt->release_ops.init.min  = MIN_NRELOPS_INIT;
  mbt->release_ops.init.max  = MAX_NRELOPS_INIT;
  mbt->release_ops.min       = MIN_NRELOPS;
  mbt->release_ops.max       = MAX_NRELOPS;
  mbt->release_ops.inc.min   = MIN_NRELOPS_INC;
  mbt->release_ops.inc.max   = MAX_NRELOPS_INC;
  mbt->min_asserts_lower     = MIN_NASSERTS_LOWER;
  mbt->max_asserts_lower     = MAX_NASSERTS_LOWER;
  mbt->min_asserts_upper     = MIN_NASSERTS_UPPER;
  mbt->max_asserts_upper     = MAX_NASSERTS_UPPER;
  mbt->p_sort_bv             = P_SORT_BV;
  mbt->p_sort_fun            = P_SORT_BV;
  mbt->p_assume              = P_ASSUME;
  mbt->p_param_exp           = P_PARAM_EXP;
  mbt->p_param_arr_exp       = P_PARAM_ARR_EXP;
  mbt->p_apply_fun           = P_APPLY_FUN;
  mbt->p_apply_uf            = P_APPLY_UF;
  mbt->p_rw                  = P_RW;
  mbt->p_read                = P_READ;
  mbt->p_cond                = P_COND;
  mbt->p_eq                  = P_EQ;
  mbt->p_dump                = P_DUMP;
  mbt->p_print_model         = P_PRINT_MODEL;
  mbt->p_model_format        = P_MODEL_FORMAT;
  return mbt;
}

static void
btormbt_delete_btormbt (BtorMBT *mbt)
{
  assert (mbt);

  BtorMemMgr *mm;
  BtorMBTBtorOpt *opt;

  mm = mbt->mm;
  while (!BTOR_EMPTY_STACK (mbt->btor_opts))
  {
    opt = BTOR_POP_STACK (mbt->btor_opts);
    btor_mem_freestr (mbt->mm, opt->name);
    if (opt->shrt) btor_mem_freestr (mbt->mm, opt->shrt);
    BTOR_DELETE (mm, opt);
  }
  BTOR_RELEASE_STACK (mbt->btor_opts);
  BTOR_DELETE (mm, mbt);
  btor_mem_mgr_delete (mm);
}

static void
btormbt_release_node (BtorMBT *mbt, BoolectorNode *node)
{
  assert (node);
  boolector_release (mbt->btor, node);
}

static bool
btormbt_is_parameterized (BtorMBT *mbt, BoolectorNode *node)
{
  assert (node);
  (void) mbt;
  // TODO (ma): workaround need API for querying parameterized flag
  return btor_node_real_addr (((BtorNode *) node))->parameterized == 1;
}

static BtorMBTExp *
btormbt_push_node (BtorMBT *mbt, BoolectorNode *node)
{
  assert (node);

  bool is_parameterized;
  BtorMBTExpStack *stack;

  is_parameterized = btormbt_is_parameterized (mbt, node);
  if (boolector_is_array (mbt->btor, node))
    stack = is_parameterized ? mbt->paramarr : mbt->arr;
  else if (boolector_is_uf (mbt->btor, node))
    stack = mbt->uf;
  else if (boolector_is_fun (mbt->btor, node))
    stack = is_parameterized ? mbt->paramfun : mbt->fun;
  else if (boolector_get_width (mbt->btor, node) == 1)
    stack = is_parameterized ? mbt->parambo : mbt->bo;
  else
    stack = is_parameterized ? mbt->parambv : mbt->bv;

  btormbt_push_exp_stack (mbt->mm, stack, node);
  return BTOR_TOP_STACK (stack->exps);
}

static BtorMBTExpStack *
btormbt_copy_exp_stack (BtorMBT *mbt, BtorMBTExpStack *expstack)
{
  uint32_t i;
  BtorMBTExpStack *res;
  BtorMBTExp *e;

  res = btormbt_new_exp_stack (mbt->mm);
  for (i = 0; i < BTOR_COUNT_STACK (expstack->exps); i++)
  {
    e = BTOR_PEEK_STACK (expstack->exps, i);
    btormbt_push_exp_stack (mbt->mm, res, boolector_copy (mbt->btor, e->exp));
  }
  res->init_layer_size  = expstack->init_layer_size;
  res->last_pos_parents = expstack->last_pos_parents;
  return res;
}

static void
btormbt_reset_assumptions (BtorMBT *mbt)
{
  BoolectorNode *ass;

  while (!BTOR_EMPTY_STACK (mbt->assumptions->exps))
  {
    ass = btormbt_pop_exp_stack (mbt->mm, mbt->assumptions);
    assert (ass);
    btormbt_release_node (mbt, ass);
  }
  btormbt_reset_exp_stack (mbt->mm, mbt->assumptions);
}

/*------------------------------------------------------------------------*/

static BtorMBT *g_btormbt;
static BtorMBTStatistics *g_btormbtstats = 0;
static char g_shmfilename[128];

#ifdef BTOR_HAVE_SIGNALS
static int32_t g_caught_sig;
static void (*sig_int_handler) (int32_t);
static void (*sig_segv_handler) (int32_t);
static void (*sig_abrt_handler) (int32_t);
static void (*sig_term_handler) (int32_t);
static void (*sig_bus_handler) (int32_t);

static int32_t g_set_alarm;
static void (*sig_alrm_handler) (int32_t);
#endif

void boolector_chkclone (Btor *);

/*------------------------------------------------------------------------*/

static void
erase (void)
{
  int32_t i;
  fputc ('\r', stdout);
  for (i = 0; i < 80; i++) fputc (' ', stdout);
  fputc ('\r', stdout);
}

static bool
is_num_str (const char *str)
{
  const char *p;
  for (p = str; *p; p++)
    if (!isdigit ((int32_t) *p)) return false;
  return true;
}

static int32_t
hash_mac (void)
{
  FILE *file = fopen ("/sys/class/net/eth0/address", "r");
  int32_t mac[6], res = 0;
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
  return current_time () - g_btormbt->start_time;
}

static double
average (double a, double b)
{
  return b ? a / b : 0;
}

/* returns power of 2 val nearest to i and its log2, minimum of is 2 */
/* used for log2 operators */
static void
next_pow_of_2 (uint32_t val, uint32_t *pow2, uint32_t *log2)
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

/*------------------------------------------------------------------------*/

static void
btormbt_msg (char *msg, ...)
{
  assert (msg);
  va_list list;
  va_start (list, msg);
  fprintf (stdout, "[btormbt] ");
  vfprintf (stdout, msg, list);
  fprintf (stdout, "\n");
  va_end (list);
  fflush (stdout);
}

static void
btormbt_error (char *msg, ...)
{
  assert (msg);

  va_list list;
  va_start (list, msg);
  fputs ("btormbt: ", stderr);
  vfprintf (stderr, msg, list);
  fprintf (stderr, "\n");
  va_end (list);
  fflush (stderr);
  btormbt_delete_btormbt (g_btormbt);
  exit (EXIT_ERROR);
}

static void
btormbt_print_stats (BtorMBT *mbt)
{
  int32_t i;
  double t = get_time ();
  btormbt_msg ("runtime %0.2f seconds", t);
  btormbt_msg ("%d rounds = %0.2f rounds per second",
               mbt->rounds,
               average (mbt->rounds, t));
  btormbt_msg (
      "%d bugs = %0.2f bugs per second", mbt->bugs, average (mbt->bugs, t));
  btormbt_msg ("%u sat calls", g_btormbtstats->num_sat);
  btormbt_msg ("%u unsat calls", g_btormbtstats->num_unsat);
  btormbt_msg ("%u incremental calls", g_btormbtstats->num_inc);
  btormbt_msg ("%u shadow clone calls", g_btormbtstats->num_shadow_clone);
  btormbt_msg ("%u clone calls", g_btormbtstats->num_clone);
  btormbt_msg ("%u simplify calls", g_btormbtstats->num_simp);

  /* print total number of created ops */
  if (mbt->verbosity > 1)
    for (i = 0; i < BTORMBT_NUM_OPS; i++)
      btormbt_msg ("  %u %s", g_btormbtstats->num_ops[i], g_op2str[i]);
}

/*------------------------------------------------------------------------*/

#ifdef BTOR_HAVE_SIGNALS
static void
reset_sig_handlers (void)
{
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
  (void) signal (SIGBUS, sig_bus_handler);
}

static void
catch_sig (int32_t sig)
{
  if (!g_caught_sig)
  {
    g_caught_sig = sig;
    printf ("\n");
    if (!g_btormbt->seeded) btormbt_print_stats (g_btormbt);
    btormbt_msg ("CAUGHT SIGNAL %d", sig);
  }
  reset_sig_handlers ();
  raise (sig);
  _exit (EXIT_ERROR);
}

static void
set_sig_handlers (void)
{
  sig_int_handler  = signal (SIGINT, catch_sig);
  sig_segv_handler = signal (SIGSEGV, catch_sig);
  sig_abrt_handler = signal (SIGABRT, catch_sig);
  sig_term_handler = signal (SIGTERM, catch_sig);
  sig_bus_handler  = signal (SIGBUS, catch_sig);
}

static void
reset_alarm (void)
{
  alarm (0);
  (void) signal (SIGALRM, sig_alrm_handler);
}

static void
catch_alarm (int32_t sig)
{
  (void) sig;
  assert (sig == SIGALRM);

  if (g_btormbt->seeded && g_set_alarm > 0)
  {
    btormbt_msg ("ALARM TRIGGERED: time limit %d seconds reached", g_set_alarm);
    btormbt_print_stats (g_btormbt);
  }
  reset_alarm ();
  _exit (EXIT_TIMEOUT);
}

static void
set_alarm (void)
{
  sig_alrm_handler = signal (SIGALRM, catch_alarm);
  assert (g_set_alarm > 0);
  alarm (g_set_alarm);
}
#endif

/*------------------------------------------------------------------------*/

/**
 * initialize probability distribution of inputs
 * parameter: ratio var:const:arr (e.g. 3:1:1)
 * normalized to BTOR_PROB_MAX
 */
static void
init_pd_inputs (BtorMBT *mbt,
                uint32_t ratio_var,
                uint32_t ratio_const,
                uint32_t ratio_arr)
{
  uint32_t sum;

  sum = ratio_var + ratio_const + ratio_arr;

  assert (sum > 0);

  mbt->round.p_var   = ((double) ratio_var / sum) * BTOR_PROB_MAX;
  mbt->round.p_const = ((double) ratio_const / sum) * BTOR_PROB_MAX;
  mbt->round.p_array = ((double) ratio_arr / sum) * BTOR_PROB_MAX;
  // TODO (ma): uf
}

/**
 * initialize probability distribution of add operation
 * parameter: ratio fun:uf:array:bv:input (e.g. 1:1:1:1:2)
 * normalized to BTOR_PROB_MAX
 */
static void
init_pd_add (BtorMBT *mbt,
             uint32_t ratio_fun,
             uint32_t ratio_uf,
             uint32_t ratio_arr_op,
             uint32_t ratio_bv_op,
             uint32_t ratio_input)
{
  uint32_t sum;

  sum = ratio_fun + ratio_uf + ratio_arr_op + ratio_bv_op + ratio_input;

  assert (sum > 0);

  mbt->round.p_bitvec_fun = ((double) ratio_fun / sum) * BTOR_PROB_MAX;
  mbt->round.p_bitvec_uf  = ((double) ratio_uf / sum)
                           * BTOR_PROB_MAX;  // TODO (ma): UF should be input
  mbt->round.p_array_op  = ((double) ratio_arr_op / sum) * BTOR_PROB_MAX;
  mbt->round.p_bitvec_op = ((double) ratio_bv_op / sum) * BTOR_PROB_MAX;
  mbt->round.p_input     = ((double) ratio_input / sum) * BTOR_PROB_MAX;
}

/**
 * initialize probability distribution of add/release op
 * parameter: ratio addop:relop (e.g. 1:0)
 * normalized to BTOR_PROB_MAX
 */
static void
init_pd_ops (BtorMBT *mbt, uint32_t ratio_add, uint32_t ratio_release)
{
  uint32_t sum;

  sum = ratio_add + ratio_release;

  assert (sum > 0);

  mbt->round.p_add     = ((double) ratio_add / sum) * BTOR_PROB_MAX;
  mbt->round.p_release = ((double) ratio_release / sum) * BTOR_PROB_MAX;
}

/*------------------------------------------------------------------------*/

/* Modify bit width of node e of width ew to be of width tow.
 * Note: param ew prevents too many boolector_get_width calls. */
static BoolectorNode *
modify_bv (BtorMBT *mbt, BoolectorNode *e, uint32_t new_width)
{
  assert (new_width > 0);

  uint32_t tmp, old_width;
  BoolectorNode *node;
  BtorMBTExp *exp;

  old_width = boolector_get_width (mbt->btor, e);
  node      = 0;
  if (new_width < old_width)
  {
    tmp  = btor_rng_pick_rand (&mbt->round.rng, 0, old_width - new_width);
    node = boolector_slice (mbt->btor, e, tmp + new_width - 1, tmp);
    g_btormbtstats->num_ops[SLICE]++;
  }
  else if (new_width > old_width)
  {
    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
    {
      node = boolector_uext (mbt->btor, e, new_width - old_width);
      g_btormbtstats->num_ops[UEXT]++;
    }
    else
    {
      node = boolector_sext (mbt->btor, e, new_width - old_width);
      g_btormbtstats->num_ops[SEXT]++;
    }
  }

  if (node)
  {
    exp = btormbt_push_node (mbt, node);
    exp->parents++;
    e = node;
  }
  assert (new_width == boolector_get_width (mbt->btor, e));
  return e;
}

/*------------------------------------------------------------------------*/

static void
btormbt_var (BtorMBT *mbt, BtorMBTExpType type)
{
  int32_t id;
  uint32_t width;
  BoolectorSort s;
  BoolectorNode *var;
  char *symbol;

  if (type == BTORMBT_BO_T)
    width = 1;
  else if (type == BTORMBT_BV_T)
    width = btor_rng_pick_rand (&mbt->round.rng, mbt->bw.min, mbt->bw.max);
  else
  {
    assert (type == BTORMBT_BB_T);
    width = btor_rng_pick_rand (&mbt->round.rng, 1, mbt->bw.max);
  }
  s   = boolector_bitvec_sort (mbt->btor, width);
  var = boolector_var (mbt->btor, s, 0);
  assert (boolector_is_var (mbt->btor, var));
  id = boolector_get_node_id (mbt->btor, var);
  BTOR_NEWN (mbt->mm, symbol, 20);
  sprintf (symbol, "mbtvar%u", id);
  boolector_set_symbol (mbt->btor, var, symbol);
  BTOR_DELETEN (mbt->mm, symbol, 20);
  btormbt_push_node (mbt, var);
  boolector_release_sort (mbt->btor, s);
  g_btormbtstats->num_ops[VAR]++;
}

static void
btormbt_const (BtorMBT *mbt)
{
  char *bits;
  const char *sbits;
  uint32_t i, width, val;
  BoolectorNode *node;
  //  BtorMBTNodeAttr attr;
  BtorMBTOperator op;
  BoolectorSort s;

  op    = btor_rng_pick_rand (&mbt->round.rng, CONST, INT);
  width = 0;
  val   = 0;

  if (op != TRUE && op != FALSE)
    width = btor_rng_pick_rand (&mbt->round.rng, 1, mbt->bw.max);

  if (op == UINT || op == INT)
  {
    if (width < 32)
      val = (1 << width) - 1;
    else
      val = UINT32_MAX - 1; /* UINT32_MAX leads to divison by 0 in pick */
    val = btor_rng_pick_rand (&mbt->round.rng, 0, val);
  }

#if 0
  bits = 0;
  if (op == CONST)
    {
      /* generate random binary string */
      BTOR_NEWN (mbt->mm, bits, width + 1);
      for (i = 0; i < width; i++)
	bits[i] = btor_rng_pick_with_prob (&mbt->round.rng, 500) ? '1' : '0';
      bits[width] = '\0';
    }
#endif

#if 1
  node = 0;
  s    = 0;
  if (op != TRUE && op != FALSE && op != CONST)
    s = boolector_bitvec_sort (mbt->btor, width);
  switch (op)
  {
    case CONST:
      /* generate random binary string */
      BTOR_NEWN (mbt->mm, bits, width + 1);
      for (i = 0; i < width; i++)
        bits[i] = btor_rng_pick_with_prob (&mbt->round.rng, 500) ? '1' : '0';
      bits[width] = '\0';
      node        = boolector_const (mbt->btor, bits);
      assert (boolector_is_const (mbt->btor, node));
      if (btor_rng_pick_with_prob (&mbt->round.rng, 100))
      {
        sbits = boolector_get_bits (mbt->btor, node);
        assert (!strcmp (bits, sbits));
        boolector_free_bits (mbt->btor, sbits);
      }
      BTOR_DELETEN (mbt->mm, bits, width + 1);
      break;
    case ZERO: node = boolector_zero (mbt->btor, s); break;
    case FALSE: node = boolector_false (mbt->btor); break;
    case ONES: node = boolector_ones (mbt->btor, s); break;
    case MIN_SIGNED: node = boolector_min_signed (mbt->btor, s); break;
    case MAX_SIGNED: node = boolector_max_signed (mbt->btor, s); break;
    case TRUE: node = boolector_true (mbt->btor); break;
    case ONE: node = boolector_one (mbt->btor, s); break;
    case UINT: node = boolector_unsigned_int (mbt->btor, val, s); break;
    default: assert (op == INT); node = boolector_int (mbt->btor, val, s);
  }
  if (op != TRUE && op != FALSE && op != CONST)
    boolector_release_sort (mbt->btor, s);
#endif
  assert (node);
  btormbt_push_node (mbt, node);
  g_btormbtstats->num_ops[op]++;
  //  attr.bv.val = val;
  //  attr.bv.width = width;
  //  attr.bv.bits = bits;
  //  (void) mk_node (mbt, op,
  //		  (BtorMBTNodeAttr) { .bv.val = val,
  //				      .bv.width = width,
  //				      .bv.bits = bits});
  //  if (bits)
  //    {
  //      assert (op == CONST);
  //      BTOR_DELETEN (mbt->mm, bits, attr.bv.width + 1);
  //    }
}

static void
btormbt_array (BtorMBT *mbt)
{
  int32_t id;
  uint32_t ew, iw;
  BoolectorNode *array;
  BoolectorSort es, is, as;
  char *symbol;

  // TODO (ma): remove ite here and use bw.min
  ew = btor_rng_pick_rand (
      &mbt->round.rng, mbt->bw.min > 2 ? mbt->bw.min : 1, mbt->bw.max);
  iw = btor_rng_pick_rand (
      &mbt->round.rng, mbt->bw_index.min, mbt->bw_index.max);
  es    = boolector_bitvec_sort (mbt->btor, ew);
  is    = boolector_bitvec_sort (mbt->btor, iw);
  as    = boolector_array_sort (mbt->btor, is, es);
  array = boolector_array (mbt->btor, as, 0);
  assert (boolector_is_array (mbt->btor, array));
  assert (boolector_is_array_var (mbt->btor, array));
  id = boolector_get_node_id (mbt->btor, array);
  BTOR_NEWN (mbt->mm, symbol, 20);
  sprintf (symbol, "mbtarr%u", id);
  boolector_set_symbol (mbt->btor, array, symbol);
  BTOR_DELETEN (mbt->mm, symbol, 20);
  btormbt_push_node (mbt, array);
  boolector_release_sort (mbt->btor, es);
  boolector_release_sort (mbt->btor, is);
  boolector_release_sort (mbt->btor, as);
  g_btormbtstats->num_ops[ARRAY]++;
}

static BoolectorNode *
btormbt_constraint (BtorMBT *mbt)
{
  uint32_t i, pos, num_nodes, start, end;
  BoolectorNode *res, *tmp, *node;

  /* select from init layer with lower probability */
  if (mbt->bo->init_layer_size
      && BTOR_COUNT_STACK (mbt->bo->exps) > mbt->bo->init_layer_size
      && btor_rng_pick_with_prob (&mbt->round.rng, 800))
    start = mbt->bo->init_layer_size - 1;
  else
    start = 0;

  end = BTOR_COUNT_STACK (mbt->bo->exps) - 1;
  num_nodes =
      btor_rng_pick_rand (&mbt->round.rng, 1, BTOR_MAX_UTIL (1, end - start));
  /* randomly choose 'num_nodes' nodes for the constraint */
  res = tmp = 0;
  for (i = 0; i < num_nodes; i++)
  {
    pos = btor_rng_pick_rand (&mbt->round.rng, start, end);
    node =
        boolector_copy (mbt->btor, BTOR_PEEK_STACK (mbt->bo->exps, pos)->exp);

    /* negate 'node' with probability 0.5 */
    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
    {
      tmp = boolector_not (mbt->btor, node);
      btormbt_release_node (mbt, node);
      node = tmp;
    }

    if (res)
    {
      tmp = boolector_or (mbt->btor, res, node);
      btormbt_release_node (mbt, res);
      btormbt_release_node (mbt, node);
      res = tmp;
    }
    else
      res = node;
  }
  assert (res);
  return res;
}

static void
btormbt_unary_op (BtorMBT *mbt, BtorMBTOperator op, BoolectorNode *e)
{
  assert (is_unary_op (op));

  uint32_t upper, lower, repeat, width;
  BoolectorNode *node;

  upper = lower = repeat = 0;
  width                  = boolector_get_width (mbt->btor, e);
  assert (width <= mbt->bw.max);

  if (op == SLICE)
  {
    upper = btor_rng_pick_rand (&mbt->round.rng, 0, width - 1);
    lower = btor_rng_pick_rand (&mbt->round.rng, 0, upper);
  }
  else if (op == UEXT || op == SEXT)
  {
    upper = btor_rng_pick_rand (&mbt->round.rng, 0, mbt->bw.max - width);
  }
  else if (op == REPEAT)
  {
    repeat = btor_rng_pick_rand (
        &mbt->round.rng, 1, ((uint32_t) MAX_BITWIDTH / width));
  }

  node = 0;
  switch (op)
  {
    case NOT: node = boolector_not (mbt->btor, e); break;
    case NEG: node = boolector_neg (mbt->btor, e); break;
    case REPEAT: node = boolector_repeat (mbt->btor, e, repeat); break;
    case SLICE: node = boolector_slice (mbt->btor, e, upper, lower); break;
    case INC: node = boolector_inc (mbt->btor, e); break;
    case DEC: node = boolector_dec (mbt->btor, e); break;
    case UEXT: node = boolector_uext (mbt->btor, e, upper); break;
    case SEXT: node = boolector_sext (mbt->btor, e, upper); break;
    case REDOR: node = boolector_redor (mbt->btor, e); break;
    case REDXOR: node = boolector_redxor (mbt->btor, e); break;
    default: assert (op == REDAND); node = boolector_redand (mbt->btor, e);
  }
  assert (node);
  btormbt_push_node (mbt, node);
  g_btormbtstats->num_ops[op]++;
}

static void
btormbt_binary_op (BtorMBT *mbt,
                   BtorMBTOperator op,
                   BoolectorNode *e0,
                   BoolectorNode *e1)
{
  assert (is_binary_op (op));

  uint32_t e0_width, e1_width, tmp0, tmp1;
  BoolectorNode *node;

  e0_width = boolector_get_width (mbt->btor, e0);
  assert (e0_width <= mbt->bw.max);
  e1_width = boolector_get_width (mbt->btor, e1);
  assert (e1_width <= mbt->bw.max);

  if ((op >= XOR && op <= SMOD) || (op >= EQ && op <= SGTE))
  {
    /* modify e1_width equal to e0_width, guarded mul and div */
    if ((op >= UMULO && op <= SDIVO) || (op >= MUL && op <= SMOD))
    {
      if (e0_width > mbt->bw_muldiv.max)
      {
        e0       = modify_bv (mbt, e0, mbt->bw_muldiv.max);
        e0_width = mbt->bw_muldiv.max;
      }
      else if (e0_width < mbt->bw_muldiv.min)
      {
        e0       = modify_bv (mbt, e0, mbt->bw_muldiv.max);
        e0_width = mbt->bw_muldiv.max;
      }
    }
    e1 = modify_bv (mbt, e1, e0_width);
  }
  else if (op >= SLL && op <= ROR)
  {
    /* modify width of e0 power of 2 and e1 log2(e0) */
    next_pow_of_2 (e0_width, &tmp0, &tmp1);
    e0       = modify_bv (mbt, e0, tmp0);
    e1       = modify_bv (mbt, e1, tmp1);
    e0_width = tmp0;
  }
  else if (op == CONCAT)
  {
    if (e0_width + e1_width > mbt->bw.max)
    {
      if (e0_width > 1)
      {
        e0       = modify_bv (mbt, e0, e0_width / 2);
        e0_width = e0_width / 2;
      }
      if (e1_width > 1)
      {
        e1       = modify_bv (mbt, e1, e1_width / 2);
        e1_width = e1_width / 2;
      }
    }
  }

  node = 0;
  switch (op)
  {
    case XOR: node = boolector_xor (mbt->btor, e0, e1); break;
    case XNOR: node = boolector_xnor (mbt->btor, e0, e1); break;
    case AND: node = boolector_and (mbt->btor, e0, e1); break;
    case NAND: node = boolector_nand (mbt->btor, e0, e1); break;
    case OR: node = boolector_or (mbt->btor, e0, e1); break;
    case NOR: node = boolector_nor (mbt->btor, e0, e1); break;
    case ADD: node = boolector_add (mbt->btor, e0, e1); break;
    case SUB: node = boolector_sub (mbt->btor, e0, e1); break;
    case MUL: node = boolector_mul (mbt->btor, e0, e1); break;
    case UDIV: node = boolector_udiv (mbt->btor, e0, e1); break;
    case SDIV: node = boolector_sdiv (mbt->btor, e0, e1); break;
    case UREM: node = boolector_urem (mbt->btor, e0, e1); break;
    case SREM: node = boolector_srem (mbt->btor, e0, e1); break;
    case SMOD: node = boolector_smod (mbt->btor, e0, e1); break;
    case SLL: node = boolector_sll (mbt->btor, e0, e1); break;
    case SRL: node = boolector_srl (mbt->btor, e0, e1); break;
    case SRA: node = boolector_sra (mbt->btor, e0, e1); break;
    case ROL: node = boolector_rol (mbt->btor, e0, e1); break;
    case ROR: node = boolector_ror (mbt->btor, e0, e1); break;
    case CONCAT: node = boolector_concat (mbt->btor, e0, e1); break;
    case EQ: node = boolector_eq (mbt->btor, e0, e1); break;
    case NE: node = boolector_ne (mbt->btor, e0, e1); break;
    case UADDO: node = boolector_uaddo (mbt->btor, e0, e1); break;
    case SADDO: node = boolector_saddo (mbt->btor, e0, e1); break;
    case USUBO: node = boolector_usubo (mbt->btor, e0, e1); break;
    case SSUBO: node = boolector_ssubo (mbt->btor, e0, e1); break;
    case UMULO: node = boolector_umulo (mbt->btor, e0, e1); break;
    case SMULO: node = boolector_smulo (mbt->btor, e0, e1); break;
    case SDIVO: node = boolector_sdivo (mbt->btor, e0, e1); break;
    case ULT: node = boolector_ult (mbt->btor, e0, e1); break;
    case SLT: node = boolector_slt (mbt->btor, e0, e1); break;
    case ULTE: node = boolector_ulte (mbt->btor, e0, e1); break;
    case SLTE: node = boolector_slte (mbt->btor, e0, e1); break;
    case UGT: node = boolector_ugt (mbt->btor, e0, e1); break;
    case SGT: node = boolector_sgt (mbt->btor, e0, e1); break;
    case UGTE: node = boolector_ugte (mbt->btor, e0, e1); break;
    case SGTE: node = boolector_sgte (mbt->btor, e0, e1); break;
    case IMPLIES: node = boolector_implies (mbt->btor, e0, e1); break;
    default: assert (op == IFF); node = boolector_iff (mbt->btor, e0, e1);
  }
  assert (node);
  btormbt_push_node (mbt, node);
  g_btormbtstats->num_ops[op]++;
}

static void
btormbt_ternary_op (BtorMBT *mbt,
                    BtorMBTOperator op,
                    BoolectorNode *e0,
                    BoolectorNode *e1,
                    BoolectorNode *e2)
{
  assert (is_ternary_op (op));
  assert (op == COND);
  assert (boolector_get_width (mbt->btor, e0) == 1);

  uint32_t e1w;

  e1w = boolector_get_width (mbt->btor, e1);
  assert (e1w <= mbt->bw.max);
  assert (boolector_get_width (mbt->btor, e2) <= mbt->bw.max);

  /* bitvectors must have same bit width */
  e2 = modify_bv (mbt, e2, e1w);
  btormbt_push_node (mbt, boolector_cond (mbt->btor, e0, e1, e2));
  g_btormbtstats->num_ops[op]++;
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
static BtorMBTExp *
btormbt_array_op (BtorMBT *mbt,
                  BtorMBTOperator op,
                  BoolectorNode *e0,
                  BoolectorNode *e1,
                  BoolectorNode *e2)
{
  assert (e0);
  assert (e1);
  assert (boolector_is_array (mbt->btor, e0));
  assert (is_array_op (op));

  BoolectorNode *node;

  node = 0;
  if (op == READ || op == WRITE)
  {
    e1 = modify_bv (mbt, e1, boolector_get_index_width (mbt->btor, e0));
    if (op == WRITE)
    {
      e2   = modify_bv (mbt, e2, boolector_get_width (mbt->btor, e0));
      node = boolector_write (mbt->btor, e0, e1, e2);
    }
    else
      node = boolector_read (mbt->btor, e0, e1);
  }
  else
  {
    assert (boolector_is_array (mbt->btor, e0));
    assert (boolector_is_array (mbt->btor, e1));
    assert (boolector_is_equal_sort (mbt->btor, e0, e1));

    if (op == EQ)
    {
      node = boolector_eq (mbt->btor, e0, e1);
      mbt->round.num_eq_fun++;
    }
    else if (op == NE)
    {
      node = boolector_ne (mbt->btor, e0, e1);
      mbt->round.num_eq_fun++;
    }
    else
    {
      assert (op == COND);
      node = boolector_cond (mbt->btor, e2, e0, e1);
      mbt->round.num_ite_fun++;
    }
  }
  assert (node);
  g_btormbtstats->num_ops[op]++;
  return btormbt_push_node (mbt, node);
}

/*------------------------------------------------------------------------*/

/* Randomly select expression by given type. Nodes with no parents
 * (yet unused) are preferred.
 *
 * force_param values:
 *   -1 ... do not select parameterized expression
 *    0 ... select parameterized expression with probability p_param_exp
 *    1 ... select parameterized expression
 */
static BoolectorNode *
select_exp (BtorMBT *mbt, BtorMBTExpType type, int32_t force_param)
{
  assert (force_param >= -1);
  assert (force_param <= 1);
  assert (force_param != 1
          || (mbt->parambo && !BTOR_EMPTY_STACK (mbt->parambo->exps))
          || (mbt->parambv && !BTOR_EMPTY_STACK (mbt->parambv->exps))
          || (mbt->paramarr && !BTOR_EMPTY_STACK (mbt->paramarr->exps)));
  assert ((!mbt->parambo && !mbt->parambv && !mbt->paramarr)
          || (mbt->parambo && mbt->parambv && mbt->paramarr));

  bool selected;
  uint32_t rand, idx, lower;
  BtorMBTExpStack *expstack, *bo, *bv, *arr;
  BtorMBTExp *exp;

  /* choose between param. exps and non-param. exps */
  if (force_param == -1
      || (force_param == 0
          && !btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_param_exp))
      /* no parameterized expressions available */
      || (!mbt->parambo && !mbt->parambv && !mbt->paramarr)
      || (BTOR_EMPTY_STACK (mbt->parambo->exps)
          && BTOR_EMPTY_STACK (mbt->parambv->exps)
          && BTOR_EMPTY_STACK (mbt->paramarr->exps)))
  {
    bo  = mbt->bo;
    bv  = mbt->bv;
    arr = mbt->arr;
  }
  else
  {
    bo  = mbt->parambo;
    bv  = mbt->parambv;
    arr = mbt->paramarr;
  }

  /* choose stack for selecting expressions */
  switch (type)
  {
    case BTORMBT_BO_T: expstack = bo; break;
    case BTORMBT_BV_T: expstack = bv; break;
    case BTORMBT_ARR_T: expstack = arr; break;
    default:
      assert (type == BTORMBT_BB_T);
      /* select target exp stack with prob. proportional to size */
      rand = btor_rng_pick_rand (
          &mbt->round.rng,
          0,
          BTOR_COUNT_STACK (bo->exps) + BTOR_COUNT_STACK (bv->exps) - 1);
      expstack = rand < BTOR_COUNT_STACK (bo->exps) ? bo : bv;
  }

  assert (!BTOR_EMPTY_STACK (expstack->exps));
  /* select first nodes without parents (not yet referenced) */
  selected = false;
  while (expstack->last_pos_parents < BTOR_COUNT_STACK (expstack->exps))
  {
    if (expstack->exps.start[expstack->last_pos_parents]->parents <= 0)
    {
      idx      = expstack->last_pos_parents++;
      selected = true;
      break;
    }
    expstack->last_pos_parents++;
  }
  if (!selected)
  {
    /* select random expression
     * select from initlayer with lower probability
     * - from range (init_layer_size - n) with p = 0.666
     * - from ragne (0 - n)         with p = 0.333 */
    if (expstack->init_layer_size
        && BTOR_COUNT_STACK (expstack->exps) > expstack->init_layer_size
        && btor_rng_pick_with_prob (&mbt->round.rng, 666))
      lower = expstack->init_layer_size - 1;
    else
      lower = 0;
    idx = btor_rng_pick_rand (
        &mbt->round.rng, lower, BTOR_COUNT_STACK (expstack->exps) - 1);
  }
  exp = BTOR_PEEK_STACK (expstack->exps, idx);
  exp->parents++;
  return exp->exp;
}

/* Search and select array expression with element width eew
 * and index width eiw.  If no suitable expression is found,
 * create new array/parameterized WRITE eew->eiw.
 */
static BoolectorNode *
select_arr_exp (BtorMBT *mbt,
                BoolectorNode *node,
                uint32_t eew,
                uint32_t eiw,
                int32_t force_param)
{
  uint32_t i, idx, sel_eew, sel_eiw, rand;
  BtorMBTExp *exp;
  BtorMBTExpStack *expstack;
  BoolectorNode *sel_e, *e[3];
  BoolectorSort es, is, as;

  /* choose between param. exps and non-param. array exps */
  assert ((!mbt->parambo && !mbt->parambv && !mbt->paramarr)
          || (mbt->parambo && mbt->parambv && mbt->paramarr));
  if (force_param == -1
      || (force_param == 0
          && !btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_param_arr_exp))
      || (!mbt->parambo && !mbt->parambv && !mbt->paramarr)
      || (!BTOR_COUNT_STACK (mbt->parambo->exps)
          && !BTOR_COUNT_STACK (mbt->parambv->exps)
          && !BTOR_COUNT_STACK (mbt->paramarr->exps)))
    expstack = mbt->arr;
  else
    expstack = mbt->paramarr;
  assert (!BTOR_EMPTY_STACK (expstack->exps));

  /* random search start idx */
  idx = i = btor_rng_pick_rand (
      &mbt->round.rng, 0, BTOR_COUNT_STACK (expstack->exps) - 1);
  do
  {
    exp     = BTOR_PEEK_STACK (expstack->exps, i);
    sel_e   = exp->exp;
    sel_eew = boolector_get_width (mbt->btor, sel_e);
    sel_eiw = boolector_get_index_width (mbt->btor, sel_e);
    if (sel_eew == eew && sel_eiw == eiw && sel_e != node)
    {
      exp->parents++;
      return sel_e;
    }
    i = (i + 1) % BTOR_COUNT_STACK (expstack->exps);
  } while (idx != i);

  /* no suitable array exp found */
  if (force_param == 1)
  {
    /* generate parameterized WRITE */
    e[0] = select_arr_exp (mbt, NULL, eew, eiw, -1);
    assert (boolector_get_index_width (mbt->btor, e[0]) == eiw);
    assert (boolector_get_width (mbt->btor, e[0]) == eew);
    rand  = btor_rng_pick_rand (&mbt->round.rng, 1, 2);
    e[1]  = select_exp (mbt, BTORMBT_BV_T, rand == 1 ? 1 : 0);
    e[2]  = select_exp (mbt, BTORMBT_BV_T, rand == 2 ? 1 : 0);
    exp   = btormbt_array_op (mbt, WRITE, e[0], e[1], e[2]);
    sel_e = exp->exp;
  }
  else
  {
    es    = boolector_bitvec_sort (mbt->btor, eew);
    is    = boolector_bitvec_sort (mbt->btor, eiw);
    as    = boolector_array_sort (mbt->btor, is, es);
    sel_e = boolector_array (mbt->btor, as, NULL);
    boolector_release_sort (mbt->btor, es);
    boolector_release_sort (mbt->btor, is);
    boolector_release_sort (mbt->btor, as);
    exp = btormbt_push_node (mbt, sel_e);
    g_btormbtstats->num_ops[ARRAY]++;
  }
  exp->parents++;
  assert (boolector_get_index_width (mbt->btor, sel_e) == eiw);
  assert (boolector_get_width (mbt->btor, sel_e) == eew);
  return sel_e;
}

/*------------------------------------------------------------------------*/

static BoolectorSort
btormbt_bv_sort (BtorMBT *mbt)
{
  uint32_t rand, width;
  BoolectorNode *bv;
  BoolectorSort sort;

  if (BTOR_COUNT_STACK (*mbt->bv_sorts)
      && btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_sort_bv))
  {
    /* use existing bv sort */
    rand = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (*mbt->bv_sorts) - 1);
    sort = mbt->bv_sorts->start[rand];
  }
  else
  {
    /* create new bv sort */
    rand = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->bv->exps) - 1);
    bv    = mbt->bv->exps.start[rand]->exp;
    width = boolector_get_width (mbt->btor, bv);
    sort  = boolector_bitvec_sort (mbt->btor, width);
    btormbt_push_sort_stack (mbt->bv_sorts, sort);
  }
  return sort;
}

static void
init_domain (BtorMBT *mbt, BoolectorSortStack *sortstack)
{
  uint32_t i, arity;

  if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_sort_fun_unary))
  {
    btormbt_push_sort_stack (sortstack, btormbt_bv_sort (mbt));
    return;
  }

  arity = btor_rng_pick_rand (
      &mbt->round.rng, mbt->sort_fun_arity.min, mbt->sort_fun_arity.max);

  for (i = 0; i < arity; i++)
    btormbt_push_sort_stack (sortstack, btormbt_bv_sort (mbt));
}

static BoolectorSort
btormbt_fun_sort (BtorMBT *mbt)
{
  uint32_t rand;
  BoolectorSort sort, codomain;
  BoolectorSortStack *domain;

  if (BTOR_COUNT_STACK (*mbt->fun_sorts)
      && btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_sort_fun))
  {
    /* use existing fun sort */
    rand = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (*mbt->fun_sorts) - 1);
    sort = mbt->fun_sorts->start[rand];
  }
  else
  {
    /* create new fun sort */
    domain = btormbt_new_sort_stack (mbt->mm);
    init_domain (mbt, domain);
    codomain = btormbt_bv_sort (mbt);
    sort     = boolector_fun_sort (
        mbt->btor, domain->start, BTOR_COUNT_STACK (*domain), codomain);
    btormbt_push_sort_stack (mbt->fun_sorts, sort);
    btormbt_release_sort_stack (mbt->mm, domain);
  }
  return sort;
}

/*------------------------------------------------------------------------*/

/* Generate parameterized unary/binary/ternary operation. */
static void
btormbt_param_bv_op (BtorMBT *mbt, int32_t op_from, int32_t op_to)
{
  uint32_t i, rand;
  BoolectorNode *e[3];
  BtorMBTOperator op;

  assert (op_from >= NOT && op_from <= COND);
  assert (op_to >= NOT && op_to <= COND);

  op = btor_rng_pick_rand (&mbt->round.rng, op_from, op_to);
  if (is_unary_op (op))
  {
    e[0] = select_exp (mbt, BTORMBT_BB_T, 1);
    btormbt_unary_op (mbt, op, e[0]);
  }
  else if (is_binary_op (op))
  {
    rand = btor_rng_pick_rand (&mbt->round.rng, 0, 1);
    for (i = 0; i < 2; i++)
    {
      e[i] = select_exp (
          mbt,
          ((op >= IMPLIES && op <= IFF) ? BTORMBT_BO_T : BTORMBT_BB_T),
          i == rand ? 1 : 0);
    }
    btormbt_binary_op (mbt, op, e[0], e[1]);
  }
  else
  {
    assert (is_ternary_op (op));
    rand = btor_rng_pick_rand (&mbt->round.rng, 0, 2);
    for (i = 0; i < 3; i++)
    {
      e[i] = select_exp (
          mbt, i == 0 ? BTORMBT_BO_T : BTORMBT_BB_T, i == rand ? 1 : 0);
    }
    btormbt_ternary_op (mbt, op, e[0], e[1], e[2]);
  }
}

/* Generate parameterized operations on arrays.
 * Force array expressions with non-parameterized arrays via parameter
 * force_arrnparr (mostly needed for initializing the paramarr stack).
 * Note that this forces either a WRITE or COND expression. */
static void
btormbt_param_array_op (BtorMBT *mbt)
{
  bool force_param;
  uint32_t rand;
  BoolectorNode *e0, *e1, *e2;
  BtorMBTOperator op;

  /* if there are no parameterized arrays yet, we have to create at least
   * one */
  force_param = BTOR_EMPTY_STACK (mbt->paramarr->exps) == 1;

  /* choose READ/WRITE with p = 0.666, else EQ/NE/COND */
  if (btor_rng_pick_with_prob (&mbt->round.rng, 666))
  {
    /* we need a parameterized array */
    if (force_param)
      op = WRITE;
    else
      op = btor_rng_pick_rand (&mbt->round.rng, READ, WRITE);
  }
  else /* evenly distribute EQ, NE and COND */
  {
    /* parameterized EQ and NE not supported */
    if (!mbt->ext || force_param
        || btor_rng_pick_with_prob (&mbt->round.rng, 333))
      op = COND;
    else
      op = btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_eq) ? EQ : NE;
  }

  e1 = e2 = 0;
  switch (op)
  {
    case WRITE:
      rand = btor_rng_pick_rand (&mbt->round.rng, 1, 2);
      e0   = select_exp (
          mbt,
          BTORMBT_ARR_T,
          force_param ? 1 : btor_rng_pick_rand (&mbt->round.rng, 0, 1));
      e1 = select_exp (mbt, BTORMBT_BV_T, rand == 1 ? 1 : 0);
      e2 = select_exp (mbt, BTORMBT_BV_T, rand == 2 ? 1 : 0);
      break;
    case READ:
      assert (!force_param);
      e0 = select_exp (
          mbt, BTORMBT_ARR_T, btor_rng_pick_rand (&mbt->round.rng, 0, 1));
      e1 = select_exp (mbt, BTORMBT_BV_T, 1);
      break;
    case COND:
      e0 = select_exp (
          mbt,
          BTORMBT_ARR_T,
          force_param ? 1 : btor_rng_pick_rand (&mbt->round.rng, 0, 1));
      e1 = select_arr_exp (
          mbt,
          e0,
          boolector_get_width (mbt->btor, e0),
          boolector_get_index_width (mbt->btor, e0),
          force_param ? 1 : btor_rng_pick_rand (&mbt->round.rng, 0, 1));
      assert (boolector_is_equal_sort (mbt->btor, e0, e1));
      e2 = select_exp (mbt, BTORMBT_BO_T, force_param);
      break;
    default:
      assert (!force_param);
      assert (mbt->ext);
      assert (op == EQ || op == NE);
      e0 = select_exp (mbt, BTORMBT_ARR_T, -1);
      e1 = select_arr_exp (mbt,
                           e0,
                           boolector_get_width (mbt->btor, e0),
                           boolector_get_index_width (mbt->btor, e0),
                           -1);
      /* parameterized array equalities not allowed */
      assert (!btormbt_is_parameterized (mbt, e0));
      assert (!btormbt_is_parameterized (mbt, e1));
      assert (boolector_is_equal_sort (mbt->btor, e0, e1));
  }

  btormbt_array_op (mbt, op, e0, e1, e2);
}

static void
btormbt_bv_fun (BtorMBT *mbt, int32_t nlevel)
{
  int32_t id;
  uint32_t i, n, width, max_param_exps, rand;
  char *symbol;
  BtorMBTExpStack *expstack;
  BtorMBTExpStack *tmpparambo, *tmpparambv, *tmpparamarr, *tmpparamfun;
  BoolectorNode *tmp, *fun, *e0, *e1, *e2;
  BoolectorNodePtrStack params, args;
  BoolectorSort s;
  BtorIntStack param_widths;

  BTOR_INIT_STACK (mbt->mm, param_widths);
  /* choose between apply on random existing and apply on new function */
  /* use existing function */
  if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_apply_fun)
      && (!BTOR_EMPTY_STACK (mbt->fun->exps)
          || (mbt->paramfun && !BTOR_EMPTY_STACK (mbt->paramfun->exps))))
  {
    /* pick fun from fun/paramfun with p = 0.5 if non-empty */
    expstack = !BTOR_EMPTY_STACK (mbt->fun->exps)
                   ? (mbt->paramfun && !BTOR_EMPTY_STACK (mbt->paramfun->exps)
                          ? (btor_rng_pick_with_prob (&mbt->round.rng, 500)
                                 ? mbt->fun
                                 : mbt->paramfun)
                          : mbt->fun)
                   : mbt->paramfun;

    rand = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (expstack->exps) - 1);

    fun = expstack->exps.start[rand]->exp;

    // FIXME (ma): sort workaround
    BtorSort *sort;
    sort = btor_sort_get_by_id (mbt->btor,
                                btor_node_get_sort_id ((BtorNode *) fun));
    for (i = 0; i < sort->fun.domain->tuple.num_elements; i++)
    {
      BTOR_PUSH_STACK (param_widths,
                       btor_sort_bv_get_width (
                           mbt->btor, sort->fun.domain->tuple.elements[i]->id));
    }
  }
  else /* generate new function */
  {
    /* save current stacks of previous scope */
    tmpparambo  = mbt->parambo;
    tmpparambv  = mbt->parambv;
    tmpparamarr = mbt->paramarr;
    tmpparamfun = mbt->paramfun;

    /* create new stacks for this scope
     * nested functions can access nodes from the parent function */
    if (tmpparambo)
      mbt->parambo = btormbt_copy_exp_stack (mbt, tmpparambo);
    else
      mbt->parambo = btormbt_new_exp_stack (mbt->mm);

    if (tmpparambv)
      mbt->parambv = btormbt_copy_exp_stack (mbt, tmpparambv);
    else
      mbt->parambv = btormbt_new_exp_stack (mbt->mm);

    if (tmpparamarr)
      mbt->paramarr = btormbt_copy_exp_stack (mbt, tmpparamarr);
    else
      mbt->paramarr = btormbt_new_exp_stack (mbt->mm);

    if (tmpparamfun)
      mbt->paramfun = btormbt_copy_exp_stack (mbt, tmpparamfun);
    else
      mbt->paramfun = btormbt_new_exp_stack (mbt->mm);

    /* choose function parameters */
    BTOR_INIT_STACK (mbt->mm, params);
    // TODO (ma): make configurable
    for (i = 0;
         i < btor_rng_pick_rand (&mbt->round.rng, MIN_NPARAMS, MAX_NPARAMS);
         i++)
    {
      // TODO (ma): remove ite here?
      width = btor_rng_pick_rand (
          &mbt->round.rng, mbt->bw.min > 2 ? mbt->bw.min : 1, mbt->bw.max);
      s   = boolector_bitvec_sort (mbt->btor, width);
      tmp = boolector_param (mbt->btor, s, 0);
      assert (boolector_is_param (mbt->btor, tmp));
      id = boolector_get_node_id (mbt->btor, tmp);
      BTOR_NEWN (mbt->mm, symbol, 20);
      sprintf (symbol, "mbtparam%u", id);
      boolector_set_symbol (mbt->btor, tmp, symbol);
      BTOR_DELETEN (mbt->mm, symbol, 20);
      boolector_release_sort (mbt->btor, s);
      BTOR_PUSH_STACK (params, tmp);
      BTOR_PUSH_STACK (param_widths, boolector_get_width (mbt->btor, tmp));
      btormbt_push_node (mbt, tmp);
      g_btormbtstats->num_ops[PARAM]++;
    }

    /* initialize parameterized stacks to be non-empty */
    if (BTOR_EMPTY_STACK (mbt->parambv->exps))
    {
      assert (!BTOR_EMPTY_STACK (mbt->parambo->exps));
      rand = btor_rng_pick_rand (
          &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->parambo->exps) - 1);
      tmp = mbt->parambo->exps.start[rand]->exp;
      assert (boolector_get_width (mbt->btor, tmp) == 1);
      modify_bv (
          mbt,
          tmp,
          btor_rng_pick_rand (&mbt->round.rng, mbt->bw.min, mbt->bw.max));
    }
    if (BTOR_EMPTY_STACK (mbt->parambo->exps))
    {
      assert (!BTOR_EMPTY_STACK (mbt->parambv->exps));
      rand = btor_rng_pick_rand (
          &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->parambv->exps) - 1);
      tmp = mbt->parambv->exps.start[rand]->exp;
      assert (boolector_get_width (mbt->btor, tmp) > 1);
      modify_bv (mbt, tmp, 1);
    }
    if (BTOR_EMPTY_STACK (mbt->paramarr->exps))
    {
      rand = btor_rng_pick_rand (&mbt->round.rng, 1, 2);
      e1   = select_exp (mbt, BTORMBT_BB_T, rand == 1 ? 1 : 0);
      e2   = select_exp (mbt, BTORMBT_BB_T, rand == 2 ? 1 : 0);
      e0   = select_arr_exp (mbt,
                           0,
                           boolector_get_width (mbt->btor, e2),
                           boolector_get_width (mbt->btor, e1),
                           -1);
      assert (btormbt_is_parameterized (mbt, e1)
              || btormbt_is_parameterized (mbt, e2));
      // TODO (ma): create parameterized acond?
      btormbt_array_op (mbt, WRITE, e0, e1, e2);
      assert (!BTOR_EMPTY_STACK (mbt->parambo->exps));
      assert (!BTOR_EMPTY_STACK (mbt->parambv->exps));
      assert (!BTOR_EMPTY_STACK (mbt->paramarr->exps));
    }

    /* generate parameterized expressions */
    max_param_exps = btor_rng_pick_rand (&mbt->round.rng, 0, MAX_NPARAMOPS);
    n              = 0;
    while (n++ < max_param_exps)
    {
      rand = btor_rng_pick_rand (&mbt->round.rng, 0, BTOR_PROB_MAX - 1);
      if (rand < mbt->round.p_bitvec_fun)
        btormbt_param_bv_op (mbt, NOT, COND);
      else if (rand < mbt->round.p_bitvec_fun + mbt->round.p_array_op)
        btormbt_param_array_op (mbt);
      else if (nlevel < MAX_NNESTEDBFUNS)
        btormbt_bv_fun (mbt, nlevel + 1);
    }

    /* pick exp from parambo/parambv with p = 0.5 if non-empty */
    expstack = !BTOR_EMPTY_STACK (mbt->parambo->exps)
                   ? (!BTOR_EMPTY_STACK (mbt->parambv->exps)
                          ? (btor_rng_pick_with_prob (&mbt->round.rng, 500)
                                 ? mbt->parambo
                                 : mbt->parambv)
                          : mbt->parambo)
                   : mbt->parambv;
    assert (!BTOR_EMPTY_STACK (expstack->exps));

    rand = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (expstack->exps) - 1);
    tmp = BTOR_PEEK_STACK (expstack->exps, rand)->exp;
    fun =
        boolector_fun (mbt->btor, params.start, BTOR_COUNT_STACK (params), tmp);
    for (i = 0; i < BTOR_COUNT_STACK (params); i++)
      boolector_is_bound_param (mbt->btor, BTOR_PEEK_STACK (params, i));

    /* cleanup */
    for (i = 0; i < BTOR_COUNT_STACK (mbt->parambo->exps); i++)
      btormbt_release_node (mbt, mbt->parambo->exps.start[i]->exp);
    btormbt_release_exp_stack (mbt->mm, mbt->parambo);
    for (i = 0; i < BTOR_COUNT_STACK (mbt->parambv->exps); i++)
      btormbt_release_node (mbt, mbt->parambv->exps.start[i]->exp);
    btormbt_release_exp_stack (mbt->mm, mbt->parambv);
    for (i = 0; i < BTOR_COUNT_STACK (mbt->paramarr->exps); i++)
      btormbt_release_node (mbt, mbt->paramarr->exps.start[i]->exp);
    btormbt_release_exp_stack (mbt->mm, mbt->paramarr);
    for (i = 0; i < BTOR_COUNT_STACK (mbt->paramfun->exps); i++)
      btormbt_release_node (mbt, mbt->paramfun->exps.start[i]->exp);
    btormbt_release_exp_stack (mbt->mm, mbt->paramfun);
    BTOR_RELEASE_STACK (params);

    /* reset scope for arguments to apply node */
    mbt->parambo  = tmpparambo;
    mbt->parambv  = tmpparambv;
    mbt->paramarr = tmpparamarr;
    mbt->paramfun = tmpparamfun;

    /* new function needs to be put into the scope of the parent */
    btormbt_push_node (mbt, fun);
    g_btormbtstats->num_ops[FUN]++;
  }
  /* on level 0, the resulting function cannot be parameterized */
  assert (nlevel > 0 || !btormbt_is_parameterized (mbt, fun));

  /* generate apply expression with arguments within scope of apply */
  BTOR_INIT_STACK (mbt->mm, args);
  for (i = 0; i < BTOR_COUNT_STACK (param_widths); i++)
  {
    width = BTOR_PEEK_STACK (param_widths, i);
    // TODO (ma): if width == 1 select BTORMBT_BO_T
    tmp = select_exp (mbt, BTORMBT_BV_T, 0);
    BTOR_PUSH_STACK (args, modify_bv (mbt, tmp, width));
  }
  assert (boolector_fun_sort_check (
              mbt->btor, args.start, BTOR_COUNT_STACK (args), fun)
          == -1);
  tmp = boolector_apply (mbt->btor, args.start, BTOR_COUNT_STACK (args), fun);
  btormbt_push_node (mbt, tmp);
  g_btormbtstats->num_ops[APPLY]++;
  BTOR_RELEASE_STACK (param_widths);
  BTOR_RELEASE_STACK (args);
}

static void
btormbt_bv_uf (BtorMBT *mbt)
{
  int32_t id;
  uint32_t width, rand;
  char *symbol;
  BoolectorNode *uf, *arg, *apply;
  BtorSortId sortid;
  BoolectorSort sort;
  BoolectorNodePtrStack stack;
  BtorTupleSortIterator it;

  /* use existing UF */
  if (BTOR_COUNT_STACK (mbt->uf->exps)
      && btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_apply_uf))
  {
    rand = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->uf->exps) - 1);
    uf = mbt->uf->exps.start[rand]->exp;
  }
  else /* create new UF */
  {
    sort = btormbt_fun_sort (mbt);
    uf   = boolector_uf (mbt->btor, sort, 0);
    assert (boolector_is_uf (mbt->btor, uf));
    id = boolector_get_node_id (mbt->btor, uf);
    BTOR_NEWN (mbt->mm, symbol, 20);
    sprintf (symbol, "mbtuf%u", id);
    boolector_set_symbol (mbt->btor, uf, symbol);
    BTOR_DELETEN (mbt->mm, symbol, 20);
    //      btormbt_push_exp_stack (mbt->mm, mbt->uf, uf);
    btormbt_push_node (mbt, uf);
    g_btormbtstats->num_ops[UF]++;
  }

  /* create apply with sort of UF */
  BTOR_INIT_STACK (mbt->mm, stack);
  btor_iter_tuple_sort_init (
      &it,
      mbt->btor,
      btor_sort_fun_get_domain (mbt->btor,
                                btor_node_get_sort_id ((BtorNode *) uf)));
  while (btor_iter_tuple_sort_has_next (&it))
  {
    sortid = btor_iter_tuple_sort_next (&it);
    width  = btor_sort_bv_get_width (mbt->btor, sortid);
    arg    = select_exp (mbt, BTORMBT_BB_T, 0);
    BTOR_PUSH_STACK (stack, modify_bv (mbt, arg, width));
  }

  /* create apply on UF */
  apply =
      boolector_apply (mbt->btor, stack.start, BTOR_COUNT_STACK (stack), uf);

  width = boolector_get_width (mbt->btor, apply);
  btormbt_push_node (mbt, apply);
  g_btormbtstats->num_ops[APPLY]++;
  BTOR_RELEASE_STACK (stack);
}

/*------------------------------------------------------------------------*/

static void *btormbt_state_new (BtorMBT *);
static void *btormbt_state_opt (BtorMBT *);
static void *btormbt_state_init (BtorMBT *);
static void *btormbt_state_main (BtorMBT *);
static void *btormbt_state_add (BtorMBT *);
static void *btormbt_state_bv_op (BtorMBT *);
static void *btormbt_state_arr_op (BtorMBT *);
static void *btormbt_state_bv_fun (BtorMBT *);
static void *btormbt_state_bv_uf (BtorMBT *);
static void *btormbt_state_input (BtorMBT *);
static void *btormbt_state_release (BtorMBT *);
static void *btormbt_state_assume_assert (BtorMBT *);
static void *btormbt_state_sat (BtorMBT *);
static void *btormbt_state_dump (BtorMBT *);
static void *btormbt_state_query_model (BtorMBT *);
static void *btormbt_state_inc (BtorMBT *);
static void *btormbt_state_delete (BtorMBT *);

static void *
btormbt_state_new (BtorMBT *mbt)
{
  /* number of initial inputs */
  mbt->round.max_inputs =
      btor_rng_pick_rand (&mbt->round.rng, mbt->inputs.min, mbt->inputs.max);

  /* number of initial operations */
  mbt->round.max_ops = btor_rng_pick_rand (
      &mbt->round.rng, mbt->ops.init.min, mbt->ops.init.max);

  // TODO (ma): UFs
  init_pd_inputs (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->vars.init.min, mbt->vars.init.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->consts.init.min, mbt->consts.init.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->arrays.init.min, mbt->arrays.init.max));

  /* no delete operation at init */
  init_pd_ops (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_ops.init.min, mbt->add_ops.init.max),
      btor_rng_pick_rand (&mbt->round.rng,
                          mbt->release_ops.init.min,
                          mbt->release_ops.init.max));

  /* no additional inputs at init */
  init_pd_add (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_funs.init.min, mbt->add_funs.init.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_uf.init.min, mbt->add_uf.init.max),
      btor_rng_pick_rand (&mbt->round.rng,
                          mbt->add_arrayops.init.min,
                          mbt->add_arrayops.init.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_bvops.init.min, mbt->add_bvops.init.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_inputs.init.min, mbt->add_inputs.init.max));

  BTORMBT_LOG (1,
               "new: pick %u ops (add:rel=%0.1f%%:%0.1f%%), %u inputs",
               mbt->round.max_ops,
               (double) mbt->round.p_add / 10,
               (double) mbt->round.p_release / 10,
               mbt->round.max_inputs);

  mbt->btor = boolector_new ();
  assert (mbt->btor);

  return btormbt_state_opt;
}

static void *
btormbt_state_opt (BtorMBT *mbt)
{
  bool inc = true;
  uint32_t i;
  BtorMBTBtorOpt *btoropt, *btoropt_engine;
  BtorUIntStack stack;

  /* enable / disable shadow clone testing ---------------------------------- */

  if (mbt->fshadow)
  {
    /* force (no) shadow clone testing */
    mbt->round.shadow = mbt->fshadow == FORCE_SHADOW_TRUE ? true : false;
  }
  else
  {
    mbt->round.shadow = false;
    /* enable shadow clone testing randomly */
    if (btor_rng_pick_with_prob (&mbt->round.rng, 100))
      mbt->round.shadow = true;
  }
  if (mbt->round.shadow && btor_rng_pick_with_prob (&mbt->round.rng, 300))
  {
    BTORMBT_LOG (1, "initial shadow clone...");
    /* cleanup done by boolector */
    boolector_chkclone (mbt->btor);
    g_btormbtstats->num_shadow_clone += 1;
    mbt->round.has_shadow = true;
  }

  /* choose logic ----------------------------------------------------------- */

  if (mbt->is_flogic)
    mbt->round.logic = mbt->flogic;
  else
  {
    BTOR_INIT_STACK (mbt->mm, stack);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_BV);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_BV);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_BV);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_BV);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_ABV);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_AUFBV);
    BTOR_PUSH_STACK (stack, BTORMBT_LOGIC_QF_UFBV);
    mbt->round.logic = BTOR_PEEK_STACK (
        stack,
        btor_rng_pick_rand (&mbt->round.rng, 0, BTOR_COUNT_STACK (stack) - 1));
    BTOR_RELEASE_STACK (stack);
  }

  /* set Boolector engine --------------------------------------------------- */

  btoropt_engine = mbt->btor_opts.start[BTOR_OPT_ENGINE];
  if (btoropt_engine->forced_by_cl)
  {
    if (btoropt_engine->val == BTOR_ENGINE_AIGPROP
        || btoropt_engine->val == BTOR_ENGINE_PROP
        || btoropt_engine->val == BTOR_ENGINE_SLS
        || (btoropt_engine->val == BTOR_ENGINE_FUN
            && (btor_opt_get (mbt->btor, BTOR_OPT_FUN_PREPROP)
                || btor_opt_get (mbt->btor, BTOR_OPT_FUN_PRESLS))))
    {
      /* reset if forced engine does not support QF_(AUF)BV */
      mbt->round.logic = BTORMBT_LOGIC_QF_BV;
    }
  }
  else
  {
    /* choose Boolector engine corresponding to supported logic */
    BTOR_INIT_STACK (mbt->mm, stack);
    BTOR_PUSH_STACK (stack, BTOR_ENGINE_FUN);
    if (mbt->round.logic == BTORMBT_LOGIC_QF_BV)
    {
      BTOR_PUSH_STACK (stack, BTOR_ENGINE_AIGPROP);
      BTOR_PUSH_STACK (stack, BTOR_ENGINE_PROP);
      BTOR_PUSH_STACK (stack, BTOR_ENGINE_SLS);
    }
    btoropt_engine->val = BTOR_PEEK_STACK (
        stack,
        btor_rng_pick_rand (&mbt->round.rng, 0, BTOR_COUNT_STACK (stack) - 1));
    BTOR_RELEASE_STACK (stack);
  }
  assert (btoropt_engine->val == BTOR_ENGINE_FUN
          || mbt->round.logic == BTORMBT_LOGIC_QF_BV);
  boolector_set_opt (mbt->btor, BTOR_OPT_ENGINE, btoropt_engine->val);

  BTORMBT_LOG (
      1,
      "opt: set logic to '%s'",
      mbt->round.logic == BTORMBT_LOGIC_QF_AUFBV
          ? "QF_AUFBV"
          : (mbt->round.logic == BTORMBT_LOGIC_QF_ABV
                 ? "QF_ABV"
                 : (mbt->round.logic == BTORMBT_LOGIC_QF_UFBV ? "QF_UFBV"
                                                              : "QF_BV")));

  BTORMBT_LOG (1,
               "opt: set boolector option '%s' to '%d'",
               btoropt_engine->name,
               btoropt_engine->val);

  /* set SAT engine --------------------------------------------------------- */

  btoropt = mbt->btor_opts.start[BTOR_OPT_SAT_ENGINE];

  if (!btoropt->forced_by_cl)
  {
    /* pick SAT engine randomly */
    btoropt->val =
        btor_rng_pick_rand (&mbt->round.rng, btoropt->min, btoropt->max);
  }

  if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
  {
    boolector_set_opt (mbt->btor, btoropt->kind, btoropt->val);
  }
  else
  {
    if (btoropt->val == BTOR_SAT_ENGINE_CADICAL)
      boolector_set_sat_solver (mbt->btor, "cadical");
    else if (btoropt->val == BTOR_SAT_ENGINE_LINGELING)
      boolector_set_sat_solver (mbt->btor, "lingeling");
    else if (btoropt->val == BTOR_SAT_ENGINE_MINISAT)
      boolector_set_sat_solver (mbt->btor, "minisat");
    else
    {
      assert (btoropt->val == BTOR_SAT_ENGINE_PICOSAT);
      boolector_set_sat_solver (mbt->btor, "picosat");
    }
  }

  BTORMBT_LOG (
      1, "opt: set boolector option '%s' to '%d'", btoropt->name, btoropt->val);

  // currently, CaDiCaL only support non-incremental calls
  if (boolector_get_opt (mbt->btor, BTOR_OPT_SAT_ENGINE)
      == BTOR_SAT_ENGINE_CADICAL)
  {
    mbt->round.logic = BTORMBT_LOGIC_QF_BV;
    BTORMBT_LOG (1, "opt: force logic to '%s'", "QF_BV");
    inc = false;
  }

  if (mbt->optfuzz)
  {
    /* set output format for dumping */
    btoropt = mbt->btor_opts.start[BTOR_OPT_OUTPUT_FORMAT];
    if (!btoropt->forced_by_cl)
    {
      if (btor_rng_pick_with_prob (&mbt->round.rng, 330))
      {
        if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
          btoropt->val = BTOR_OUTPUT_FORMAT_AIGER_ASCII;
        else
          btoropt->val = BTOR_OUTPUT_FORMAT_AIGER_BINARY;
      }
      else
      {
        if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
          btoropt->val = BTOR_OUTPUT_FORMAT_BTOR;
        else
          btoropt->val = BTOR_OUTPUT_FORMAT_SMT2;
      }
    }
    boolector_set_opt (mbt->btor, BTOR_OPT_OUTPUT_FORMAT, btoropt->val);

    /* set output number format */
    btoropt = mbt->btor_opts.start[BTOR_OPT_OUTPUT_NUMBER_FORMAT];
    if (!btoropt->forced_by_cl)
      btoropt->val =
          btor_rng_pick_rand (&mbt->round.rng, btoropt->min, btoropt->max);
    boolector_set_opt (mbt->btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, btoropt->val);
  }

  /* set Boolector options */
  for (i = 0; i < BTOR_COUNT_STACK (mbt->btor_opts); i++)
  {
    btoropt = BTOR_PEEK_STACK (mbt->btor_opts, i);
    assert (boolector_has_opt (mbt->btor, btoropt->kind));

    if (!mbt->optfuzz && !btoropt->forced_by_cl) continue;

    /* skip, has already been set */
    if (btoropt->kind == BTOR_OPT_ENGINE || btoropt->kind == BTOR_OPT_SAT_ENGINE
        || btoropt->kind == BTOR_OPT_OUTPUT_FORMAT
        || btoropt->kind == BTOR_OPT_OUTPUT_NUMBER_FORMAT)
    {
      continue;
    }

    /* skip with prob = 0.5 */
    if ((btoropt->kind == BTOR_OPT_INCREMENTAL
         || btoropt->kind == BTOR_OPT_MODEL_GEN)
        && btor_rng_pick_with_prob (&mbt->round.rng, 500))
    {
      continue;
    }
    /* skip with prob = 0.1
     * note: do not skip engine options (value is picked between min and
     * max anyway, increases probability to enable engine options) */
    else if ((!btoropt->is_engine_opt || btoropt->engine != btoropt_engine->val)
             && btor_rng_pick_with_prob (&mbt->round.rng, 900))
    {
      continue;
    }

    /* avoid invalid option combinations */
    // FIXME remove as soon as ucopt works with mgen
    /* do not enable unconstrained optimization if either model
     * generation or incremental is enabled */
    if (btoropt->kind == BTOR_OPT_UCOPT
        && (boolector_get_opt (mbt->btor, BTOR_OPT_MODEL_GEN)
            || boolector_get_opt (mbt->btor, BTOR_OPT_INCREMENTAL)))
    {
      continue;
    }
    else if ((btoropt->kind == BTOR_OPT_MODEL_GEN
              || btoropt->kind == BTOR_OPT_INCREMENTAL)
             && boolector_get_opt (mbt->btor, BTOR_OPT_UCOPT))
    {
      continue;
    }
    /* do not enable justification if dual propagation is enabled */
    else if (btoropt->kind == BTOR_OPT_FUN_JUST
             && boolector_get_opt (mbt->btor, BTOR_OPT_FUN_DUAL_PROP))
    {
      continue;
    }
    else if (btoropt->kind == BTOR_OPT_FUN_DUAL_PROP
             && boolector_get_opt (mbt->btor, BTOR_OPT_FUN_JUST))
    {
      continue;
    }

    if (!btoropt->forced_by_cl)
    {
      /* pick option randomly */
      btoropt->val =
          btor_rng_pick_rand (&mbt->round.rng, btoropt->min, btoropt->max);
    }
    /* if an option is set via command line the value is saved in
     * btoropt->val */

    /* set boolector option */
    if (btoropt->kind != BTOR_OPT_INCREMENTAL || btoropt->val != 1 || inc)
    {
      boolector_set_opt (mbt->btor, btoropt->kind, btoropt->val);
      BTORMBT_LOG (1,
                   "opt: set boolector option '%s' to '%u'",
                   btoropt->name,
                   btoropt->val);
    }

    /* set some mbt specific options */
    // NOTE: inc flag required since CaDiCaL does not yet support incremental
    // mode
    if (btoropt->kind == BTOR_OPT_INCREMENTAL && btoropt->val == 1 && inc)
    {
      mbt->round.inc = true;
      mbt->round.max_ninc =
          btor_rng_pick_rand (&mbt->round.rng, MIN_INC_CALLS, MAX_INC_CALLS);
    }
    else if (btoropt->kind == BTOR_OPT_MODEL_GEN && btoropt->val > 0)
    {
      mbt->round.mgen = true;
      if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_print_model))
        mbt->round.print_model = true;
    }
  }

  /* configure logic */
  switch (mbt->round.logic)
  {
    case BTORMBT_LOGIC_QF_BV:
      g_btormbt->create_funs   = false;
      g_btormbt->create_ufs    = false;
      g_btormbt->create_arrays = false;
      break;
    case BTORMBT_LOGIC_QF_UFBV:
      g_btormbt->create_funs   = false;
      g_btormbt->create_ufs    = true;
      g_btormbt->create_arrays = false;
      break;
    case BTORMBT_LOGIC_QF_ABV:
      g_btormbt->create_funs   = false;
      g_btormbt->create_ufs    = false;
      g_btormbt->create_arrays = true;
      break;
    default:
      assert (mbt->round.logic == BTORMBT_LOGIC_QF_AUFBV);
      g_btormbt->create_funs   = true;
      g_btormbt->create_ufs    = true;
      g_btormbt->create_arrays = true;
  }

  if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_dump))
  {
    mbt->round.dump = true;
  }

  /* make formulas extensional with probability of 0.1 */
  if (btor_rng_pick_with_prob (&mbt->round.rng, 100)) mbt->ext = true;

  return btormbt_state_init;
}

static void *
btormbt_state_init (BtorMBT *mbt)
{
  // TODO (ma): UFs?
  if (BTOR_COUNT_STACK (mbt->bo->exps) + BTOR_COUNT_STACK (mbt->bv->exps)
          + BTOR_COUNT_STACK (mbt->arr->exps)
      < mbt->round.max_inputs)
  {
    return btormbt_state_input;
  }

  // TODO (ma): UFs?
  /* generate at least one bool-var, one bv-var and one arr;
   * to ensure nonempty expression stacks */
  if (BTOR_COUNT_STACK (mbt->bo->exps) < 1) btormbt_var (mbt, BTORMBT_BO_T);
  if (BTOR_COUNT_STACK (mbt->bv->exps) < 1) btormbt_var (mbt, BTORMBT_BV_T);
  if (mbt->create_arrays && BTOR_COUNT_STACK (mbt->arr->exps) < 1)
    btormbt_array (mbt);

  if (mbt->round.ops < mbt->round.max_ops)
  {
    mbt->round.ops++;
    BTORMBT_LOG_STATUS (2, "init");
    if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->round.p_add))
      return btormbt_state_add;
    else
      return btormbt_state_release;
  }

  BTORMBT_LOG_STATUS (1, "init");
  mbt->bo->init_layer_size  = BTOR_COUNT_STACK (mbt->bo->exps);
  mbt->bv->init_layer_size  = BTOR_COUNT_STACK (mbt->bv->exps);
  mbt->arr->init_layer_size = BTOR_COUNT_STACK (mbt->arr->exps);

  /* adapt paramters for main */
  mbt->round.ops = 0;
  mbt->round.max_ops =
      btor_rng_pick_rand (&mbt->round.rng, mbt->ops.min, mbt->ops.max);
  /* how many operations should be assertions?
   * -> round.ops.max and nass should be in relation (the more ops, the more
   * assertions) in order to keep the sat/unsat ratio balanced */
  if (mbt->round.max_ops < mbt->max_ops_lower)
  {
    mbt->round.max_ass = BTORMBT_MIN (
        mbt->round.max_ops,
        btor_rng_pick_rand (
            &mbt->round.rng, mbt->min_asserts_lower, mbt->max_asserts_lower));
  }
  else
  {
    mbt->round.max_ass = btor_rng_pick_rand (
        &mbt->round.rng, mbt->min_asserts_upper, mbt->max_asserts_upper);
  }

  init_pd_inputs (
      mbt,
      btor_rng_pick_rand (&mbt->round.rng, mbt->vars.min, mbt->vars.max),
      btor_rng_pick_rand (&mbt->round.rng, mbt->consts.min, mbt->consts.max),
      btor_rng_pick_rand (&mbt->round.rng, mbt->arrays.min, mbt->arrays.max));

  init_pd_ops (
      mbt,
      btor_rng_pick_rand (&mbt->round.rng, mbt->add_ops.min, mbt->add_ops.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->release_ops.min, mbt->release_ops.max));

  init_pd_add (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_funs.min, mbt->add_funs.max),
      btor_rng_pick_rand (&mbt->round.rng, mbt->add_uf.min, mbt->add_uf.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_arrayops.min, mbt->add_arrayops.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_bvops.min, mbt->add_bvops.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_inputs.min, mbt->add_inputs.max));

  BTORMBT_LOG (
      1,
      "main: pick %u ops (add:rel=%0.1f%%:%0.1f%%), ~%u asserts/assumes",
      mbt->round.max_ops,
      (double) mbt->round.p_add / 10,
      (double) mbt->round.p_release / 10,
      mbt->round.max_ass);

  mbt->round.is_init = true;
  return btormbt_state_main;
}

static void *
btormbt_state_main (BtorMBT *mbt)
{
  assert (BTOR_COUNT_STACK (mbt->bo->exps) > 0);
  assert (BTOR_COUNT_STACK (mbt->bv->exps) > 0);
  assert (!mbt->create_arrays || BTOR_COUNT_STACK (mbt->arr->exps) > 0);

  Btor *clone;
  BoolectorNode *node, *cnode;
  const char *symbol, *csymbol;
  size_t i;
  int32_t j, id;
  BtorMBTExpStack *exp_stack;
  BtorMBTExpStack *exp_stacks[5] = {
      mbt->bo, mbt->bv, mbt->arr, mbt->fun, mbt->uf};

#ifdef NDEBUG
  (void) csymbol;
#endif

  /* main operations */
  if (mbt->round.ops < mbt->round.max_ops)
  {
    mbt->round.ops++;
    BTORMBT_LOG_STATUS (2, "main");
    if (mbt->round.max_ass > mbt->round.max_ops
        || btor_rng_pick_with_prob (
               &mbt->round.rng,
               ((double) mbt->round.max_ass / mbt->round.max_ops)
                   * BTOR_PROB_MAX))
    {
      /* pick with prob=0.0001 */
      if (mbt->round.inc && btor_rng_pick_with_prob (&mbt->round.rng, 100))
      {
        if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
        {
          mbt->round.asserts += mbt->round.assumes;
          mbt->round.asserts_tot += mbt->round.assumes;
          boolector_fixate_assumptions (mbt->btor);
          btormbt_reset_assumptions (mbt);
        }
        else
        {
          boolector_reset_assumptions (mbt->btor);
          btormbt_reset_assumptions (mbt);
        }
        mbt->round.assumes = 0;
      }

      return btormbt_state_assume_assert;
    }
    else if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->round.p_add))
    {
      return btormbt_state_add;
    }
    else
    {
      return btormbt_state_release;
    }
  }

  BTORMBT_LOG_STATUS (1, "main");
  BTORMBT_LOG (1,
               "main: asserts %d, assumes %d",
               mbt->round.asserts_tot,
               mbt->round.assumes);

  if (mbt->round.shadow
      && (!mbt->round.has_shadow
          || !btor_rng_pick_with_prob (&mbt->round.rng, 100)))
  {
    BTORMBT_LOG (1, "cloning...");
    /* cleanup done by boolector */
    boolector_chkclone (mbt->btor);
    g_btormbtstats->num_shadow_clone += 1;
    mbt->round.has_shadow = true;
  }

  if (btor_rng_pick_with_prob (&mbt->round.rng, 100))
  {
    g_btormbtstats->num_simp += 1;
    (void) boolector_simplify (mbt->btor);
  }

  if (btor_rng_pick_with_prob (&mbt->round.rng, 100))
  {
    g_btormbtstats->num_clone += 1;

    clone = boolector_clone (mbt->btor);

    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
      boolector_reset_stats (clone);
    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
      boolector_reset_time (clone);
    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
      boolector_print_stats (clone);

    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
    {
      for (j = 0; j < 5; j++)
      {
        exp_stack = exp_stacks[j];
        for (i = 0; i < BTOR_COUNT_STACK (exp_stack->exps); i++)
        {
          node = BTOR_PEEK_STACK (exp_stack->exps,
                                  btor_rng_pick_rand (
                                      &mbt->round.rng,
                                      0,
                                      BTOR_COUNT_STACK (exp_stack->exps) - 1))
                     ->exp;
          assert (boolector_get_btor (node) == mbt->btor);
          id     = boolector_get_node_id (mbt->btor, node);
          symbol = boolector_get_symbol (mbt->btor, node);
          cnode  = boolector_match_node (clone, node);
          assert (boolector_get_btor (cnode) == clone);
          assert (id == boolector_get_node_id (clone, cnode));
          assert (boolector_get_sort (mbt->btor, node)
                  == boolector_get_sort (clone, cnode));
          csymbol = boolector_get_symbol (clone, cnode);
          assert ((!symbol && !csymbol) || !strcmp (symbol, csymbol));
          if (boolector_is_fun (mbt->btor, node))
          {
            assert (boolector_fun_get_domain_sort (mbt->btor, node)
                    == boolector_fun_get_domain_sort (clone, cnode));
            assert (boolector_fun_get_codomain_sort (mbt->btor, node)
                    == boolector_fun_get_codomain_sort (clone, cnode));
          }
          boolector_release (clone, cnode);

          cnode = boolector_match_node_by_id (clone, id < 0 ? -id : id);
          assert (boolector_get_btor (cnode) == clone);
          csymbol = boolector_get_symbol (clone, cnode);
          assert (boolector_get_sort (mbt->btor, node)
                  == boolector_get_sort (clone, cnode));
          assert ((!symbol && !csymbol) || !strcmp (symbol, csymbol));
          if (boolector_is_fun (mbt->btor, node))
          {
            assert (boolector_fun_get_domain_sort (mbt->btor, node)
                    == boolector_fun_get_domain_sort (clone, cnode));
            assert (boolector_fun_get_codomain_sort (mbt->btor, node)
                    == boolector_fun_get_codomain_sort (clone, cnode));
          }
          boolector_release (clone, cnode);

          if (symbol)
          {
            cnode = boolector_match_node_by_symbol (clone, symbol);
            assert (boolector_get_btor (cnode) == clone);
            assert (id == boolector_get_node_id (clone, cnode));
            assert (boolector_get_sort (mbt->btor, node)
                    == boolector_get_sort (clone, cnode));
            if (boolector_is_fun (mbt->btor, node))
            {
              assert (boolector_fun_get_domain_sort (mbt->btor, node)
                      == boolector_fun_get_domain_sort (clone, cnode));
              assert (boolector_fun_get_codomain_sort (mbt->btor, node)
                      == boolector_fun_get_codomain_sort (clone, cnode));
            }
            boolector_release (clone, cnode);
          }
        }
      }
    }

    boolector_delete (clone);
  }

  if (mbt->round.dump) return btormbt_state_dump;

  return btormbt_state_sat;
}

static void *
btormbt_state_add (BtorMBT *mbt)
{
  void *next;
  uint32_t rand;

  rand = btor_rng_pick_rand (&mbt->round.rng, 0, BTOR_PROB_MAX - 1);

  if (rand < mbt->round.p_bitvec_op)
  {
    next = btormbt_state_bv_op;
  }
  else if (mbt->create_arrays
           && rand < mbt->round.p_bitvec_op + mbt->round.p_array_op)
  {
    next = btormbt_state_arr_op;
  }
  else if (mbt->create_funs
           && rand < mbt->round.p_bitvec_op + mbt->round.p_array_op
                         + mbt->round.p_bitvec_fun)
  {
    next = btormbt_state_bv_fun;
  }
  else if (mbt->create_ufs
           && rand < mbt->round.p_bitvec_op + mbt->round.p_array_op
                         + mbt->round.p_bitvec_fun + mbt->round.p_bitvec_uf)
  {
    next = btormbt_state_bv_uf;
  }
  else
  {
    next = btormbt_state_input;
  }

  return next;
}

static void *
btormbt_state_bv_op (BtorMBT *mbt)
{
  BoolectorNode *e0, *e1, *e2;

  BtorMBTOperator op = btor_rng_pick_rand (&mbt->round.rng, NOT, COND);

  if (is_unary_op (op))
  {
    e0 = select_exp (mbt, BTORMBT_BB_T, 0);
    btormbt_unary_op (mbt, op, e0);
  }
  else if (is_binary_op (op))
  {
    e0 = select_exp (
        mbt, ((op >= IMPLIES && op <= IFF) ? BTORMBT_BO_T : BTORMBT_BB_T), 0);
    e1 = select_exp (
        mbt, ((op >= IMPLIES && op <= IFF) ? BTORMBT_BO_T : BTORMBT_BB_T), 0);
    btormbt_binary_op (mbt, op, e0, e1);
  }
  else
  {
    assert (is_ternary_op (op));
    e0 = select_exp (mbt, BTORMBT_BO_T, 0);
    // TODO (ma): BTORMBT_BO_T also possible for e1 and e2
    e1 = select_exp (mbt, BTORMBT_BB_T, 0);
    e2 = select_exp (mbt, BTORMBT_BB_T, 0);
    btormbt_ternary_op (mbt, op, e0, e1, e2);
  }
  return (mbt->round.is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_arr_op (BtorMBT *mbt)
{
  uint32_t e0w, e0iw;
  BtorMBTOperator op;
  BoolectorNode *e0, *e1, *e2;

  e0   = select_exp (mbt, BTORMBT_ARR_T, 0);
  e0w  = boolector_get_width (mbt->btor, e0);
  e0iw = boolector_get_index_width (mbt->btor, e0);

  e2 = NULL;

  /* use read/write with p=0.666 else EQ/NE/COND */
  if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_rw))
  {
    op = btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_read) ? READ : WRITE;
    e1 = select_exp (mbt, BTORMBT_BV_T, 0);
    if (op == WRITE) e2 = select_exp (mbt, BTORMBT_BV_T, 0);
    btormbt_array_op (mbt, op, e0, e1, e2);
  }
  else
  {
    /* select EQ/NE/COND with same propability */
    if (!mbt->ext || btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_cond))
      op = COND;
    else
      op = btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_eq) ? EQ : NE;
    e1 = select_arr_exp (mbt, e0, e0w, e0iw, op == EQ || op == NE ? -1 : 0);
    if (op == COND) e2 = select_exp (mbt, BTORMBT_BO_T, 0);
    btormbt_array_op (mbt, op, e0, e1, e2);
  }

  return (mbt->round.is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_bv_uf (BtorMBT *mbt)
{
  btormbt_bv_uf (mbt);
  return mbt->round.is_init ? btormbt_state_main : btormbt_state_init;
}

static void *
btormbt_state_bv_fun (BtorMBT *mbt)
{
  assert (!mbt->parambo);
  assert (!mbt->parambv);
  assert (!mbt->paramarr);
  assert (!mbt->paramfun);

  btormbt_bv_fun (mbt, 0);
  assert (!mbt->parambo);
  assert (!mbt->parambv);
  assert (!mbt->paramarr);
  assert (!mbt->paramfun);
  return (mbt->round.is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_input (BtorMBT *mbt)
{
  // TODO (ma): UFs?
  if (mbt->create_arrays
      && btor_rng_pick_with_prob (&mbt->round.rng, mbt->round.p_array))
  {
    btormbt_array (mbt);
  }
  if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->round.p_var))
  {
    btormbt_var (mbt, BTORMBT_BB_T);
  }
  else
  {
    btormbt_const (mbt);
  }

  return (mbt->round.is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_release (BtorMBT *mbt)
{
  uint32_t idx, rand;
  BoolectorNode *node;
  BtorMBTExpStack *stack;

  /* select target exp stack with probabilty proportional to size */
  rand = btor_rng_pick_rand (&mbt->round.rng,
                             0,
                             BTOR_COUNT_STACK (mbt->bo->exps)
                                 + BTOR_COUNT_STACK (mbt->bv->exps)
                                 + BTOR_COUNT_STACK (mbt->arr->exps) - 1);
  if (rand < BTOR_COUNT_STACK (mbt->bo->exps))
    stack = mbt->bo;
  else if (rand < BTOR_COUNT_STACK (mbt->bo->exps)
                      + BTOR_COUNT_STACK (mbt->bv->exps))
    stack = mbt->bv;
  else
    stack = mbt->arr;
  if (BTOR_COUNT_STACK (stack->exps) > 1)
  {
    idx = btor_rng_pick_rand (
        &mbt->round.rng, 0, BTOR_COUNT_STACK (stack->exps) - 1);
    node = BTOR_PEEK_STACK (stack->exps, idx)->exp;
    assert (stack != mbt->bo || boolector_get_width (mbt->btor, node) == 1);
    assert (stack != mbt->bv || boolector_get_width (mbt->btor, node) > 1);
    assert (stack != mbt->arr || boolector_is_array (mbt->btor, node));
    btormbt_release_node (mbt, node);
    btormbt_del_exp_stack (mbt->mm, stack, idx);
  }
  return (mbt->round.is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_assume_assert (BtorMBT *mbt)
{
  BoolectorNode *node;

  node = btormbt_constraint (mbt);

  if (mbt->round.inc
      && btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_assume))
  {
    boolector_assume (mbt->btor, node);
    btormbt_push_exp_stack (mbt->mm, mbt->assumptions, node);
    mbt->round.assumes++;
  }
  else
  {
    boolector_assert (mbt->btor, node);
    btormbt_release_node (mbt, node);
    mbt->round.asserts++;
    mbt->round.asserts_tot++;
  }
  return btormbt_state_main;
}

static void *
btormbt_state_dump (BtorMBT *mbt)
{
  uint32_t tmppid;
  Btor *tmpbtor;
  FILE *outfile;
  int32_t len, pres, pstat;
  char *outfilename, *emsg, *envname = 0;
  uint32_t outformat;
  BoolectorNode *node;

  tmppid    = getpid ();
  outformat = boolector_get_opt (mbt->btor, BTOR_OPT_OUTPUT_FORMAT);

  if (outformat == BTOR_OUTPUT_FORMAT_AIGER_ASCII
      && !BTOR_COUNT_STACK (mbt->uf->exps) && !BTOR_COUNT_STACK (mbt->fun->exps)
      && !BTOR_COUNT_STACK (mbt->arr->exps))
  {
    boolector_dump_aiger_ascii (
        mbt->btor, stdout, btor_rng_pick_rand (&mbt->round.rng, 0, 1));
  }
  else if (outformat == BTOR_OUTPUT_FORMAT_AIGER_BINARY
           && !BTOR_COUNT_STACK (mbt->uf->exps)
           && !BTOR_COUNT_STACK (mbt->fun->exps)
           && !BTOR_COUNT_STACK (mbt->arr->exps))
  {
    boolector_dump_aiger_binary (
        mbt->btor, stdout, btor_rng_pick_rand (&mbt->round.rng, 0, 1));
  }
  else if ((outformat == BTOR_OUTPUT_FORMAT_BTOR
            || outformat == BTOR_OUTPUT_FORMAT_SMT2)
           // TODO: we cannot dump ite over functions to smt2/btor right now
           && mbt->round.num_ite_fun == 0)
  {
    len = 40 + strlen ("/tmp/btormbt-bug-.") + btor_util_num_digits (tmppid);
    BTOR_NEWN (mbt->mm, outfilename, len);

    if (outformat == BTOR_OUTPUT_FORMAT_BTOR
        // TODO: UF support in BTOR format not yet implemented
        && !BTOR_COUNT_STACK (mbt->uf->exps)
        // TODO: we cannot parse equality over lambdas in btor right now
        && mbt->round.num_eq_fun == 0)
    {
      sprintf (outfilename,
               "/tmp/btormbt-bug-%d%s",
               tmppid,
               btor_rng_pick_with_prob (&mbt->round.rng, 500) ? ".btor" : "");
      outfile = fopen (outfilename, "w");
      assert (outfile);
      boolector_dump_btor (mbt->btor, outfile);
    }
    else
    {
      sprintf (outfilename,
               "/tmp/btormbt-bug-%d%s",
               tmppid,
               btor_rng_pick_with_prob (&mbt->round.rng, 500) ? ".smt2" : "");
      outfile = fopen (outfilename, "w");
      assert (outfile);
      boolector_dump_smt2 (mbt->btor, outfile);
    }

    fclose (outfile);
    outfile = fopen (outfilename, "r");
    if ((envname = getenv ("BTORAPITRACE"))) unsetenv ("BTORAPITRACE");

    tmpbtor = boolector_new ();
    boolector_set_opt (tmpbtor, BTOR_OPT_PARSE_INTERACTIVE, 0);
    if (btor_rng_pick_with_prob (&mbt->round.rng, 500))
    {
      pres = boolector_parse (
          tmpbtor, outfile, outfilename, stdout, &emsg, &pstat);
      (void) pres;
      if (emsg) fprintf (stderr, "error while parsing dumped file: %s\n", emsg);
      assert (pres != BOOLECTOR_PARSE_ERROR);
    }
    else if (outformat == BTOR_OUTPUT_FORMAT_BTOR
             && !BTOR_COUNT_STACK (mbt->uf->exps)
             // TODO: we cannot parse equality over lambdas in btor right now
             && mbt->round.num_eq_fun == 0)
    {
      pres = boolector_parse_btor (
          tmpbtor, outfile, outfilename, stdout, &emsg, &pstat);
      (void) pres;
      if (emsg) fprintf (stderr, "error while parsing dumped file: %s\n", emsg);
      assert (pres != BOOLECTOR_PARSE_ERROR);
    }
    else
    {
      pres = boolector_parse_smt2 (
          tmpbtor, outfile, outfilename, stdout, &emsg, &pstat);
      (void) pres;
      if (emsg)
        fprintf (
            stderr, "btormbt: error while parsing dumped file: %s\n", emsg);
      assert (pres != BOOLECTOR_PARSE_ERROR);
    }
    (void) pstat;
    boolector_delete (tmpbtor);
    fclose (outfile);
    unlink (outfilename);
    BTOR_DELETEN (mbt->mm, outfilename, len);
    if (envname) setenv ("BTORAPITRACE", envname, 1);

    /* dump some random nodes, one per exp type */
    if (BTOR_COUNT_STACK (mbt->bo->exps))
    {
      node = BTOR_PEEK_STACK (
                 mbt->bo->exps,
                 btor_rng_pick_rand (
                     &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->bo->exps) - 1))
                 ->exp;
      if (outformat == BTOR_OUTPUT_FORMAT_BTOR)
        boolector_dump_btor_node (mbt->btor, stdout, node);
      else
        boolector_dump_smt2_node (mbt->btor, stdout, node);
    }
    if (BTOR_COUNT_STACK (mbt->bv->exps))
    {
      node = BTOR_PEEK_STACK (
                 mbt->bv->exps,
                 btor_rng_pick_rand (
                     &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->bv->exps) - 1))
                 ->exp;
      if (outformat == BTOR_OUTPUT_FORMAT_BTOR)
        boolector_dump_btor_node (mbt->btor, stdout, node);
      else
        boolector_dump_smt2_node (mbt->btor, stdout, node);
    }
    if (BTOR_COUNT_STACK (mbt->arr->exps))
    {
      node = BTOR_PEEK_STACK (
                 mbt->arr->exps,
                 btor_rng_pick_rand (
                     &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->arr->exps) - 1))
                 ->exp;
      if (outformat == BTOR_OUTPUT_FORMAT_BTOR)
        boolector_dump_btor_node (mbt->btor, stdout, node);
      else
        boolector_dump_smt2_node (mbt->btor, stdout, node);
    }
    if (BTOR_COUNT_STACK (mbt->uf->exps))
    {
      node = BTOR_PEEK_STACK (
                 mbt->uf->exps,
                 btor_rng_pick_rand (
                     &mbt->round.rng, 0, BTOR_COUNT_STACK (mbt->uf->exps) - 1))
                 ->exp;
      if (outformat == BTOR_OUTPUT_FORMAT_BTOR)
        boolector_dump_btor_node (mbt->btor, stdout, node);
      else
        boolector_dump_smt2_node (mbt->btor, stdout, node);
    }
  }

  return btor_rng_pick_with_prob (&mbt->round.rng, 500) ? btormbt_state_delete
                                                        : btormbt_state_main;
}

static void *
btormbt_state_sat (BtorMBT *mbt)
{
  size_t i;
  int32_t res;
  bool isfailed;
  BoolectorNode *ass;

  BTORMBT_LOG (1, "calling sat...");
  res = boolector_sat (mbt->btor);
  if (res == BOOLECTOR_UNSAT)
  {
    BTORMBT_LOG (1, "unsat");
    g_btormbtstats->num_unsat += 1;
  }
  else if (res == BOOLECTOR_SAT)
  {
    BTORMBT_LOG (1, "sat");
    g_btormbtstats->num_sat += 1;
  }
  else
    BTORMBT_LOG (1, "sat call returned %d", res);

  if (res == BOOLECTOR_UNSAT
      && boolector_get_opt (mbt->btor, BTOR_OPT_ENGINE) == BTOR_ENGINE_FUN)
  {
    if (!btor_rng_pick_with_prob (&mbt->round.rng, 500))
    {
      /* log failed assumptions */
      for (i = 0; i < BTOR_COUNT_STACK (mbt->assumptions->exps); i++)
      {
        ass = BTOR_PEEK_STACK (mbt->assumptions->exps, i)->exp;
        assert (ass);
        isfailed = boolector_failed (mbt->btor, ass);
        BTORMBT_LOG (1, "assumption %p failed: %d", ass, isfailed);
      }
    }
    else
    {
      BoolectorNode **failed = boolector_get_failed_assumptions (mbt->btor);
      for (i = 0; failed[i] != NULL; i++)
      {
        ass = failed[i];
        assert (ass);
        assert (boolector_failed (mbt->btor, ass));
      }
    }
  }

  if (mbt->round.shadow && !btor_rng_pick_with_prob (&mbt->round.rng, 100))
  {
    BTORMBT_LOG (1, "cloning...");
    assert (mbt->round.has_shadow == true);
    /* cleanup done by boolector */
    boolector_chkclone (mbt->btor);
    g_btormbtstats->num_shadow_clone += 1;
  }

  if (mbt->round.mgen && res == BOOLECTOR_SAT) return btormbt_state_query_model;
  if (mbt->round.inc && mbt->round.ninc < mbt->round.max_ninc)
    return btormbt_state_inc;
  return btormbt_state_delete;
}

static void *
btormbt_state_query_model (BtorMBT *mbt)
{
  size_t i;
  int32_t j, k;
  uint32_t size   = 0;
  const char *ass = NULL;
  char **indices = NULL, **values = NULL, *symbol;
  BoolectorNode *exp;
  BtorConstCharPtrStack bvass_stack;
  BtorCharPtrPtrStack funass_stack, ufass_stack;
  BtorIntStack arrsize_stack, ufsize_stack;
  BtorMBTExpStack *exp_stack;
  BtorMBTExpStack *exp_stacks[5] = {
      mbt->bo, mbt->bv, mbt->arr, mbt->fun, mbt->uf};

  assert (mbt->round.mgen);

  BTOR_INIT_STACK (mbt->mm, bvass_stack);
  BTOR_INIT_STACK (mbt->mm, funass_stack);
  BTOR_INIT_STACK (mbt->mm, ufass_stack);
  BTOR_INIT_STACK (mbt->mm, arrsize_stack);
  BTOR_INIT_STACK (mbt->mm, ufsize_stack);

  if (mbt->round.print_model)
  {
    if (btor_rng_pick_with_prob (&mbt->round.rng, mbt->p_model_format))
      boolector_print_model (mbt->btor, "btor", stdout);
    else
      boolector_print_model (mbt->btor, "smt2", stdout);
  }

  BTOR_CNEWN (mbt->mm, symbol, 20);
  for (k = 0; k < 5; k++)
  {
    exp_stack = exp_stacks[k];
    if (exp_stack == mbt->bo || exp_stack == mbt->bv)
      sprintf (symbol, "mbtass");
    else if (exp_stack == mbt->arr)
      sprintf (symbol, "mbtarr");
    else if (exp_stack == mbt->fun)
      sprintf (symbol, "mbtfun");
    else if (exp_stack == mbt->uf)
      sprintf (symbol, "mbtuf");

    for (i = 0; i < BTOR_COUNT_STACK (exp_stack->exps); i++)
    {
      exp = exp_stack->exps.start[i]->exp;
      if (exp_stack == mbt->bo || exp_stack == mbt->bv)
      {
        ass = boolector_bv_assignment (mbt->btor, exp);
        BTOR_PUSH_STACK (bvass_stack, ass);
      }
      else if (exp_stack == mbt->arr)
      {
        boolector_array_assignment (mbt->btor, exp, &indices, &values, &size);
        if (size > 0)
        {
          BTOR_PUSH_STACK (arrsize_stack, size);
          BTOR_PUSH_STACK (funass_stack, indices);
          BTOR_PUSH_STACK (funass_stack, values);
        }
      }
      else
      {
        assert (exp_stack == mbt->fun || exp_stack == mbt->uf);
        boolector_uf_assignment (mbt->btor, exp, &indices, &values, &size);
        if (size > 0)
        {
          BTOR_PUSH_STACK (ufsize_stack, size);
          BTOR_PUSH_STACK (ufass_stack, indices);
          BTOR_PUSH_STACK (ufass_stack, values);
        }
      }
      boolector_print_value_smt2 (
          mbt->btor,
          exp,
          btor_rng_pick_with_prob (&mbt->round.rng, 500) ? symbol : 0,
          stdout);
    }
  }
  BTOR_DELETEN (mbt->mm, symbol, 20);

  if (mbt->round.shadow && !btor_rng_pick_with_prob (&mbt->round.rng, 100))
  {
    BTORMBT_LOG (1, "cloning...");
    assert (mbt->round.has_shadow == true);
    /* cleanup done by boolector */
    boolector_chkclone (mbt->btor);
    g_btormbtstats->num_shadow_clone += 1;
  }

  /* release assignments */
  while (!BTOR_EMPTY_STACK (bvass_stack))
    boolector_free_bv_assignment (mbt->btor, BTOR_POP_STACK (bvass_stack));
  BTOR_RELEASE_STACK (bvass_stack);
  for (i = 0, j = 0; i < BTOR_COUNT_STACK (arrsize_stack); i++, j += 2)
  {
    size    = BTOR_PEEK_STACK (arrsize_stack, i);
    indices = BTOR_PEEK_STACK (funass_stack, j);
    values  = BTOR_PEEK_STACK (funass_stack, j + 1);
    boolector_free_array_assignment (mbt->btor, indices, values, size);
  }
  BTOR_RELEASE_STACK (funass_stack);
  BTOR_RELEASE_STACK (arrsize_stack);
  for (i = 0, j = 0; i < BTOR_COUNT_STACK (ufsize_stack); i++, j += 2)
  {
    size    = BTOR_PEEK_STACK (ufsize_stack, i);
    indices = BTOR_PEEK_STACK (ufass_stack, j);
    values  = BTOR_PEEK_STACK (ufass_stack, j + 1);
    boolector_free_uf_assignment (mbt->btor, indices, values, size);
  }
  BTOR_RELEASE_STACK (ufass_stack);
  BTOR_RELEASE_STACK (ufsize_stack);

  if (mbt->round.inc && mbt->round.ninc < mbt->round.max_ninc)
    return btormbt_state_inc;

  return btormbt_state_delete;
}

static void *
btormbt_state_inc (BtorMBT *mbt)
{
  mbt->round.ninc += 1;
  g_btormbtstats->num_inc += 1;

  btormbt_reset_assumptions (mbt);

  /* reset / reinit */
  mbt->round.ops     = 0;
  mbt->round.max_ass = mbt->round.max_ass - mbt->round.asserts;
  mbt->round.assumes = 0;
  mbt->round.asserts = 0;

  mbt->round.max_ops =
      btor_rng_pick_rand (&mbt->round.rng, mbt->ops.inc.min, mbt->ops.inc.max);

  init_pd_inputs (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->vars.inc.min, mbt->vars.inc.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->consts.inc.min, mbt->consts.inc.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->arrays.inc.min, mbt->arrays.inc.max));

  init_pd_ops (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_ops.inc.min, mbt->add_ops.inc.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->release_ops.inc.min, mbt->release_ops.inc.max));

  init_pd_add (
      mbt,
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_funs.inc.min, mbt->add_funs.inc.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_uf.inc.min, mbt->add_uf.inc.max),
      btor_rng_pick_rand (&mbt->round.rng,
                          mbt->add_arrayops.inc.min,
                          mbt->add_arrayops.inc.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_bvops.inc.min, mbt->add_bvops.inc.max),
      btor_rng_pick_rand (
          &mbt->round.rng, mbt->add_inputs.inc.min, mbt->add_inputs.inc.max));

  BTORMBT_LOG (1,
               "inc: pick %u ops (add:rel=%0.1f%%:%0.1f%%)",
               mbt->round.max_ops,
               (double) mbt->round.p_add / 10,
               (double) mbt->round.p_release / 10);
  BTORMBT_LOG (1, "number of increments: %u", mbt->round.ninc);

  return btormbt_state_main;
}

static void *
btormbt_state_delete (BtorMBT *mbt)
{
  assert (mbt);
  assert (mbt->btor);

  bool release_all;

  release_all = btor_rng_pick_with_prob (&mbt->round.rng, 100);

  RELEASE_EXP_STACK (bo, !release_all);
  RELEASE_EXP_STACK (bv, !release_all);
  RELEASE_EXP_STACK (arr, !release_all);
  RELEASE_EXP_STACK (fun, !release_all);
  RELEASE_EXP_STACK (uf, !release_all);
  RELEASE_EXP_STACK (assumptions, !release_all);

  RELEASE_SORT_STACK (bv_sorts);
  RELEASE_SORT_STACK (fun_sorts);

  assert (mbt->parambo == NULL);
  assert (mbt->parambv == NULL);
  assert (mbt->paramarr == NULL);
  assert (mbt->paramfun == NULL);

  if (release_all) boolector_release_all (mbt->btor);
  assert (boolector_get_refs (mbt->btor) == 0);
  boolector_delete (mbt->btor);
  mbt->btor = NULL;
  return 0;
}

/*------------------------------------------------------------------------*/

static void
reset_round_data (BtorMBT *mbt)
{
  /* (re)init */
  assert (!mbt->assumptions);
  assert (!mbt->bo);
  assert (!mbt->bv);
  assert (!mbt->arr);
  assert (!mbt->fun);
  assert (!mbt->uf);
  assert (!mbt->parambo);
  assert (!mbt->parambv);
  assert (!mbt->paramarr);
  assert (!mbt->paramfun);
  assert (!mbt->bv_sorts);
  assert (!mbt->fun_sorts);

  memset (&mbt->round, 0, sizeof (mbt->round));

  mbt->assumptions = btormbt_new_exp_stack (mbt->mm);
  mbt->bo          = btormbt_new_exp_stack (mbt->mm);
  mbt->bv          = btormbt_new_exp_stack (mbt->mm);
  mbt->arr         = btormbt_new_exp_stack (mbt->mm);
  mbt->fun         = btormbt_new_exp_stack (mbt->mm);
  mbt->uf          = btormbt_new_exp_stack (mbt->mm);
  mbt->bv_sorts    = btormbt_new_sort_stack (mbt->mm);
  mbt->fun_sorts   = btormbt_new_sort_stack (mbt->mm);
  btor_rng_init (&mbt->round.rng, mbt->seed);
}

static int32_t
run (BtorMBT *mbt)
{
  assert (mbt);

  BtorMBTState state, next;
  int32_t status, null;
  pid_t id;

  if (!mbt->seeded && (id = fork ()))
  {
    mbt->forked++;
    fflush (stdout);
#ifdef BTOR_HAVE_SIGNALS
    reset_alarm ();
#endif
#ifndef NDEBUG
    pid_t wid =
#endif
        wait (&status);
    assert (wid == id);
  }
  else
  {
#ifdef BTOR_HAVE_SIGNALS
    if (g_set_alarm)
    {
      set_alarm ();
      BTORMBT_LOG (1, "set time limit to %d second(s)", g_set_alarm);
    }
#endif

    /* redirect output from child to /dev/null if we don't want to have
     * verbose output */
    if (!mbt->seeded || !mbt->verbosity)
    {
      null = open ("/dev/null", O_WRONLY);
      dup2 (null, STDOUT_FILENO);
      /* do not redirect stderr if run is seeded (we want to see the failed
       * assertion or error msg) */
      if (!mbt->seeded) dup2 (null, STDERR_FILENO);
      close (null);
    }

    /* (re)init */
    reset_round_data (mbt);

    /* start traversing states */
    for (state = btormbt_state_new; state; state = next) next = state (mbt);

    btormbt_delete_btormbt (g_btormbt);
    exit (EXIT_OK);
  }

  return status;
}

/*------------------------------------------------------------------------*/

int32_t
main (int32_t argc, char **argv)
{
  int32_t exitcode;
  int32_t i, mac, pid, prev, res, status;
  size_t j;
  uint32_t val;
  char *name, *cmd, *tmp;
  int32_t namelen, cmdlen, tmppid, fd;
  BtorMBTBtorOpt *btoropt, *tmpopt;

  g_btormbt             = btormbt_new_btormbt ();
  g_btormbt->start_time = current_time ();

  pid      = 0;
  prev     = 0;
  exitcode = 0;
  namelen  = 0;

  for (i = 1; i < argc; i++)
  {
    /* general options */
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
    {
      printf ("%s", BTORMBT_USAGE);
      exitcode = EXIT_OK;
      goto EXIT;
    }
    else if (!strcmp (argv[i], "-v"))
    {
      g_btormbt->verbosity++;
    }
    else if (!strcmp (argv[i], "-q"))
    {
      g_btormbt->quiet = true;
    }
    else if (!strcmp (argv[i], "-s"))
    {
      if (++i == argc) btormbt_error ("argument to '-s' missing (try '-h')");
      if (!is_num_str (argv[i]))
        btormbt_error ("argument '%s' to '-s' is not a number (try '-h')",
                       argv[i]);
      g_btormbt->fshadow = atoi (argv[i]);
      if (g_btormbt->fshadow != 0 && g_btormbt->fshadow != 1)
        btormbt_error ("invalid argument to '-s' (try '-h')");
      g_btormbt->fshadow =
          g_btormbt->fshadow ? FORCE_SHADOW_TRUE : FORCE_SHADOW_FALSE;
    }
    else if (!strcmp (argv[i], "-o"))
    {
      g_btormbt->optfuzz = false;
    }
    else if (!strcmp (argv[i], "-O"))
    {
      if (++i == argc) btormbt_error ("argument to '-O' missing (try '-h')");
      if (argv[i][0] == '-')
        btormbt_error ("invalid output directory given (try '-h')");
      g_btormbt->out = argv[i];
      DIR *dir       = opendir (argv[i]);
      if (dir)
        closedir (dir);
      else
        btormbt_error ("given output directory does not exist");
    }
    else if (!strcmp (argv[i], "-f"))
    {
      g_btormbt->quit_after_first = true;
    }
    else if (!strcmp (argv[i], "-m"))
    {
      if (++i == argc) btormbt_error ("argument to '-m' missing (try '-h')");
      if (!is_num_str (argv[i]))
        btormbt_error ("argument '%s' to '-m' is not a number (try '-h')",
                       argv[i]);
      g_btormbt->max_rounds = atoi (argv[i]);
    }
#ifdef BTOR_HAVE_SIGNALS
    else if (!strcmp (argv[i], "-t"))
    {
      if (++i == argc) btormbt_error ("argument to '-t' missing (try '-h')");
      if (!is_num_str (argv[i]))
        btormbt_error ("argument '%s' to '-t' is not a number (try '-h')",
                       argv[i]);
      g_set_alarm = atoi (argv[i]);
    }
#endif
    else if (!strncmp (argv[i], "--logic", 7))
    {
      if (++i == argc)
        btormbt_error ("argument to '--logic' missing (try '-h')");
      g_btormbt->is_flogic = true;
      if (!strcmp (argv[i], "QF_BV"))
        g_btormbt->flogic = BTORMBT_LOGIC_QF_BV;
      else if (!strcmp (argv[i], "QF_ABV"))
        g_btormbt->flogic = BTORMBT_LOGIC_QF_ABV;
      else if (!strcmp (argv[i], "QF_AUFBV"))
        g_btormbt->flogic = BTORMBT_LOGIC_QF_AUFBV;
      else if (!strcmp (argv[i], "QF_UFBV"))
        g_btormbt->flogic = BTORMBT_LOGIC_QF_UFBV;
      else
      {
        btormbt_error ("invalid argument to '--logic' (try '-h')");
      }
    }
    /* boolector options */
    else if (!strcmp (argv[i], "-b"))
    {
      if (++i == argc) btormbt_error ("argument to '-b' missing (try '-h')");
      assert (BTOR_COUNT_STACK (g_btormbt->btor_opts));
      for (j = 0, btoropt = 0; j < BTOR_COUNT_STACK (g_btormbt->btor_opts); j++)
      {
        tmpopt = BTOR_PEEK_STACK (g_btormbt->btor_opts, j);
        assert (tmpopt);
        if (!strcmp (tmpopt->name, argv[i])
            || (tmpopt->shrt && !strcmp (tmpopt->shrt, argv[i])))
        {
          btoropt = tmpopt;
          break;
        }
      }
      if (!btoropt) btormbt_error ("invalid boolector option '%s'", argv[i]);
      if (++i == argc) btormbt_error ("argument to '-b' missing (try '-h')");
      val = (uint32_t) strtol (argv[i], &tmp, 10);
      if (tmp[0] != 0) btormbt_error ("invalid argument to '-b' (try '-h')");
      btoropt->val = val;
#if !defined(BTOR_USE_LINGELING) && !defined(BTOR_USE_PICOSAT) \
    && !defined(BTOR_USE_MINISAT)
      if (btoropt->kind == BTOR_OPT_INCREMENTAL)
      {
        btormbt_error ("no SAT solver with incremental support compiled in");
      }
#endif
      btoropt->forced_by_cl = true;
    }
    else if (!is_num_str (argv[i]))
    {
      btormbt_error ("invalid command line option '%s' (try '-h')", argv[i]);
    }
    else
    {
      g_btormbt->seed   = atoi (argv[i]);
      g_btormbt->seeded = true;
    }
  }

  g_btormbt->ppid = getpid ();
#ifdef BTOR_HAVE_SIGNALS
  set_sig_handlers ();
#endif

  /* open shared memory file for statistics */
  sprintf (g_shmfilename, "/tmp/btormbt-shm-%d", getpid ());
  if ((fd = open (g_shmfilename, O_RDWR | O_CREAT, S_IRWXU)) < 0)
    btormbt_error ("failed to create shared memory file");
  g_btormbtstats = mmap (0,
                         sizeof (BtorMBTStatistics),
                         PROT_READ | PROT_WRITE,
                         MAP_ANONYMOUS | MAP_SHARED,
                         fd,
                         0);
  if (close (fd)) btormbt_error ("failed to close shared memory file");
  (void) unlink (g_shmfilename);
  memset (g_btormbtstats, 0, sizeof (BtorMBTStatistics));

  mac = hash_mac ();
  for (g_btormbt->rounds = 0; g_btormbt->rounds < g_btormbt->max_rounds;
       g_btormbt->rounds++)
  {
    if (!(prev & 1)) prev++;

    if (!g_btormbt->seeded)
    {
      g_btormbt->seed = mac;
      g_btormbt->seed *= 123301093;
      g_btormbt->seed += times (0);
      g_btormbt->seed *= 223531513;
      g_btormbt->seed += pid;
      g_btormbt->seed *= 31752023;
      g_btormbt->seed += prev;
      g_btormbt->seed *= 43376579;
      prev = g_btormbt->seed = g_btormbt->seed >> 1;

      if (!g_btormbt->quiet)
      {
        if (g_btormbt->terminal) erase ();
        printf ("%d %d ", g_btormbt->rounds, g_btormbt->seed);
        fflush (stdout);
      }

      /* reset verbosity flag for initial run, only print on replay */
      status = run (g_btormbt);
    }
    else
      status = run (g_btormbt);

    if (WIFEXITED (status))
      res = WEXITSTATUS (status);
    else if (WIFSIGNALED (status))
      res = EXIT_SIGNALED;
    else
      res = EXIT_UNKNOWN;

    /* replay run on error */
    if (!g_btormbt->seeded && res == EXIT_ERROR)
    {
      g_btormbt->bugs++;

      if (!(name = getenv ("BTORAPITRACE")))
      {
        tmppid  = getpid ();
        namelen = 40 + btor_util_num_digits (tmppid);
        BTOR_NEWN (g_btormbt->mm, name, namelen);
        sprintf (name, "/tmp/bug-%d-mbt.trace", tmppid);
        /* replay run */
        setenv ("BTORAPITRACE", name, 1);
        i = run (g_btormbt);
        assert (WIFEXITED (i));
        assert (WEXITSTATUS (i) == res);
        unsetenv ("BTORAPITRACE");
      }

      if (g_btormbt->out)
      {
        cmdlen = 40 + strlen (name) + strlen (g_btormbt->out)
                 + btor_util_num_digits (g_btormbt->seed);
        BTOR_NEWN (g_btormbt->mm, cmd, cmdlen);
        sprintf (cmd,
                 "cp %s %s/btormbt-bug-%d.trace",
                 name,
                 g_btormbt->out,
                 g_btormbt->seed);
      }
      else
      {
        cmdlen = 40 + strlen (name) + btor_util_num_digits (g_btormbt->seed);
        BTOR_NEWN (g_btormbt->mm, cmd, cmdlen);
        sprintf (cmd, "cp %s btormbt-bug-%d.trace", name, g_btormbt->seed);
      }

      if (!getenv ("BTORAPITRACE")) BTOR_DELETEN (g_btormbt->mm, name, namelen);

      if (system (cmd))
      {
        printf ("Error on copy command %s \n", cmd);
        exitcode = EXIT_ERROR;
        goto DONE;
      }

      BTOR_DELETEN (g_btormbt->mm, cmd, cmdlen);
    }

    if (res == EXIT_SIGNALED)
    {
      if (g_btormbt->verbosity) printf ("signal %d", WTERMSIG (status));
    }
    else if (res == EXIT_UNKNOWN)
    {
      if (g_btormbt->verbosity) printf ("unknown");
    }
#ifdef BTOR_HAVE_SIGNALS
    else if (res == EXIT_TIMEOUT)
    {
      BTORMBT_LOG (1, "TIMEOUT: time limit %d seconds reached\n", g_set_alarm);
      if (!g_btormbt->verbosity)
        printf ("timed out after %d second(s)\n", g_set_alarm);
    }
#endif
    else if (res == EXIT_ERROR)
    {
      if (g_btormbt->quiet) printf ("%d ", g_btormbt->seed);
      printf ("exit %d\n", res);
    }

    if (g_btormbt->rounds && g_btormbt->rounds % 10000 == 0)
    {
      printf ("\n");
      btormbt_print_stats (g_btormbt);
    }

    if ((res == EXIT_ERROR && g_btormbt->quit_after_first) || g_btormbt->seeded)
      break;
  }

  if (g_btormbt->verbosity)
  {
    if (g_btormbt->terminal) erase ();
    printf ("forked %d\n", g_btormbt->forked);
  }

DONE:
  if (!g_btormbt->quit_after_first && !g_btormbt->seeded)
    btormbt_print_stats (g_btormbt);
EXIT:
  if (munmap (g_btormbtstats, sizeof (BtorMBTStatistics)))
    btormbt_error ("failed to unmap shared memory");
  btormbt_delete_btormbt (g_btormbt);
  exit (exitcode);
}
