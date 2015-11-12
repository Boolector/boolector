/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Christian Reisenberger.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2013-2014 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolector.h"
#include "btorcore.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"
// FIXME (ma): external sort handling?
#include "btoropt.h"
#include "btorsort.h"

#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

#define NORM_VAL 1000.0f

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
#define MIN_NASSERTS_LOWER 5
#define MAX_NASSERTS_LOWER 25
#define MIN_NASSERTS_UPPER 20
#define MAX_NASSERTS_UPPER 30

#define P_SORT_BV 0.5
#define P_SORT_FUN 0.5
#define P_SORT_FUN_UNARY 0.1
#define P_ASSUME 0.8
#define P_PARAM_EXP 0.5
#define P_PARAM_ARR_EXP 0.5
#define P_APPLY_FUN 0.5
#define P_APPLY_UF 0.5
#define P_RW 0.66
#define P_READ 0.5
#define P_COND 0.33
#define P_EQ 0.5
#define P_INC 0.33
#define P_DUMP 0.1
#define P_PRINT_MODEL 0.1
#define P_MODEL_FORMAT 0.5

#define EXIT_OK 0
#define EXIT_ERROR 1
#define EXIT_TIMEOUT 2
#define EXIT_SIGNALED 3
#define EXIT_UNKNOWN 4

/*------------------------------------------------------------------------*/

#define BTORMBT_STR(str) #str
#define BTORMBT_M2STR(m) BTORMBT_STR (m)

/*------------------------------------------------------------------------*/

#define BTORMBT_USAGE                                                          \
  "usage: mbt [<option>]\n"                                                    \
  "\n"                                                                         \
  "where <option> is one of the following:\n"                                  \
  "\n"                                                                         \
  "  -h, --help                       print this message and exit\n"           \
  "  -ha, --help-advanced             print all options\n"                     \
  "\n"                                                                         \
  "  -v, --verbose                    be extra verbose\n"                      \
  "  -q, --quiet                      be extra quiet (stats only)\n"           \
  "  -k, --keep-lines                 do not clear output lines\n"             \
  "\n"                                                                         \
  "  -s, --shadow                     create and check shadow clone\n"         \
  "  -o, --out                        output directory for saving traces\n"    \
  "  -f, --quit-after-first           quit after first bug encountered\n"      \
  "  -m <maxruns>                     quit after <maxruns> rounds\n"           \
  "  -t <seconds>                     set time limit for calls to boolector\n" \
  "\n"                                                                         \
  "  --logic <logic>                  generate <logic> formulas only, "        \
  "available\n"                                                                \
  "                                   logics are: QF_BV,QF_UFBV,QF_ABV,"       \
  "QF_AUFBV\n"                                                                 \
  "                                   (default: QF_AUFBV)\n"                   \
  "  -e, --extensionality             use extensionality\n"                    \
  "  -b <btoropt> <val>               set boolector option <btoropt>\n"

/*------------------------------------------------------------------------*/

#define BTORMBT_USAGE_ADVANCED \
  "\n" \
  "-------------------------------------------------------------------------\n"\
  "\nadvanced options:\n\n" \
  "  --bw <min> <max>                 bit width (min: " \
                                      BTORMBT_M2STR (MIN_BITWIDTH) ") [" \
                                      BTORMBT_M2STR (MIN_BITWIDTH) " "\
                                      BTORMBT_M2STR (MAX_BITWIDTH) "]\n" \
  "  --index-bw <min> <max>           index bit width (min: " \
                                      BTORMBT_M2STR (MIN_INDEXWIDTH) ") [" \
                                      BTORMBT_M2STR (MIN_INDEXWIDTH) " " \
                                      BTORMBT_M2STR (MAX_INDEXWIDTH) "]\n" \
  "  --muldiv-bw <min> <max>          bit width for mul/div (min: " \
                                      BTORMBT_M2STR (MIN_MULDIVWIDTH) ") [" \
                                      BTORMBT_M2STR (MIN_MULDIVWIDTH) " " \
                                      BTORMBT_M2STR (MAX_MULDIVWIDTH) "]\n" \
  "\n" \
  "  --sort-fun-arity <min> <max>     fun sort min and max arity [" \
                                      BTORMBT_M2STR (MIN_SORT_FUN_ARITY) \
                                      BTORMBT_M2STR (MAX_SORT_FUN_ARITY) \
                                     "]\n" \
  "\n" \
  "  --inputs <min> <max>             num inputs [" \
                                      BTORMBT_M2STR (MIN_NLITS) " " \
                                      BTORMBT_M2STR (MAX_NLITS) "]\n" \
  "  --vars-init <min> <max>          num vars for initial layer [" \
                                      BTORMBT_M2STR (MIN_NVARS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NVARS_INIT) "]\n" \
  "  --vars <min> <max>               num vars after initial layer [" \
                                      BTORMBT_M2STR (MIN_NVARS) " " \
                                      BTORMBT_M2STR (MAX_NVARS) "]\n" \
  "  --vars-inc <min> <max>           num vars for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NVARS_INC) " " \
                                      BTORMBT_M2STR (MAX_NVARS_INC) "]\n" \
  "  --consts-init <min> <max>        num constants for initial layer [" \
                                      BTORMBT_M2STR (MIN_NCONSTS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NCONSTS_INIT) "]\n" \
  "  --consts <min> <max>             num constants after initial " \
                                     "layer [" \
                                      BTORMBT_M2STR (MIN_NCONSTS) " " \
                                      BTORMBT_M2STR (MAX_NCONSTS) "]\n" \
  "  --consts-inc <min> <max>         num constants for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NCONSTS_INC) " " \
                                      BTORMBT_M2STR (MAX_NCONSTS_INC) "]\n" \
  "  --arrays-init <min> <max>        num arrays for initial layer [" \
                                      BTORMBT_M2STR (MIN_NARRS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NARRS_INIT) "]\n" \
  "  --arrays <min> <max>             num arrays after initial layer [" \
                                      BTORMBT_M2STR (MIN_NARRS) " " \
                                      BTORMBT_M2STR (MAX_NARRS) "]\n" \
  "  --arrays-inc <min> <max>         num arrays for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NARRS_INC) " " \
                                      BTORMBT_M2STR (MAX_NARRS_INC) "]\n" \
  "  --ops-init <min> <max>           num ops for init layer [" \
                                      BTORMBT_M2STR (MIN_NOPS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NOPS_INIT) "]\n" \
  "  --ops <min> <max>                num ops after init layer [" \
                                      BTORMBT_M2STR (MIN_NOPS) " " \
                                      BTORMBT_M2STR (MAX_NOPS) "]\n" \
  "  --ops-inc <min> <max>            num ops for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NOPS_INC) " " \
                                      BTORMBT_M2STR (MAX_NOPS_INC) "]\n" \
  "\n" \
  "  --max-ops-lower <val>            lower bound for max-ops in current " \
                                     "round [" \
                                      BTORMBT_M2STR (MAX_NOPS_LOWER) "]\n" \
  "\n" \
  "  --asserts-lower <min> <max>      num assertions for current\n" \
  "                                     max-ops < max-ops-lower [" \
                                      BTORMBT_M2STR (MIN_NASSERTS_LOWER) " " \
                                      BTORMBT_M2STR (MAX_NASSERTS_LOWER) "]\n" \
  "  --asserts-upper <min> <max>      num assertions for current\n" \
  "                                    max-ops >= max-ops-lower [" \
                                      BTORMBT_M2STR (MIN_NASSERTS_UPPER) " " \
                                      BTORMBT_M2STR (MAX_NASSERTS_UPPER) "]\n" \
  "\n add/release phase options:\n" \
  "  --add-ops-init <min> <max>       num add ops for init layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NADDOPS_INIT) "]\n" \
  "  --add-ops <min> <max>            num add ops after init layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPS) " " \
                                      BTORMBT_M2STR (MAX_NADDOPS) "]\n" \
  "  --add-ops-inc <min> <max>        num add ops for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NADDOPS_INC) " " \
                                      BTORMBT_M2STR (MAX_NADDOPS_INC) "]\n" \
  "  --release-ops-init <min> <max>   num release ops for init layer [" \
                                      BTORMBT_M2STR (MIN_NRELOPS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NRELOPS_INIT) "]\n" \
  "  --release-ops <min> <max>        num release ops after init layer ["\
                                      BTORMBT_M2STR (MIN_NRELOPS) " " \
                                      BTORMBT_M2STR (MAX_NRELOPS) "]\n" \
  "  --release-ops-inc <min> <max>    num release ops for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NRELOPS_INC) " " \
                                      BTORMBT_M2STR (MAX_NRELOPS_INC) "]\n" \
  "  --add-funs-init <min> <max>      num funs for initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPFUNS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NADDOPFUNS_INIT)"]\n"\
  "  --add-funs <min> <max>           num funs after initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPFUNS) " " \
                                      BTORMBT_M2STR (MAX_NADDOPFUNS) "]\n" \
  "  --add-funs-inc <min> <max>       num funs for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NADDOPFUNS_INC) " " \
                                      BTORMBT_M2STR (MAX_NADDOPFUNS_INC) "]\n" \
  "  --add-arrayops-init <min> <max>  num array ops for initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPAFUNS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NADDOPAFUNS_INIT)"]\n"\
  "  --add-arrayops <min> <max>       num array ops after initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPAFUNS) " " \
                                      BTORMBT_M2STR (MAX_NADDOPAFUNS) "]\n" \
  "  --add-arrayops-inc <min> <max>   num array ops for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NADDOPAFUNS_INC) " " \
                                      BTORMBT_M2STR (MAX_NADDOPAFUNS_INC) "]\n"\
  "  --add-bitvecops-init <min> <max> num bv ops for initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPBFUNS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NADDOPBFUNS_INIT)"]\n"\
  "  --add-bitvecops <min> <max>      num bv ops after initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPBFUNS) " " \
                                      BTORMBT_M2STR (MAX_NADDOPBFUNS) "]\n" \
  "  --add-bitvecops-inc <min> <max>  num bv ops for reinit. inc. step [" \
                                      BTORMBT_M2STR (MIN_NADDOPBFUNS_INC) " " \
                                      BTORMBT_M2STR (MAX_NADDOPBFUNS_INC) "]\n"\
  "  --add-inputs-init <min> <max>    num inputs for initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPLITS_INIT) " " \
                                      BTORMBT_M2STR (MAX_NADDOPLITS_INIT) "]\n"\
  "  --add-inputs <min> <max>         num inputs after initial layer [" \
                                      BTORMBT_M2STR (MIN_NADDOPLITS) " " \
                                      BTORMBT_M2STR (MAX_NADDOPLITS) "]\n" \
  "  --add-inputs-inc <min> <max>     num inputs for reinit. inc. step ["\
                                      BTORMBT_M2STR (MIN_NADDOPLITS_INC) " " \
                                      BTORMBT_M2STR (MAX_NADDOPLITS_INC) "]\n" \
  "\n probability options:\n" \
  "  --p-sort-bv <val>                choose existing over new bv sort [" \
                                      BTORMBT_M2STR (P_SORT_BV) "]\n" \
  "  --p-sort-fun <val>               choose existing over new fun sort [" \
                                      BTORMBT_M2STR (P_SORT_FUN) "]\n" \
  "  --p-sort-fun-unary <val>         choose unary fun sort [" \
                                      BTORMBT_M2STR (P_SORT_FUN_UNARY) "]\n" \
  "  --p-assume <val>                 choose assumption over assertion in \n" \
  "                                   incremental mode [" \
                                      BTORMBT_M2STR (P_ASSUME) "] \n" \
  "  --p-param-exp <val>              choose parameterized over\n" \
  "                                   non-parameterized expressions [" \
                                      BTORMBT_M2STR (P_PARAM_EXP) "]\n" \
  "  --p-param-arr-exp <val>          choose parameterized over\n" \
  "                                   non-parameterized array expressions [" \
                                      BTORMBT_M2STR (P_PARAM_ARR_EXP) "]\n" \
  "  --p-apply-fun <val>              choose apply on existing over new\n"\
  "                                   function [" \
                                      BTORMBT_M2STR (P_APPLY_FUN) "]\n" \
  "  --p-apply-uf <val>               choose apply on existing over new\n"\
  "                                   uninterpreted function [" \
                                      BTORMBT_M2STR (P_APPLY_UF) "]\n" \
  "  --p-rw <val>                     choose read/write over eq/ne/cond [" \
                                      BTORMBT_M2STR (P_RW) "]\n" \
  "  --p-read <val>                   choose read over write [" \
                                      BTORMBT_M2STR (P_READ) "]\n" \
  "  --p-cond <val>                   choose cond over eq/ne [" \
                                      BTORMBT_M2STR (P_COND) "]\n" \
  "  --p-eq <val>                     choose eq over ne [" \
                                      BTORMBT_M2STR (P_EQ) "]\n" \
  "  --p-inc <val>                    choose an incremental step [" \
                                      BTORMBT_M2STR (P_INC) "]\n" \
  "  --p-dump <val>                   dump formula [" \
                                      BTORMBT_M2STR (P_DUMP) "]\n" \
  "  --p-print-model <val>            print model [" \
                                      BTORMBT_M2STR (P_PRINT_MODEL) "]\n" \
  "  --p-model-format <val>           model format (btor:smt2) [" \
                                      BTORMBT_M2STR (P_MODEL_FORMAT) "]\n" \
  "\n other options:\n" \
  "  --output-format <string>         force dump/model output format\n" \
  "                                   available formats are: btor,smt1,smt2\n"

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

#define BTORMBT_LOG_STATUS(l, prefix)                                        \
  BTORMBT_LOG (l,                                                            \
               prefix " (%d): bool %ld, bv %ld, array %ld, fun %ld, uf %ld", \
               g_btormbt->ops,                                               \
               BTOR_COUNT_STACK (g_btormbt->bo->exps),                       \
               BTOR_COUNT_STACK (g_btormbt->bv->exps),                       \
               BTOR_COUNT_STACK (g_btormbt->arr->exps),                      \
               BTOR_COUNT_STACK (g_btormbt->fun->exps),                      \
               BTOR_COUNT_STACK (g_btormbt->uf->exps));

/*------------------------------------------------------------------------*/

#define BTORMBT_MIN(x, y) ((x) < (y) ? (x) : (y))

/*------------------------------------------------------------------------*/

typedef struct RNG
{
  unsigned z, w;
} RNG;

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
  assert (from <= to);

  unsigned tmp;

  to  = to == UINT_MAX ? UINT_MAX - 1 : to;
  tmp = nextrand (rng_ptr);
  tmp %= to - from + 1;
  tmp += from;
  return tmp;
}

/*------------------------------------------------------------------------*/

typedef enum Op
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
  APPLY,
  /* do not remove */
  BTORMBT_NUM_OPS
} Op;

const char *const g_op2str[] = {
    "param",   "fun",   "uf",    "const", "zero",  "false",  "ones",   "true",
    "one",     "uint",  "int",   "var",   "array", "not",    "neg",    "slice",
    "inc",     "dec",   "uext",  "sext",  "redor", "redxor", "redand", "eq",
    "ne",      "uaddo", "saddo", "usubo", "ssubo", "umulo",  "smulo",  "sdivo",
    "ult",     "slt",   "ulte",  "slte",  "ugt",   "sgt",    "ugte",   "sgte",
    "implies", "iff",   "xor",   "xnor",  "and",   "nand",   "or",     "nor",
    "add",     "sub",   "mul",   "udiv",  "sdiv",  "urem",   "srem",   "smod",
    "sll",     "srl",   "sra",   "rol",   "ror",   "concat", "cond",   "read",
    "write",   "apply",
};

static int
is_unary_op (Op op)
{
  return op >= NOT && op <= REDAND;
}

static int
is_boolean_unary_op (Op op)
{
  return (op >= REDOR && op <= REDAND);
}

static int
is_binary_op (Op op)
{
  return (op >= EQ && op <= CONCAT);
}

static int
is_boolean_binary_op (Op op)
{
  return (op >= EQ && op <= IFF);
}

#ifndef NDEBUG
static int
is_ternary_op (Op op)
{
  return op == COND;
}

static int
is_array_op (Op op)
{
  return (op >= COND && op <= WRITE) || (op >= EQ && op <= NE);
}
#endif

/*------------------------------------------------------------------------*/

typedef struct BtorMBT BtorMBT;
static void btormbt_release_node (BtorMBT *mbt, BoolectorNode *node);

struct BtorMBTBtorOpt
{
  char *name;
  char *shrt;
  int val; /* only used for options specified via command line */
  int min;
  int max;
  bool set_by_cl; /* if option is already set by command line, we do not
                     choose a random value for this option */
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
  unsigned parents; /* number of parents */
};

typedef struct BtorMBTExp BtorMBTExp;

BTOR_DECLARE_STACK (BtorMBTExpPtr, BtorMBTExp *);

struct BtorMBTExpStack
{
  BtorMBTExpPtrStack exps;
  int last_pos_parents; /* position of last parents check */
  int init_layer_size;  /* size of initial layer */
};

typedef struct BtorMBTExpStack BtorMBTExpStack;

static BtorMBTExpStack *
btormbt_new_exp_stack (BtorMemMgr *mm)
{
  assert (mm);
  BtorMBTExpStack *res;

  BTOR_CNEW (mm, res);
  BTOR_INIT_STACK (res->exps);
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
  BTOR_PUSH_STACK (mm, expstack->exps, e);
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
btormbt_del_exp_stack (BtorMemMgr *mm, BtorMBTExpStack *expstack, int idx)
{
  assert (expstack);
  assert (idx >= 0 && idx < BTOR_COUNT_STACK (expstack->exps));

  int i;

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

  int i;

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
  BTOR_RELEASE_STACK (mm, expstack->exps);
  BTOR_DELETE (mm, expstack);
}

#define RELEASE_EXP_STACK(stack)                                  \
  do                                                              \
  {                                                               \
    int i;                                                        \
    for (i = 0; i < BTOR_COUNT_STACK (mbt->stack->exps); i++)     \
      btormbt_release_node (mbt, mbt->stack->exps.start[i]->exp); \
    btormbt_release_exp_stack (mbt->mm, mbt->stack);              \
    mbt->stack = 0;                                               \
  } while (0)

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BoolectorSort, BoolectorSort);

static BoolectorSortStack *
btormbt_new_sort_stack (BtorMemMgr *mm)
{
  assert (mm);
  BoolectorSortStack *res;

  BTOR_CNEW (mm, res);
  BTOR_INIT_STACK (*res);
  return res;
}

static void
btormbt_push_sort_stack (BtorMemMgr *mm,
                         BoolectorSortStack *sortstack,
                         BoolectorSort sort)
{
  assert (mm);
  assert (sortstack);
  assert (sort);

  BTOR_PUSH_STACK (mm, *sortstack, sort);
}

static void
btormbt_release_sort_stack (BtorMemMgr *mm, BoolectorSortStack *sortstack)
{
  assert (sortstack);

  if (!sortstack) return;
  BTOR_RELEASE_STACK (mm, *sortstack);
  BTOR_DELETE (mm, sortstack);
}

#define RELEASE_SORT_STACK(stack)                               \
  do                                                            \
  {                                                             \
    int i;                                                      \
    for (i = 0; i < BTOR_COUNT_STACK (*mbt->stack); i++)        \
      boolector_release_sort (mbt->btor, mbt->stack->start[i]); \
    btormbt_release_sort_stack (mbt->mm, mbt->stack);           \
    mbt->stack = 0;                                             \
  } while (0)

/*------------------------------------------------------------------------*/
struct BtorMBTStatistics
{
  /* total numbers for all rounds */
  unsigned num_sat;
  unsigned num_unsat;
  Op num_ops[BTORMBT_NUM_OPS];

  /* avg. numbers per round */
};

typedef struct BtorMBTStatistics BtorMBTStatistics;

struct BtorMBT
{
  BtorMemMgr *mm;

  Btor *btor;
  BtorMBTBtorOptPtrStack btor_opts; /* all available boolector options */

  double start_time;

  int seed;
  bool seeded;
  int rounds;
  int bugs;
  int forked;
  int ppid; /* parent pid */
  int verbosity;

  bool quiet;
  bool terminal;
  int quit_after_first;
  int ext;
  int shadow;
  char *out;
  bool create_funs;
  bool create_ufs;
  bool create_arrays;

  int g_max_rounds;

  int g_min_bw;
  int g_max_bw;
  int g_min_index_bw;
  int g_max_index_bw;
  int g_min_muldiv_bw;
  int g_max_muldiv_bw;

  int g_min_sort_fun_arity;
  int g_max_sort_fun_arity;

  int g_min_inputs; /* min number of inputs in a round */
  int g_max_inputs; /* max number of inputs in a round */

  int g_min_vars_init; /* min number of variables (initial layer) */
  int g_max_vars_init; /* max number of variables (initial layer) */
  int g_min_vars;      /* min number of variables (after init. layer) */
  int g_max_vars;      /* max number of variables (after init. layer) */
  int g_min_vars_inc;  /* min number of variables (reinit inc step) */
  int g_max_vars_inc;  /* max number of variables (reinit inc step) */

  int g_min_consts_init; /* min number of constants (initial layer) */
  int g_max_consts_init; /* max number of constants (initial layer) */
  int g_min_consts;      /* min number of constants (after init. layer) */
  int g_max_consts;      /* max number of constants (after init. layer) */
  int g_min_consts_inc;  /* min number of constants (reinit inc step) */
  int g_max_consts_inc;  /* max number of constants (reinit inc step) */

  int g_min_arrays_init; /* min number of arrays (initial layer) */
  int g_max_arrays_init; /* max number of arrays (initial layer) */
  int g_min_arrays;      /* min number of arrays (after init. layer) */
  int g_max_arrays;      /* max number of arrays (after init. layer) */
  int g_min_arrays_inc;  /* min number of arrays (reinit inc step) */
  int g_max_arrays_inc;  /* max number of arrays (reinit inc step) */

  /* add/release phase options */
  int g_min_add_funs_init; /* min funs (initial layer) */
  int g_max_add_funs_init; /* max funs (initial layer) */
  int g_min_add_funs;      /* min funs (after init. layer) */
  int g_max_add_funs;      /* max funs (after init. layer) */
  int g_min_add_funs_inc;  /* min funs (reinit inc step) */
  int g_max_add_funs_inc;  /* max funs (reinit inc step) */

  int g_min_add_uf_init; /* min ufs (initial layer) */
  int g_max_add_uf_init; /* max ufs (initial layer) */
  int g_min_add_uf;      /* min ufs (after init. layer) */
  int g_max_add_uf;      /* max ufs (after init. layer) */
  int g_min_add_uf_inc;  /* min ufs (reinit inc step) */
  int g_max_add_uf_inc;  /* max ufs (reinit inc step) */

  int g_min_add_arrayops_init; /* min array ops (initial layer) */
  int g_max_add_arrayops_init; /* max array ops (initial layer) */
  int g_min_add_arrayops;      /* min array ops (after init. layer) */
  int g_max_add_arrayops;      /* max array ops (after init. layer) */
  int g_min_add_arrayops_inc;  /* min array ops (reinit inc step) */
  int g_max_add_arrayops_inc;  /* max array ops (reinit inc step) */

  int g_min_add_bitvecops_init; /* min bv ops (initial layer) */
  int g_max_add_bitvecops_init; /* max bv ops (initial layer) */
  int g_min_add_bitvecops;      /* min bv ops (after init. layer) */
  int g_max_add_bitvecops;      /* max bv ops (after init. layer) */
  int g_min_add_bitvecops_inc;  /* min bv ops (reinit inc step) */
  int g_max_add_bitvecops_inc;  /* max bv ops (reinit inc step) */

  int g_min_add_inputs_init; /* min inputs (initial layer) */
  int g_max_add_inputs_init; /* max inputs (initial layer) */
  int g_min_add_inputs;      /* min inputs (after init. layer) */
  int g_max_add_inputs;      /* max inputs (after init. layer) */
  int g_min_add_inputs_inc;  /* min inputs (reinit inc step) */
  int g_max_add_inputs_inc;  /* max inputs (reinit inc step) */

  int g_min_ops_init; /* min operations (initial layer) */
  int g_max_ops_init; /* max operations (initial layer) */
  int g_min_ops;      /* min operations (after init. layer) */
  int g_max_ops;      /* max operations (after init. layer) */
  int g_min_ops_inc;  /* min operations (reinit inc step) */
  int g_max_ops_inc;  /* max operations (reinit inc step) */

  int g_min_add_ops_init; /* min add ops (initial layer) */
  int g_max_add_ops_init; /* max add ops (initial layer) */
  int g_min_add_ops;      /* min add ops (after init. layer) */
  int g_max_add_ops;      /* max add ops (after init. layer) */
  int g_min_add_ops_inc;  /* min add ops (reinit inc step) */
  int g_max_add_ops_inc;  /* max add ops (reinit inc step) */

  int g_min_release_ops_init; /* min release ops (initial layer) */
  int g_max_release_ops_init; /* max release ops (initial layer) */
  int g_min_release_ops;      /* min release ops (after init. layer) */
  int g_max_release_ops;      /* max release ops (after init. layer) */
  int g_min_release_ops_inc;  /* min release ops (reinit inc step) */
  int g_max_release_ops_inc;  /* max release ops (reinit inc step) */

  int g_max_ops_lower; /* lower bound for current max_ops (for
                           determining max_ass of current round) */

  int g_min_asserts_lower; /* min number of assertions in a round
                               for max_ops < g_max_ops_lower */
  int g_max_asserts_lower; /* max number of assertions in a round
                               for max_ops < g_max_ops_lower */
  int g_min_asserts_upper; /* min number of assertions in a round
                               for max_ops >= g_max_ops_lower */
  int g_max_asserts_upper; /* max number of assertions in a round
                               for max_ops >= g_max_ops_lower */

  /* propability options */
  int p_sort_bv;        /* probability of choosing an existing bv sort over
                           creating a new one */
  int p_sort_fun;       /* probability of choosing an existing fun sort over
                           creating a new one */
  int p_sort_fun_unary; /* probability of choosing a unary fun sort */
  int p_assume;         /* probability of choosing an assumption over an
                           an assertion in incremental mode */
  int p_param_exp;      /* probability of choosing parameterized expressions
                           over non-parameterized expressions */
  int p_param_arr_exp;  /* probability of choosing parameterized expressions
                           over non-parameterized array expressions */
  int p_apply_fun;      /* probability of choosing an apply on an existing
                           over an apply on a new function */
  int p_apply_uf;       /* probability of choosing an apply on an existing
                           over an apply on a new uninterpreted function */
  int p_rw;             /* probability of choosing read/write over
                           eq/ne/cond */
  int p_read;           /* probability of choosing read over write */
  int p_cond;           /* probability of choosing cond over eq/ne */
  int p_eq;             /* probability of choosing eq over ne */
  int p_inc;            /* probability of choosing an incremental step */
  int p_dump;           /* probability of dumping formula and exit */
  int p_print_model;    /* probability of printing the model after a sat call */
  int p_model_format;   /* probability of using btor over smt2 format when
                           printing a model */
  /* other options */
  char *output_format; /* force output format for dumping/printing models */

  /* round counters */
  int r_add_init;     /* number of add operations (wrt to number of release
                         operations (initial layer) */
  int r_release_init; /* number of release operations (wrt to number of
                         add operations (initial layer) */
  int r_add;          /* number of add operations (wrt to number of release
                         operations (after initial layer) */
  int r_release;      /* number of release operations (wrt to number of
                         add operations (after initial layer) */
  int r_add_inc;      /* number of add operations (wrt to number of release
                         operations (reinit inc step) */
  int r_release_inc;  /* number of release operations (wrt to number of
                         add operations (reinit inc step) */

  BtorMBTExpStack *assumptions;
  BtorMBTExpStack *bo, *bv, *arr, *fun, *uf;
  BtorMBTExpStack *parambo, *parambv, *paramarr, *paramfun;
  BtorMBTExpStack *cnf;
  BoolectorSortStack *bv_sorts, *fun_sorts;

  /* Note: no global settings after this point! Do not change order! */

  int is_init;
  int inc;
  int mgen;
  int dump;
  int print_model;

  /* prob. distribution of variables, constants, arrays in current round */
  float p_var, p_const, p_array;
  /* prop. distrbution of add and release operations in current round */
  float p_add, p_release;
  /* prob. distribution of functions (without macros and array operations),
   * array operations, macros, inputs in current round */
  float p_bitvec_fun, p_bitvec_uf, p_array_op, p_bitvec_op, p_input;

  int ops;     /* number of operations in current round */
  int asserts; /* number of produced asserts in current round */
  int assumes; /* number of produced assumes in current round */

  int max_inputs; /* max number of inputs in current round */
  int max_ops;    /* max number of operations in current round */
  int max_ass;    /* max number of asserts / assumes in current round */

  int tot_asserts; /* total number of asserts in current round */

  RNG rng;
};

typedef void *(*BtorMBTState) (BtorMBT *, unsigned rand);

static BtorMBT *
btormbt_new_btormbt (void)
{
  const char *opt;
  BtorMBT *mbt;
  BtorMemMgr *mm;
  Btor *tmpbtor;
  BtorMBTBtorOpt *btoropt;

  mm = btor_new_mem_mgr ();
  BTOR_CNEW (mm, mbt);
  mbt->mm = mm;

  BTOR_INIT_STACK (mbt->btor_opts);

  /* retrieve all available boolector options */
  tmpbtor = boolector_new ();
  for (opt = boolector_first_opt (tmpbtor); opt;
       opt = boolector_next_opt (tmpbtor, opt))
  {
    BTOR_NEW (mm, btoropt);
    btoropt->name = btor_strdup (mm, opt);
    btoropt->shrt = btor_strdup (mm, boolector_get_opt_shrt (tmpbtor, opt));
    btoropt->val  = boolector_get_opt_val (tmpbtor, opt);
    btoropt->min  = boolector_get_opt_min (tmpbtor, opt);
    btoropt->max  = boolector_get_opt_max (tmpbtor, opt);
    /* disabling incremental not supported */
    if (!strcmp (opt, "incremental")) btoropt->min = btoropt->max;
    btoropt->set_by_cl = false;
    BTOR_PUSH_STACK (mm, mbt->btor_opts, btoropt);
  }
  boolector_delete (tmpbtor);

  mbt->g_max_rounds             = INT_MAX;
  mbt->seed                     = -1;
  mbt->seeded                   = false;
  mbt->terminal                 = isatty (1) == 1;
  mbt->ext                      = 0;
  mbt->create_funs              = true;
  mbt->create_ufs               = true;
  mbt->create_arrays            = true;
  mbt->g_min_bw                 = MIN_BITWIDTH;
  mbt->g_max_bw                 = MAX_BITWIDTH;
  mbt->g_min_index_bw           = MIN_INDEXWIDTH;
  mbt->g_max_index_bw           = MAX_INDEXWIDTH;
  mbt->g_min_muldiv_bw          = MIN_MULDIVWIDTH;
  mbt->g_max_muldiv_bw          = MAX_MULDIVWIDTH;
  mbt->g_min_sort_fun_arity     = MIN_SORT_FUN_ARITY;
  mbt->g_max_sort_fun_arity     = MAX_SORT_FUN_ARITY;
  mbt->g_min_inputs             = MIN_NLITS;
  mbt->g_max_inputs             = MAX_NLITS;
  mbt->g_min_vars_init          = MIN_NVARS_INIT;
  mbt->g_max_vars_init          = MAX_NVARS_INIT;
  mbt->g_min_vars               = MIN_NVARS;
  mbt->g_max_vars               = MAX_NVARS;
  mbt->g_min_vars_inc           = MIN_NVARS_INC;
  mbt->g_max_vars_inc           = MAX_NVARS_INC;
  mbt->g_min_consts_init        = MIN_NCONSTS_INIT;
  mbt->g_max_consts_init        = MAX_NCONSTS_INIT;
  mbt->g_min_consts             = MIN_NCONSTS;
  mbt->g_max_consts             = MAX_NCONSTS;
  mbt->g_min_consts_inc         = MIN_NCONSTS_INC;
  mbt->g_max_consts_inc         = MAX_NCONSTS_INC;
  mbt->g_min_arrays_init        = MIN_NARRS_INIT;
  mbt->g_max_arrays_init        = MAX_NARRS_INIT;
  mbt->g_min_arrays             = MIN_NARRS;
  mbt->g_max_arrays             = MAX_NARRS;
  mbt->g_min_arrays_inc         = MIN_NARRS_INC;
  mbt->g_max_arrays_inc         = MAX_NARRS_INC;
  mbt->g_min_add_funs_init      = MIN_NADDOPFUNS_INIT;
  mbt->g_max_add_funs_init      = MAX_NADDOPFUNS_INIT;
  mbt->g_min_add_funs           = MIN_NADDOPFUNS;
  mbt->g_max_add_funs           = MAX_NADDOPFUNS;
  mbt->g_min_add_funs_inc       = MIN_NADDOPFUNS_INC;
  mbt->g_max_add_funs_inc       = MAX_NADDOPFUNS_INC;
  mbt->g_min_add_uf_init        = MIN_NADDOPUF_INIT;
  mbt->g_max_add_uf_init        = MAX_NADDOPUF_INIT;
  mbt->g_min_add_uf             = MIN_NADDOPUF;
  mbt->g_max_add_uf             = MAX_NADDOPUF;
  mbt->g_min_add_uf_inc         = MIN_NADDOPUF_INC;
  mbt->g_max_add_uf_inc         = MAX_NADDOPUF_INC;
  mbt->g_min_add_arrayops_init  = MIN_NADDOPAFUNS_INIT;
  mbt->g_max_add_arrayops_init  = MAX_NADDOPAFUNS_INIT;
  mbt->g_min_add_arrayops       = MIN_NADDOPAFUNS;
  mbt->g_max_add_arrayops       = MAX_NADDOPAFUNS;
  mbt->g_min_add_arrayops_inc   = MIN_NADDOPAFUNS_INC;
  mbt->g_max_add_arrayops_inc   = MAX_NADDOPAFUNS_INC;
  mbt->g_min_add_bitvecops_init = MIN_NADDOPBFUNS_INIT;
  mbt->g_max_add_bitvecops_init = MAX_NADDOPBFUNS_INIT;
  mbt->g_min_add_bitvecops      = MIN_NADDOPBFUNS;
  mbt->g_max_add_bitvecops      = MAX_NADDOPBFUNS;
  mbt->g_min_add_bitvecops_inc  = MIN_NADDOPBFUNS_INC;
  mbt->g_max_add_bitvecops_inc  = MAX_NADDOPBFUNS_INC;
  mbt->g_min_add_inputs_init    = MIN_NADDOPLITS_INIT;
  mbt->g_max_add_inputs_init    = MAX_NADDOPLITS_INIT;
  mbt->g_min_add_inputs         = MIN_NADDOPLITS;
  mbt->g_max_add_inputs         = MAX_NADDOPLITS;
  mbt->g_min_add_inputs_inc     = MIN_NADDOPLITS_INC;
  mbt->g_max_add_inputs_inc     = MAX_NADDOPLITS_INC;
  mbt->g_min_ops_init           = MIN_NOPS_INIT;
  mbt->g_max_ops_init           = MAX_NOPS_INIT;
  mbt->g_min_ops                = MIN_NOPS;
  mbt->g_max_ops                = MAX_NOPS;
  mbt->g_min_ops_inc            = MIN_NOPS_INC;
  mbt->g_max_ops_inc            = MAX_NOPS_INC;
  mbt->g_min_add_ops_init       = MIN_NADDOPS_INIT;
  mbt->g_max_add_ops_init       = MAX_NADDOPS_INIT;
  mbt->g_min_add_ops            = MIN_NADDOPS;
  mbt->g_max_add_ops            = MAX_NADDOPS;
  mbt->g_min_add_ops_inc        = MIN_NADDOPS_INC;
  mbt->g_max_add_ops_inc        = MAX_NADDOPS_INC;
  mbt->g_min_release_ops_init   = MIN_NRELOPS_INIT;
  mbt->g_max_release_ops_init   = MAX_NRELOPS_INIT;
  mbt->g_min_release_ops        = MIN_NRELOPS;
  mbt->g_max_release_ops        = MAX_NRELOPS;
  mbt->g_min_release_ops_inc    = MIN_NRELOPS_INC;
  mbt->g_max_release_ops_inc    = MAX_NRELOPS_INC;
  mbt->g_min_asserts_lower      = MIN_NASSERTS_LOWER;
  mbt->g_max_asserts_lower      = MAX_NASSERTS_LOWER;
  mbt->g_min_asserts_upper      = MIN_NASSERTS_UPPER;
  mbt->g_max_asserts_upper      = MAX_NASSERTS_UPPER;
  mbt->p_sort_bv                = P_SORT_BV * NORM_VAL;
  mbt->p_sort_fun               = P_SORT_BV * NORM_VAL;
  mbt->p_assume                 = P_ASSUME * NORM_VAL;
  mbt->p_param_exp              = P_PARAM_EXP * NORM_VAL;
  mbt->p_param_arr_exp          = P_PARAM_ARR_EXP * NORM_VAL;
  mbt->p_apply_fun              = P_APPLY_FUN * NORM_VAL;
  mbt->p_apply_uf               = P_APPLY_UF * NORM_VAL;
  mbt->p_rw                     = P_RW * NORM_VAL;
  mbt->p_read                   = P_READ * NORM_VAL;
  mbt->p_cond                   = P_COND * NORM_VAL;
  mbt->p_eq                     = P_EQ * NORM_VAL;
  mbt->p_inc                    = P_INC * NORM_VAL;
  mbt->p_dump                   = P_DUMP * NORM_VAL;
  mbt->p_print_model            = P_PRINT_MODEL * NORM_VAL;
  mbt->p_model_format           = P_MODEL_FORMAT * NORM_VAL;
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
    btor_freestr (mbt->mm, opt->name);
    if (opt->shrt) btor_freestr (mbt->mm, opt->shrt);
    BTOR_DELETE (mm, opt);
  }
  BTOR_RELEASE_STACK (mm, mbt->btor_opts);
  BTOR_DELETE (mm, mbt);
  btor_delete_mem_mgr (mm);
}

static void
btormbt_release_node (BtorMBT *mbt, BoolectorNode *node)
{
  assert (node);
  assert (BTOR_REAL_ADDR_NODE (node)->ext_refs > 0);  // TODO (ma): cast...
  boolector_release (mbt->btor, node);
}

static bool
btormbt_is_parameterized (BtorMBT *mbt, BoolectorNode *node)
{
  assert (node);
  // TODO (ma): workaround need API for querying parameterized flag
  return BTOR_REAL_ADDR_NODE (((BtorNode *) node))->parameterized == 1;
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
  // TODO (ma): workaround need API for querying if UF
  else if (BTOR_IS_UF_NODE (BTOR_REAL_ADDR_NODE ((BtorNode *) node)))
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
  int i;
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

#if 0
struct node_attr_t
{
  union
    {
      struct
	{
	  char * bits;
	  int width;
	  int val;
	} bv;
      struct
	{
	  
	  int upper;
	  int lower;
	} slice;
      struct
	{
	  int pad;
	} ext;
      struct
	{
	  int index;  /* index bit width */
	  int elem;   /* element bit width */
	} arr;
    };
  union
    {
      struct
	{
	  BoolectorNode *e0;
	} unary;
      struct
	{
	  BoolectorNode *e0;
	  BoolectorNode *e1;
	} binary;
      struct
	{
	  BoolectorNode *e0;
	  BoolectorNode *e1;
	  BoolectorNode *e2;
	} ternary;
     };
};

typedef union node_attr_t BtorMBTNodeAttr;

static BoolectorNode *
mk_node (BtorMBT * mbt, Op op, BtorMBTNodeAttr attr)
{
  BoolectorNode *node;

//      case CONST:
//	/* generate random binary string */
//	BTOR_NEWN (mbt->mm, buff, width + 1);
//	for (i = 0; i < width; i++)
//	  buff[i] = pick (rng, 0, 1) ? '1' : '0';
//	buff[width] = '\0';
//	node = boolector_const (mbt->btor, buff);
//	BTOR_DELETEN (mbt->mm, buff, width + 1);
//	break;
//      case ZERO:  node = boolector_zero (mbt->btor, width); break;
//      case FALSE: node = boolector_false (mbt->btor); break;
//      case ONES:  node = boolector_ones (mbt->btor, width); break;
//      case TRUE:  node = boolector_true (mbt->btor); break;
//      case ONE:   node = boolector_one (mbt->btor, width); break;
//      case UINT:  node = boolector_unsigned_int (mbt->btor, val, width); break;
//      default:
//	assert (op == INT);
//        node = boolector_int (mbt->btor, val, width);

  node = 0;
  switch (op)
    {
      case CONST: node = boolector_const (mbt->btor, attr.bv.bits); break;
      case ZERO:  node = boolector_zero (mbt->btor, attr.bv.width); break;
      case FALSE: node = boolector_false (mbt->btor); break;
      case TRUE:  node = boolector_true (mbt->btor); break;
      case ONES:  node = boolector_ones (mbt->btor, attr.bv.width); break;
      case ONE:   node = boolector_one (mbt->btor, attr.bv.width); break;
      case UINT:
	node = boolector_unsigned_int (mbt->btor, attr.bv.val, attr.bv.width);
	break;
      case INT:
	node = boolector_int (mbt->btor, attr.bv.val, attr.bv.width);
	break;
      case VAR: node = boolector_var (mbt->btor, attr.bv.width, 0); break;
      case ARRAY:
	node = boolector_array (mbt->btor, attr.arr.index, attr.arr.elem, 0);
	break;
      case NOT: node = boolector_not (mbt->btor, attr.unary.e0); break;
      case NEG: node = boolector_neg (mbt->btor, attr.unary.e0); break;
      case SLICE: node = boolector_slice (mbt->btor, attr.unary.e0,break;
      case INC: break;
      case DEC: break;
      case UEXT: break;
      case SEXT: break;
      case REDOR: break;
      case REDXOR: break;
      case REDAND: break;
      case EQ: break;
      case NE: break;
      case UADDO: break;
      case SADDO: break;
      case USUBO: break;
      case SSUBO: break;
      case UMULO: break;
      case SMULO: break;
      case SDIVO: break;
      case ULT: break;
      case SLT: break;
      case ULTE: break;
      case SLTE: break;
      case UGT: break;
      case SGT: break;
      case UGTE: break;
      case SGTE: break;
      case IMPLIES: break;
      case IFF: break;
      case XOR: break;
      case XNOR: break;
      case AND: break;
      case NAND: break;
      case OR: break;
      case NOR: break;
      case ADD: break;
      case SUB: break;
      case MUL: break;
      case UDIV: break;
      case SDIV: break;
      case UREM: break;
      case SREM: break;
      case SMOD: break;
      case SLL: break;
      case SRL: break;
      case SRA: break;
      case ROL: break;
      case ROR: break;
      case CONCAT: break;
      case COND: break;
      case READ: break;
      case WRITE: break;
      default:
	assert (op == APPLY);
    }
  assert (node);
  return node;
}
#endif

/*------------------------------------------------------------------------*/

static BtorMBT *g_btormbt;
static BtorMBTStatistics *g_btormbtstats = 0;
static char g_shmfilename[128];

static int g_caught_sig;
static void (*sig_int_handler) (int);
static void (*sig_segv_handler) (int);
static void (*sig_abrt_handler) (int);
static void (*sig_term_handler) (int);
static void (*sig_bus_handler) (int);

static int g_set_alarm;
static void (*sig_alrm_handler) (int);

// TODO (ma): why do we need this?
void boolector_chkclone (Btor *);

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
    if (!isdigit ((int) *p)) return 0;
  return 1;
}

static int
isfloatnumstr (const char *str)
{
  const char *p;
  for (p = str; *p; p++)
    if (!isdigit ((int) *p) && *p != '.') return 0;
  return 1;
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
  return current_time () - g_btormbt->start_time;
}

static double
average (double a, double b)
{
  return b ? a / b : 0;
}

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
  int i;
  double t = get_time ();
  btormbt_msg ("runtime %0.2f seconds", t);
  btormbt_msg ("%d rounds = %0.2f rounds per second",
               mbt->rounds,
               average (mbt->rounds, t));
  btormbt_msg (
      "%d bugs = %0.2f bugs per second", mbt->bugs, average (mbt->bugs, t));
  btormbt_msg ("%u sat calls", g_btormbtstats->num_sat);
  btormbt_msg ("%u unsat calls", g_btormbtstats->num_unsat);

  /* print total number of created ops */
  if (mbt->verbosity > 1)
    for (i = 0; i < BTORMBT_NUM_OPS; i++)
      btormbt_msg ("  %u %s", g_btormbtstats->num_ops[i], g_op2str[i]);
}

/*------------------------------------------------------------------------*/

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
catch_sig (int sig)
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
  exit (EXIT_ERROR);
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
catch_alarm (int sig)
{
  (void) sig;
  assert (sig == SIGALRM);

  if (g_set_alarm > 0)
  {
    btormbt_msg ("ALARM TRIGGERED: time limit %d seconds reached", g_set_alarm);
    btormbt_print_stats (g_btormbt);
  }
  reset_alarm ();
  exit (EXIT_TIMEOUT);
}

static void
set_alarm (void)
{
  sig_alrm_handler = signal (SIGALRM, catch_alarm);
  assert (g_set_alarm > 0);
  alarm (g_set_alarm);
}

/*------------------------------------------------------------------------*/

/**
 * initialize probability distribution of inputs
 * parameter: ratio var:const:arr (e.g. 3:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_inputs (BtorMBT *mbt,
                float ratio_var,
                float ratio_const,
                float ratio_arr)
{
  float sum;

  sum = ratio_var + ratio_const + ratio_arr;

  assert (sum > 0);

  mbt->p_var   = (ratio_var * NORM_VAL) / sum;
  mbt->p_const = (ratio_const * NORM_VAL) / sum;
  mbt->p_array = (ratio_arr * NORM_VAL) / sum;
  // TODO (ma): uf
}

/**
 * initialize probability distribution of add operation
 * parameter: ratio fun:uf:array:bv:input (e.g. 1:1:1:1:2)
 * normalized to NORM_VAL
 */
static void
init_pd_add (BtorMBT *mbt,
             float ratio_fun,
             float ratio_uf,
             float ratio_arr_op,
             float ratio_bv_op,
             float ratio_input)
{
  float sum;

  sum = ratio_fun + ratio_uf + ratio_arr_op + ratio_bv_op + ratio_input;

  assert (sum > 0);

  mbt->p_bitvec_fun = (ratio_fun * NORM_VAL) / sum;
  mbt->p_bitvec_uf =
      (ratio_uf * NORM_VAL) / sum;  // TODO (ma): UF should be input
  mbt->p_array_op  = (ratio_arr_op * NORM_VAL) / sum;
  mbt->p_bitvec_op = (ratio_bv_op * NORM_VAL) / sum;
  mbt->p_input     = (ratio_input * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add/release op
 * parameter: ratio addop:relop (e.g. 1:0)
 * normalized to NORM_VAL
 */
static void
init_pd_ops (BtorMBT *mbt, float ratio_add, float ratio_release)
{
  float sum;

  sum = ratio_add + ratio_release;

  assert (sum > 0);

  mbt->p_add     = (ratio_add * NORM_VAL) / sum;
  mbt->p_release = (ratio_release * NORM_VAL) / sum;
}

/*------------------------------------------------------------------------*/

/* Modify bit width of node e of width ew to be of width tow.
 * Note: param ew prevents too many boolector_get_width calls. */
static BoolectorNode *
modify_bv (BtorMBT *mbt, RNG *rng, BoolectorNode *e, int new_width)
{
  assert (new_width > 0);

  int tmp, old_width;
  BoolectorNode *node;
  BtorMBTExp *exp;

  old_width = boolector_get_width (mbt->btor, e);
  node      = 0;
  if (new_width < old_width)
  {
    tmp  = pick (rng, 0, old_width - new_width);
    node = boolector_slice (mbt->btor, e, tmp + new_width - 1, tmp);
    g_btormbtstats->num_ops[SLICE]++;
  }
  else if (new_width > old_width)
  {
    if (pick (rng, 0, 1))
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
btormbt_var (BtorMBT *mbt, RNG *rng, BtorMBTExpType type)
{
  int width;

  if (type == BTORMBT_BO_T)
    width = 1;
  else if (type == BTORMBT_BV_T)
    width = pick (rng, mbt->g_min_bw, mbt->g_max_bw);
  else
  {
    assert (type = BTORMBT_BB_T);
    width = pick (rng, 1, mbt->g_max_bw);
  }
  btormbt_push_node (mbt, boolector_var (mbt->btor, width, 0));
  g_btormbtstats->num_ops[VAR]++;
}

static void
btormbt_const (BtorMBT *mbt, RNG *rng)
{
  char *bits;
  int width, val, i;
  BoolectorNode *node;
  //  BtorMBTNodeAttr attr;
  Op op;

  op    = pick (rng, CONST, INT);
  width = 0;
  val   = 0;

  if (op != TRUE && op != FALSE) width = pick (rng, 1, mbt->g_max_bw);

  if (op == UINT || op == INT)
  {
    if (width < 32)
      val = (1 << width) - 1;
    else
      val = UINT_MAX - 1; /* UINT_MAX leads to divison by 0 in pick */
    val = pick (rng, 0, val);
  }

#if 0
  bits = 0;
  if (op == CONST)
    {
      /* generate random binary string */
      BTOR_NEWN (mbt->mm, bits, width + 1);
      for (i = 0; i < width; i++)
	bits[i] = pick (rng, 0, 1) ? '1' : '0';
      bits[width] = '\0';
    }
#endif

#if 1
  node = 0;
  switch (op)
  {
    case CONST:
      /* generate random binary string */
      BTOR_NEWN (mbt->mm, bits, width + 1);
      for (i = 0; i < width; i++) bits[i] = pick (rng, 0, 1) ? '1' : '0';
      bits[width] = '\0';
      node        = boolector_const (mbt->btor, bits);
      BTOR_DELETEN (mbt->mm, bits, width + 1);
      break;
    case ZERO: node = boolector_zero (mbt->btor, width); break;
    case FALSE: node = boolector_false (mbt->btor); break;
    case ONES: node = boolector_ones (mbt->btor, width); break;
    case TRUE: node = boolector_true (mbt->btor); break;
    case ONE: node = boolector_one (mbt->btor, width); break;
    case UINT: node = boolector_unsigned_int (mbt->btor, val, width); break;
    default: assert (op == INT); node = boolector_int (mbt->btor, val, width);
  }
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
btormbt_array (BtorMBT *mbt, RNG *rng)
{
  int ew, iw;

  // TODO (ma): remove ite here and use g_min_bw
  ew = pick (rng, mbt->g_min_bw > 2 ? mbt->g_min_bw : 1, mbt->g_max_bw);
  iw = pick (rng, mbt->g_min_index_bw, mbt->g_max_index_bw);

  btormbt_push_node (mbt, boolector_array (mbt->btor, ew, iw, 0));
  g_btormbtstats->num_ops[ARRAY]++;
}

#if 0
/* randomly select variables from bo within the range ifrom - ito */
static BoolectorNode *
btormbt_clause (BtorMBT * mbt, RNG * rng, int ifrom, int ito)
{
  int i, idx;
  BoolectorNode *e0, *e1;
  BtorMBTExpStack *expstack;
  
  expstack = mbt->bo;
  e0 = NULL;
  /* make clause with 3 boolean expressions */
  for (i = 0; i < 3; i++)
    {
      idx = pick (rng, ifrom, ito);
      if (e0 == NULL)
	{
	  e0 = expstack->exps.start[idx]->exp;
	  if (pick (rng, 0, 1))
	    {
	      e0 = boolector_not (mbt->btor, e0);
	      btormbt_push_exp_stack (mbt->mm, mbt->cnf, e0);
	    }
	}
      else
	{
	  e1 = expstack->exps.start[idx]->exp;
	  if (pick (rng, 0, 1))
	    {
	      e1 = boolector_not (mbt->btor, e1);
	      btormbt_push_exp_stack (mbt->mm, mbt->cnf, e1);
	    }
	  e0 = boolector_or (mbt->btor, e0, e1);
	  btormbt_push_exp_stack (mbt->mm, mbt->cnf, e0);
	}
    }
  return e0;
}
#endif

static BoolectorNode *
btormbt_constraint (BtorMBT *mbt, RNG *rng)
{
  int i, pos, num_nodes, start, end;
  BoolectorNode *res, *tmp, *node;

  /* select from init layer with lower probability */
  if (mbt->bo->init_layer_size
      && BTOR_COUNT_STACK (mbt->bo->exps) > mbt->bo->init_layer_size
      && pick (rng, 0, 4))
    start = mbt->bo->init_layer_size - 1;
  else
    start = 0;

  end       = BTOR_COUNT_STACK (mbt->bo->exps) - 1;
  num_nodes = pick (rng, 1, BTOR_MAX_UTIL (1, end - start));
  /* randomly choose 'num_nodes' nodes for the constraint */
  res = tmp = 0;
  for (i = 0; i < num_nodes; i++)
  {
    pos = pick (rng, start, end);
    node =
        boolector_copy (mbt->btor, BTOR_PEEK_STACK (mbt->bo->exps, pos)->exp);

    /* negate 'node' with probability 0.5 */
    if (pick (rng, 0, 1))
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
btormbt_unary_op (BtorMBT *mbt, RNG *rng, Op op, BoolectorNode *e)
{
  assert (is_unary_op (op));

  int upper, lower, width;
  BoolectorNode *node;

  upper = lower = 0;
  width         = boolector_get_width (mbt->btor, e);
  assert (width <= mbt->g_max_bw);

  if (op == SLICE)
  {
    upper = pick (rng, 0, width - 1);
    lower = pick (rng, 0, upper);
  }
  else if (op == UEXT || op == SEXT)
    upper = pick (rng, 0, mbt->g_max_bw - width);

  node = 0;
  switch (op)
  {
    case NOT: node = boolector_not (mbt->btor, e); break;
    case NEG: node = boolector_neg (mbt->btor, e); break;
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
btormbt_binary_op (
    BtorMBT *mbt, RNG *rng, Op op, BoolectorNode *e0, BoolectorNode *e1)
{
  assert (is_binary_op (op));

  int tmp0, tmp1, e0_width, e1_width;
  BoolectorNode *node;

  e0_width = boolector_get_width (mbt->btor, e0);
  assert (e0_width <= mbt->g_max_bw);
  e1_width = boolector_get_width (mbt->btor, e1);
  assert (e1_width <= mbt->g_max_bw);

  if ((op >= XOR && op <= SMOD) || (op >= EQ && op <= SGTE))
  {
    /* modify e1_width equal to e0_width, guarded mul and div */
    if ((op >= UMULO && op <= SDIVO) || (op >= MUL && op <= SMOD))
    {
      if (e0_width > mbt->g_max_muldiv_bw)
      {
        e0       = modify_bv (mbt, rng, e0, mbt->g_max_muldiv_bw);
        e0_width = mbt->g_max_muldiv_bw;
      }
      else if (e0_width < mbt->g_min_muldiv_bw)
      {
        e0       = modify_bv (mbt, rng, e0, mbt->g_max_muldiv_bw);
        e0_width = mbt->g_max_muldiv_bw;
      }
    }
    e1 = modify_bv (mbt, rng, e1, e0_width);
  }
  else if (op >= SLL && op <= ROR)
  {
    /* modify width of e0 power of 2 and e1 log2(e0) */
    nextpow2 (e0_width, &tmp0, &tmp1);
    e0       = modify_bv (mbt, rng, e0, tmp0);
    e1       = modify_bv (mbt, rng, e1, tmp1);
    e0_width = tmp0;
  }
  else if (op == CONCAT)
  {
    if (e0_width + e1_width > mbt->g_max_bw)
    {
      if (e0_width > 1)
      {
        e0       = modify_bv (mbt, rng, e0, e0_width / 2);
        e0_width = e0_width / 2;
      }
      if (e1_width > 1)
      {
        e1       = modify_bv (mbt, rng, e1, e1_width / 2);
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
                    RNG *rng,
                    Op op,
                    BoolectorNode *e0,
                    BoolectorNode *e1,
                    BoolectorNode *e2)
{
  assert (is_ternary_op (op));
  assert (op == COND);
  assert (boolector_get_width (mbt->btor, e0) == 1);

  (void) op;
  int e1w, e2w;

  e1w = boolector_get_width (mbt->btor, e1);
  assert (e1w <= mbt->g_max_bw);
  e2w = boolector_get_width (mbt->btor, e2);
  assert (e2w <= mbt->g_max_bw);

  /* bitvectors must have same bit width */
  e2 = modify_bv (mbt, rng, e2, e1w);
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
                  RNG *rng,
                  Op op,
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
    e1 = modify_bv (mbt, rng, e1, boolector_get_index_width (mbt->btor, e0));
    if (op == WRITE)
    {
      e2   = modify_bv (mbt, rng, e2, boolector_get_width (mbt->btor, e0));
      node = boolector_write (mbt->btor, e0, e1, e2);
    }
    else
      node = boolector_read (mbt->btor, e0, e1);
  }
  else
  {
    assert (boolector_is_array (mbt->btor, e0));
    assert (boolector_is_equal_sort (mbt->btor, e0, e1));

    if (op == EQ)
      node = boolector_eq (mbt->btor, e0, e1);
    else if (op == NE)
      node = boolector_ne (mbt->btor, e0, e1);
    else
    {
      assert (op == COND);
      node = boolector_cond (mbt->btor, e2, e0, e1);
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
select_exp (BtorMBT *mbt, RNG *rng, BtorMBTExpType type, int force_param)
{
  assert (force_param >= -1);
  assert (force_param <= 1);
  assert (force_param != 1
          || (mbt->parambo && !BTOR_EMPTY_STACK (mbt->parambo->exps))
          || (mbt->parambv && !BTOR_EMPTY_STACK (mbt->parambv->exps))
          || (mbt->paramarr && !BTOR_EMPTY_STACK (mbt->paramarr->exps)));
  assert ((!mbt->parambo && !mbt->parambv && !mbt->paramarr)
          || (mbt->parambo && mbt->parambv && mbt->paramarr));

  int rand, idx, lower;
  BtorMBTExpStack *expstack, *bo, *bv, *arr;
  BtorMBTExp *exp;

  /* choose between param. exps and non-param. exps */
  rand = pick (rng, 0, NORM_VAL - 1);
  if (force_param == -1
      || (force_param == 0 && rand >= mbt->p_param_exp)
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
      rand =
          pick (rng,
                0,
                BTOR_COUNT_STACK (bo->exps) + BTOR_COUNT_STACK (bv->exps) - 1);
      expstack = rand < BTOR_COUNT_STACK (bo->exps) ? bo : bv;
  }

  assert (!BTOR_EMPTY_STACK (expstack->exps));
  /* select first nodes without parents (not yet referenced) */
  idx = -1;
  while (expstack->last_pos_parents < BTOR_COUNT_STACK (expstack->exps))
  {
    if (expstack->exps.start[expstack->last_pos_parents]->parents <= 0)
    {
      idx = expstack->last_pos_parents++;
      break;
    }
    expstack->last_pos_parents++;
  }
  if (idx < 0)
  {
    /* select random expression
     * select from initlayer with lower probability
     * - from range (init_layer_size - n) with p = 0.666
     * - from ragne (0 - n)         with p = 0.333 */
    if (expstack->init_layer_size
        && BTOR_COUNT_STACK (expstack->exps) > expstack->init_layer_size
        && pick (rng, 0, 3))
      lower = expstack->init_layer_size - 1;
    else
      lower = 0;
    idx = pick (rng, lower, BTOR_COUNT_STACK (expstack->exps) - 1);
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
                RNG *rng,
                BoolectorNode *node,
                int eew,
                int eiw,
                int force_param)
{
  int i, rand, idx, sel_eew, sel_eiw;
  BtorMBTExp *exp;
  BtorMBTExpStack *expstack;
  BoolectorNode *sel_e, *e[3];

  /* choose between param. exps and non-param. array exps */
  rand = pick (rng, 0, NORM_VAL - 1);
  assert ((!mbt->parambo && !mbt->parambv && !mbt->paramarr)
          || (mbt->parambo && mbt->parambv && mbt->paramarr));
  if (force_param == -1 || (force_param == 0 && rand >= mbt->p_param_arr_exp)
      || (!mbt->parambo && !mbt->parambv && !mbt->paramarr)
      || (!BTOR_COUNT_STACK (mbt->parambo->exps)
          && !BTOR_COUNT_STACK (mbt->parambv->exps)
          && !BTOR_COUNT_STACK (mbt->paramarr->exps)))
    expstack = mbt->arr;
  else
    expstack = mbt->paramarr;
  assert (!BTOR_EMPTY_STACK (expstack->exps));

  /* random search start idx */
  idx = i = pick (rng, 0, BTOR_COUNT_STACK (expstack->exps) - 1);
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
    e[0] = select_arr_exp (mbt, rng, NULL, eew, eiw, -1);
    assert (boolector_get_index_width (mbt->btor, e[0]) == eiw);
    assert (boolector_get_width (mbt->btor, e[0]) == eew);
    rand  = pick (rng, 1, 2);
    e[1]  = select_exp (mbt, rng, BTORMBT_BV_T, rand == 1 ? 1 : 0);
    e[2]  = select_exp (mbt, rng, BTORMBT_BV_T, rand == 2 ? 1 : 0);
    exp   = btormbt_array_op (mbt, rng, WRITE, e[0], e[1], e[2]);
    sel_e = exp->exp;
  }
  else
  {
    sel_e = boolector_array (mbt->btor, eew, eiw, NULL);
    exp   = btormbt_push_node (mbt, sel_e);
    g_btormbtstats->num_ops[ARRAY]++;
  }
  exp->parents++;
  assert (boolector_get_index_width (mbt->btor, sel_e) == eiw);
  assert (boolector_get_width (mbt->btor, sel_e) == eew);
  return sel_e;
}

/*------------------------------------------------------------------------*/

static BoolectorSort
btormbt_bv_sort (BtorMBT *mbt, unsigned r)
{
  int rand, len;
  RNG rng;
  BoolectorNode *bv;
  BoolectorSort sort;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  if (BTOR_COUNT_STACK (*mbt->bv_sorts) && rand < mbt->p_sort_bv)
  {
    /* use existing bv sort */
    rand = pick (&rng, 0, BTOR_COUNT_STACK (*mbt->bv_sorts) - 1);
    sort = mbt->bv_sorts->start[rand];
  }
  else
  {
    /* create new bv sort */
    rand = pick (&rng, 0, BTOR_COUNT_STACK (mbt->bv->exps) - 1);
    bv   = mbt->bv->exps.start[rand]->exp;
    len  = boolector_get_width (mbt->btor, bv);
    sort = boolector_bitvec_sort (mbt->btor, len);
    btormbt_push_sort_stack (mbt->mm, mbt->bv_sorts, sort);
  }
  return sort;
}

static void
init_domain (BtorMBT *mbt, unsigned r, BoolectorSortStack *sortstack)
{
  int i, arity, rand;
  RNG rng;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  if (rand < mbt->p_sort_fun_unary)
  {
    btormbt_push_sort_stack (mbt->mm, sortstack, btormbt_bv_sort (mbt, r));
    return;
  }

  arity = pick (&rng, mbt->g_min_sort_fun_arity, mbt->g_max_sort_fun_arity);
  for (i = 0; i < arity; i++)
    btormbt_push_sort_stack (mbt->mm, sortstack, btormbt_bv_sort (mbt, r));
}

static BoolectorSort
btormbt_fun_sort (BtorMBT *mbt, unsigned r)
{
  int rand;
  RNG rng;
  BoolectorSort sort, codomain;
  BoolectorSortStack *domain;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  if (BTOR_COUNT_STACK (*mbt->fun_sorts) && rand < mbt->p_sort_fun)
  {
    /* use existing fun sort */
    rand = pick (&rng, 0, BTOR_COUNT_STACK (*mbt->fun_sorts) - 1);
    sort = mbt->fun_sorts->start[rand];
  }
  else
  {
    /* create new fun sort */
    domain = btormbt_new_sort_stack (mbt->mm);
    init_domain (mbt, r, domain);
    codomain = btormbt_bv_sort (mbt, r);
    sort     = boolector_fun_sort (
        mbt->btor, domain->start, BTOR_COUNT_STACK (*domain), codomain);
    btormbt_push_sort_stack (mbt->mm, mbt->fun_sorts, sort);
    btormbt_release_sort_stack (mbt->mm, domain);
  }
  return sort;
}

/*------------------------------------------------------------------------*/

/* Generate parameterized unary/binary/ternary operation. */
static void
btormbt_param_bv_op (BtorMBT *mbt, RNG *rng, int op_from, int op_to)
{
  int i, rand;
  BoolectorNode *e[3];
  Op op;

  assert (op_from >= NOT && op_from <= COND);
  assert (op_to >= NOT && op_to <= COND);

  op = pick (rng, op_from, op_to);
  if (is_unary_op (op))
  {
    e[0] = select_exp (mbt, rng, BTORMBT_BB_T, 1);
    btormbt_unary_op (mbt, rng, op, e[0]);
  }
  else if (is_binary_op (op))
  {
    rand = pick (rng, 0, 1);
    for (i = 0; i < 2; i++)
      e[i] = select_exp (
          mbt,
          rng,
          ((op >= IMPLIES && op <= IFF) ? BTORMBT_BO_T : BTORMBT_BB_T),
          i == rand ? 1 : 0);
    btormbt_binary_op (mbt, rng, op, e[0], e[1]);
  }
  else
  {
    assert (is_ternary_op (op));
    rand = pick (rng, 0, 2);
    for (i = 0; i < 3; i++)
      e[i] = select_exp (
          mbt, rng, i == 0 ? BTORMBT_BO_T : BTORMBT_BB_T, i == rand ? 1 : 0);
    btormbt_ternary_op (mbt, rng, op, e[0], e[1], e[2]);
  }
}

/* Generate parameterized operations on arrays.
 * Force array expressions with non-parameterized arrays via parameter
 * force_arrnparr (mostly needed for initializing the paramarr stack).
 * Note that this forces either a WRITE or COND expression. */
static void
btormbt_param_array_op (BtorMBT *mbt, RNG *rng)
{
  bool force_param;
  int rand;
  BoolectorNode *e0, *e1, *e2;
  Op op;

  /* if there are no parameterized arrays yet, we have to create at least
   * one */
  force_param = BTOR_EMPTY_STACK (mbt->paramarr->exps) == 1;

  /* choose READ/WRITE with p = 0.666, else EQ/NE/COND */
  if (pick (rng, 0, 2))
  {
    /* we need a parameterized array */
    if (force_param)
      op = WRITE;
    else
      op = pick (rng, READ, WRITE);
  }
  else /* evenly distribute EQ, NE and COND */
  {
    /* parameterized EQ and NE not supported */
    if (!mbt->ext || force_param || pick (rng, 0, 2) == 0)
      op = COND;
    else
    {
      rand = pick (rng, 0, NORM_VAL - 1);
      op   = rand < mbt->p_eq ? EQ : NE;
    }
  }

  e1 = e2 = 0;
  switch (op)
  {
    case WRITE:
      rand = pick (rng, 1, 2);
      e0   = select_exp (
          mbt, rng, BTORMBT_ARR_T, force_param ? 1 : pick (rng, 0, 1));
      e1 = select_exp (mbt, rng, BTORMBT_BV_T, rand == 1 ? 1 : 0);
      e2 = select_exp (mbt, rng, BTORMBT_BV_T, rand == 2 ? 1 : 0);
      break;
    case READ:
      assert (!force_param);
      e0 = select_exp (mbt, rng, BTORMBT_ARR_T, pick (rng, 0, 1));
      e1 = select_exp (mbt, rng, BTORMBT_BV_T, 1);
      break;
    case COND:
      e0 = select_exp (
          mbt, rng, BTORMBT_ARR_T, force_param ? 1 : pick (rng, 0, 1));
      e1 = select_arr_exp (mbt,
                           rng,
                           e0,
                           boolector_get_width (mbt->btor, e0),
                           boolector_get_index_width (mbt->btor, e0),
                           force_param ? 1 : pick (rng, 0, 1));
      assert (boolector_is_equal_sort (mbt->btor, e0, e1));
      e2 = select_exp (mbt, rng, BTORMBT_BO_T, force_param);
      break;
    default:
      assert (!force_param);
      assert (mbt->ext);
      assert (op == EQ || op == NE);
      e0 = select_exp (mbt, rng, BTORMBT_ARR_T, -1);
      e1 = select_arr_exp (mbt,
                           rng,
                           e0,
                           boolector_get_width (mbt->btor, e0),
                           boolector_get_index_width (mbt->btor, e0),
                           -1);
      /* parameterized array equalities not allowed */
      assert (!btormbt_is_parameterized (mbt, e0));
      assert (!btormbt_is_parameterized (mbt, e1));
      assert (boolector_is_equal_sort (mbt->btor, e0, e1));
  }

  btormbt_array_op (mbt, rng, op, e0, e1, e2);
}

static void
btormbt_bv_fun (BtorMBT *mbt, unsigned r, int nlevel)
{
  int i, n, width, max_ops, rand;
  BtorMBTExpStack *expstack;
  BtorMBTExpStack *tmpparambo, *tmpparambv, *tmpparamarr, *tmpparamfun;
  BoolectorNode *tmp, *fun, *e0, *e1, *e2;
  BoolectorNodePtrStack params, args;
  BtorIntStack param_widths;
  RNG rng;

  BTOR_INIT_STACK (param_widths);
  rng = initrng (r);
  /* choose between apply on random existing and apply on new function */
  rand = pick (&rng, 0, NORM_VAL - 1);
  /* use existing function */
  if (rand < mbt->p_apply_fun
      && (!BTOR_EMPTY_STACK (mbt->fun->exps)
          || (mbt->paramfun && !BTOR_EMPTY_STACK (mbt->paramfun->exps))))
  {
    /* pick fun from fun/paramfun with p = 0.5 if non-empty */
    expstack = !BTOR_EMPTY_STACK (mbt->fun->exps)
                   ? (mbt->paramfun && !BTOR_EMPTY_STACK (mbt->paramfun->exps)
                          ? (pick (&rng, 0, 1) ? mbt->fun : mbt->paramfun)
                          : mbt->fun)
                   : mbt->paramfun;
    rand = pick (&rng, 0, BTOR_COUNT_STACK (expstack->exps) - 1);
    fun  = expstack->exps.start[rand]->exp;

    // FIXME (ma): sort workaround
    BtorSort *sort;
    sort = btor_get_sort_by_id (&mbt->btor->sorts_unique_table,
                                ((BtorNode *) fun)->sort_id);
    for (i = 0; i < (int) sort->fun.domain->tuple.num_elements; i++)
    {
      BTOR_PUSH_STACK (
          mbt->mm,
          param_widths,
          btor_get_width_bitvec_sort (&mbt->btor->sorts_unique_table,
                                      sort->fun.domain->tuple.elements[i]->id));
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
    BTOR_INIT_STACK (params);
    // TODO (ma): make configurable
    for (i = 0; i < pick (&rng, MIN_NPARAMS, MAX_NPARAMS); i++)
    {
      // TODO (ma): remove ite here?
      width = pick (&rng, mbt->g_min_bw > 2 ? mbt->g_min_bw : 1, mbt->g_max_bw);
      tmp   = boolector_param (mbt->btor, width, 0);
      BTOR_PUSH_STACK (mbt->mm, params, tmp);
      BTOR_PUSH_STACK (
          mbt->mm, param_widths, boolector_get_width (mbt->btor, tmp));
      btormbt_push_node (mbt, tmp);
      g_btormbtstats->num_ops[PARAM]++;
    }

    /* initialize parameterized stacks to be non-empty */
    if (BTOR_EMPTY_STACK (mbt->parambv->exps))
    {
      assert (!BTOR_EMPTY_STACK (mbt->parambo->exps));
      rand = pick (&rng, 0, BTOR_COUNT_STACK (mbt->parambo->exps) - 1);
      tmp  = mbt->parambo->exps.start[rand]->exp;
      assert (boolector_get_width (mbt->btor, tmp) == 1);
      modify_bv (mbt, &rng, tmp, pick (&rng, mbt->g_min_bw, mbt->g_max_bw));
    }
    if (BTOR_EMPTY_STACK (mbt->parambo->exps))
    {
      assert (!BTOR_EMPTY_STACK (mbt->parambv->exps));
      rand = pick (&rng, 0, BTOR_COUNT_STACK (mbt->parambv->exps) - 1);
      tmp  = mbt->parambv->exps.start[rand]->exp;
      assert (boolector_get_width (mbt->btor, tmp) > 1);
      modify_bv (mbt, &rng, tmp, 1);
    }
    if (BTOR_EMPTY_STACK (mbt->paramarr->exps))
    {
      rand = pick (&rng, 1, 2);
      e1   = select_exp (mbt, &rng, BTORMBT_BB_T, rand == 1 ? 1 : 0);
      e2   = select_exp (mbt, &rng, BTORMBT_BB_T, rand == 2 ? 1 : 0);
      e0   = select_arr_exp (mbt,
                           &rng,
                           0,
                           boolector_get_width (mbt->btor, e2),
                           boolector_get_width (mbt->btor, e1),
                           -1);
      assert (btormbt_is_parameterized (mbt, e1)
              || btormbt_is_parameterized (mbt, e2));
      // TODO (ma): create parameterized acond?
      btormbt_array_op (mbt, &rng, WRITE, e0, e1, e2);
      assert (!BTOR_EMPTY_STACK (mbt->parambo->exps));
      assert (!BTOR_EMPTY_STACK (mbt->parambv->exps));
      assert (!BTOR_EMPTY_STACK (mbt->paramarr->exps));
    }

    /* generate parameterized expressions */
    max_ops = pick (&rng, 0, MAX_NPARAMOPS);
    n       = 0;
    while (n++ < max_ops)
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < mbt->p_bitvec_fun)
        btormbt_param_bv_op (mbt, &rng, NOT, COND);
      else if (rand < mbt->p_bitvec_fun + mbt->p_array_op)
        btormbt_param_array_op (mbt, &rng);
      else if (nlevel < MAX_NNESTEDBFUNS)
        btormbt_bv_fun (mbt, nextrand (&rng), nlevel + 1);
    }

    /* pick exp from parambo/parambv with p = 0.5 if non-empty */
    expstack = !BTOR_EMPTY_STACK (mbt->parambo->exps)
                   ? (!BTOR_EMPTY_STACK (mbt->parambv->exps)
                          ? (pick (&rng, 0, 1) ? mbt->parambo : mbt->parambv)
                          : mbt->parambo)
                   : mbt->parambv;
    assert (!BTOR_EMPTY_STACK (expstack->exps));
    rand = pick (&rng, 0, BTOR_COUNT_STACK (expstack->exps) - 1);
    tmp  = BTOR_PEEK_STACK (expstack->exps, rand)->exp;
    fun =
        boolector_fun (mbt->btor, params.start, BTOR_COUNT_STACK (params), tmp);

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
    BTOR_RELEASE_STACK (mbt->mm, params);

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
  BTOR_INIT_STACK (args);
  for (i = 0; i < BTOR_COUNT_STACK (param_widths); i++)
  {
    width = BTOR_PEEK_STACK (param_widths, i);
    // TODO (ma): if width == 1 select BTORMBT_BO_T
    tmp = select_exp (mbt, &rng, BTORMBT_BV_T, 0);
    BTOR_PUSH_STACK (mbt->mm, args, modify_bv (mbt, &rng, tmp, width));
  }

  tmp = boolector_apply (mbt->btor, args.start, BTOR_COUNT_STACK (args), fun);
  btormbt_push_node (mbt, tmp);
  g_btormbtstats->num_ops[APPLY]++;
  BTOR_RELEASE_STACK (mbt->mm, param_widths);
  BTOR_RELEASE_STACK (mbt->mm, args);
}

static void
btormbt_bv_uf (BtorMBT *mbt, unsigned r)
{
  unsigned len;
  int rand;
  RNG rng;
  BoolectorNode *uf, *arg, *apply;
  BoolectorSort sort;
  BoolectorNodePtrStack stack;
  BtorTupleSortIterator it;
  BtorSortUniqueTable *sorts;

  rng   = initrng (r);
  rand  = pick (&rng, 0, NORM_VAL - 1);
  sorts = &mbt->btor->sorts_unique_table;

  /* use existing UF */
  if (BTOR_COUNT_STACK (mbt->uf->exps) && rand < mbt->p_apply_uf)
  {
    rand = pick (&rng, 0, BTOR_COUNT_STACK (mbt->uf->exps) - 1);
    uf   = mbt->uf->exps.start[rand]->exp;
  }
  else /* create new UF */
  {
    sort = btormbt_fun_sort (mbt, r);
    uf   = boolector_uf (mbt->btor, sort, 0);
    //      btormbt_push_exp_stack (mbt->mm, mbt->uf, uf);
    btormbt_push_node (mbt, uf);
    g_btormbtstats->num_ops[UF]++;
  }

  /* create apply with sort of UF */
  BTOR_INIT_STACK (stack);
  btor_init_tuple_sort_iterator (
      &it, sorts, btor_get_domain_fun_sort (sorts, ((BtorNode *) uf)->sort_id));
  while (btor_has_next_tuple_sort_iterator (&it))
  {
    sort = btor_next_tuple_sort_iterator (&it);
    len  = btor_get_width_bitvec_sort (sorts, sort);
    arg  = select_exp (mbt, &rng, BTORMBT_BB_T, 0);
    BTOR_PUSH_STACK (mbt->mm, stack, modify_bv (mbt, &rng, arg, len));
  }

  /* create apply on UF */
  apply =
      boolector_apply (mbt->btor, stack.start, BTOR_COUNT_STACK (stack), uf);

  len = boolector_get_width (mbt->btor, apply);
  btormbt_push_node (mbt, apply);
  g_btormbtstats->num_ops[APPLY]++;
  BTOR_RELEASE_STACK (mbt->mm, stack);
}

/*------------------------------------------------------------------------*/

static void *btormbt_state_new (BtorMBT *, unsigned);
static void *btormbt_state_opt (BtorMBT *, unsigned);
static void *btormbt_state_init (BtorMBT *, unsigned);
static void *btormbt_state_main (BtorMBT *, unsigned);
static void *btormbt_state_add (BtorMBT *, unsigned);
static void *btormbt_state_bv_op (BtorMBT *, unsigned);
static void *btormbt_state_arr_op (BtorMBT *, unsigned);
static void *btormbt_state_bv_fun (BtorMBT *, unsigned);
static void *btormbt_state_bv_uf (BtorMBT *, unsigned);
static void *btormbt_state_input (BtorMBT *, unsigned);
static void *btormbt_state_release (BtorMBT *, unsigned);
static void *btormbt_state_assume_assert (BtorMBT *, unsigned);
static void *btormbt_state_sat (BtorMBT *, unsigned);
static void *btormbt_state_dump (BtorMBT *, unsigned);
static void *btormbt_state_model_gen (BtorMBT *, unsigned);
static void *btormbt_state_model_inc (BtorMBT *, unsigned);
static void *btormbt_state_delete (BtorMBT *, unsigned);

static void *
btormbt_state_new (BtorMBT *mbt, unsigned r)
{
  RNG rng = initrng (r);

  /* number of initial inputs */
  mbt->max_inputs = pick (&rng, mbt->g_min_inputs, mbt->g_max_inputs);
  /* number of initial operations */
  mbt->max_ops = pick (&rng, mbt->g_min_ops_init, mbt->g_max_ops_init);

  // TODO (ma): UFs
  init_pd_inputs (mbt,
                  pick (&rng, mbt->g_min_vars_init, mbt->g_max_vars_init),
                  pick (&rng, mbt->g_min_consts_init, mbt->g_max_consts_init),
                  pick (&rng, mbt->g_min_arrays_init, mbt->g_max_arrays_init));

  /* no delete operation at init */
  init_pd_ops (
      mbt,
      pick (&rng, mbt->g_min_add_ops_init, mbt->g_max_add_ops_init),
      pick (&rng, mbt->g_min_release_ops_init, mbt->g_max_release_ops_init));

  /* no additional inputs at init */
  init_pd_add (
      mbt,
      pick (&rng, mbt->g_min_add_funs_init, mbt->g_max_add_funs_init),
      pick (&rng, mbt->g_min_add_uf_init, mbt->g_max_add_uf_init),
      pick (&rng, mbt->g_min_add_arrayops_init, mbt->g_max_add_arrayops_init),
      pick (&rng, mbt->g_min_add_bitvecops_init, mbt->g_max_add_bitvecops_init),
      pick (&rng, mbt->g_min_add_inputs_init, mbt->g_max_add_inputs_init));

  BTORMBT_LOG (1,
               "new: pick %d ops (add:rel=%0.1f%%:%0.1f%%), %d inputs",
               mbt->max_ops,
               mbt->p_add / 10,
               mbt->p_release / 10,
               mbt->max_inputs);

  mbt->btor = boolector_new ();
  assert (mbt->btor);
  // TODO (ma): move to opt
  if (mbt->shadow)
  {
    BTORMBT_LOG (1, "initial shadow clone...");
    /* cleanup done by boolector */
    boolector_chkclone (mbt->btor);
  }

  return btormbt_state_opt;
}

static void *
btormbt_state_opt (BtorMBT *mbt, unsigned r)
{
  int i, set_sat_solver = 1;
  BtorMBTBtorOpt *btoropt;
  RNG rng = initrng (r);

  /* reset every round */
  mbt->dump        = 0;
  mbt->inc         = 0;
  mbt->mgen        = 0;
  mbt->print_model = 0;
  mbt->ext         = 0;

  /* set random sat solver */
#ifdef BTOR_USE_LINGELING
  if (!mbt->shadow && pick (&rng, 0, 1) && set_sat_solver)
  {
    boolector_set_sat_solver_lingeling (mbt->btor, 0, 0);
    set_sat_solver = 0;
  }
#endif
#ifdef BTOR_USE_PICOSAT
  if (!mbt->shadow && pick (&rng, 0, 1) && set_sat_solver)
  {
    boolector_set_sat_solver_picosat (mbt->btor);
    set_sat_solver = 0;
  }
#endif
#ifdef BTOR_USE_MINISAT
  if (!mbt->shadow && pick (&rng, 0, 1) && set_sat_solver)
    boolector_set_sat_solver_minisat (mbt->btor);
#endif

  /* set random options */
  for (i = 0; i < BTOR_COUNT_STACK (mbt->btor_opts); i++)
  {
    btoropt = BTOR_PEEK_STACK (mbt->btor_opts, i);
    if (!btoropt->set_by_cl)
    {
      /* choose options with probability 0.5 */
      if (!strcmp (btoropt->name, BTOR_OPT_INCREMENTAL)
          || !strcmp (btoropt->name, BTOR_OPT_MODEL_GEN))
      {
        if (pick (&rng, 0, 1)) continue;
      }
      else /* choose other options with probability 0.1 */
      {
        if (pick (&rng, 0, 9)) continue;
      }
      /* exclude some combinations of options (dependent on option order in
       * btoropts.h) */
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
      // FIXME remove as soon as ucopt works with mgen
      /* do not enable unconstrained optimization if either model
       * generation or incremental is enabled */
      if (!strcmp (btoropt->name, BTOR_OPT_UCOPT)
          && (boolector_get_opt_val (mbt->btor, BTOR_OPT_MODEL_GEN)
              || boolector_get_opt_val (mbt->btor, BTOR_OPT_INCREMENTAL)))
        continue;
#endif
      /* do not enable beta reduction probing if model generation is
       * enabled */
      if (!strcmp (btoropt->name, BTOR_OPT_PBRA)
          && boolector_get_opt_val (mbt->btor, BTOR_OPT_MODEL_GEN))
        continue;

      /* do not enable justification if dual propagation is enabled */
      if (!strcmp (btoropt->name, BTOR_OPT_JUST)
          && boolector_get_opt_val (mbt->btor, BTOR_OPT_DUAL_PROP))
        continue;

      btoropt->val = pick (&rng, btoropt->min, btoropt->max);
    }
    BTORMBT_LOG (1,
                 "opt: set boolector option '%s' to '%d'",
                 btoropt->name,
                 btoropt->val);
    /* if an option is set via command line the value is saved in
     * btoropt->val */
    boolector_set_opt (mbt->btor, btoropt->name, btoropt->val);

    /* set some mbt specific options */
    if (!strcmp (btoropt->name, BTOR_OPT_INCREMENTAL) && btoropt->val == 1)
      mbt->inc = 1;
    else if (!strcmp (btoropt->name, BTOR_OPT_MODEL_GEN) && btoropt->val > 0)
    {
      mbt->mgen = 1;
      if (pick (&rng, 0, NORM_VAL - 1) < mbt->p_print_model)
        mbt->print_model = 1;
    }
  }

  if (!mbt->inc && !mbt->mgen && pick (&rng, 0, NORM_VAL - 1) < mbt->p_dump)
    mbt->dump = 1;

  /* make formulas extensional with probability of 0.1 */
  if (pick (&rng, 0, 9)) mbt->ext = 1;

  return btormbt_state_init;
}

static void *
btormbt_state_init (BtorMBT *mbt, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  // TODO (ma): UFs?
  if (BTOR_COUNT_STACK (mbt->bo->exps) + BTOR_COUNT_STACK (mbt->bv->exps)
          + BTOR_COUNT_STACK (mbt->arr->exps)
      < mbt->max_inputs)
  {
    return btormbt_state_input;
  }

  // TODO (ma): UFs?
  /* generate at least one bool-var, one bv-var and one arr;
   * to ensure nonempty expression stacks */
  if (BTOR_COUNT_STACK (mbt->bo->exps) < 1)
    btormbt_var (mbt, &rng, BTORMBT_BO_T);
  if (BTOR_COUNT_STACK (mbt->bv->exps) < 1)
    btormbt_var (mbt, &rng, BTORMBT_BV_T);
  if (mbt->create_arrays && BTOR_COUNT_STACK (mbt->arr->exps) < 1)
    btormbt_array (mbt, &rng);

  if (mbt->ops < mbt->max_ops)
  {
    mbt->ops++;
    BTORMBT_LOG_STATUS (2, "init");
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < mbt->p_add)
      return btormbt_state_add;
    else
      return btormbt_state_release;
  }

  BTORMBT_LOG_STATUS (1, "init");
  mbt->bo->init_layer_size  = BTOR_COUNT_STACK (mbt->bo->exps);
  mbt->bv->init_layer_size  = BTOR_COUNT_STACK (mbt->bv->exps);
  mbt->arr->init_layer_size = BTOR_COUNT_STACK (mbt->arr->exps);

  /* adapt paramters for main */
  mbt->ops     = 0;
  mbt->max_ops = pick (&rng, mbt->g_min_ops, mbt->g_max_ops);
  /* how many operations should be assertions?
   * -> max_ops and nass should be in relation (the more ops, the more
   * assertions) in order to keep the sat/unsat ratio balanced */
  if (mbt->max_ops < mbt->g_max_ops_lower)
    mbt->max_ass = BTORMBT_MIN (
        mbt->max_ops,
        pick (&rng, mbt->g_min_asserts_lower, mbt->g_max_asserts_lower));
  else
    mbt->max_ass =
        pick (&rng, mbt->g_min_asserts_upper, mbt->g_max_asserts_upper);

  init_pd_inputs (mbt,
                  pick (&rng, mbt->g_min_vars, mbt->g_max_vars),
                  pick (&rng, mbt->g_min_consts, mbt->g_max_consts),
                  pick (&rng, mbt->g_min_arrays, mbt->g_max_arrays));
  init_pd_ops (mbt,
               pick (&rng, mbt->g_min_add_ops, mbt->g_max_add_ops),
               pick (&rng, mbt->g_min_release_ops, mbt->g_max_release_ops));
  init_pd_add (mbt,
               pick (&rng, mbt->g_min_add_funs, mbt->g_max_add_funs),
               pick (&rng, mbt->g_min_add_uf, mbt->g_max_add_uf),
               pick (&rng, mbt->g_min_add_arrayops, mbt->g_max_add_arrayops),
               pick (&rng, mbt->g_min_add_bitvecops, mbt->g_max_add_bitvecops),
               pick (&rng, mbt->g_min_add_inputs, mbt->g_max_add_inputs));

  BTORMBT_LOG (
      1,
      "main: pick %d ops (add:rel=%0.1f%%:%0.1f%%), ~%d asserts/assumes",
      mbt->max_ops,
      mbt->p_add / 10,
      mbt->p_release / 10,
      mbt->max_ass);

  mbt->is_init = 1;
  return btormbt_state_main;
}

static void *
btormbt_state_main (BtorMBT *mbt, unsigned r)
{
  float rand;
  RNG rng = initrng (r);

  assert (BTOR_COUNT_STACK (mbt->bo->exps) > 0);
  assert (BTOR_COUNT_STACK (mbt->bv->exps) > 0);
  assert (!mbt->create_arrays || BTOR_COUNT_STACK (mbt->arr->exps) > 0);

  /* main operations */
  if (mbt->ops < mbt->max_ops)
  {
    mbt->ops++;
    BTORMBT_LOG_STATUS (2, "main");
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < mbt->max_ass * NORM_VAL / mbt->max_ops)
      return btormbt_state_assume_assert;
    else
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < mbt->p_add)
        return btormbt_state_add;
      else
        return btormbt_state_release;
    }
  }

  BTORMBT_LOG_STATUS (1, "main");
  BTORMBT_LOG (
      1, "main: asserts %d, assumes %d", mbt->tot_asserts, mbt->assumes);

  if (mbt->dump) return btormbt_state_dump;

  return btormbt_state_sat;
}

static void *
btormbt_state_add (BtorMBT *mbt, unsigned r)
{
  int rand;
  void *next;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);

  if (rand < mbt->p_bitvec_op)
    next = btormbt_state_bv_op;
  else if (mbt->create_arrays && rand < mbt->p_bitvec_op + mbt->p_array_op)
    next = btormbt_state_arr_op;
  else if (mbt->create_funs
           && rand < mbt->p_bitvec_op + mbt->p_array_op + mbt->p_bitvec_fun)
    next = btormbt_state_bv_fun;
  else if (mbt->create_ufs
           && rand < mbt->p_bitvec_op + mbt->p_array_op + mbt->p_bitvec_fun
                         + mbt->p_bitvec_uf)
    next = btormbt_state_bv_uf;
  else
    next = btormbt_state_input;

  return next;
}

static void *
btormbt_state_bv_op (BtorMBT *mbt, unsigned r)
{
  BoolectorNode *e0, *e1, *e2;
  RNG rng = initrng (r);

  Op op = pick (&rng, NOT, COND);

  if (is_unary_op (op))
  {
    e0 = select_exp (mbt, &rng, BTORMBT_BB_T, 0);
    btormbt_unary_op (mbt, &rng, op, e0);
  }
  else if (is_binary_op (op))
  {
    e0 = select_exp (
        mbt,
        &rng,
        ((op >= IMPLIES && op <= IFF) ? BTORMBT_BO_T : BTORMBT_BB_T),
        0);
    e1 = select_exp (
        mbt,
        &rng,
        ((op >= IMPLIES && op <= IFF) ? BTORMBT_BO_T : BTORMBT_BB_T),
        0);
    btormbt_binary_op (mbt, &rng, op, e0, e1);
  }
  else
  {
    assert (is_ternary_op (op));
    e0 = select_exp (mbt, &rng, BTORMBT_BO_T, 0);
    // TODO (ma): BTORMBT_BO_T also possible for e1 and e2
    e1 = select_exp (mbt, &rng, BTORMBT_BB_T, 0);
    e2 = select_exp (mbt, &rng, BTORMBT_BB_T, 0);
    btormbt_ternary_op (mbt, &rng, op, e0, e1, e2);
  }
  return (mbt->is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_arr_op (BtorMBT *mbt, unsigned r)
{
  int e0w, e0iw, rand;
  Op op;
  BoolectorNode *e0, *e1, *e2;
  RNG rng;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  e0   = select_exp (mbt, &rng, BTORMBT_ARR_T, 0);
  e0w  = boolector_get_width (mbt->btor, e0);
  e0iw = boolector_get_index_width (mbt->btor, e0);

  e2 = NULL;

  /* use read/write with p=0.666 else EQ/NE/COND */
  if (rand < mbt->p_rw)
  {
    rand = pick (&rng, 0, NORM_VAL - 1);
    op   = rand < mbt->p_read ? READ : WRITE;
    e1   = select_exp (mbt, &rng, BTORMBT_BV_T, 0);
    if (op == WRITE) e2 = select_exp (mbt, &rng, BTORMBT_BV_T, 0);
    btormbt_array_op (mbt, &rng, op, e0, e1, e2);
  }
  else
  {
    /* select EQ/NE/COND with same propability */
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (!mbt->ext || rand < mbt->p_cond)
      op = COND;
    else
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      op   = rand < mbt->p_eq ? EQ : NE;
    }
    e1 = select_arr_exp (
        mbt, &rng, e0, e0w, e0iw, op == EQ || op == NE ? -1 : 0);
    if (op == COND) e2 = select_exp (mbt, &rng, BTORMBT_BO_T, 0);
    btormbt_array_op (mbt, &rng, op, e0, e1, e2);
  }

  return (mbt->is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_bv_uf (BtorMBT *mbt, unsigned r)
{
  btormbt_bv_uf (mbt, r);
  return mbt->is_init ? btormbt_state_main : btormbt_state_init;
}

static void *
btormbt_state_bv_fun (BtorMBT *mbt, unsigned r)
{
  assert (!mbt->parambo);
  assert (!mbt->parambv);
  assert (!mbt->paramarr);
  assert (!mbt->paramfun);

  btormbt_bv_fun (mbt, r, 0);
  assert (!mbt->parambo);
  assert (!mbt->parambv);
  assert (!mbt->paramarr);
  assert (!mbt->paramfun);
  return (mbt->is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_input (BtorMBT *mbt, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  // TODO (ma): UFs?
  rand = pick (&rng, 0, NORM_VAL - 1);
  if (mbt->create_arrays && rand < mbt->p_array) btormbt_array (mbt, &rng);
  if (rand < mbt->p_var)
    btormbt_var (mbt, &rng, BTORMBT_BB_T);
  else
    btormbt_const (mbt, &rng);

  return (mbt->is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_release (BtorMBT *mbt, unsigned r)
{
  int idx, rand;
  BoolectorNode *node;
  BtorMBTExpStack *stack;
  RNG rng = initrng (r);

  /* select target exp stack with probabilty proportional to size */
  rand =
      pick (&rng,
            0,
            BTOR_COUNT_STACK (mbt->bo->exps) + BTOR_COUNT_STACK (mbt->bv->exps)
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
    idx  = pick (&rng, 0, BTOR_COUNT_STACK (stack->exps) - 1);
    node = BTOR_PEEK_STACK (stack->exps, idx)->exp;
    assert (stack != mbt->bo || boolector_get_width (mbt->btor, node) == 1);
    assert (stack != mbt->bv || boolector_get_width (mbt->btor, node) > 1);
    assert (stack != mbt->arr || boolector_is_array (mbt->btor, node));
    btormbt_release_node (mbt, node);
    btormbt_del_exp_stack (mbt->mm, stack, idx);
  }
  return (mbt->is_init ? btormbt_state_main : btormbt_state_init);
}

static void *
btormbt_state_assume_assert (BtorMBT *mbt, unsigned r)
{
  int rand;
  BoolectorNode *node;
  RNG rng = initrng (r);

#if 0
  int lower;
  /* select from init layer with lower probability */
  lower = mbt->bo->init_layer_size
    && BTOR_COUNT_STACK (mbt->bo->exps) > mbt->bo->init_layer_size
          && pick (&rng, 0, 4) ?  mbt->bo->init_layer_size - 1 : 0;
  node = btormbt_clause (mbt, &rng, lower, BTOR_COUNT_STACK (mbt->bo->exps) - 1);
  assert (!BTOR_REAL_ADDR_NODE (node)->parameterized);
#else
  node = btormbt_constraint (mbt, &rng);
#endif
  rand = pick (&rng, 0, NORM_VAL - 1);
  if (mbt->inc && rand < mbt->p_assume)
  {
    boolector_assume (mbt->btor, node);
    btormbt_push_exp_stack (mbt->mm, mbt->assumptions, node);
    mbt->assumes++;
  }
  else
  {
    boolector_assert (mbt->btor, node);
    btormbt_release_node (mbt, node);
    mbt->asserts++;
    mbt->tot_asserts++;
  }
  return btormbt_state_main;
}

static void *
btormbt_state_dump (BtorMBT *mbt, unsigned r)
{
  assert (!mbt->inc);
  assert (!mbt->mgen);

  int rand;
  RNG rng;
  rng = initrng (r);

  // TODO (ma): UF support in BTOR format not yet implemented
  // TODO (ma): SMT1 dumping not possible for extensional benchmarks (lambdas
  //		cannot be eliminated)
  if (mbt->output_format)
  {
    if (!strcmp (mbt->output_format, "btor")
        && !BTOR_COUNT_STACK (mbt->uf->exps))
      boolector_dump_btor (mbt->btor, stdout);
    else if (!mbt->ext && !strcmp (mbt->output_format, "smt1"))
      boolector_dump_smt1 (mbt->btor, stdout);
    else if (!strcmp (mbt->output_format, "smt2"))
      boolector_dump_smt2 (mbt->btor, stdout);
  }
  else
  {
    rand = pick (&rng, 0, 2);
    if (rand == 0 && !BTOR_COUNT_STACK (mbt->uf->exps))
      boolector_dump_btor (mbt->btor, stdout);
    else if (!mbt->ext && rand == 1)
      boolector_dump_smt1 (mbt->btor, stdout);
    else
      boolector_dump_smt2 (mbt->btor, stdout);
  }
  return btormbt_state_delete;
}

static void *
btormbt_state_sat (BtorMBT *mbt, unsigned r)
{
  int i, res, failed;
  RNG rng;
  BoolectorNode *ass;

  rng = initrng (r);

  if (mbt->shadow && !pick (&rng, 0, 50))
  {
    BTORMBT_LOG (1, "cloning...");
    /* cleanup done by boolector */
    boolector_chkclone (mbt->btor);
  }

  BTORMBT_LOG (1, "calling sat...");
  res = boolector_sat (mbt->btor);
  if (res == BOOLECTOR_UNSAT)
  {
    BTORMBT_LOG (1, "unsat");
    g_btormbtstats->num_unsat++;
  }
  else if (res == BOOLECTOR_SAT)
  {
    BTORMBT_LOG (1, "sat");
    g_btormbtstats->num_sat++;
    if (mbt->print_model)
    {
      if (pick (&rng, 0, NORM_VAL - 1) < mbt->p_model_format)
        boolector_print_model (mbt->btor, "btor", stdout);
      else
        boolector_print_model (mbt->btor, "smt2", stdout);
    }
  }
  else
    BTORMBT_LOG (1, "sat call returned %d", res);

  if (res == BOOLECTOR_UNSAT)
  {
    /* check failed assumptions */
    for (i = 0; i < BTOR_COUNT_STACK (mbt->assumptions->exps); i++)
    {
      ass = BTOR_PEEK_STACK (mbt->assumptions->exps, i)->exp;
      assert (ass);
      failed = boolector_failed (mbt->btor, ass);
      BTORMBT_LOG (1, "assumption %p failed: %d", ass, failed);
    }
  }
  /* release assumptions */
  while (!BTOR_EMPTY_STACK (mbt->assumptions->exps))
  {
    ass = btormbt_pop_exp_stack (mbt->mm, mbt->assumptions);
    assert (ass);
    btormbt_release_node (mbt, ass);
  }
  btormbt_reset_exp_stack (mbt->mm, mbt->assumptions);

  return mbt->mgen && res == BOOLECTOR_SAT ? btormbt_state_model_gen
                                           : btormbt_state_model_inc;
}

static void *
btormbt_state_model_gen (BtorMBT *mbt, unsigned r)
{
  (void) r;
  int i, size = 0;
  const char *bv = NULL;
  char **indices = NULL, **values = NULL;

  assert (mbt->mgen);

  for (i = 0; i < BTOR_COUNT_STACK (mbt->bo->exps); i++)
  {
    bv = boolector_bv_assignment (mbt->btor, mbt->bo->exps.start[i]->exp);
    boolector_free_bv_assignment (mbt->btor, (char *) bv);
  }
  for (i = 0; i < BTOR_COUNT_STACK (mbt->bv->exps); i++)
  {
    bv = boolector_bv_assignment (mbt->btor, mbt->bv->exps.start[i]->exp);
    boolector_free_bv_assignment (mbt->btor, (char *) bv);
  }
  for (i = 0; i < BTOR_COUNT_STACK (mbt->arr->exps); i++)
  {
    boolector_array_assignment (
        mbt->btor, mbt->arr->exps.start[i]->exp, &indices, &values, &size);
    if (size > 0)
      boolector_free_array_assignment (mbt->btor, indices, values, size);
  }
  for (i = 0; i < BTOR_COUNT_STACK (mbt->uf->exps); i++)
  {
    boolector_uf_assignment (
        mbt->btor, mbt->uf->exps.start[i]->exp, &indices, &values, &size);
    if (size > 0)
      boolector_free_uf_assignment (mbt->btor, indices, values, size);
  }
  return btormbt_state_model_inc;
}

static void *
btormbt_state_model_inc (BtorMBT *mbt, unsigned r)
{
  int i, rand;
  RNG rng;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  /* release cnf expressions */
  for (i = 0; i < BTOR_COUNT_STACK (mbt->cnf->exps); i++)
    btormbt_release_node (mbt, mbt->cnf->exps.start[i]->exp);
  btormbt_reset_exp_stack (mbt->mm, mbt->cnf);

  if (mbt->inc && rand < mbt->p_inc)
  {
    mbt->inc++;
    mbt->ops     = 0; /* reset */
    mbt->max_ass = mbt->max_ass - mbt->asserts;
    mbt->assumes = 0; /* reset */
    mbt->asserts = 0;

    mbt->max_ops = pick (&rng, mbt->g_min_ops_inc, mbt->g_max_ops_inc);

    init_pd_inputs (mbt,
                    pick (&rng, mbt->g_min_vars_inc, mbt->g_max_vars_inc),
                    pick (&rng, mbt->g_min_consts_inc, mbt->g_max_consts_inc),
                    pick (&rng, mbt->g_min_arrays_inc, mbt->g_max_arrays_inc));
    init_pd_ops (
        mbt,
        pick (&rng, mbt->g_min_add_ops_inc, mbt->g_max_add_ops_inc),
        pick (&rng, mbt->g_min_release_ops_inc, mbt->g_max_release_ops_inc));
    init_pd_add (
        mbt,
        pick (&rng, mbt->g_min_add_funs_inc, mbt->g_max_add_funs_inc),
        pick (&rng, mbt->g_min_add_uf_inc, mbt->g_max_add_uf_inc),
        pick (&rng, mbt->g_min_add_arrayops_inc, mbt->g_max_add_arrayops_inc),
        pick (&rng, mbt->g_min_add_bitvecops_inc, mbt->g_max_add_bitvecops_inc),
        pick (&rng, mbt->g_min_add_inputs_inc, mbt->g_max_add_inputs_inc));
    BTORMBT_LOG (1,
                 "inc: pick %d ops (add:rel=%0.1f%%:%0.1f%%)",
                 mbt->max_ops,
                 mbt->p_add / 10,
                 mbt->p_release / 10);
    if (mbt->inc) BTORMBT_LOG (1, "number of increments: %d", mbt->inc - 1);

    return btormbt_state_main;
  }
  return btormbt_state_delete;
}

static void *
btormbt_state_delete (BtorMBT *mbt, unsigned r)
{
  (void) r;
  assert (mbt);
  assert (mbt->btor);

  RELEASE_EXP_STACK (bo);
  RELEASE_EXP_STACK (bv);
  RELEASE_EXP_STACK (arr);
  RELEASE_EXP_STACK (fun);
  RELEASE_EXP_STACK (uf);
  RELEASE_EXP_STACK (cnf);
  RELEASE_EXP_STACK (assumptions);

  RELEASE_SORT_STACK (bv_sorts);
  RELEASE_SORT_STACK (fun_sorts);

  assert (mbt->parambo == NULL);
  assert (mbt->parambv == NULL);
  assert (mbt->paramarr == NULL);
  assert (mbt->paramfun == NULL);

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
  assert (!mbt->cnf);
  assert (!mbt->parambo);
  assert (!mbt->parambv);
  assert (!mbt->paramarr);
  assert (!mbt->paramfun);
  assert (!mbt->bv_sorts);
  assert (!mbt->fun_sorts);

  memset (&mbt->is_init, 0, (char *) &mbt->rng - (char *) &mbt->is_init);

  mbt->assumptions = btormbt_new_exp_stack (mbt->mm);
  mbt->bo          = btormbt_new_exp_stack (mbt->mm);
  mbt->bv          = btormbt_new_exp_stack (mbt->mm);
  mbt->arr         = btormbt_new_exp_stack (mbt->mm);
  mbt->fun         = btormbt_new_exp_stack (mbt->mm);
  mbt->uf          = btormbt_new_exp_stack (mbt->mm);
  mbt->cnf         = btormbt_new_exp_stack (mbt->mm);
  mbt->bv_sorts    = btormbt_new_sort_stack (mbt->mm);
  mbt->fun_sorts   = btormbt_new_sort_stack (mbt->mm);
  mbt->rng.z = mbt->rng.w = mbt->seed;
}

static int
run (BtorMBT *mbt)
{
  assert (mbt);

  BtorMBTState state, next;
  unsigned rand;
  int status, null;
  pid_t id;

  if (!mbt->seeded && (id = fork ()))
  {
    mbt->forked++;
    fflush (stdout);
    reset_alarm ();
#ifndef NDEBUG
    pid_t wid =
#endif
        wait (&status);
    assert (wid == id);
  }
  else
  {
    if (g_set_alarm)
    {
      set_alarm ();
      BTORMBT_LOG (1, "set time limit to %d second(s)", g_set_alarm);
    }

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
    for (state = btormbt_state_new; state; state = next)
    {
      rand = nextrand (&mbt->rng);
      next = state (mbt, rand);
    }

    btormbt_delete_btormbt (g_btormbt);
    exit (EXIT_OK);
  }

  return status;
}

/*------------------------------------------------------------------------*/

int
main (int argc, char **argv)
{
  int exitcode;
  int i, j, val, mac, pid, prev, res, status;
  char *name, *cmd, *tmp;
  int namelen, cmdlen, tmppid, fd;
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
    else if (!strcmp (argv[i], "-ha") || !strcmp (argv[i], "--help-advanced"))
    {
      printf ("%s", BTORMBT_USAGE);
      printf ("%s", BTORMBT_USAGE_ADVANCED);
      exitcode = EXIT_OK;
      goto EXIT;
    }
    else if (!strcmp (argv[i], "-v") || !strcmp (argv[i], "--verbose"))
    {
      g_btormbt->verbosity++;
    }
    else if (!strcmp (argv[i], "-q") || !strcmp (argv[i], "--quiet"))
    {
      g_btormbt->quiet = true;
    }
    else if (!strcmp (argv[i], "-k") || !strcmp (argv[i], "--keep-lines"))
    {
      g_btormbt->terminal = false;
    }
    else if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--shadow-clone"))
    {
      g_btormbt->shadow = 1;
    }
    else if (!strcmp (argv[i], "-o") || !strcmp (argv[i], "--out"))
    {
      if (++i == argc) btormbt_error ("argument to '-o' missing (try '-h')");
      if (argv[i][0] == '-')
        btormbt_error ("invalid output directory given (try '-h')");
      g_btormbt->out = argv[i];
      DIR *dir       = opendir (argv[i]);
      if (dir)
        closedir (dir);
      else
        btormbt_error ("given output directory does not exist");
    }
    else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--quit-after-first"))
    {
      g_btormbt->quit_after_first = 1;
    }
    else if (!strcmp (argv[i], "-m"))
    {
      if (++i == argc) btormbt_error ("argument to '-m' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument '%s' to '-m' is not a number (try '-h')",
                       argv[i]);
      g_btormbt->g_max_rounds = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "-t"))
    {
      if (++i == argc) btormbt_error ("argument to '-t' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument '%s' to '-t' is not a number (try '-h')",
                       argv[i]);
      g_set_alarm = atoi (argv[i]);
    }
    else if (!strncmp (argv[i], "--logic", 7))
    {
      if (++i == argc)
        btormbt_error ("argument to '--logic' missing (try '-h')");
      if (!strcmp (argv[i], "QF_BV"))
      {
        g_btormbt->create_funs   = false;
        g_btormbt->create_ufs    = false;
        g_btormbt->create_arrays = false;
      }
      else if (!strcmp (argv[i], "QF_UFBV"))
      {
        g_btormbt->create_funs   = false;
        g_btormbt->create_ufs    = true;
        g_btormbt->create_arrays = false;
      }
      else if (!strcmp (argv[i], "QF_ABV"))
      {
        g_btormbt->create_funs   = false;
        g_btormbt->create_ufs    = false;
        g_btormbt->create_arrays = true;
      }
      else if (!strcmp (argv[i], "QF_AUFBV"))
      {
        g_btormbt->create_funs   = true;
        g_btormbt->create_ufs    = true;
        g_btormbt->create_arrays = true;
      }
      else
      {
        btormbt_error ("invalid argument to '--logic' (try '-h')");
      }
    }
    else if (!strcmp (argv[i], "-e") || !strcmp (argv[i], "--extensionality"))
    {
      g_btormbt->ext = 1;
    }
    /* boolector options */
    else if (!strcmp (argv[i], "-b"))
    {
      if (++i == argc) btormbt_error ("argument to '-b' missing (try '-h')");
      btoropt = 0;
      for (j = 0; j < BTOR_COUNT_STACK (g_btormbt->btor_opts); j++)
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
      val = (int) strtol (argv[i], &tmp, 10);
      if (tmp[0] != 0) btormbt_error ("invalid argument to '-b' (try '-h')");
      btoropt->val       = val;
      btoropt->set_by_cl = true;
    }

    /* advanced options */
    else if (!strcmp (argv[i], "--bw"))
    {
      if (++i == argc) btormbt_error ("argument to '--bw' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--bw' is not a number (try '-h')");
      g_btormbt->g_min_bw = atoi (argv[i]);
      if (g_btormbt->g_min_bw < MIN_BITWIDTH)
        btormbt_error (
            "min value of '--bw' must not be less than %d "
            "(try '-h')",
            MIN_BITWIDTH);
      if (++i == argc) btormbt_error ("argument to '--bw' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--bw' is not a number (try '-h')");
      g_btormbt->g_max_bw = atoi (argv[i]);
      if (g_btormbt->g_max_bw < g_btormbt->g_min_bw)
        btormbt_error (
            "min value for '--bw' must be less or equal than max value "
            "(try '-h')");
    }
    else if (!strcmp (argv[i], "--index-bw"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--index-bw' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--index-bw' is not a number (try '-h')");
      g_btormbt->g_min_index_bw = atoi (argv[i]);
      if (g_btormbt->g_min_index_bw < MIN_INDEXWIDTH)
        btormbt_error (
            "min value of '--index-bw' must not be less "
            "than %d (try '-h')",
            MIN_INDEXWIDTH);
      if (++i == argc)
        btormbt_error ("argument to '--index-bw' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--index-bw' is not a number (try '-h')");
      g_btormbt->g_max_index_bw = atoi (argv[i]);
      if (g_btormbt->g_max_index_bw < g_btormbt->g_min_index_bw)
        btormbt_error (
            "min value of '--index-bw' must be less or equal than max value "
            "(try '-h')");
    }
    else if (!strcmp (argv[i], "--muldiv-bw"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--muldiv-bw' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--muldiv-bw' is not a number (try '-h')");
      g_btormbt->g_min_muldiv_bw = atoi (argv[i]);
      if (g_btormbt->g_min_muldiv_bw < MIN_MULDIVWIDTH)
        btormbt_error (
            "min value of '--muldiv-bw' must not be less "
            "than %d (try '-h')",
            MIN_MULDIVWIDTH);
      if (++i == argc)
        btormbt_error ("argument to '--muldiv-bw' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--muldiv-bw' is not a number (try '-h')");
      g_btormbt->g_max_muldiv_bw = atoi (argv[i]);
      if (g_btormbt->g_max_muldiv_bw < g_btormbt->g_min_muldiv_bw)
        btormbt_error (
            "min value of '--muldiv-bw' must be less or equal than "
            "max value (try '-h')");
    }
    else if (!strcmp (argv[i], "--sort-fun-arity"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--sort-fun-arity' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--sort-fun-arity' is not a number (try '-h')");
      g_btormbt->g_min_sort_fun_arity = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--sort-fun-arity' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--sort-fun-arity' is not a number (try '-h')");
      g_btormbt->g_max_sort_fun_arity = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--inputs"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--inputs' is not a number (try '-h')");
      g_btormbt->g_min_inputs = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--inputs' is not a number (try '-h')");
      g_btormbt->g_max_inputs = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--vars-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--vars-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--vars-init' is not a number (try '-h')");
      g_btormbt->g_min_vars_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--vars-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--vars-init' is not a number (try '-h')");
      g_btormbt->g_max_vars_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--vars"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--vars' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--vars' is not a number (try '-h')");
      g_btormbt->g_min_vars = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--vars' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--vars' is not a number (try '-h')");
      g_btormbt->g_max_vars = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--vars-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--vars-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--vars-inc' is not a number (try '-h')");
      g_btormbt->g_min_vars_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--vars-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--vars-inc' is not a number (try '-h')");
      g_btormbt->g_max_vars_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--consts-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--consts-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--consts-init' is not a number (try '-h')");
      g_btormbt->g_min_consts_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--consts-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--consts-init' is not a number (try '-h')");
      g_btormbt->g_max_consts_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--consts"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--consts' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--consts' is not a number (try '-h')");
      g_btormbt->g_min_consts = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--consts' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--consts' is not a number (try '-h')");
      g_btormbt->g_max_consts = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--consts-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--consts-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--consts-inc' is not a number (try '-h')");
      g_btormbt->g_min_consts_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--consts-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--consts-inc' is not a number (try '-h')");
      g_btormbt->g_max_consts_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--arrays-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--arrays-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--arrays-init' is not a number (try '-h')");
      g_btormbt->g_min_arrays_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--arrays-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--arrays-init' is not a number (try '-h')");
      g_btormbt->g_max_arrays_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--arrays"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--arrays' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--arrays' is not a number (try '-h')");
      g_btormbt->g_min_arrays = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--arrays' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--arrays' is not a number (try '-h')");
      g_btormbt->g_max_arrays = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--arrays-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--arrays-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--arrays-inc' is not a number (try '-h')");
      g_btormbt->g_min_arrays_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--arrays-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--arrays-inc' is not a number (try '-h')");
      g_btormbt->g_max_arrays_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-funs-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-funs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-funs-init' is not a number (try '-h')");
      g_btormbt->g_min_add_funs_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-funs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-funs-init' is not a number (try '-h')");
      g_btormbt->g_max_add_funs_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-funs"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-funs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--add-funs' is not a number (try '-h')");
      g_btormbt->g_min_add_funs = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-funs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--add-funs' is not a number (try '-h')");
      g_btormbt->g_max_add_funs = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-funs-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-funs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-funs-inc' is not a number (try '-h')");
      g_btormbt->g_min_add_funs_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-funs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-funs-inc' is not a number (try '-h')");
      g_btormbt->g_max_add_funs_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-arrayops-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-arrayops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-arrayops-init' is not a number (try '-h')");
      g_btormbt->g_min_add_arrayops_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-arrayops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-arrayops-init' is not a number (try '-h')");
      g_btormbt->g_max_add_arrayops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-arrayops"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-arrayops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-arrayops' is not a number (try '-h')");
      g_btormbt->g_min_add_arrayops = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-arrayops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-arrayops' is not a number (try '-h')");
      g_btormbt->g_max_add_arrayops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-arrayops-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-arrayops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-arrayops-inc' is not a number (try '-h')");
      g_btormbt->g_min_add_arrayops_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-arrayops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-arrayops-inc' is not a number (try '-h')");
      g_btormbt->g_max_add_arrayops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-bitvecops-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-bitvecops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-bitvecops-init' is not a number (try '-h')");
      g_btormbt->g_min_add_bitvecops_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-bitvecops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-bitvecops-init' is not a number (try '-h')");
      g_btormbt->g_max_add_bitvecops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-bitvecops"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-bitvecops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-bitvecops' is not a number (try '-h')");
      g_btormbt->g_min_add_bitvecops = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-bitvecops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-bitvecops' is not a number (try '-h')");
      g_btormbt->g_max_add_bitvecops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-bitvecops-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-bitvecops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-bitvecops-inc' is not a number (try '-h')");
      g_btormbt->g_min_add_bitvecops_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-bitvecops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-bitvecops-inc' is not a number (try '-h')");
      g_btormbt->g_max_add_bitvecops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-inputs-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-inputs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-inputs-init' is not a number (try '-h')");
      g_btormbt->g_min_add_inputs_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-inputs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-inputs-init' is not a number (try '-h')");
      g_btormbt->g_max_add_inputs_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-inputs"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--add-inputs' is not a number (try '-h')");
      g_btormbt->g_min_add_inputs = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--add-inputs' is not a number (try '-h')");
      g_btormbt->g_max_add_inputs = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-inputs-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-inputs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-inputs-inc' is not a number (try '-h')");
      g_btormbt->g_min_add_inputs_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-inputs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-inputs-inc' is not a number (try '-h')");
      g_btormbt->g_max_add_inputs_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--ops-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--ops-init' is not a number (try '-h')");
      g_btormbt->g_min_ops_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--ops-init' is not a number (try '-h')");
      g_btormbt->g_max_ops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--ops"))
    {
      if (++i == argc) btormbt_error ("argument to '--ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--ops' is not a number (try '-h')");
      g_btormbt->g_min_ops = atoi (argv[i]);
      if (++i == argc) btormbt_error ("argument to '--ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--ops' is not a number (try '-h')");
      g_btormbt->g_max_ops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--ops-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--ops-inc' is not a number (try '-h')");
      g_btormbt->g_min_ops_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--ops-inc' is not a number (try '-h')");
      g_btormbt->g_max_ops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-ops-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-ops-init' is not a number (try '-h')");
      g_btormbt->g_min_add_ops_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-ops-init' is not a number (try '-h')");
      g_btormbt->g_max_add_ops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-ops"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--add-ops' is not a number (try '-h')");
      g_btormbt->g_min_add_ops = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error ("argument to '--add-ops' is not a number (try '-h')");
      g_btormbt->g_max_add_ops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-ops-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--add-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-ops-inc' is not a number (try '-h')");
      g_btormbt->g_min_add_ops_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--add-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--add-ops-inc' is not a number (try '-h')");
      g_btormbt->g_max_add_ops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--release-ops-init"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--release-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--release-ops-init' is not a number (try '-h')");
      g_btormbt->g_min_release_ops_init = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--release-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--release-ops-init' is not a number (try '-h')");
      g_btormbt->g_max_release_ops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--release-ops"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--release-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--release-ops' is not a number (try '-h')");
      g_btormbt->g_min_release_ops = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--release-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--release-ops' is not a number (try '-h')");
      g_btormbt->g_max_release_ops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--release-ops-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--release-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--release-ops-inc' is not a number (try '-h')");
      g_btormbt->g_min_release_ops_inc = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--release-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--release-ops-inc' is not a number (try '-h')");
      g_btormbt->g_max_release_ops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--max-ops-lower"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--max-ops-lower' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--max-ops-lower' is not a number (try '-h')");
      g_btormbt->g_max_ops_lower = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--asserts-lower"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--asserts-lower' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--asserts-lower' is not a number (try '-h')");
      g_btormbt->g_min_asserts_lower = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--asserts-lower' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--asserts-lower' is not a number (try '-h')");
      g_btormbt->g_max_asserts_lower = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--asserts-upper"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--asserts-upper' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--asserts-upper' is not a number (try '-h')");
      g_btormbt->g_min_asserts_upper = atoi (argv[i]);
      if (++i == argc)
        btormbt_error ("argument to '--asserts-upper' missing (try '-h')");
      if (!isnumstr (argv[i]))
        btormbt_error (
            "argument to '--asserts-upper' is not a number (try '-h')");
      g_btormbt->g_max_asserts_upper = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--p-sort-bv"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-sort-bv' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-sort-bv' is not a number (try '-h')");
      g_btormbt->p_sort_bv = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_sort_bv > NORM_VAL)
        btormbt_error ("argument to '--p-sort-bv' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-sort-fun"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-sort-fun' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-sort-fun' is not a number (try '-h')");
      g_btormbt->p_sort_fun = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_sort_fun > NORM_VAL)
        btormbt_error ("argument to '--p-sort-fun' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-sort-fun-unary"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-sort-fun-unary' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error (
            "argument to '--p-sort-fun-unary' is not a number (try '-h')");
      g_btormbt->p_sort_fun_unary = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_sort_fun_unary > NORM_VAL)
        btormbt_error ("argument to '--p-sort-fun-unary' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-assume"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-assume' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-assume' is not a number (try '-h')");
      g_btormbt->p_assume = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_assume > NORM_VAL)
        btormbt_error ("argument to '--p-assume' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-param-exp"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-param-exp' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error (
            "argument to '--p-param-exp' is not a number (try '-h')");
      g_btormbt->p_param_exp = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_param_exp > NORM_VAL)
        btormbt_error ("argument to '--p-param-exp' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-param-arr-exp"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-param-arr-exp' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error (
            "argument to '--p-param-arr-exp' is not a number (try '-h')");
      g_btormbt->p_param_arr_exp = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_param_arr_exp > NORM_VAL)
        btormbt_error ("argument to '--p-param-arr-exp' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-apply-fun"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-apply-fun' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error (
            "argument to '--p-apply-fun' is not a number (try '-h')");
      g_btormbt->p_apply_fun = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_apply_fun > NORM_VAL)
        btormbt_error ("argument to '--p-apply-fun' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-apply-uf"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-apply-uf' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-apply-uf' is not a number (try '-h')");
      g_btormbt->p_apply_uf = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_apply_uf > NORM_VAL)
        btormbt_error ("argument to '--p-apply-uf' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-rw"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-rw' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-rw' is not a number (try '-h')");
      g_btormbt->p_rw = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_rw > NORM_VAL)
        btormbt_error ("argument to '--p-rw' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-read"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-read' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-read' is not a number (try '-h')");
      g_btormbt->p_read = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_read > NORM_VAL)
        btormbt_error ("argument to '--p-read' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-cond"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-cond' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-cond' is not a number (try '-h')");
      g_btormbt->p_cond = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_cond > NORM_VAL)
        btormbt_error ("argument to '--p-cond' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-eq"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-eq' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-eq' is not a number (try '-h')");
      g_btormbt->p_eq = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_eq > NORM_VAL)
        btormbt_error ("argument to '--p-eq' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-inc"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-inc' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-inc' is not a number (try '-h')");
      g_btormbt->p_inc = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_inc > NORM_VAL)
        btormbt_error ("argument to '--p-inc' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-dump"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-dump' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error ("argument to '--p-dump' is not a number (try '-h')");
      g_btormbt->p_dump = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_dump > NORM_VAL)
        btormbt_error ("argument to '--p-dump' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-print-model"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-print-model' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error (
            "argument to '--p-print-model' is not a number (try '-h')");
      g_btormbt->p_print_model = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_print_model > NORM_VAL)
        btormbt_error ("argument to '--p-print-model' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-model-format"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--p-model-format' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        btormbt_error (
            "argument to '--p-model-format' is not a number (try '-h')");
      g_btormbt->p_model_format = atof (argv[i]) * NORM_VAL;
      if (g_btormbt->p_print_model > NORM_VAL)
        btormbt_error ("argument to '--p-model-format' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--output-format"))
    {
      if (++i == argc)
        btormbt_error ("argument to '--output-format' missing (try '-h')");
      if (strcmp (argv[i], "btor") && strcmp (argv[i], "smt1")
          && strcmp (argv[i], "smt2"))
        btormbt_error ("argument to '--output-format' is invalid (try '-h')");
      g_btormbt->output_format = argv[i];
    }
    else if (!isnumstr (argv[i]))
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
  set_sig_handlers ();

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

  mac = hashmac ();
  for (g_btormbt->rounds = 0; g_btormbt->rounds < g_btormbt->g_max_rounds;
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
      prev = g_btormbt->seed = abs (g_btormbt->seed) >> 1;

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
        namelen = 40 + btor_num_digits_util (tmppid);
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
                 + btor_num_digits_util (g_btormbt->seed);
        BTOR_NEWN (g_btormbt->mm, cmd, cmdlen);
        sprintf (cmd,
                 "cp %s %s/btormbt-bug-%d.trace",
                 name,
                 g_btormbt->out,
                 g_btormbt->seed);
      }
      else
      {
        cmdlen = 40 + strlen (name) + btor_num_digits_util (g_btormbt->seed);
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
    else if (res == EXIT_TIMEOUT)
    {
      BTORMBT_LOG (1, "TIMEOUT: time limit %d seconds reached\n", g_set_alarm);
      if (!g_btormbt->verbosity)
        printf ("timed out after %d second(s)\n", g_set_alarm);
    }
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
