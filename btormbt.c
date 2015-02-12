/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Christian Reisenberger.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolector.h"
#include "btorcore.h"

#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

// TODO externalize all parameters

/*------------------------------------------------------------------------*/

#define NORM_VAL 1000.0f

#define MAX_BITWIDTH 128 /* must be >= 2 */
#define MAX_INDEXWIDTH 8
#define MAX_MULDIVWIDTH 8

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

#ifndef NBTORLOG
#define BTORMBT_LOG_USAGE \
  "  --blog <loglevel>                enable boolector logging\n"
#else
#define BTORMBT_LOG_USAGE ""
#endif

#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
#define BTORMBT_UCOPT_USAGE \
  "  -uc, --enable-ucopt              enable unconstrained optimization\n"
#else
#define BTORMBT_UCOPT_USAGE ""
#endif

#define BTORMBT_USAGE                                                          \
  "usage: btormbt [<option>]\n"                                                \
  "\n"                                                                         \
  "where <option> is one of the following:\n"                                  \
  "\n"                                                                         \
  "  -h, --help                       print this message and exit\n"           \
  "  -ha, --help-advanced             print all options\n"                     \
  "  -v, --verbose                    be verbose\n"                            \
  "  -q, --quiet                      be quiet (only print stats)\n"           \
  "  -k, --keep-lines                 do not clear output lines\n"             \
  "  -n, --no-modelgen                do not enable model generation \n"       \
  "  -e, --extensionality             use extensionality\n"                    \
  "  -dp, --dual-prop                 enable dual prop optimization\n"         \
  "  -ju, --justification             enable justification "                   \
  "optimization\n" BTORMBT_UCOPT_USAGE                                         \
  "  -s, --shadow                     create and check shadow clone\n"         \
  "  -o, --out                        output directory for saving traces\n"    \
  "\n"                                                                         \
  "  -f, --quit-after-first           quit after first bug encountered\n"      \
  "  -m <maxruns>                     quit after <maxruns> rounds\n"           \
  "  -t <seconds>                     set time limit for calls to boolector\n" \
  "\n"                                                                         \
  "  --bverb <verblevel>              enable boolector "                       \
  "verbosity\n" BTORMBT_LOG_USAGE

#define BTORMBT_USAGE_ADVANCED \
  "\nadvanced options:\n" \
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
  "  --p-param-exp <val>              choose parameterized over\n" \
  "                                    non-parameterized expressions [" \
                                      BTORMBT_M2STR (P_PARAM_EXP) "]\n" \
  "  --p-param-arr-exp <val>          choose parameterized over\n" \
  "                                    non-parameterized array expressions [" \
                                      BTORMBT_M2STR (P_PARAM_ARR_EXP) "]\n" \
  "  --p-apply-fun <val>              choose apply on existing over new\n"\
  "                                    function [" \
                                      BTORMBT_M2STR (P_APPLY_FUN) "]\n" \
  "  --p-apply-uf <val>               choose apply on existing over new\n"\
  "                                    uninterpreted function [" \
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
  "                                    (btor,smt1,smt2)\n"

/*------------------------------------------------------------------------*/

#define BTORMBT_LOG(l, fmt, args...) \
  do                                 \
  {                                  \
    if (l <= btormbt->verbose)       \
    {                                \
      printf ("[btormbt] ");         \
      printf (fmt, ##args);          \
      printf ("\n");                 \
    }                                \
  } while (0)

#define BTORMBT_LOG_STATUS(l, prefix)                                   \
  BTORMBT_LOG (l,                                                       \
               prefix " (%d): bool %d, bv %d, array %d, fun %d, uf %d", \
               btormbt->ops,                                            \
               btormbt->bo.n,                                           \
               btormbt->bv.n,                                           \
               btormbt->arr.n,                                          \
               btormbt->fun.n,                                          \
               btormbt->uf.n);

/*------------------------------------------------------------------------*/

#define BTORMBT_MIN(x, y) ((x) < (y) ? (x) : (y))

/*------------------------------------------------------------------------*/

typedef struct RNG
{
  unsigned z, w;
} RNG;

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
  BoolectorNode *exp;
  int pars; /* number of parents */
} Exp;

typedef struct ExpStack
{
  Exp *exps;
  int size, n, sexp; /* marker for selected expressions */
  int initlayer;     /* marker for init layer */
} ExpStack;

typedef struct SortStack
{
  BoolectorSort **sorts;
  int size, n;
  //  int initlayer;
} SortStack;

typedef struct BtorMBT
{
  Btor *btor;

  double start_time;

  int seed;
  int seeded;
  int rounds;
  int bugs;
  int forked;
  int ppid; /* parent pid */

  int verbose;
  int quiet;
  int terminal;
  int quit_after_first;
  int force_nomgen;
  int ext;
  int dual_prop;
  int just;
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  int ucopt;
#endif
  int shadow;
  char *out;
  int time_limit;

  int bloglevel;
  int bverblevel;

  int g_max_rounds;

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
  int p_param_exp;     /* probability of choosing parameterized expressions
                          over non-parameterized expressions */
  int p_param_arr_exp; /* probability of choosing parameterized expressions
                          over non-parameterized array expressions */
  int p_apply_fun;     /* probability of choosing an apply on an existing
                          over an apply on a new function */
  int p_apply_uf;      /* probability of choosing an apply on an existing
                          over an apply on a new uninterpreted function */
  int p_rw;            /* probability of choosing read/write over
                          eq/ne/cond */
  int p_read;          /* probability of choosing read over write */
  int p_cond;          /* probability of choosing cond over eq/ne */
  int p_eq;            /* probability of choosing eq over ne */
  int p_inc;           /* probability of choosing an incremental step */
  int p_dump;          /* probability of dumping formula and exit */
  int p_print_model;   /* probability of printing the model after a sat call */
  int p_model_format;  /* probability of using btor over smt2 format when
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
  /* prob. distribution of assertions in current round */
  float p_ass;

  int ops;     /* number of operations in current round */
  int asserts; /* number of produced asserts in current round */
  int assumes; /* number of produced assumes in current round */

  int max_inputs; /* max number of inputs in current round */
  int max_ops;    /* max number of operations in current round */
  int max_ass;    /* max number of asserts / assumes in current round */

  int tot_asserts; /* total number of asserts in current round */

  ExpStack assumptions;
  ExpStack bo, bv, arr, fun, uf;
  ExpStack *parambo, *parambv, *paramarr;
  ExpStack cnf;
  SortStack bv_sorts, fun_sorts;

  RNG rng;
} BtorMBT;

typedef void *(*State) (BtorMBT *, unsigned rand);

/*------------------------------------------------------------------------*/

static BtorMBT *
new_btormbt (void)
{
  BtorMBT *btormbt;

  btormbt = malloc (sizeof (BtorMBT));
  memset (btormbt, 0, sizeof (BtorMBT));
  btormbt->g_max_rounds             = INT_MAX;
  btormbt->seed                     = -1;
  btormbt->seeded                   = 0;
  btormbt->terminal                 = isatty (1);
  btormbt->ext                      = 0;
  btormbt->g_min_inputs             = MIN_NLITS;
  btormbt->g_max_inputs             = MAX_NLITS;
  btormbt->g_min_vars_init          = MIN_NVARS_INIT;
  btormbt->g_max_vars_init          = MAX_NVARS_INIT;
  btormbt->g_min_vars               = MIN_NVARS;
  btormbt->g_max_vars               = MAX_NVARS;
  btormbt->g_min_vars_inc           = MIN_NVARS_INC;
  btormbt->g_max_vars_inc           = MAX_NVARS_INC;
  btormbt->g_min_consts_init        = MIN_NCONSTS_INIT;
  btormbt->g_max_consts_init        = MAX_NCONSTS_INIT;
  btormbt->g_min_consts             = MIN_NCONSTS;
  btormbt->g_max_consts             = MAX_NCONSTS;
  btormbt->g_min_consts_inc         = MIN_NCONSTS_INC;
  btormbt->g_max_consts_inc         = MAX_NCONSTS_INC;
  btormbt->g_min_arrays_init        = MIN_NARRS_INIT;
  btormbt->g_max_arrays_init        = MAX_NARRS_INIT;
  btormbt->g_min_arrays             = MIN_NARRS;
  btormbt->g_max_arrays             = MAX_NARRS;
  btormbt->g_min_arrays_inc         = MIN_NARRS_INC;
  btormbt->g_max_arrays_inc         = MAX_NARRS_INC;
  btormbt->g_min_add_funs_init      = MIN_NADDOPFUNS_INIT;
  btormbt->g_max_add_funs_init      = MAX_NADDOPFUNS_INIT;
  btormbt->g_min_add_funs           = MIN_NADDOPFUNS;
  btormbt->g_max_add_funs           = MAX_NADDOPFUNS;
  btormbt->g_min_add_funs_inc       = MIN_NADDOPFUNS_INC;
  btormbt->g_max_add_funs_inc       = MAX_NADDOPFUNS_INC;
  btormbt->g_min_add_uf_init        = MIN_NADDOPUF_INIT;
  btormbt->g_max_add_uf_init        = MAX_NADDOPUF_INIT;
  btormbt->g_min_add_uf             = MIN_NADDOPUF;
  btormbt->g_max_add_uf             = MAX_NADDOPUF;
  btormbt->g_min_add_uf_inc         = MIN_NADDOPUF_INC;
  btormbt->g_max_add_uf_inc         = MAX_NADDOPUF_INC;
  btormbt->g_min_add_arrayops_init  = MIN_NADDOPAFUNS_INIT;
  btormbt->g_max_add_arrayops_init  = MAX_NADDOPAFUNS_INIT;
  btormbt->g_min_add_arrayops       = MIN_NADDOPAFUNS;
  btormbt->g_max_add_arrayops       = MAX_NADDOPAFUNS;
  btormbt->g_min_add_arrayops_inc   = MIN_NADDOPAFUNS_INC;
  btormbt->g_max_add_arrayops_inc   = MAX_NADDOPAFUNS_INC;
  btormbt->g_min_add_bitvecops_init = MIN_NADDOPBFUNS_INIT;
  btormbt->g_max_add_bitvecops_init = MAX_NADDOPBFUNS_INIT;
  btormbt->g_min_add_bitvecops      = MIN_NADDOPBFUNS;
  btormbt->g_max_add_bitvecops      = MAX_NADDOPBFUNS;
  btormbt->g_min_add_bitvecops_inc  = MIN_NADDOPBFUNS_INC;
  btormbt->g_max_add_bitvecops_inc  = MAX_NADDOPBFUNS_INC;
  btormbt->g_min_add_inputs_init    = MIN_NADDOPLITS_INIT;
  btormbt->g_max_add_inputs_init    = MAX_NADDOPLITS_INIT;
  btormbt->g_min_add_inputs         = MIN_NADDOPLITS;
  btormbt->g_max_add_inputs         = MAX_NADDOPLITS;
  btormbt->g_min_add_inputs_inc     = MIN_NADDOPLITS_INC;
  btormbt->g_max_add_inputs_inc     = MAX_NADDOPLITS_INC;
  btormbt->g_min_ops_init           = MIN_NOPS_INIT;
  btormbt->g_max_ops_init           = MAX_NOPS_INIT;
  btormbt->g_min_ops                = MIN_NOPS;
  btormbt->g_max_ops                = MAX_NOPS;
  btormbt->g_min_ops_inc            = MIN_NOPS_INC;
  btormbt->g_max_ops_inc            = MAX_NOPS_INC;
  btormbt->g_min_add_ops_init       = MIN_NADDOPS_INIT;
  btormbt->g_max_add_ops_init       = MAX_NADDOPS_INIT;
  btormbt->g_min_add_ops            = MIN_NADDOPS;
  btormbt->g_max_add_ops            = MAX_NADDOPS;
  btormbt->g_min_add_ops_inc        = MIN_NADDOPS_INC;
  btormbt->g_max_add_ops_inc        = MAX_NADDOPS_INC;
  btormbt->g_min_release_ops_init   = MIN_NRELOPS_INIT;
  btormbt->g_max_release_ops_init   = MAX_NRELOPS_INIT;
  btormbt->g_min_release_ops        = MIN_NRELOPS;
  btormbt->g_max_release_ops        = MAX_NRELOPS;
  btormbt->g_min_release_ops_inc    = MIN_NRELOPS_INC;
  btormbt->g_max_release_ops_inc    = MAX_NRELOPS_INC;
  btormbt->g_min_asserts_lower      = MIN_NASSERTS_LOWER;
  btormbt->g_max_asserts_lower      = MAX_NASSERTS_LOWER;
  btormbt->g_min_asserts_upper      = MIN_NASSERTS_UPPER;
  btormbt->g_max_asserts_upper      = MAX_NASSERTS_UPPER;
  btormbt->p_param_exp              = P_PARAM_EXP * NORM_VAL;
  btormbt->p_param_arr_exp          = P_PARAM_ARR_EXP * NORM_VAL;
  btormbt->p_apply_fun              = P_APPLY_FUN * NORM_VAL;
  btormbt->p_apply_uf               = P_APPLY_UF * NORM_VAL;
  btormbt->p_rw                     = P_RW * NORM_VAL;
  btormbt->p_read                   = P_READ * NORM_VAL;
  btormbt->p_cond                   = P_COND * NORM_VAL;
  btormbt->p_eq                     = P_EQ * NORM_VAL;
  btormbt->p_inc                    = P_INC * NORM_VAL;
  btormbt->p_dump                   = P_DUMP * NORM_VAL;
  btormbt->p_print_model            = P_PRINT_MODEL * NORM_VAL;
  btormbt->p_model_format           = P_MODEL_FORMAT * NORM_VAL;
  return btormbt;
}

/*------------------------------------------------------------------------*/

static BtorMBT *btormbt;

void boolector_chkclone (Btor *);

/*------------------------------------------------------------------------*/

void
ss_init (SortStack *ss)
{
  memset (ss, 0, sizeof (SortStack));
}

static void
ss_push (SortStack *ss, BoolectorSort *sort)
{
  assert (ss);
  assert (sort);

  if (ss->n == ss->size)
  {
    ss->size  = ss->size ? ss->size * 2 : 2;
    ss->sorts = realloc (ss->sorts, ss->size * sizeof *ss->sorts);
  }
  ss->sorts[ss->n] = sort;
  ss->n++;
}

#if 0
static BoolectorSort *
ss_pop (SortStack * ss)
{
  if (!ss->n) return 0;
  ss->n -= 1;
  return ss->sorts[ss->n];
}

static void
ss_del (SortStack *ss, int idx)
{
  assert (ss);
  assert (idx >= 0 && idx < ss->n);

  int i;

  for (i = idx; i < ss->n - 1; i++)
    ss->sorts[i] = ss->sorts[i + 1];
  ss->n -= 1;
}

static void
ss_reset (SortStack * ss)
{
  assert (ss);
  ss->n = 0;
}
#endif

static void
ss_release (SortStack *ss)
{
  if (!ss) return;

  ss->n    = 0;
  ss->size = 0;
  free (ss->sorts);
  ss->sorts = 0;
}

void
es_init (ExpStack *es)
{
  memset (es, 0, sizeof (ExpStack));
}

void
es_push (ExpStack *es, BoolectorNode *exp)
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

BoolectorNode *
es_pop (ExpStack *es)
{
  BoolectorNode *res;

  if (!es->n) return 0;
  es->n -= 1;
  res = es->exps[es->n].exp;
  return res;
}

static void
es_del (ExpStack *es, int idx)
{
  assert (es);
  assert (idx >= 0 && idx < es->n);

  int i;

  for (i = idx; i < es->n - 1; i++) es->exps[i] = es->exps[i + 1];
  es->n -= 1;
  if (idx < es->sexp) es->sexp -= 1;
}

static void
es_reset (ExpStack *es)
{
  assert (es);

  es->n         = 0;
  es->sexp      = 0;
  es->initlayer = 0;
}

void
es_release (ExpStack *es)
{
  if (!es) return;

  es->n         = 0;
  es->size      = 0;
  es->sexp      = 0;
  es->initlayer = 0;
  free (es->exps);
  es->exps = NULL;
}

/*------------------------------------------------------------------------*/

/**
 * initialize probability distribution of inputs
 * parameter: ratio var:const:arr (e.g. 3:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_inputs (BtorMBT *btormbt,
                float ratio_var,
                float ratio_const,
                float ratio_arr)
{
  float sum;

  sum = ratio_var + ratio_const + ratio_arr;

  assert (sum > 0);

  btormbt->p_var   = (ratio_var * NORM_VAL) / sum;
  btormbt->p_const = (ratio_const * NORM_VAL) / sum;
  btormbt->p_array = (ratio_arr * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add operation
 * parameter: ratio fun:array_op:lit (e.g. 1:1:1)
 * normalized to NORM_VAL
 */
static void
init_pd_add (BtorMBT *btormbt,
             float ratio_fun,
             float ratio_uf,
             float ratio_afun,
             float ratio_bfun,
             float ratio_lit)
{
  float sum;

  sum = ratio_fun + ratio_uf + ratio_afun + ratio_lit;

  assert (sum > 0);

  btormbt->p_bitvec_fun = (ratio_fun * NORM_VAL) / sum;
  btormbt->p_bitvec_uf  = (ratio_uf * NORM_VAL) / sum;
  btormbt->p_array_op   = (ratio_afun * NORM_VAL) / sum;
  btormbt->p_bitvec_op  = (ratio_bfun * NORM_VAL) / sum;
  btormbt->p_input      = (ratio_lit * NORM_VAL) / sum;
}

/**
 * initialize probability distribution of add/release op
 * parameter: ratio addop:relop (e.g. 1:0)
 * normalized to NORM_VAL
 */
static void
init_pd_ops (BtorMBT *btormbt, float ratio_add, float ratio_release)
{
  float sum;

  sum = ratio_add + ratio_release;

  assert (sum > 0);

  btormbt->p_add     = (ratio_add * NORM_VAL) / sum;
  btormbt->p_release = (ratio_release * NORM_VAL) / sum;
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
is_ternary_fun (Op op)
{
  return op == COND;
}

static int
is_array_fun (Op op)
{
  return (op >= COND && op <= WRITE) || (op >= EQ && op <= NE);
}
#endif

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
static BoolectorNode *
modifybv (
    BtorMBT *btormbt, RNG *rng, BoolectorNode *e, int ew, int tow, int is_param)
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
    e = (pick (rng, 0, 1) ? boolector_uext (btormbt->btor, e, tow - ew)
                          : boolector_sext (btormbt->btor, e, tow - ew));
    es_push (es, e);
    es->exps[es->n - 1].pars++;
  }

  assert (tow == boolector_get_width (btormbt->btor, e));
  return e;
}

static void
create_var (BtorMBT *btormbt, RNG *rng, ExpType type)
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
create_const (BtorMBT *btormbt, RNG *rng)
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
create_array (BtorMBT *btormbt, RNG *rng)
{
  int ew = pick (rng, 1, MAX_BITWIDTH);
  int iw = pick (rng, 1, MAX_INDEXWIDTH);

  es_push (&btormbt->arr, boolector_array (btormbt->btor, ew, iw, NULL));
}

/* randomly select variables from bo within the range ifrom - ito */
static BoolectorNode *
create_clause (BtorMBT *btormbt, RNG *rng, int ifrom, int ito)
{
  int i, idx;
  BoolectorNode *e0, *e1;
  ExpStack *es;

  es = &btormbt->bo;
  e0 = NULL;
  /* make clause with 3 boolean expressions */
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
unary_op (BtorMBT *btormbt, RNG *rng, Op op, BoolectorNode *e0, int is_param)
{
  int tmp0, tmp1, e0w, rw;
  ExpStack *es;

  tmp0 = 0;
  tmp1 = 0;

  assert (is_unary_op (op));
  e0w = boolector_get_width (btormbt->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  /* set default result width */
  if (is_boolean_unary_op (op))
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
binary_op (BtorMBT *btormbt,
           RNG *rng,
           Op op,
           BoolectorNode *e0,
           BoolectorNode *e1,
           int is_param)
{
  int tmp0, tmp1, e0w, e1w, rw;
  ExpStack *es;

  assert (is_binary_op (op));
  e0w = boolector_get_width (btormbt->btor, e0);
  assert (e0w <= MAX_BITWIDTH);
  e1w = boolector_get_width (btormbt->btor, e1);
  assert (e1w <= MAX_BITWIDTH);

  /* set default result width */
  if (is_boolean_binary_op (op))
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
    e1 = modifybv (btormbt, rng, e1, e1w, e0w, is_param);
  }
  else if (op >= SLL && op <= ROR)
  {
    /* modify width of e0 power of 2 and e1 log2(e0) */
    nextpow2 (e0w, &tmp0, &tmp1);
    e0  = modifybv (btormbt, rng, e0, e0w, tmp0, is_param);
    e1  = modifybv (btormbt, rng, e1, e1w, tmp1, is_param);
    e0w = tmp0;
    rw  = e0w;
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
             BoolectorNode *e0,
             BoolectorNode *e1,
             BoolectorNode *e2,
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
  e2 = modifybv (btormbt, rng, e2, e2w, e1w, is_param);

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
array_op (BtorMBT *btormbt,
          RNG *rng,
          Op op,
          BoolectorNode *e0,
          BoolectorNode *e1,
          BoolectorNode *e2,
          int is_param)
{
  assert (e0);
  assert (e1);
  assert (boolector_is_array (btormbt->btor, e0));
  assert (is_array_fun (op));

  int e0w, e0iw, e1w, e2w;
  ExpStack *es;

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

/* Randomly select expression by given type. Nodes with no parents
 * (yet unused) are preferred.
 */
static BoolectorNode *
selexp (
    BtorMBT *btormbt, RNG *rng, ExpType type, int force_param, int *is_param)
{
  assert (force_param != 1 || (btormbt->parambo && btormbt->parambo->n)
          || (btormbt->parambv && btormbt->parambv->n)
          || (btormbt->paramarr && btormbt->paramarr->n));

  int rand, i, bw, idx = -1;
  ExpStack *es, *bo, *bv, *arr;
  BoolectorNode *exp, *e[3];

  /* choose between param. exps and non-param. exps */
  rand = pick (rng, 0, NORM_VAL - 1);
  assert ((!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr)
          || (btormbt->parambo && btormbt->parambv && btormbt->paramarr));
  if (force_param == -1
      || (!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr)
      || (!btormbt->parambo->n && !btormbt->parambv->n && !btormbt->paramarr->n)
      || (force_param == 0 && rand >= btormbt->p_param_exp))
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
      array_op (btormbt, rng, WRITE, e[0], e[1], e[2], 1);
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
static BoolectorNode *
selarrexp (BtorMBT *btormbt,
           RNG *rng,
           BoolectorNode *exp,
           int eew,
           int eiw,
           int force_param)
{
  int i, rand, idx, sel_eew, sel_eiw;
  ExpStack *es;
  BoolectorNode *sel_e, *e[3];

  /* choose between param. exps and non-param. array exps */
  rand = pick (rng, 0, NORM_VAL - 1);
  assert ((!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr)
          || (btormbt->parambo && btormbt->parambv && btormbt->paramarr));
  if (force_param == -1
      || (!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr)
      || (!btormbt->parambo->n && !btormbt->parambv->n && !btormbt->paramarr->n)
      || (force_param == 0 && rand >= btormbt->p_param_arr_exp))
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
    array_op (btormbt, rng, WRITE, e[0], e[1], e[2], 1);
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
  BoolectorNode *e[3];
  Op op;

  assert (op_from >= NOT && op_from <= COND);
  assert (op_to >= NOT && op_to <= COND);

  op = pick (rng, op_from, op_to);
  if (is_unary_op (op))
  {
    e[0] = selexp (btormbt, rng, T_BB, 1, NULL);
    unary_op (btormbt, rng, op, e[0], 1);
  }
  else if (is_binary_op (op))
  {
    rand = pick (rng, 0, 1);
    for (i = 0; i < 2; i++)
      e[i] = selexp (btormbt,
                     rng,
                     ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB),
                     i == rand ? 1 : 0,
                     NULL);
    binary_op (btormbt, rng, op, e[0], e[1], 1);
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
  BoolectorNode *e[3];
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
    op = rand >= 0 && pick (rng, 0, 2) && btormbt->ext ? pick (rng, EQ, NE)
                                                       : COND;
    e[1] =
        selarrexp (btormbt, rng, e[0], eew, eiw, rand == -1 ? rand : rand ^ 1);
    if (op == COND) e[2] = selexp (btormbt, rng, T_BO, rand < 0 ? 1 : 0, NULL);
  }
  array_op (btormbt, rng, op, e[0], e[1], e[2], 1);
}

static void
bitvec_fun (BtorMBT *btormbt, unsigned r, int *nparams, int *width, int nlevel)
{
  int i, n, np, ip, w, max_ops, rand;
  ExpStack parambo, parambv, paramarr;
  ExpStack *es, *tmpparambo, *tmpparambv, *tmpparamarr;
  BoolectorNode *tmp, *fun, **params, **args;
  RNG rng;

  rng = initrng (r);
  /* choose between apply on random existing and apply on new function */
  rand = pick (&rng, 0, NORM_VAL - 1);
  if (btormbt->fun.n && rand < btormbt->p_apply_fun) /* use existing function */
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
    params   = malloc (sizeof (BoolectorNode *) * *nparams);
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
    max_ops = pick (&rng, 0, MAX_NPARAMOPS);
    n       = 0;
  BFUN_PICK_FUN_TYPE:
    while (n++ < max_ops)
    {
      assert (parambo.n);
      assert (parambv.n);
      assert (paramarr.n);
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < btormbt->p_bitvec_fun)
        param_fun (btormbt, &rng, NOT, COND);
      else if (rand < btormbt->p_bitvec_fun + btormbt->p_array_op)
        param_afun (btormbt, &rng, 0);
      else
      {
        if (nlevel < MAX_NNESTEDBFUNS)
        {
          bitvec_fun (btormbt, nextrand (&rng), &np, &w, nlevel + 1);
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
    fun  = boolector_fun (btormbt->btor, params, *nparams, es->exps[rand].exp);
    es_push (&btormbt->fun, fun);

    /* reset scope for arguments to apply node */
    btormbt->parambo  = tmpparambo;
    btormbt->parambv  = tmpparambv;
    btormbt->paramarr = tmpparamarr;

    /* cleanup */
    for (i = 0; i < parambo.n; i++)
      boolector_release (btormbt->btor, parambo.exps[i].exp);
    es_release (&parambo);
    for (i = 0; i < parambv.n; i++)
      boolector_release (btormbt->btor, parambv.exps[i].exp);
    es_release (&parambv);
    for (i = 0; i < paramarr.n; i++)
      boolector_release (btormbt->btor, paramarr.exps[i].exp);
    es_release (&paramarr);
    free (params);
  }

  /* generate apply expression with arguments within scope of apply */
  args = malloc (sizeof (BoolectorNode *) * *nparams);
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

  tmp = boolector_apply (btormbt->btor, args, *nparams, fun);
  es_push (boolector_get_width (btormbt->btor, fun) == 1
               ? (BTOR_REAL_ADDR_NODE (tmp)->parameterized ? btormbt->parambo
                                                           : &btormbt->bo)
               : (BTOR_REAL_ADDR_NODE (tmp)->parameterized ? btormbt->parambv
                                                           : &btormbt->bv),
           tmp);

  free (args);
}

static BoolectorSort *
bitvec_sort (BtorMBT *btormbt, unsigned r)
{
  int rand, len;
  RNG rng;
  BoolectorNode *bv;
  BoolectorSort *sort;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  // TODO: option for 0.5 p_sort_bv
  if (btormbt->bv_sorts.n && rand < 0.5) /* use existing bv sort */
  {
    rand = pick (&rng, 0, btormbt->bv_sorts.n - 1);
    sort = btormbt->bv_sorts.sorts[rand];
  }
  else /* create new bv sort */
  {
    rand = pick (&rng, 0, btormbt->bv.n - 1);
    bv   = btormbt->bv.exps[rand].exp;
    len  = boolector_get_width (btormbt->btor, bv);
    sort = boolector_bitvec_sort (btormbt->btor, len);
    ss_push (&btormbt->bv_sorts, sort);
  }
  return sort;
}

static void
init_domain (BtorMBT *btormbt, unsigned r, SortStack *ss)
{
  int i, arity, rand;
  RNG rng;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  // TODO: option for 0.1 p_sort_fun_unary?
  if (rand < 0.1)
  {
    ss_push (ss, bitvec_sort (btormbt, r));
    return;
  }

  // TODO: option for 2 sort_fun_min_arity
  // TODO: option for 10 sort_fun_max_arity
  arity = pick (&rng, 2, 10);
  for (i = 0; i < arity; i++) ss_push (ss, bitvec_sort (btormbt, r));
}

static BoolectorSort *
fun_sort (BtorMBT *btormbt, unsigned r)
{
  int rand;
  RNG rng;
  BoolectorSort *sort, *codomain;
  SortStack domain;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  // TODO: option for 0.5 p_sort_fun
  if (btormbt->fun_sorts.n && rand < 0.5) /* use existing fun sort */
  {
    rand = pick (&rng, 0, btormbt->fun_sorts.n - 1);
    sort = btormbt->fun_sorts.sorts[rand];
  }
  else /* create new fun sort */
  {
    ss_init (&domain);
    init_domain (btormbt, r, &domain);
    codomain = bitvec_sort (btormbt, r);
    sort = boolector_fun_sort (btormbt->btor, domain.sorts, domain.n, codomain);
    ss_push (&btormbt->fun_sorts, sort);
    ss_release (&domain);
  }
  return sort;
}

static void
bitvec_uf (BtorMBT *btormbt, unsigned r)
{
  int i, rand, len;
  RNG rng;
  BoolectorNode *uf, *arg, *apply, **args;
  BoolectorSort *sort;
  ExpStack stack;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  if (btormbt->uf.n && rand < btormbt->p_apply_uf) /* use existing UF */
  {
    rand = pick (&rng, 0, btormbt->uf.n - 1);
    uf   = btormbt->uf.exps[rand].exp;
  }
  else /* create new UF */
  {
    sort = fun_sort (btormbt, r);
    uf   = boolector_uf (btormbt->btor, sort, 0);
    es_push (&btormbt->uf, uf);
  }

  /* create apply with sort of UF */
  es_init (&stack);
  // TODO: no api function yet for sort handling
  BtorSort *s = ((BtorUFNode *) uf)->sort->fun.domain;
  if (s->kind == BTOR_TUPLE_SORT)
  {
    for (i = 0; i < s->tuple.num_elements; i++)
    {
      assert (s->tuple.elements[i]->kind == BTOR_BITVEC_SORT);
      len = s->tuple.elements[i]->bitvec.len;
      arg = selexp (btormbt, &rng, T_BB, 0, 0);
      es_push (&stack,
               modifybv (btormbt,
                         &rng,
                         arg,
                         boolector_get_width (btormbt->btor, arg),
                         len,
                         0));
    }
  }
  else
  {
    assert (s->kind == BTOR_BITVEC_SORT);
    len = s->bitvec.len;
    arg = selexp (btormbt, &rng, T_BB, 0, 0);
    es_push (&stack,
             modifybv (btormbt,
                       &rng,
                       arg,
                       boolector_get_width (btormbt->btor, arg),
                       len,
                       0));
  }

  /* create apply on UF */
  args = malloc (stack.n * sizeof (BoolectorNode *));
  for (i = 0; i < stack.n; i++) args[i] = stack.exps[i].exp;
  apply = boolector_apply (btormbt->btor, args, stack.n, uf);

  len = boolector_get_width (btormbt->btor, apply);
  es_push (len == 1 ? &btormbt->bo : &btormbt->bv, apply);
  free (args);
  es_release (&stack);
}

/*------------------------------------------------------------------------*/

/* states */
static void *_new (BtorMBT *, unsigned);
static void *_opt (BtorMBT *, unsigned);
static void *_init (BtorMBT *, unsigned);
static void *_main (BtorMBT *, unsigned);
static void *_add (BtorMBT *, unsigned);
static void *_bitvec_op (BtorMBT *, unsigned);
static void *_array_op (BtorMBT *, unsigned);
static void *_bitvec_fun (BtorMBT *, unsigned);
static void *_bitvec_uf (BtorMBT *, unsigned);
static void *_input (BtorMBT *, unsigned);
static void *_release (BtorMBT *, unsigned);
static void *_ass (BtorMBT *, unsigned);
static void *_sat (BtorMBT *, unsigned);
static void *_dump (BtorMBT *, unsigned);
static void *_mgen (BtorMBT *, unsigned);
static void *_inc (BtorMBT *, unsigned);
static void *_del (BtorMBT *, unsigned);

static void *
_new (BtorMBT *btormbt, unsigned r)
{
  RNG rng = initrng (r);

  /* number of initial literals */
  btormbt->max_inputs =
      pick (&rng, btormbt->g_min_inputs, btormbt->g_max_inputs);
  /* number of initial operations */
  btormbt->max_ops =
      pick (&rng, btormbt->g_min_ops_init, btormbt->g_max_ops_init);

  init_pd_inputs (
      btormbt,
      pick (&rng, btormbt->g_min_vars_init, btormbt->g_max_vars_init),
      pick (&rng, btormbt->g_min_consts_init, btormbt->g_max_consts_init),
      pick (&rng, btormbt->g_min_arrays_init, btormbt->g_max_arrays_init));

  /* no delete operation at init */
  init_pd_ops (
      btormbt,
      pick (&rng, btormbt->g_min_add_ops_init, btormbt->g_max_add_ops_init),
      pick (&rng,
            btormbt->g_min_release_ops_init,
            btormbt->g_max_release_ops_init));

  /* no additional inputs at init */
  init_pd_add (
      btormbt,
      pick (&rng, btormbt->g_min_add_funs_init, btormbt->g_max_add_funs_init),
      pick (&rng, btormbt->g_min_add_uf_init, btormbt->g_max_add_uf_init),
      pick (&rng,
            btormbt->g_min_add_arrayops_init,
            btormbt->g_max_add_arrayops_init),
      pick (&rng,
            btormbt->g_min_add_bitvecops_init,
            btormbt->g_max_add_bitvecops_init),
      pick (&rng,
            btormbt->g_min_add_inputs_init,
            btormbt->g_max_add_inputs_init));

  BTORMBT_LOG (1,
               "new: pick %d ops (add:rel=%0.1f%%:%0.1f%%), %d inputs",
               btormbt->max_ops,
               btormbt->p_add / 10,
               btormbt->p_release / 10,
               btormbt->max_inputs);

  btormbt->btor = boolector_new ();
  assert (btormbt->btor);
  if (btormbt->shadow)
  {
    BTORMBT_LOG (1, "initial shadow clone...");
    /* cleanup done by boolector */
    boolector_chkclone (btormbt->btor);
  }
  return _opt;
}

static void *
_opt (BtorMBT *btormbt, unsigned r)
{
  int rw, set_sat_solver = 1;
  RNG rng = initrng (r);

  if (btormbt->dual_prop)
  {
    BTORMBT_LOG (1, "opt: enable dual prop");
    boolector_set_opt (btormbt->btor, "dual_prop", 1);
  }

  if (btormbt->just)
  {
    BTORMBT_LOG (1, "opt: enable justification");
    boolector_set_opt (btormbt->btor, "just", 1);
  }

#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
  if (btormbt->ucopt)
  {
    BTORMBT_LOG (1, "opt: enable unconstrained optimization");
    boolector_set_opt (btormbt->btor, "ucopt", 1);
  }
#endif

  if (btormbt->bloglevel)
  {
    BTORMBT_LOG (1, "opt: log level: '%d'", btormbt->bloglevel);
    boolector_set_opt (btormbt->btor, "loglevel", btormbt->bloglevel);
  }
  if (btormbt->bverblevel)
  {
    BTORMBT_LOG (1, "opt: verbose level: '%d'", btormbt->bverblevel);
    boolector_set_opt (btormbt->btor, "verbosity", btormbt->bverblevel);
  }

  if (pick (&rng, 0, NORM_VAL - 1) < btormbt->p_dump) btormbt->dump = 1;

    /* set random sat solver */
#ifdef BTOR_USE_LINGELING
  if (!btormbt->shadow && pick (&rng, 0, 1) && set_sat_solver)
  {
    boolector_set_sat_solver_lingeling (btormbt->btor, 0, 0);
    set_sat_solver = 0;
  }
#endif
#ifdef BTOR_USE_PICOSAT
  if (!btormbt->shadow && pick (&rng, 0, 1) && set_sat_solver)
  {
    boolector_set_sat_solver_picosat (btormbt->btor);
    set_sat_solver = 0;
  }
#endif
#ifdef BTOR_USE_MINISAT
  if (!btormbt->shadow && pick (&rng, 0, 1) && set_sat_solver)
    boolector_set_sat_solver_minisat (btormbt->btor);
#endif

  btormbt->mgen = 0;
  if (!btormbt->dump && !btormbt->force_nomgen
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
      && !btormbt->ucopt
#endif
      && pick (&rng, 0, 1))
  {
    BTORMBT_LOG (1, "opt: enable model generation");
    boolector_set_opt (btormbt->btor, "model_gen", 1);
    btormbt->mgen = 1;
  }

  if (btormbt->mgen && pick (&rng, 0, NORM_VAL - 1) < btormbt->p_print_model)
  {
    btormbt->print_model = 1;
    boolector_set_opt (btormbt->btor, "pretty_print", 0);
  }

  if (!btormbt->dump
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
      && !btormbt->ucopt
#endif
      && pick (&rng, 0, 1))
  {
    BTORMBT_LOG (1, "opt: enable incremental usage");
    boolector_set_opt (btormbt->btor, "incremental", 1);
    btormbt->inc = 1;
  }

  if (pick (&rng, 0, 9) == 5)
  {
    BTORMBT_LOG (1, "opt: enable full beta reduction");
    boolector_set_opt (btormbt->btor, "beta_reduce_all", 1);
  }

  rw = pick (&rng, 0, 3);
  BTORMBT_LOG (1, "opt: set rewrite level %d", rw);
  boolector_set_opt (btormbt->btor, "rewrite_level", rw);

  return _init;
}

static void *
_init (BtorMBT *btormbt, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  if (btormbt->bo.n + btormbt->bv.n + btormbt->arr.n < btormbt->max_inputs)
  {
    return _input;
  }

  /* generate at least one bool-var, one bv-var and one arr;
   * to ensure nonempty expression stacks */
  if (btormbt->bo.n < 1) create_var (btormbt, &rng, T_BO);
  if (btormbt->bv.n < 1) create_var (btormbt, &rng, T_BV);
  if (btormbt->arr.n < 1) create_array (btormbt, &rng);

  if (btormbt->ops < btormbt->max_ops)
  {
    btormbt->ops++;
    BTORMBT_LOG_STATUS (2, "init");
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < btormbt->p_add)
      return _add;
    else
      return _release;
  }

  BTORMBT_LOG_STATUS (1, "init");
  btormbt->bo.initlayer  = btormbt->bo.n;
  btormbt->bv.initlayer  = btormbt->bv.n;
  btormbt->arr.initlayer = btormbt->arr.n;

  /* adapt paramters for main */
  btormbt->ops     = 0;
  btormbt->max_ops = pick (&rng, btormbt->g_min_ops, btormbt->g_max_ops);
  /* how many operations should be assertions?
   * -> max_ops and nass should be in relation (the more ops, the more
   * assertions) in order to keep the sat/unsat ratio balanced */
  if (btormbt->max_ops < btormbt->g_max_ops_lower)
    btormbt->max_ass = BTORMBT_MIN (
        btormbt->max_ops,
        pick (
            &rng, btormbt->g_min_asserts_lower, btormbt->g_max_asserts_lower));
  else
    btormbt->max_ass =
        pick (&rng, btormbt->g_min_asserts_upper, btormbt->g_max_asserts_upper);

  init_pd_inputs (btormbt,
                  pick (&rng, btormbt->g_min_vars, btormbt->g_max_vars),
                  pick (&rng, btormbt->g_min_consts, btormbt->g_max_consts),
                  pick (&rng, btormbt->g_min_arrays, btormbt->g_max_arrays));
  init_pd_ops (
      btormbt,
      pick (&rng, btormbt->g_min_add_ops, btormbt->g_max_add_ops),
      pick (&rng, btormbt->g_min_release_ops, btormbt->g_max_release_ops));
  init_pd_add (
      btormbt,
      pick (&rng, btormbt->g_min_add_funs, btormbt->g_max_add_funs),
      pick (&rng, btormbt->g_min_add_uf, btormbt->g_max_add_uf),
      pick (&rng, btormbt->g_min_add_arrayops, btormbt->g_max_add_arrayops),
      pick (&rng, btormbt->g_min_add_bitvecops, btormbt->g_max_add_bitvecops),
      pick (&rng, btormbt->g_min_add_inputs, btormbt->g_max_add_inputs));

  BTORMBT_LOG (
      1,
      "main: pick %d ops (add:rel=%0.1f%%:%0.1f%%), ~%d asserts/assumes",
      btormbt->max_ops,
      btormbt->p_add / 10,
      btormbt->p_release / 10,
      btormbt->max_ass);

  btormbt->is_init = 1;
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
  if (btormbt->ops < btormbt->max_ops)
  {
    btormbt->ops++;
    BTORMBT_LOG_STATUS (2, "main");
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (rand < btormbt->max_ass * NORM_VAL / btormbt->max_ops)
      return _ass;
    else
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      if (rand < btormbt->p_add)
        return _add;
      else
        return _release;
    }
  }

  BTORMBT_LOG_STATUS (1, "main");
  BTORMBT_LOG (1,
               "main: asserts %d, assumes %d",
               btormbt->tot_asserts,
               btormbt->assumes);

  if (btormbt->dump) return _dump;

  return _sat;
}

static void *
_add (BtorMBT *btormbt, unsigned r)
{
  int rand;
  void *next;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);

  if (rand < btormbt->p_bitvec_op)
    next = _bitvec_op;
  else if (rand < btormbt->p_bitvec_op + btormbt->p_array_op)
    next = _array_op;
  else if (rand
           < btormbt->p_bitvec_op + btormbt->p_array_op + btormbt->p_bitvec_fun)
    next = _bitvec_fun;
  else if (rand < btormbt->p_bitvec_op + btormbt->p_array_op
                      + btormbt->p_bitvec_fun + btormbt->p_bitvec_uf)
    next = _bitvec_uf;
  else
    next = _input;

  return next;
}

static void *
_bitvec_op (BtorMBT *btormbt, unsigned r)
{
  BoolectorNode *e0, *e1, *e2;
  RNG rng = initrng (r);

  Op op = pick (&rng, NOT, COND);

  if (is_unary_op (op))
  {
    e0 = selexp (btormbt, &rng, T_BB, 0, NULL);
    unary_op (btormbt, &rng, op, e0, 0);
  }
  else if (is_binary_op (op))
  {
    e0 = selexp (
        btormbt, &rng, ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB), 0, NULL);
    e1 = selexp (
        btormbt, &rng, ((op >= IMPLIES && op <= IFF) ? T_BO : T_BB), 0, NULL);
    binary_op (btormbt, &rng, op, e0, e1, 0);
  }
  else
  {
    assert (is_ternary_fun (op));
    e0 = selexp (btormbt, &rng, T_BO, 0, NULL);
    e1 = selexp (btormbt, &rng, T_BB, 0, NULL);
    e2 = selexp (btormbt, &rng, T_BB, 0, NULL);
    ternary_fun (btormbt, &rng, op, e0, e1, e2, 0);
  }
  return (btormbt->is_init ? _main : _init);
}

static void *
_array_op (BtorMBT *btormbt, unsigned r)
{
  int e0w, e0iw, rand;
  Op op;
  BoolectorNode *e0, *e1, *e2;
  RNG rng;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  e0   = selexp (btormbt, &rng, T_ARR, 0, NULL);
  e0w  = boolector_get_width (btormbt->btor, e0);
  e0iw = boolector_get_index_width (btormbt->btor, e0);

  e2 = NULL;

  /* use read/write with p=0.666 else EQ/NE/COND */
  if (rand < btormbt->p_rw)
  {
    rand = pick (&rng, 0, NORM_VAL - 1);
    op   = rand < btormbt->p_read ? READ : WRITE;
    e1   = selexp (btormbt, &rng, T_BV, 0, NULL);
    if (op == WRITE) e2 = selexp (btormbt, &rng, T_BV, 0, NULL);
    array_op (btormbt, &rng, op, e0, e1, e2, 0);
  }
  else
  {
    /* select EQ/NE/COND with same propability */
    rand = pick (&rng, 0, NORM_VAL - 1);
    if (!btormbt->ext || rand < btormbt->p_cond)
      op = COND;
    else
    {
      rand = pick (&rng, 0, NORM_VAL - 1);
      op   = rand < btormbt->p_eq ? EQ : NE;
    }
    e1 = selarrexp (btormbt, &rng, e0, e0w, e0iw, 0);
    if (op == COND) e2 = selexp (btormbt, &rng, T_BO, 0, NULL);
    array_op (btormbt, &rng, op, e0, e1, e2, 0);
  }

  return (btormbt->is_init ? _main : _init);
}

static void *
_bitvec_uf (BtorMBT *btormbt, unsigned r)
{
  bitvec_uf (btormbt, r);
  return btormbt->is_init ? _main : _init;
}

static void *
_bitvec_fun (BtorMBT *btormbt, unsigned r)
{
  assert (!btormbt->parambo && !btormbt->parambv && !btormbt->paramarr);

  int nparams, width;

  bitvec_fun (btormbt, r, &nparams, &width, 0);

  btormbt->parambo = btormbt->parambv = btormbt->paramarr = NULL; /* cleanup */

  return (btormbt->is_init ? _main : _init);
}

static void *
_input (BtorMBT *btormbt, unsigned r)
{
  int rand;
  RNG rng = initrng (r);

  rand = pick (&rng, 0, NORM_VAL - 1);
  if (rand < btormbt->p_var)
    create_var (btormbt, &rng, T_BB);
  else if (rand < btormbt->p_const + btormbt->p_var)
    create_const (btormbt, &rng);
  else
    create_array (btormbt, &rng);

  return (btormbt->is_init ? _main : _init);
}

static void *
_release (BtorMBT *btormbt, unsigned r)
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

    boolector_release (btormbt->btor, es->exps[idx].exp);
    es_del (es, idx);
  }
  return (btormbt->is_init ? _main : _init);
}

static void *
_ass (BtorMBT *btormbt, unsigned r)
{
  int lower;
  BoolectorNode *node;
  RNG rng = initrng (r);

  /* select from init layer with lower probability */
  lower = btormbt->bo.initlayer && btormbt->bo.n > btormbt->bo.initlayer
                  && pick (&rng, 0, 4)
              ? btormbt->bo.initlayer - 1
              : 0;
  node = create_clause (btormbt, &rng, lower, btormbt->bo.n - 1);
  assert (!BTOR_REAL_ADDR_NODE (node)->parameterized);

  // TODO: use p_ass here?
  if (btormbt->inc && pick (&rng, 0, 4))
  {
    boolector_assume (btormbt->btor, node);
    es_push (&btormbt->assumptions, node);
    btormbt->assumes++;
  }
  else
  {
    boolector_assert (btormbt->btor, node);
    btormbt->asserts++;
    btormbt->tot_asserts++;
  }
  return _main;
}

static void *
_dump (BtorMBT *btormbt, unsigned r)
{
  assert (!btormbt->inc);
  assert (!btormbt->mgen);

  int rand;
  RNG rng;
  rng = initrng (r);

  // TODO: UF support in BTOR format not yet implemented
  if (btormbt->output_format)
  {
    if (!strcmp (btormbt->output_format, "btor") && !btormbt->uf.n)
      boolector_dump_btor (btormbt->btor, stdout);
    else if (!strcmp (btormbt->output_format, "smt1"))
      boolector_dump_smt1 (btormbt->btor, stdout);
    else if (!strcmp (btormbt->output_format, "smt2"))
      boolector_dump_smt2 (btormbt->btor, stdout);
  }
  else
  {
    rand = pick (&rng, 0, 2);
    if (rand == 0 && !btormbt->uf.n)
      boolector_dump_btor (btormbt->btor, stdout);
    else if (rand == 1)
      boolector_dump_smt1 (btormbt->btor, stdout);
    else
      boolector_dump_smt2 (btormbt->btor, stdout);
  }
  return _del;
}

static void *
_sat (BtorMBT *btormbt, unsigned r)
{
  int res, failed;
  RNG rng;
  BoolectorNode *ass;

  rng = initrng (r);

  if (btormbt->shadow && !pick (&rng, 0, 50))
  {
    BTORMBT_LOG (1, "cloning...");
    /* cleanup done by boolector */
    boolector_chkclone (btormbt->btor);
  }

  BTORMBT_LOG (1, "calling sat...");
  res = boolector_sat (btormbt->btor);
  if (res == BOOLECTOR_UNSAT)
    BTORMBT_LOG (1, "unsat");
  else if (res == BOOLECTOR_SAT)
  {
    BTORMBT_LOG (1, "sat");
    if (btormbt->print_model)
    {
      if (pick (&rng, 0, NORM_VAL - 1) < btormbt->p_model_format)
        boolector_print_model (btormbt->btor, "btor", stdout);
      else
        boolector_print_model (btormbt->btor, "smt2", stdout);
    }
  }
  else
    BTORMBT_LOG (1, "sat call returned %d", res);

  while (res == BOOLECTOR_UNSAT && btormbt->assumptions.n)
  {
    ass = es_pop (&btormbt->assumptions);
    assert (ass);
    failed = boolector_failed (btormbt->btor, ass);
    BTORMBT_LOG (1, "assumption %p failed: %d", ass, failed);
  }
  es_reset (&btormbt->assumptions);

  return btormbt->mgen && res == BOOLECTOR_SAT ? _mgen : _inc;
}

static void *
_mgen (BtorMBT *btormbt, unsigned r)
{
  (void) r;
  int i, size = 0;
  const char *bv = NULL;
  char **indices = NULL, **values = NULL;

  assert (btormbt->mgen);

  for (i = 0; i < btormbt->bo.n; i++)
  {
    bv = boolector_bv_assignment (btormbt->btor, btormbt->bo.exps[i].exp);
    boolector_free_bv_assignment (btormbt->btor, (char *) bv);
  }
  for (i = 0; i < btormbt->bv.n; i++)
  {
    bv = boolector_bv_assignment (btormbt->btor, btormbt->bv.exps[i].exp);
    boolector_free_bv_assignment (btormbt->btor, (char *) bv);
  }
  for (i = 0; i < btormbt->arr.n; i++)
  {
    boolector_array_assignment (
        btormbt->btor, btormbt->arr.exps[i].exp, &indices, &values, &size);
    if (size > 0)
      boolector_free_array_assignment (btormbt->btor, indices, values, size);
  }
  for (i = 0; i < btormbt->uf.n; i++)
  {
    boolector_uf_assignment (
        btormbt->btor, btormbt->uf.exps[i].exp, &indices, &values, &size);
    if (size > 0)
      boolector_free_uf_assignment (btormbt->btor, indices, values, size);
  }
  return _inc;
}

static void *
_inc (BtorMBT *btormbt, unsigned r)
{
  int i, rand;
  RNG rng;

  rng  = initrng (r);
  rand = pick (&rng, 0, NORM_VAL - 1);

  /* release cnf expressions */
  for (i = 0; i < btormbt->cnf.n; i++)
    boolector_release (btormbt->btor, btormbt->cnf.exps[i].exp);
  es_reset (&btormbt->cnf);

  if (btormbt->inc && rand < btormbt->p_inc)
  {
    btormbt->inc++;
    btormbt->ops     = 0; /* reset */
    btormbt->max_ass = btormbt->max_ass - btormbt->asserts;
    btormbt->assumes = 0; /* reset */
    btormbt->asserts = 0;

    btormbt->max_ops =
        pick (&rng, btormbt->g_min_ops_inc, btormbt->g_max_ops_inc);

    init_pd_inputs (
        btormbt,
        pick (&rng, btormbt->g_min_vars_inc, btormbt->g_max_vars_inc),
        pick (&rng, btormbt->g_min_consts_inc, btormbt->g_max_consts_inc),
        pick (&rng, btormbt->g_min_arrays_inc, btormbt->g_max_arrays_inc));
    init_pd_ops (
        btormbt,
        pick (&rng, btormbt->g_min_add_ops_inc, btormbt->g_max_add_ops_inc),
        pick (&rng,
              btormbt->g_min_release_ops_inc,
              btormbt->g_max_release_ops_inc));
    init_pd_add (
        btormbt,
        pick (&rng, btormbt->g_min_add_funs_inc, btormbt->g_max_add_funs_inc),
        pick (&rng, btormbt->g_min_add_uf_inc, btormbt->g_max_add_uf_inc),
        pick (&rng,
              btormbt->g_min_add_arrayops_inc,
              btormbt->g_max_add_arrayops_inc),
        pick (&rng,
              btormbt->g_min_add_bitvecops_inc,
              btormbt->g_max_add_bitvecops_inc),
        pick (&rng,
              btormbt->g_min_add_inputs_inc,
              btormbt->g_max_add_inputs_inc));
    BTORMBT_LOG (1,
                 "inc: pick %d ops (add:rel=%0.1f%%:%0.1f%%)",
                 btormbt->max_ops,
                 btormbt->p_add / 10,
                 btormbt->p_release / 10);
    if (btormbt->inc)
      BTORMBT_LOG (1, "number of increments: %d", btormbt->inc - 1);

    return _main;
  }
  return _del;
}

#define RELEASE_EXP_STACK(stack)                                     \
  do                                                                 \
  {                                                                  \
    int i;                                                           \
    for (i = 0; i < btormbt->stack.n; i++)                           \
      boolector_release (btormbt->btor, btormbt->stack.exps[i].exp); \
    es_release (&btormbt->stack);                                    \
  } while (0)

#define RELEASE_SORT_STACK(stack)                                      \
  do                                                                   \
  {                                                                    \
    int i;                                                             \
    for (i = 0; i < btormbt->stack.n; i++)                             \
      boolector_release_sort (btormbt->btor, btormbt->stack.sorts[i]); \
    ss_release (&btormbt->stack);                                      \
  } while (0)

static void *
_del (BtorMBT *btormbt, unsigned r)
{
  (void) r;
  assert (btormbt);
  assert (btormbt->btor);

  RELEASE_EXP_STACK (bo);
  RELEASE_EXP_STACK (bv);
  RELEASE_EXP_STACK (arr);
  RELEASE_EXP_STACK (fun);
  RELEASE_EXP_STACK (uf);
  RELEASE_EXP_STACK (cnf);
  es_release (&btormbt->assumptions);

  RELEASE_SORT_STACK (bv_sorts);
  RELEASE_SORT_STACK (fun_sorts);

  assert (btormbt->parambo == NULL);
  assert (btormbt->parambv == NULL);
  assert (btormbt->paramarr == NULL);

  boolector_delete (btormbt->btor);
  btormbt->btor = NULL;
  return 0;
}

static void
rantrav (BtorMBT *btormbt)
{
  assert (btormbt);

  State state, next;
  unsigned rand;

  memset (&btormbt->is_init,
          0,
          (char *) &btormbt->rng - (char *) &btormbt->is_init);
  assert (btormbt->is_init == 0);
  assert (btormbt->tot_asserts == 0);
  btormbt->rng.z = btormbt->rng.w = btormbt->seed;

  /* state loop */
  for (state = _new; state; state = next)
  {
    rand = nextrand (&btormbt->rng);
    next = state (btormbt, rand);
  }
}

static void (*sig_alrm_handler) (int);

static void
reset_alarm (void)
{
  alarm (0);
  (void) signal (SIGALRM, sig_alrm_handler);
}

static void
catch_alarm (int sig)
{
  assert (sig == SIGALRM);
  (void) sig;

  reset_alarm ();
  exit (EXIT_TIMEOUT);
}

static void
set_alarm (void)
{
  sig_alrm_handler = signal (SIGALRM, catch_alarm);
  assert (btormbt->time_limit > 0);
  alarm (btormbt->time_limit);
}

static int
run (BtorMBT *btormbt)
{
  assert (btormbt);

  int status, null;
  pid_t id;

  if (!btormbt->seeded && (id = fork ()))
  {
    btormbt->forked++;
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
    if (btormbt->time_limit)
    {
      set_alarm ();
      BTORMBT_LOG (1, "set time limit to %d second(s)", btormbt->time_limit);
    }

    /* redirect output from child to /dev/null if we don't want to have
     * verbose output */
    if (!btormbt->seeded && !btormbt->verbose)
    {
      null = open ("/dev/null", O_WRONLY);
      dup2 (null, STDOUT_FILENO);
      dup2 (null, STDERR_FILENO);
      close (null);
    }

    rantrav (btormbt);
    exit (EXIT_OK);
  }

  return status;
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

static int
isfloatnumstr (const char *str)
{
  const char *p;
  for (p = str; *p; p++)
    if (!isdigit (*p) && !*p == '.') return 0;
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
  exit (EXIT_ERROR);
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
  return current_time () - btormbt->start_time;
}

static double
average (double a, double b)
{
  return b ? a / b : 0;
}

static void
stats (BtorMBT *btormbt)
{
  double t = get_time ();
  printf ("finished after %0.2f seconds\n", t);
  printf ("%d rounds = %0.2f rounds per second\n",
          btormbt->rounds,
          average (btormbt->rounds, t));
  printf ("%d bugs = %0.2f bugs per second\n",
          btormbt->bugs,
          average (btormbt->bugs, t));
}

/* Note: - do not call non-reentrant function here, see:
 *         https://www.securecoding.cert.org/confluence/display/seccode/SIG30-C.+Call+only+asynchronous-safe+functions+within+signal+handlers
 *       - do not use printf here (causes segfault when SIGINT and valgrind) */
static void
sig_handler (int sig)
{
  char str[100];

  sprintf (str, "*** btormbt: caught signal %d\n\n", sig);
  if (!write (STDOUT_FILENO, str, strlen (str)))
  {
    // error message failed ....
  }
  /* Note: if _exit is used here (which is reentrant, in contrast to exit),
   *       atexit handler is not called. Hence, use exit here. */
  exit (EXIT_ERROR);
}

static void
set_sig_handlers (void)
{
  (void) signal (SIGINT, sig_handler);
  (void) signal (SIGSEGV, sig_handler);
  (void) signal (SIGABRT, sig_handler);
  (void) signal (SIGTERM, sig_handler);
}

static void
finish (void)
{
  fflush (stderr);
  fflush (stdout);
  if (btormbt->ppid == getpid ()) stats (btormbt);
  free (btormbt);
  fflush (stdout);
}

int
main (int argc, char **argv)
{
  int i, mac, pid, prev, res, verbose, status;
  char *name, *cmd;

  btormbt             = new_btormbt ();
  btormbt->start_time = current_time ();

  pid  = 0;
  prev = 0;

  atexit (finish);

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
    {
      printf ("%s", BTORMBT_USAGE);
      exit (EXIT_OK);
    }
    else if (!strcmp (argv[i], "-ha") || !strcmp (argv[i], "--help-advanced"))
    {
      printf ("%s", BTORMBT_USAGE);
      printf ("%s", BTORMBT_USAGE_ADVANCED);
      exit (EXIT_OK);
    }
    else if (!strcmp (argv[i], "-v") || !strcmp (argv[i], "--verbose"))
      btormbt->verbose++;
    else if (!strcmp (argv[i], "-q") || !strcmp (argv[i], "--quiet"))
      btormbt->quiet = 1;
    else if (!strcmp (argv[i], "-k") || !strcmp (argv[i], "--keep-lines"))
      btormbt->terminal = 0;
    else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--quit-after-first"))
      btormbt->quit_after_first = 1;
    else if (!strcmp (argv[i], "-n") || !strcmp (argv[i], "--no-modelgen"))
      btormbt->force_nomgen = 1;
    else if (!strcmp (argv[i], "-e") || !strcmp (argv[i], "--extensionality"))
      btormbt->ext = 1;
    else if (!strcmp (argv[i], "-dp")
             || !strcmp (argv[i], "--enable-dual-prop"))
      btormbt->dual_prop = 1;
    else if (!strcmp (argv[i], "-ju") || !strcmp (argv[i], "--enable-just"))
      btormbt->just = 1;
#ifndef BTOR_DO_NOT_OPTIMIZE_UNCONSTRAINED
    else if (!strcmp (argv[i], "-uc") || !strcmp (argv[i], "--enable-ucopt"))
      btormbt->ucopt = 1;
#endif
    else if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--shadow-clone"))
      btormbt->shadow = 1;
    else if (!strcmp (argv[i], "-o") || !strcmp (argv[i], "--out"))
    {
      if (++i == argc) die ("argument to '-o' missing (try '-h')");
      if (argv[i][0] == '-') die ("invalid output directory given (try '-h')");
      btormbt->out = argv[i];
      DIR *dir     = opendir (argv[i]);
      if (dir)
        closedir (dir);
      else
        die ("given output directory does not exist");
    }
    else if (!strcmp (argv[i], "-m"))
    {
      if (++i == argc) die ("argument to '-m' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument '%s' to '-m' is not a number (try '-h')", argv[i]);
      btormbt->g_max_rounds = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "-t"))
    {
      if (++i == argc) die ("argument to '-t' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument '%s' to '-t' is not a number (try '-h')", argv[i]);
      btormbt->time_limit = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--blog"))
    {
      if (++i == argc) die ("argument to '--blog' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument '%s' to '--blog' not a number (try '-h')", argv[i]);
      btormbt->bloglevel = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--bverb"))
    {
      if (++i == argc) die ("argument to '--bverb' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument '%s' to '--bverb' not a number (try '-h')", argv[i]);
      btormbt->bverblevel = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--inputs"))
    {
      if (++i == argc) die ("argument to '--inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--inputs' is not a number (try '-h')");
      btormbt->g_min_inputs = atoi (argv[i]);
      if (++i == argc) die ("argument to '--inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--inputs' is not a number (try '-h')");
      btormbt->g_max_inputs = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--vars-init"))
    {
      if (++i == argc) die ("argument to '--vars-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--vars-init' is not a number (try '-h')");
      btormbt->g_min_vars_init = atoi (argv[i]);
      if (++i == argc) die ("argument to '--vars-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--vars-init' is not a number (try '-h')");
      btormbt->g_max_vars_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--vars"))
    {
      if (++i == argc) die ("argument to '--vars' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--vars' is not a number (try '-h')");
      btormbt->g_min_vars = atoi (argv[i]);
      if (++i == argc) die ("argument to '--vars' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--vars' is not a number (try '-h')");
      btormbt->g_max_vars = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--vars-inc"))
    {
      if (++i == argc) die ("argument to '--vars-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--vars-inc' is not a number (try '-h')");
      btormbt->g_min_vars_inc = atoi (argv[i]);
      if (++i == argc) die ("argument to '--vars-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--vars-inc' is not a number (try '-h')");
      btormbt->g_max_vars_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--consts-init"))
    {
      if (++i == argc) die ("argument to '--consts-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--consts-init' is not a number (try '-h')");
      btormbt->g_min_consts_init = atoi (argv[i]);
      if (++i == argc) die ("argument to '--consts-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--consts-init' is not a number (try '-h')");
      btormbt->g_max_consts_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--consts"))
    {
      if (++i == argc) die ("argument to '--consts' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--consts' is not a number (try '-h')");
      btormbt->g_min_consts = atoi (argv[i]);
      if (++i == argc) die ("argument to '--consts' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--consts' is not a number (try '-h')");
      btormbt->g_max_consts = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--consts-inc"))
    {
      if (++i == argc) die ("argument to '--consts-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--consts-inc' is not a number (try '-h')");
      btormbt->g_min_consts_inc = atoi (argv[i]);
      if (++i == argc) die ("argument to '--consts-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--consts-inc' is not a number (try '-h')");
      btormbt->g_max_consts_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--arrays-init"))
    {
      if (++i == argc) die ("argument to '--arrays-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--arrays-init' is not a number (try '-h')");
      btormbt->g_min_arrays_init = atoi (argv[i]);
      if (++i == argc) die ("argument to '--arrays-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--arrays-init' is not a number (try '-h')");
      btormbt->g_max_arrays_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--arrays"))
    {
      if (++i == argc) die ("argument to '--arrays' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--arrays' is not a number (try '-h')");
      btormbt->g_min_arrays = atoi (argv[i]);
      if (++i == argc) die ("argument to '--arrays' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--arrays' is not a number (try '-h')");
      btormbt->g_max_arrays = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--arrays-inc"))
    {
      if (++i == argc) die ("argument to '--arrays-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--arrays-inc' is not a number (try '-h')");
      btormbt->g_min_arrays_inc = atoi (argv[i]);
      if (++i == argc) die ("argument to '--arrays-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--arrays-inc' is not a number (try '-h')");
      btormbt->g_max_arrays_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-funs-init"))
    {
      if (++i == argc) die ("argument to '--add-funs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-funs-init' is not a number (try '-h')");
      btormbt->g_min_add_funs_init = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-funs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-funs-init' is not a number (try '-h')");
      btormbt->g_max_add_funs_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-funs"))
    {
      if (++i == argc) die ("argument to '--add-funs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-funs' is not a number (try '-h')");
      btormbt->g_min_add_funs = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-funs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-funs' is not a number (try '-h')");
      btormbt->g_max_add_funs = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-funs-inc"))
    {
      if (++i == argc) die ("argument to '--add-funs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-funs-inc' is not a number (try '-h')");
      btormbt->g_min_add_funs_inc = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-funs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-funs-inc' is not a number (try '-h')");
      btormbt->g_max_add_funs_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-arrayops-init"))
    {
      if (++i == argc)
        die ("argument to '--add-arrayops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-arrayops-init' is not a number (try '-h')");
      btormbt->g_min_add_arrayops_init = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--add-arrayops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-arrayops-init' is not a number (try '-h')");
      btormbt->g_max_add_arrayops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-arrayops"))
    {
      if (++i == argc) die ("argument to '--add-arrayops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-arrayops' is not a number (try '-h')");
      btormbt->g_min_add_arrayops = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-arrayops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-arrayops' is not a number (try '-h')");
      btormbt->g_max_add_arrayops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-arrayops-inc"))
    {
      if (++i == argc)
        die ("argument to '--add-arrayops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-arrayops-inc' is not a number (try '-h')");
      btormbt->g_min_add_arrayops_inc = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--add-arrayops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-arrayops-inc' is not a number (try '-h')");
      btormbt->g_max_add_arrayops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-bitvecops-init"))
    {
      if (++i == argc)
        die ("argument to '--add-bitvecops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-bitvecops-init' is not a number (try '-h')");
      btormbt->g_min_add_bitvecops_init = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--add-bitvecops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-bitvecops-init' is not a number (try '-h')");
      btormbt->g_max_add_bitvecops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-bitvecops"))
    {
      if (++i == argc) die ("argument to '--add-bitvecops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-bitvecops' is not a number (try '-h')");
      btormbt->g_min_add_bitvecops = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-bitvecops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-bitvecops' is not a number (try '-h')");
      btormbt->g_max_add_bitvecops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-bitvecops-inc"))
    {
      if (++i == argc)
        die ("argument to '--add-bitvecops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-bitvecops-inc' is not a number (try '-h')");
      btormbt->g_min_add_bitvecops_inc = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--add-bitvecops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-bitvecops-inc' is not a number (try '-h')");
      btormbt->g_max_add_bitvecops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-inputs-init"))
    {
      if (++i == argc)
        die ("argument to '--add-inputs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-inputs-init' is not a number (try '-h')");
      btormbt->g_min_add_inputs_init = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--add-inputs-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-inputs-init' is not a number (try '-h')");
      btormbt->g_max_add_inputs_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-inputs"))
    {
      if (++i == argc) die ("argument to '--add-inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-inputs' is not a number (try '-h')");
      btormbt->g_min_add_inputs = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-inputs' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-inputs' is not a number (try '-h')");
      btormbt->g_max_add_inputs = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-inputs-inc"))
    {
      if (++i == argc)
        die ("argument to '--add-inputs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-inputs-inc' is not a number (try '-h')");
      btormbt->g_min_add_inputs_inc = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--add-inputs-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-inputs-inc' is not a number (try '-h')");
      btormbt->g_max_add_inputs_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--ops-init"))
    {
      if (++i == argc) die ("argument to '--ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--ops-init' is not a number (try '-h')");
      btormbt->g_min_ops_init = atoi (argv[i]);
      if (++i == argc) die ("argument to '--ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--ops-init' is not a number (try '-h')");
      btormbt->g_max_ops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--ops"))
    {
      if (++i == argc) die ("argument to '--ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--ops' is not a number (try '-h')");
      btormbt->g_min_ops = atoi (argv[i]);
      if (++i == argc) die ("argument to '--ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--ops' is not a number (try '-h')");
      btormbt->g_max_ops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--ops-inc"))
    {
      if (++i == argc) die ("argument to '--ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--ops-inc' is not a number (try '-h')");
      btormbt->g_min_ops_inc = atoi (argv[i]);
      if (++i == argc) die ("argument to '--ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--ops-inc' is not a number (try '-h')");
      btormbt->g_max_ops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-ops-init"))
    {
      if (++i == argc) die ("argument to '--add-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-ops-init' is not a number (try '-h')");
      btormbt->g_min_add_ops_init = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-ops-init' is not a number (try '-h')");
      btormbt->g_max_add_ops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-ops"))
    {
      if (++i == argc) die ("argument to '--add-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-ops' is not a number (try '-h')");
      btormbt->g_min_add_ops = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-ops' is not a number (try '-h')");
      btormbt->g_max_add_ops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--add-ops-inc"))
    {
      if (++i == argc) die ("argument to '--add-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-ops-inc' is not a number (try '-h')");
      btormbt->g_min_add_ops_inc = atoi (argv[i]);
      if (++i == argc) die ("argument to '--add-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--add-ops-inc' is not a number (try '-h')");
      btormbt->g_max_add_ops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--release-ops-init"))
    {
      if (++i == argc)
        die ("argument to '--release-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--release-ops-init' is not a number (try '-h')");
      btormbt->g_min_release_ops_init = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--release-ops-init' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--release-ops-init' is not a number (try '-h')");
      btormbt->g_max_release_ops_init = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--release-ops"))
    {
      if (++i == argc) die ("argument to '--release-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--release-ops' is not a number (try '-h')");
      btormbt->g_min_release_ops = atoi (argv[i]);
      if (++i == argc) die ("argument to '--release-ops' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--release-ops' is not a number (try '-h')");
      btormbt->g_max_release_ops = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--release-ops-inc"))
    {
      if (++i == argc)
        die ("argument to '--release-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--release-ops-inc' is not a number (try '-h')");
      btormbt->g_min_release_ops_inc = atoi (argv[i]);
      if (++i == argc)
        die ("argument to '--release-ops-inc' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--release-ops-inc' is not a number (try '-h')");
      btormbt->g_max_release_ops_inc = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--max-ops-lower"))
    {
      if (++i == argc) die ("argument to '--max-ops-lower' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--max-ops-lower' is not a number (try '-h')");
      btormbt->g_max_ops_lower = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--asserts-lower"))
    {
      if (++i == argc) die ("argument to '--asserts-lower' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--asserts-lower' is not a number (try '-h')");
      btormbt->g_min_asserts_lower = atoi (argv[i]);
      if (++i == argc) die ("argument to '--asserts-lower' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--asserts-lower' is not a number (try '-h')");
      btormbt->g_max_asserts_lower = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--asserts-upper"))
    {
      if (++i == argc) die ("argument to '--asserts-upper' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--asserts-upper' is not a number (try '-h')");
      btormbt->g_min_asserts_upper = atoi (argv[i]);
      if (++i == argc) die ("argument to '--asserts-upper' missing (try '-h')");
      if (!isnumstr (argv[i]))
        die ("argument to '--asserts-upper' is not a number (try '-h')");
      btormbt->g_max_asserts_upper = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--p-param-exp"))
    {
      if (++i == argc) die ("argument to '--p-param-exp' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-param-exp' is not a number (try '-h')");
      btormbt->p_param_exp = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_param_exp > NORM_VAL)
        die ("argument to '--p-param-exp' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-param-arr-exp"))
    {
      if (++i == argc)
        die ("argument to '--p-param-arr-exp' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-param-arr-exp' is not a number (try '-h')");
      btormbt->p_param_arr_exp = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_param_arr_exp > NORM_VAL)
        die ("argument to '--p-param-arr-exp' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-apply-fun"))
    {
      if (++i == argc) die ("argument to '--p-apply-fun' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-apply-fun' is not a number (try '-h')");
      btormbt->p_apply_fun = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_apply_fun > NORM_VAL)
        die ("argument to '--p-apply-fun' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-apply-uf"))
    {
      if (++i == argc) die ("argument to '--p-apply-uf' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-apply-uf' is not a number (try '-h')");
      btormbt->p_apply_uf = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_apply_uf > NORM_VAL)
        die ("argument to '--p-apply-uf' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-rw"))
    {
      if (++i == argc) die ("argument to '--p-rw' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-rw' is not a number (try '-h')");
      btormbt->p_rw = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_rw > NORM_VAL) die ("argument to '--p-rw' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-read"))
    {
      if (++i == argc) die ("argument to '--p-read' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-read' is not a number (try '-h')");
      btormbt->p_read = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_read > NORM_VAL)
        die ("argument to '--p-read' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-cond"))
    {
      if (++i == argc) die ("argument to '--p-cond' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-cond' is not a number (try '-h')");
      btormbt->p_cond = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_cond > NORM_VAL)
        die ("argument to '--p-cond' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-eq"))
    {
      if (++i == argc) die ("argument to '--p-eq' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-eq' is not a number (try '-h')");
      btormbt->p_eq = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_eq > NORM_VAL) die ("argument to '--p-eq' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-inc"))
    {
      if (++i == argc) die ("argument to '--p-inc' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-inc' is not a number (try '-h')");
      btormbt->p_inc = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_inc > NORM_VAL)
        die ("argument to '--p-inc' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-dump"))
    {
      if (++i == argc) die ("argument to '--p-dump' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-dump' is not a number (try '-h')");
      btormbt->p_dump = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_dump > NORM_VAL)
        die ("argument to '--p-dump' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-print-model"))
    {
      if (++i == argc) die ("argument to '--p-print-model' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-print-model' is not a number (try '-h')");
      btormbt->p_print_model = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_print_model > NORM_VAL)
        die ("argument to '--p-print-model' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--p-model-format"))
    {
      if (++i == argc)
        die ("argument to '--p-model-format' missing (try '-h')");
      if (!isfloatnumstr (argv[i]))
        die ("argument to '--p-model-format' is not a number (try '-h')");
      btormbt->p_model_format = atof (argv[i]) * NORM_VAL;
      if (btormbt->p_print_model > NORM_VAL)
        die ("argument to '--p-model-format' must be < 1.0");
    }
    else if (!strcmp (argv[i], "--output-format"))
    {
      if (++i == argc) die ("argument to '--output-format' missing (try '-h')");
      if (strcmp (argv[i], "btor") && strcmp (argv[i], "smt1")
          && strcmp (argv[i], "smt2"))
        die ("argument to '--output-format' is invalid (try '-h')");
      btormbt->output_format = argv[i];
    }
    else if (!isnumstr (argv[i]))
    {
      die ("invalid command line option '%s' (try '-h')", argv[i]);
    }
    else
    {
      btormbt->seed   = atoi (argv[i]);
      btormbt->seeded = 1;
    }
  }

  btormbt->ppid = getpid ();
  set_sig_handlers ();

  mac = hashmac ();
  for (btormbt->rounds = 0; btormbt->rounds < btormbt->g_max_rounds;
       btormbt->rounds++)
  {
    if (!(prev & 1)) prev++;

    if (!btormbt->seeded)
    {
      btormbt->seed = mac;
      btormbt->seed *= 123301093;
      btormbt->seed += times (0);
      btormbt->seed *= 223531513;
      btormbt->seed += pid;
      btormbt->seed *= 31752023;
      btormbt->seed += prev;
      btormbt->seed *= 43376579;
      prev = btormbt->seed = abs (btormbt->seed) >> 1;

      if (!btormbt->quiet)
      {
        if (btormbt->terminal) erase ();
        printf ("%d %d ", btormbt->rounds, btormbt->seed);
        fflush (stdout);
      }

      /* reset verbose flag for initial run, only print on replay */
      verbose          = btormbt->verbose;
      btormbt->verbose = 0;
      status           = run (btormbt);
      btormbt->verbose = verbose;
    }
    else
      status = run (btormbt);

    if (WIFEXITED (status))
      res = WEXITSTATUS (status);
    else if (WIFSIGNALED (status))
      res = EXIT_SIGNALED;
    else
      res = EXIT_UNKNOWN;

    /* replay run on error */
    if (!btormbt->seeded && res == EXIT_ERROR)
    {
      btormbt->bugs++;

      if (!(name = getenv ("BTORAPITRACE")))
      {
        name = malloc (100 * sizeof (char));
        sprintf (name, "/tmp/bug-%d-mbt.trace", getpid ());
        /* replay run */
        setenv ("BTORAPITRACE", name, 1);
        i = run (btormbt);
        assert (WIFEXITED (i));
        assert (WEXITSTATUS (i) == res);
        unsetenv ("BTORAPITRACE");
      }

      if (btormbt->out)
      {
        cmd = malloc (strlen (name) + 80 + strlen (btormbt->out) + 1);
        sprintf (cmd,
                 "cp %s %s/btormbt-bug-%d.trace",
                 name,
                 btormbt->out,
                 btormbt->seed);
      }
      else
      {
        cmd = malloc (strlen (name) + 80);
        sprintf (cmd, "cp %s btormbt-bug-%d.trace", name, btormbt->seed);
      }

      if (!getenv ("BTORAPITRACE")) free (name);
      if (system (cmd))
      {
        printf ("Error on copy command %s \n", cmd);
        exit (EXIT_ERROR);
      }
      free (cmd);
    }

    if (res == EXIT_SIGNALED)
    {
      if (btormbt->verbose) printf ("signal %d", WTERMSIG (status));
    }
    else if (res == EXIT_UNKNOWN)
    {
      if (btormbt->verbose) printf ("unknown");
    }
    else if (res == EXIT_TIMEOUT)
    {
      BTORMBT_LOG (
          1, "TIMEOUT: time limit %d seconds reached\n", btormbt->time_limit);
      if (!btormbt->verbose)
        printf ("timed out after %d second(s)\n", btormbt->time_limit);
    }
    else if (res == EXIT_ERROR)
    {
      if (btormbt->quiet) printf ("%d ", btormbt->seed);
      printf ("exit %d\n", res);
    }

    if ((res == EXIT_ERROR && btormbt->quit_after_first) || btormbt->seeded)
      break;
  }
  if (btormbt->verbose)
  {
    if (btormbt->terminal) erase ();
    printf ("forked %d\n", btormbt->forked);
  }
  return 0;
}
