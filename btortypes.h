/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *  Copyright (C) 2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORTYPES_H_INCLUDED
#define BTORTYPES_H_INCLUDED

typedef struct Btor Btor;
typedef struct BtorNode BtorNode;

enum BtorSolverResult
{
  BTOR_RESULT_SAT     = 10,
  BTOR_RESULT_UNSAT   = 20,
  BTOR_RESULT_UNKNOWN = 0,
};

typedef enum BtorSolverResult BtorSolverResult;

/* public API types */
typedef struct BoolectorNode BoolectorNode;
typedef unsigned BoolectorSort;

/* Boolector options */
enum BtorOption
{
  BTOR_OPT_MODEL_GEN,
  BTOR_OPT_INCREMENTAL,
  BTOR_OPT_INCREMENTAL_ALL,
  BTOR_OPT_INPUT_FORMAT,
  BTOR_OPT_OUTPUT_NUMBER_FORMAT,
  BTOR_OPT_OUTPUT_FORMAT,
  BTOR_OPT_ENGINE,
  BTOR_OPT_SAT_ENGINE,
  BTOR_OPT_AUTO_CLEANUP,
  BTOR_OPT_PRETTY_PRINT,
  BTOR_OPT_EXIT_CODES,
  BTOR_OPT_SEED,
  BTOR_OPT_VERBOSITY,
  BTOR_OPT_LOGLEVEL,
  /* simplifier --------------------------------------------------------- */
  BTOR_OPT_REWRITE_LEVEL,
  BTOR_OPT_SKELETON_PREPROC,
  BTOR_OPT_ACKERMANN,
  BTOR_OPT_BETA_REDUCE_ALL,
  BTOR_OPT_ELIMINATE_SLICES,
  BTOR_OPT_VAR_SUBST,
  BTOR_OPT_UCOPT,
  BTOR_OPT_MERGE_LAMBDAS,
  BTOR_OPT_EXTRACT_LAMBDAS,
  /* FUN engine --------------------------------------------------------- */
  BTOR_OPT_FUN_DUAL_PROP,
  BTOR_OPT_FUN_JUST,
  BTOR_OPT_FUN_JUST_HEURISTIC,
  BTOR_OPT_FUN_LAZY_SYNTHESIZE,
  BTOR_OPT_FUN_EAGER_LEMMAS,
  /* SLS engine --------------------------------------------------------- */
  BTOR_OPT_SLS_STRATEGY,
  BTOR_OPT_SLS_JUST,
  BTOR_OPT_SLS_MOVE_GW,
  BTOR_OPT_SLS_MOVE_RANGE,
  BTOR_OPT_SLS_MOVE_SEGMENT,
  BTOR_OPT_SLS_MOVE_RAND_WALK,
  BTOR_OPT_SLS_MOVE_RAND_WALK_PROB,
  BTOR_OPT_SLS_MOVE_RAND_ALL,
  BTOR_OPT_SLS_MOVE_RAND_RANGE,
  BTOR_OPT_SLS_MOVE_PROP,
  BTOR_OPT_SLS_MOVE_PROP_N_PROP,
  BTOR_OPT_SLS_MOVE_PROP_N_SLS,
  BTOR_OPT_SLS_MOVE_PROP_FORCE_RW,
  BTOR_OPT_SLS_MOVE_INC_MOVE_TEST,
  BTOR_OPT_SLS_USE_RESTARTS,
  BTOR_OPT_SLS_USE_BANDIT,
  /* PROP engine --------------------------------------------------------- */
  BTOR_OPT_PROP_USE_RESTARTS,
  BTOR_OPT_PROP_USE_BANDIT,
  BTOR_OPT_PROP_USE_FULL_PATH,
  BTOR_OPT_PROP_USE_INV_VALUE_PROB,
  BTOR_OPT_PROP_FLIP_COND_PROB,
  /* internal options --------------------------------------------------- */
  BTOR_OPT_SORT_EXP,
  BTOR_OPT_SORT_AIG,
  BTOR_OPT_SORT_AIGVEC,
  BTOR_OPT_AUTO_CLEANUP_INTERNAL,
  BTOR_OPT_SIMPLIFY_CONSTRAINTS,
#ifdef BTOR_CHECK_FAILED
  BTOR_OPT_CHK_FAILED_ASSUMPTIONS,
#endif
  BTOR_OPT_PARSE_INTERACTIVE,
#ifdef BTOR_USE_LINGELING
  BTOR_OPT_SAT_ENGINE_LGL_FORK,
#endif
  /* this MUST be the last entry! */
  BTOR_OPT_NUM_OPTS,
};
typedef enum BtorOption BtorOption;

#endif
