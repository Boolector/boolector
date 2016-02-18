/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2014-2015 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOROPTS_H_INCLUDED
#define BTOROPTS_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "btortypes.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"

/*------------------------------------------------------------------------*/

#define BTOR_VERBOSITY_MAX 4

enum BtorOptSatEngines
{
  BTOR_SAT_ENGINE_MIN,
#ifdef BTOR_USE_LINGELING
  BTOR_SAT_ENGINE_LINGELING,
#endif
#ifdef BTOR_USE_PICOSAT
  BTOR_SAT_ENGINE_PICOSAT,
#endif
#ifdef BTOR_USE_MINISAT
  BTOR_SAT_ENGINE_MINISAT,
#endif
  BTOR_SAT_ENGINE_MAX,
};
#define BTOR_SAT_ENGINE_DFLT (BTOR_SAT_ENGINE_MIN + 1)

#define BTOR_ENGINE_CORE 0
#define BTOR_ENGINE_SLS 1
#define BTOR_ENGINE_DFLT BTOR_ENGINE_CORE
#define BTOR_ENGINE_MIN BTOR_ENGINE_CORE
#define BTOR_ENGINE_MAX BTOR_ENGINE_SLS

#define BTOR_INPUT_FORMAT_NONE 0
#define BTOR_INPUT_FORMAT_BTOR 1
#define BTOR_INPUT_FORMAT_BTOR2 2
#define BTOR_INPUT_FORMAT_SMT1 3
#define BTOR_INPUT_FORMAT_SMT2 4
#define BTOR_INPUT_FORMAT_DFLT BTOR_INPUT_FORMAT_NONE
#define BTOR_INPUT_FORMAT_MIN BTOR_INPUT_FORMAT_NONE
#define BTOR_INPUT_FORMAT_MAX BTOR_INPUT_FORMAT_SMT2

#define BTOR_OUTPUT_BASE_BIN 0
#define BTOR_OUTPUT_BASE_HEX 1
#define BTOR_OUTPUT_BASE_DEC 2
#define BTOR_OUTPUT_BASE_DFLT BTOR_OUTPUT_BASE_BIN
#define BTOR_OUTPUT_BASE_MIN BTOR_OUTPUT_BASE_BIN
#define BTOR_OUTPUT_BASE_MAX BTOR_OUTPUT_BASE_DEC

#define BTOR_OUTPUT_FORMAT_BTOR 1
#define BTOR_OUTPUT_FORMAT_BTOR2 2
#define BTOR_OUTPUT_FORMAT_SMT2 3
#define BTOR_OUTPUT_FORMAT_AIGER_ASCII 4
#define BTOR_OUTPUT_FORMAT_AIGER_BINARY 5
#define BTOR_OUTPUT_FORMAT_DFLT BTOR_OUTPUT_FORMAT_BTOR
#define BTOR_OUTPUT_FORMAT_MIN BTOR_OUTPUT_FORMAT_BTOR
#define BTOR_OUTPUT_FORMAT_MAX BTOR_OUTPUT_FORMAT_AIGER_BINARY

#define BTOR_JUST_HEUR_LEFT 0
#define BTOR_JUST_HEUR_BRANCH_MIN_APP 1
#define BTOR_JUST_HEUR_BRANCH_MIN_DEP 2
#define BTOR_JUST_HEUR_DFLT BTOR_JUST_HEUR_BRANCH_MIN_APP
#define BTOR_JUST_HEUR_MIN BTOR_JUST_HEUR_LEFT
#define BTOR_JUST_HEUR_MAX BTOR_JUST_HEUR_BRANCH_MIN_DEP

#define BTOR_SLS_STRAT_BEST_MOVE 0
#define BTOR_SLS_STRAT_PROB_RAND_WALK 1
#define BTOR_SLS_STRAT_FIRST_BEST_MOVE 2
#define BTOR_SLS_STRAT_BEST_SAME_MOVE 3
#define BTOR_SLS_STRAT_ALWAYS_PROP 4
#define BTOR_SLS_STRAT_DFLT BTOR_SLS_STRAT_BEST_MOVE
#define BTOR_SLS_STRAT_MIN 0
#define BTOR_SLS_STRAT_MAX 4

/*------------------------------------------------------------------------*/

typedef struct BtorOpt
{
  int internal;     /* internal option? */
  bool isflag;      /* flag? */
  const char *shrt; /* short option identifier (may be 0) */
  const char *lng;  /* long option identifier */
  const char *desc; /* description */
  uint32_t val;     /* value */
  uint32_t dflt;    /* default value */
  uint32_t min;     /* min value */
  uint32_t max;     /* max value */
  char *valstr;     /* optional option string value */
} BtorOpt;

/*------------------------------------------------------------------------*/

#define BTOR_OPT_MODEL_GEN "model_gen"
#define BTOR_OPT_INCREMENTAL "incremental"
#define BTOR_OPT_INCREMENTAL_ALL "incremental_all"
#define BTOR_OPT_INPUT_FORMAT "input_format"
#define BTOR_OPT_OUTPUT_NUMBER_FORMAT "output_number_format"
#define BTOR_OPT_OUTPUT_FORMAT "output_format"
#define BTOR_OPT_ENGINE "engine"
#define BTOR_OPT_SAT_ENGINE "sat_engine"
#define BTOR_OPT_AUTO_CLEANUP "auto_cleanup"
#define BTOR_OPT_PRETTY_PRINT "pretty_print"
#define BTOR_OPT_EXIT_CODES "exit_codes"
#define BTOR_OPT_SEED "seed"
#define BTOR_OPT_VERBOSITY "verbosity"
#define BTOR_OPT_LOGLEVEL "loglevel"
/* simplifier --------------------------------------------------------- */
#define BTOR_OPT_REWRITE_LEVEL "rewrite_level"
#define BTOR_OPT_SKELETON_PREPROC "skeleton_preproc"
#define BTOR_OPT_ACKERMANN "ackermannize"
#define BTOR_OPT_BETA_REDUCE_ALL "beta_reduce_all"
#define BTOR_OPT_ELIMINATE_SLICES "eliminate_slices"
#define BTOR_OPT_VAR_SUBST "var_subst"
#define BTOR_OPT_UCOPT "ucopt"
#define BTOR_OPT_MERGE_LAMBDAS "merge_lambdas"
#define BTOR_OPT_EXTRACT_LAMBDAS "extract_lambdas"
/* fun engine --------------------------------------------------------- */
#define BTOR_OPT_FUN_DUAL_PROP "fun:dual_prop"
#define BTOR_OPT_FUN_JUST "fun:just"
#define BTOR_OPT_FUN_JUST_HEURISTIC "fun:just_heuristic"
#define BTOR_OPT_FUN_LAZY_SYNTHESIZE "fun:lazy_synthesize"
#define BTOR_OPT_FUN_EAGER_LEMMAS "fun:eager_lemmas"
/* SLS engine --------------------------------------------------------- */
#define BTOR_OPT_SLS_STRATEGY "sls:strategy"
#define BTOR_OPT_SLS_JUST "sls:just"
#define BTOR_OPT_SLS_MOVE_GW "sls:move_gw"
#define BTOR_OPT_SLS_MOVE_RANGE "sls:move_range"
#define BTOR_OPT_SLS_MOVE_SEGMENT "sls:move_segment"
#define BTOR_OPT_SLS_MOVE_RAND_WALK "sls:move_rand_walk"
#define BTOR_OPT_SLS_MOVE_RAND_WALK_PROB "sls:move_rand_walk_prob"
#define BTOR_OPT_SLS_MOVE_RAND_ALL "sls:move_rand_all"
#define BTOR_OPT_SLS_MOVE_RAND_RANGE "sls:move_rand_range"
#define BTOR_OPT_SLS_MOVE_PROP "sls:move_prop"
#define BTOR_OPT_SLS_MOVE_PROP_N_PROP "sls:move_prop_n_prop"
#define BTOR_OPT_SLS_MOVE_PROP_N_SLS "sls:move_prop_n_sls"
#define BTOR_OPT_SLS_MOVE_PROP_FORCE_RW "sls:move_prop_force_rw"
#define BTOR_OPT_SLS_MOVE_PROP_NO_FLIP_COND "sls:move_prop_no_flip_cond"
#define BTOR_OPT_SLS_MOVE_PROP_FLIP_COND_PROB "sls:move_prop_flip_cond_prob"
#define BTOR_OPT_SLS_MOVE_INC_MOVE_TEST "sls:move_inc_move_test"
#define BTOR_OPT_SLS_USE_RESTARTS "sls:use_restarts"
#define BTOR_OPT_SLS_USE_BANDIT "sls:use_bandit"
/* internal options --------------------------------------------------- */
#define BTOR_OPT_SORT_EXP "sort_exp"
#define BTOR_OPT_SORT_AIG "sort_aig"
#define BTOR_OPT_SORT_AIGVEC "sort_aigvec"
#define BTOR_OPT_AUTO_CLEANUP_INTERNAL "auto_cleanup_internal"
#define BTOR_OPT_SIMPLIFY_CONSTRAINTS "simplify_constraints"
#define BTOR_OPT_RW_NORMALIZE "rw_normalize"
#ifdef BTOR_CHECK_FAILED
#define BTOR_OPT_CHK_FAILED_ASSUMPTIONS "chk_failed_assumptions"
#endif
#define BTOR_OPT_PARSE_INTERACTIVE "parse_interactive"
#ifdef BTOR_USE_LINGELING
#define BTOR_OPT_SAT_ENGINE_LGL_FORK "sat_engine_lgl_fork"
#endif

/*------------------------------------------------------------------------*/

void btor_init_opts (Btor *btor);
BtorPtrHashTable *btor_clone_opts (BtorMemMgr *mm, BtorPtrHashTable *options);
void btor_delete_opts (Btor *btor);

bool btor_has_opt (Btor *btor, const char *name);

uint32_t btor_get_opt (Btor *btor, const char *name);
uint32_t btor_get_opt_min (Btor *btor, const char *name);
uint32_t btor_get_opt_max (Btor *btor, const char *name);
uint32_t btor_get_opt_dflt (Btor *btor, const char *name);
const char *btor_get_opt_shrt (Btor *btor, const char *name);
const char *btor_get_opt_desc (Btor *btor, const char *name);
const char *btor_get_opt_valstr (Btor *btor, const char *name);

void btor_set_opt (Btor *btor, const char *name, uint32_t val);
void btor_set_opt_str (Btor *btor, const char *name, const char *str);

const char *btor_first_opt (Btor *btor);
const char *btor_next_opt (Btor *btor, const char *cur);
#endif
