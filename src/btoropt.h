/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2020 Aina Niemetz.
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *  Copyright (C) 2014-2015 Armin Biere.
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

struct BtorOpt
{
  bool internal;              /* internal option? */
  bool isflag;                /* flag? */
  const char *shrt;           /* short option identifier (may be 0) */
  const char *lng;            /* long option identifier */
  const char *desc;           /* description */
  uint32_t val;               /* value */
  uint32_t dflt;              /* default value */
  uint32_t min;               /* min value */
  uint32_t max;               /* max value */
  char *valstr;               /* optional option string value */
  BtorPtrHashTable *options;  /* maps option CL value strings to enum values */
};
typedef struct BtorOpt BtorOpt;

/*------------------------------------------------------------------------*/

/**
 * Represents the data required to print help messages for options that
 * expect an enum value rather than an (u)int value. This is mainly needed
 * for invoking the solver via the command line (with '--<opt>=help').
 */
struct BtorOptHelp
{
  int32_t val;     /* the enum value */
  const char *msg; /* the help message */
};
typedef struct BtorOptHelp BtorOptHelp;

/*------------------------------------------------------------------------*/

/* enum BtorOption is in btortypes.h */

#define BTOR_OPT_NUM_OPTS_STR "end_of_options_marker"
#define BTOR_OPT_INVALID_OPT_STR "invalid_option"

/*------------------------------------------------------------------------*/

#define BTOR_VERBOSITY_MAX 4

#define BTOR_PROB_MAX 1000

/* enums for option values are defined in btortypes.h */

#define BTOR_SAT_ENGINE_MIN BTOR_SAT_ENGINE_LINGELING
#define BTOR_SAT_ENGINE_MAX BTOR_SAT_ENGINE_CMS
#ifdef BTOR_USE_CADICAL
#define BTOR_SAT_ENGINE_DFLT BTOR_SAT_ENGINE_CADICAL
#elif BTOR_USE_LINGELING
#define BTOR_SAT_ENGINE_DFLT BTOR_SAT_ENGINE_LINGELING
#elif BTOR_USE_PICOSAT
#define BTOR_SAT_ENGINE_DFLT BTOR_SAT_ENGINE_PICOSAT
#elif BTOR_USE_MINISAT
#define BTOR_SAT_ENGINE_DFLT BTOR_SAT_ENGINE_MINISAT
#elif BTOR_USE_CMS
#define BTOR_SAT_ENGINE_DFLT BTOR_SAT_ENGINE_CMS
#endif
extern const char *const g_btor_se_name[BTOR_SAT_ENGINE_MAX + 1];

#define BTOR_ENGINE_MIN BTOR_ENGINE_FUN
#define BTOR_ENGINE_MAX BTOR_ENGINE_QUANT
#define BTOR_ENGINE_DFLT BTOR_ENGINE_FUN

#define BTOR_INPUT_FORMAT_MIN BTOR_INPUT_FORMAT_NONE
#define BTOR_INPUT_FORMAT_MAX BTOR_INPUT_FORMAT_SMT2
#define BTOR_INPUT_FORMAT_DFLT BTOR_INPUT_FORMAT_NONE

#define BTOR_OUTPUT_BASE_MIN BTOR_OUTPUT_BASE_BIN
#define BTOR_OUTPUT_BASE_MAX BTOR_OUTPUT_BASE_DEC
#define BTOR_OUTPUT_BASE_DFLT BTOR_OUTPUT_BASE_BIN

#define BTOR_OUTPUT_FORMAT_MIN BTOR_OUTPUT_FORMAT_NONE
#define BTOR_OUTPUT_FORMAT_MAX BTOR_OUTPUT_FORMAT_AIGER_BINARY
#define BTOR_OUTPUT_FORMAT_DFLT BTOR_OUTPUT_FORMAT_NONE

#define BTOR_DP_QSORT_MIN BTOR_DP_QSORT_JUST
#define BTOR_DP_QSORT_MAX BTOR_DP_QSORT_DESC
#define BTOR_DP_QSORT_DFLT BTOR_DP_QSORT_JUST

#define BTOR_JUST_HEUR_MIN BTOR_JUST_HEUR_BRANCH_LEFT
#define BTOR_JUST_HEUR_MAX BTOR_JUST_HEUR_BRANCH_MIN_DEP
#define BTOR_JUST_HEUR_DFLT BTOR_JUST_HEUR_BRANCH_MIN_APP

#define BTOR_SLS_STRAT_MIN BTOR_SLS_STRAT_BEST_MOVE
#define BTOR_SLS_STRAT_MAX BTOR_SLS_STRAT_ALWAYS_PROP
#define BTOR_SLS_STRAT_DFLT BTOR_SLS_STRAT_BEST_MOVE

#define BTOR_PROP_PATH_SEL_MIN BTOR_PROP_PATH_SEL_CONTROLLING
#define BTOR_PROP_PATH_SEL_MAX BTOR_PROP_PATH_SEL_RANDOM
#define BTOR_PROP_PATH_SEL_DFLT BTOR_PROP_PATH_SEL_ESSENTIAL

#define BTOR_QUANT_SYNTH_MIN BTOR_QUANT_SYNTH_NONE
#define BTOR_QUANT_SYNTH_MAX BTOR_QUANT_SYNTH_ELMR
#define BTOR_QUANT_SYNTH_DFLT BTOR_QUANT_SYNTH_ELMR

#define BTOR_FUN_EAGER_LEMMAS_MIN BTOR_FUN_EAGER_LEMMAS_NONE
#define BTOR_FUN_EAGER_LEMMAS_MAX BTOR_FUN_EAGER_LEMMAS_ALL
#define BTOR_FUN_EAGER_LEMMAS_DFLT BTOR_FUN_EAGER_LEMMAS_CONF

#define BTOR_INCREMENTAL_SMT1_MIN BTOR_INCREMENTAL_SMT1_BASIC
#define BTOR_INCREMENTAL_SMT1_MAX BTOR_INCREMENTAL_SMT1_CONTINUE
#define BTOR_INCREMENTAL_SMT1_DFLT BTOR_INCREMENTAL_SMT1_BASIC

#define BTOR_BETA_REDUCE_MIN BTOR_BETA_REDUCE_NONE
#define BTOR_BETA_REDUCE_MAX BTOR_BETA_REDUCE_ALL
#define BTOR_BETA_REDUCE_DFLT BTOR_BETA_REDUCE_NONE

/*------------------------------------------------------------------------*/

void btor_opt_init_opts (Btor *btor);
void btor_opt_clone_opts (Btor *btor, Btor *clone);
void btor_opt_delete_opts (Btor *btor);

bool btor_opt_is_valid (const Btor *btor, const BtorOption opt);

uint32_t btor_opt_get (const Btor *btor, const BtorOption opt);
uint32_t btor_opt_get_min (const Btor *btor, const BtorOption opt);
uint32_t btor_opt_get_max (const Btor *btor, const BtorOption opt);
uint32_t btor_opt_get_dflt (const Btor *btor, const BtorOption opt);
const char *btor_opt_get_lng (const Btor *btor, const BtorOption opt);
const char *btor_opt_get_shrt (const Btor *btor, const BtorOption opt);
const char *btor_opt_get_desc (const Btor *btor, const BtorOption opt);
const char *btor_opt_get_valstr (const Btor *btor, const BtorOption opt);

void btor_opt_set (Btor *btor, const BtorOption opt, uint32_t val);
void btor_opt_set_str (Btor *btor, const BtorOption opt, const char *str);

BtorOption btor_opt_first (Btor *btor);
BtorOption btor_opt_next (Btor *btor, BtorOption cur);

#ifndef NBTORLOG
void btor_opt_log_opts (Btor *btor);
#endif
#endif
