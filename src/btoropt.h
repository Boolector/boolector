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

struct BtorOpt
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
};

typedef struct BtorOpt BtorOpt;

/*------------------------------------------------------------------------*/

/* enum BtorOption is in btortypes.h */

/*------------------------------------------------------------------------*/

#define BTOR_VERBOSITY_MAX 4

#define BTOR_PROB_MAX 1000

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

#define BTOR_ENGINE_FUN 0
#define BTOR_ENGINE_SLS 1
#define BTOR_ENGINE_PROP 2
#define BTOR_ENGINE_AIGPROP 3
#define BTOR_ENGINE_EF 4
#define BTOR_ENGINE_DFLT BTOR_ENGINE_FUN
#define BTOR_ENGINE_MIN BTOR_ENGINE_FUN
#define BTOR_ENGINE_MAX BTOR_ENGINE_EF

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

#if 0
#define BTOR_EF_QINST_CONST 0
#define BTOR_EF_QINST_SYM 1
#define BTOR_EF_QINST_SYNTH 2
#define BTOR_EF_QINST_DEFAULT BTOR_EF_QINST_CONST
#define BTOR_EF_QINST_MIN BTOR_EF_QINST_CONST
#define BTOR_EF_QINST_MAX BTOR_EF_QINST_SYNTH
#endif

#define BTOR_EF_FINDPM_NONE 0
#define BTOR_EF_FINDPM_REF 1
#define BTOR_EF_FINDPM_DEFAULT BTOR_EF_FINDPM_REF
#define BTOR_EF_FINDPM_MIN BTOR_EF_FINDPM_NONE
#define BTOR_EF_FINDPM_MAX BTOR_EF_FINDPM_REF

/*------------------------------------------------------------------------*/

void btor_init_opts (Btor *btor);
void btor_clone_opts (Btor *btor, Btor *clone);
void btor_delete_opts (Btor *btor);

bool btor_has_opt (Btor *btor, BtorOption opt);

uint32_t btor_get_opt (Btor *btor, BtorOption opt);
uint32_t btor_get_opt_min (Btor *btor, BtorOption opt);
uint32_t btor_get_opt_max (Btor *btor, BtorOption opt);
uint32_t btor_get_opt_dflt (Btor *btor, BtorOption opt);
const char *btor_get_opt_lng (Btor *btor, BtorOption opt);
const char *btor_get_opt_shrt (Btor *btor, BtorOption opt);
const char *btor_get_opt_desc (Btor *btor, BtorOption opt);
const char *btor_get_opt_valstr (Btor *btor, BtorOption opt);

void btor_set_opt (Btor *btor, BtorOption name, uint32_t val);
void btor_set_opt_str (Btor *btor, BtorOption name, const char *str);

BtorOption btor_first_opt (Btor *btor);
BtorOption btor_next_opt (Btor *btor, BtorOption cur);

#ifndef NBTORLOG
void btor_log_opts (Btor *btor);
#endif
#endif
