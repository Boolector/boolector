/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTOR_AIGPROP_H_INCLUDED
#define BTOR_AIGPROP_H_INCLUDED

#include "btoraig.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btorrng.h"

#define BTOR_AIGPROP_UNKNOWN 0
#define BTOR_AIGPROP_SAT 10
#define BTOR_AIGPROP_UNSAT 20

struct BtorAIGProp
{
  BtorAIGMgr *amgr;
  BtorIntHashTable *roots;
  BtorIntHashTable *unsatroots;
  BtorIntHashTable *score;
  BtorIntHashTable *model;
  BtorIntHashTable *parents;

  BtorRNG rng;

  uint32_t loglevel;
  uint32_t seed;
  uint32_t use_restarts;
  uint32_t use_bandit;

  struct
  {
    uint32_t moves;
    uint32_t restarts;
  } stats;

  struct
  {
    double sat;
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BtorAIGProp BtorAIGProp;

BtorAIGProp *btor_aigprop_new_aigprop (BtorAIGMgr *amgr,
                                       uint32_t loglevel,
                                       uint32_t seed,
                                       uint32_t use_restarts,
                                       uint32_t use_bandit);

BtorAIGProp *btor_aigprop_clone_aigprop (BtorAIGMgr *clone, BtorAIGProp *aprop);
void btor_aigprop_delete_aigprop (BtorAIGProp *aprop);

int32_t btor_aigprop_get_assignment_aig (BtorAIGProp *aprop, BtorAIG *aig);
void btor_aigprop_generate_model (BtorAIGProp *aprop, bool reset);

int32_t btor_aigprop_sat (BtorAIGProp *aprop, BtorIntHashTable *roots);

#if 0
void btor_aigprop_print_stats (BtorAIGProp * aprop);
void btor_aigprop_print_time_stats (BtorAIGProp * aprop);
#endif

#endif
