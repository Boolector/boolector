/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef AIGPROP_H_INCLUDED
#define AIGPROP_H_INCLUDED

#include "btoraig.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

#define AIGPROP_UNKNOWN 0
#define AIGPROP_SAT 10
#define AIGPROP_UNSAT 20

struct AIGProp
{
  BtorAIGMgr *amgr;
  BtorPtrHashTable *roots;
  BtorPtrHashTable *score;
  BtorPtrHashTable *model;

  BtorRNG rng;

  uint32_t loglevel;
  uint32_t seed;

  struct
  {
    uint32_t moves;
    uint32_t restarts;
  } stats;

  struct
  {
    double sat;
  } time;
};

typedef struct AIGProp AIGProp;

AIGProp *aigprop_new_aigprop (BtorAIGMgr *amgr, uint32_t seed);
AIGProp *aigprop_clone_aigprop (BtorAIGMgr *clone, AIGProp *aprop);
void aigprop_delete_aigprop (AIGProp *aprop);

int aigprop_get_assignment_aig (BtorPtrHashTable *model, BtorAIG *aig);
void aigprop_generate_model (AIGProp *aprop, int reset);

int aigprop_sat (AIGProp *aprop);

void aigprop_print_stats (AIGProp *aprop);
void aigprop_print_time_stats (AIGProp *aprop);

#endif
