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
#include "utils/btorhash.h"

struct AIGProp
{
  BtorAIGMgr *amgr;
  BtorPtrHashTable *roots;
  BtorPtrHashTable *score;
  BtorPtrHashTable *model;
};

typedef struct AIGProp AIGProp;

AIGProp *aigprop_new_aigprop (BtorAIGMgr *amgr);

void aigprop_generate_model (AIGProp *aprop);

int aigprop_sat (AIGProp *aprop);

#endif
