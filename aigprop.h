/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoraig.h"
#include "utils/btorhash.h"

void aigprop_generate_model (BtorAIGMgr* amgr,
                             BtorPtrHashTable* roots,
                             BtorPtrHashTable* model);

void aigprop_move (BtorAIGMgr* amgr,
                   BtorPtrHashTable* roots,
                   BtorPtrHashTable* model);
