/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBITBLAST_H_INCLUDED
#define BTORBITBLAST_H_INCLUDED

#include "btoraigvec.h"
#include "btortypes.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

BtorAIGVec *btor_bitblast_exp (Btor *btor,
                               BtorAIGVecMgr *avmgr,
                               BtorNode *exp,
                               BtorPtrHashTable *node_to_aigvec,
                               BtorIntHashTable *symbols);

#endif
