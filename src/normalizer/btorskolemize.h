/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSKOLEMIZE_H_INCLUDED
#define BTORSKOLEMIZE_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

void btor_skolemize (Btor* btor);

BtorNode* btor_skolemize_node (Btor* btor,
                               BtorNode* root,
                               BtorIntHashTable* node_map,
                               BtorPtrHashTable* skolem_consts);

#endif
