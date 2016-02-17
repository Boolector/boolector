/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSYNTHFUN_H_INCLUDED
#define BTORSYNTHFUN_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashptr.h"

BtorNode* btor_synthesize_fun (Btor* btor,
                               BtorNode* uf,
                               const BtorPtrHashTable* model,
                               BtorNode* candidate);

#endif
