/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSUBST_H_INCLUDED
#define BTORSUBST_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashptr.h"

void btor_substitute_and_rebuild (Btor *btor, BtorPtrHashTable *substs);

#endif
