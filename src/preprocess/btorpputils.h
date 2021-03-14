/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPPUTILS_H_INCLUDED
#define BTORPPUTILS_H_INCLUDED

#include "btortypes.h"
#include "btornode.h"

void btor_pputils_collect_lambdas (Btor *btor, BtorNodePtrStack * lambdas);

#endif
