/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
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
