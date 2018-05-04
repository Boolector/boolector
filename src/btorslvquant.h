/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLVQUANT_H_INCLUDED
#define BTORSLVQUANT_H_INCLUDED

#include "btorslv.h"
#include "btortypes.h"

BtorSolver* btor_new_quantifier_solver (Btor* btor);

#endif
