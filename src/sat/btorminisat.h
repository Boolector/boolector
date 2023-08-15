/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMINISAT_H_INCLUDED
#define BTORMINISAT_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_MINISAT
/*------------------------------------------------------------------------*/

#include "btorsat.h"

bool btor_sat_enable_minisat (BtorSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
