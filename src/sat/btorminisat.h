/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2012 Armin Biere.
 *  Copyright (C) 2017 Mathias Preiner.
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
