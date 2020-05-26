/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Andrew V. Jones
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSATKISSAT_H_INCLUDED
#define BTORSATKISSAT_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "btorsat.h"

bool btor_sat_enable_kissat (BtorSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
