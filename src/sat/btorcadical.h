/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCADICAL_H_INCLUDED
#define BTORCADICAL_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_CADICAL
/*------------------------------------------------------------------------*/

#include "btorsat.h"

bool btor_sat_enable_cadical (BtorSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
