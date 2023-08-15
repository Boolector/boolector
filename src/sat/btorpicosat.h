/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSATPICOSAT_H_INCLUDED
#define BTORSATPICOSAT_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_PICOSAT
/*------------------------------------------------------------------------*/

#include "btorsat.h"

bool btor_sat_enable_picosat (BtorSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
