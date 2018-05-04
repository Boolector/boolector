/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
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
