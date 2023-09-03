/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCMS_H_INCLUDED
#define BTORCMS_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_CMS
/*------------------------------------------------------------------------*/

#include "btorsat.h"

bool btor_sat_enable_cms (BtorSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
