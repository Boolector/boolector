/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSATLGL_H_INCLUDED
#define BTORSATLGL_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_LINGELING
/*------------------------------------------------------------------------*/

#include "btorsat.h"
#include "lglib.h"

typedef struct BtorLGL BtorLGL;

struct BtorLGL
{
  LGL* lgl;
  int32_t nforked, blimit;
};

bool btor_sat_enable_lingeling (BtorSATMgr* smgr);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
