/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  All rights reserved.
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
  int nforked, blimit;
};

bool btor_sat_enable_lingeling (BtorSATMgr* smgr,
                                const char* options,
                                bool fork);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
