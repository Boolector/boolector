/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORAIGMAP_H_INCLUDED
#define BTORAIGMAP_H_INCLUDED

/*------------------------------------------------------------------------*/

#include "boolector.h"
#include "btoraig.h"

/*------------------------------------------------------------------------*/

/* Simple map for AIG node.  Same reference counting and signed/tagged
 * behavior as BtorNodeMap.
 */
struct BtorAIGMap
{
  Btor *btor;           /* managing (owning) map internals */
  BtorAIGMgr *amgr_src; /* managing (owning) source aigs */
  BtorAIGMgr *amgr_dst; /* managing (owning) destination aigs */
  BtorPtrHashTable *table;
};

typedef struct BtorAIGMap BtorAIGMap;

/*------------------------------------------------------------------------*/

BtorAIGMap *btor_aigmap_new (Btor *, BtorAIGMgr *, BtorAIGMgr *);
BtorAIG *btor_aigmap_mapped (BtorAIGMap *, BtorAIG *);
void btor_aigmap_map (BtorAIGMap *, BtorAIG *src, BtorAIG *dst);
void btor_aigmap_delete (BtorAIGMap *);

/*------------------------------------------------------------------------*/

#endif
