/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
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

BtorAIGMap *btor_new_aig_map (Btor *, BtorAIGMgr *, BtorAIGMgr *);
BtorAIG *btor_mapped_aig (BtorAIGMap *, BtorAIG *);
void btor_map_aig (BtorAIGMap *, BtorAIG *src, BtorAIG *dst);
void btor_delete_aig_map (BtorAIGMap *);

/*------------------------------------------------------------------------*/

#endif
