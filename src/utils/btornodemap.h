/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORNODEMAP_H_INCLUDED
#define BTORNODEMAP_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/
/* Simple map for expression node.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'btor_nodemap_map'.  Succesfull look-up
 * through 'btor_nodemap_mapped' does not add a reference.  The destructor
 * releases all the owned references.  Mapping is signed, e.g. if you map
 * 'a' to 'b', then '~a' is implicitly mapped to '~b', too.
 */
struct BtorNodeMap
{
  Btor *btor;  // For managing (owning) map memory
               // Otherwise src and dst can have different
               // Boolector instances (even != 'btor')!!!
  BtorPtrHashTable *table;
};

typedef struct BtorNodeMap BtorNodeMap;

/*------------------------------------------------------------------------*/

BtorNodeMap *btor_nodemap_new (Btor *btor);
BtorNode *btor_nodemap_mapped (BtorNodeMap *map, const BtorNode *node);
void btor_nodemap_map (BtorNodeMap *map, BtorNode *src, BtorNode *dst);
void btor_nodemap_delete (BtorNodeMap *map);

/*------------------------------------------------------------------------*/
/* iterators    						          */
/*------------------------------------------------------------------------*/

typedef struct BtorNodeMapIterator
{
  BtorPtrHashTableIterator it;
} BtorNodeMapIterator;

void btor_iter_nodemap_init (BtorNodeMapIterator *it, const BtorNodeMap *map);
void btor_iter_nodemap_init_reversed (BtorNodeMapIterator *it,
                                      const BtorNodeMap *map);
void btor_iter_nodemap_queue (BtorNodeMapIterator *it, const BtorNodeMap *map);
bool btor_iter_nodemap_has_next (const BtorNodeMapIterator *it);
BtorNode *btor_iter_nodemap_next (BtorNodeMapIterator *it);
BtorHashTableData *btor_iter_nodemap_next_data (BtorNodeMapIterator *it);

/*------------------------------------------------------------------------*/

#endif
