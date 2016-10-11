/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
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
 * zero 'src' and 'dst' nodes added in 'btor_map_node'.  Succesful look-up
 * through 'btor_mapped_node' does not add a reference.  The destructor
 * releases all the owned references.  Mapping is signed, e.g. if you map
 * 'a' to 'b', then '~a' is implicitely mapped to '~b', too.
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

BtorNodeMap *btor_new_node_map (Btor *btor);
BtorNode *btor_mapped_node (BtorNodeMap *map, const BtorNode *node);
int btor_count_map (const BtorNodeMap *map);
void btor_map_node (BtorNodeMap *map, BtorNode *src, BtorNode *dst);
void btor_delete_node_map (BtorNodeMap *map);

/*------------------------------------------------------------------------*/

#endif
