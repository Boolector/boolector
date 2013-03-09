/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *
 *  All rights reserved.
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORMAP_H_INCLUDED
#define BTORMAP_H_INCLUDED

#include "btorexp.h"

/*------------------------------------------------------------------------*/
/* Simple map for expression node.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'btor_map_node'.  Succesful look-up
 * through 'btor_mapped_node' does not add a reference.  The desctructor
 * releases all the owned references.
 */
typedef struct BtorPtrHashTable BtorNodeMap;

/*------------------------------------------------------------------------*/

BtorNodeMap *btor_new_node_map (Btor *);
BtorNode *btor_mapped_node (BtorNodeMap *, BtorNode *);
void btor_map_node (Btor *, BtorNodeMap *, BtorNode *src, BtorNode *dst);
void btor_delete_node_map (Btor *, BtorNodeMap *);

/*------------------------------------------------------------------------*/

BtorNode *btor_substitute_node (Btor *, BtorMap *assignment, BtorNode *);

/*------------------------------------------------------------------------*/

#endif
