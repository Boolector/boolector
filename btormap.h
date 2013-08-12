/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORMAP_H_INCLUDED
#define BTORMAP_H_INCLUDED

#include "btoraig.h"
#include "btorexp.h"

/*------------------------------------------------------------------------*/

#define BTOR_COUNT_MAP(MAP) (assert (MAP), (MAP)->count)

/*------------------------------------------------------------------------*/
/* Simple map for expression node.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'btor_map_node'.  Succesful look-up
 * through 'btor_mapped_node' does not add a reference.  The destructor
 * releases all the owned references.  Mapping is signed, e.g. if you  map
 * 'a' to 'b', then implicilty you map '~a' to '~b' too.
 */
typedef struct BtorPtrHashTable BtorNodeMap;

/*------------------------------------------------------------------------*/

BtorNodeMap *btor_new_node_map (Btor *);
BtorNode *btor_mapped_node (BtorNodeMap *, BtorNode *);
void btor_map_node (Btor *, BtorNodeMap *, BtorNode *src, BtorNode *dst);
void btor_delete_node_map (Btor *, BtorNodeMap *);

/*------------------------------------------------------------------------*/

BtorNode *btor_non_recursive_substitute_node (Btor *,
                                              BtorNodeMap *,
                                              BtorNode *);

/*------------------------------------------------------------------------*/
/* Extended mapping.  A 'BtorNodeMapper' function should return a NEW
 * reference to the result of mapping the argument node (using the arbitrary
 * state) or a 0 pointer if it can not map it.  The idea is that such a
 * mapper implements the base case of a (non-recursive) substitution.
 * The mapper will only be called with non-inverted nodes as arguments.
 */
typedef BtorNode *(*BtorNodeMapper) (Btor *, void *state, BtorNode *);

BtorNode *btor_non_recursive_extended_substitute_node (
    Btor *,
    BtorNodeMap *,   // share/cache substitution results
    void *state,     // for the mapper
    BtorNodeMapper,  // see above
    BtorNode *root);

/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* Simple map for AIG node.  Same reference counting and signed behavior
 * as BtorNodeMap.
 */
typedef struct BtorPtrHashTable BtorAIGMap;

/*------------------------------------------------------------------------*/

BtorAIGMap *btor_new_aig_map (Btor *);
BtorAIG *btor_mapped_aig (BtorAIGMap *, BtorAIG *);
void btor_map_aig (Btor *, BtorAIGMap *, BtorAIG *src, BtorAIG *dst);
void btor_delete_aig_map (Btor *, BtorAIGMap *);

/*------------------------------------------------------------------------*/

#endif
