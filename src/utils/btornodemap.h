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
#ifndef BTORNODEMAP_H_INCLUDED
#define BTORNODEMAP_H_INCLUDED

/*========================================================================*/
/* After 'defactorizing' this code into 'btornodemap.h' and 'boolectormap.h'
 * this internal version became obsolete and currently only is used in the
 * regression suite.  We might want to keep it around for a while until
 * the external version in 'boolectormap.h' which goes through the external
 * API (that is 'boolector_...' functions and not 'btor_...' function) is
 * stable.  This split into two versions became necessary after we introduced
 * and now check proper external reference counting.
 */
/*========================================================================*/

#include "boolector.h"
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

BtorNodeMap *btor_new_node_map (Btor *);
BtorNode *btor_mapped_node (BtorNodeMap *, BtorNode *);
int btor_count_map (BtorNodeMap *map);
void btor_map_node (BtorNodeMap *, BtorNode *src, BtorNode *dst);
void btor_delete_node_map (BtorNodeMap *);

/*------------------------------------------------------------------------*/

BtorNode *btor_non_recursive_substitute_node (Btor *,
                                              BtorNodeMap *,
                                              BtorNode *);

/*------------------------------------------------------------------------*/
/* Extended mapping.  A 'BtorNodeMapper' function should return a NEW
 * reference to the result of mapping the argument node (using the arbitrary
 * state) or a 0 pointer if it can not map it.  The idea is that such a
 * mapper implements the base case of a (non-recursive) substitution.
 *
 * The mapper will only be called with non-inverted and simplified
 * nodes as arguments.
 */
typedef BtorNode *(*BtorNodeMapper) (Btor *, void *state, BtorNode *);

/* References returned by a 'BtorNodeMapper' are not restricted to be
 * allocated internally, hence we need a matching release operation.
 */
typedef void (*BtorNodeReleaser) (Btor *, BtorNode *);

BtorNode *btor_non_recursive_extended_substitute_node (
    Btor *,
    BtorNodeMap *,     // share/cache substitution results
    void *state,       // for the mapper
    BtorNodeMapper,    // see above
    BtorNodeReleaser,  // see above
    BtorNode *root);

/*------------------------------------------------------------------------*/

#endif
