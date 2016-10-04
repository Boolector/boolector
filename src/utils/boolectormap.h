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
#ifndef BOOLECTORMAP_H_INCLUDED
#define BOOLECTORMAP_H_INCLUDED

/*------------------------------------------------------------------------*/

#include "boolector.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/
/* Simple map for expression nodes.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'boolector_map_node'.  Succesful
 * look-up through 'boolector_mapped_node' does not add a reference.  The
 * destructor releases all the owned references.  Mapping is signed, e.g.,
 * if you map * 'a' to 'b', then '~a' is implicitely mapped to '~b', too.
 */
struct BoolectorNodeMap
{
  Btor *btor;  // For managing (owning) map memory
               // Otherwise src and dst can have different
               // Boolector instances (even != 'btor')!!!
  BtorPtrHashTable *table;
};

typedef struct BoolectorNodeMap BoolectorNodeMap;

/*------------------------------------------------------------------------*/

BoolectorNodeMap *boolector_new_node_map (Btor *btor);
void boolector_delete_node_map (BoolectorNodeMap *);

void boolector_map_node (BoolectorNodeMap *map,
                         BoolectorNode *src,
                         BoolectorNode *dst);

BoolectorNode *boolector_mapped_node (BoolectorNodeMap *map, BoolectorNode *n);

int boolector_count_map (BoolectorNodeMap *map);

/*------------------------------------------------------------------------*/

BoolectorNode *boolector_non_recursive_substitute_node (Btor *btor,
                                                        BoolectorNodeMap *map,
                                                        BoolectorNode *n);

/*------------------------------------------------------------------------*/
/* Extended mapping.  A 'BoolectorNodeMapper' function should return a NEW
 * reference to the result of mapping the argument node (using the arbitrary
 * state) or a 0 pointer if it can not map it.  The idea is that such a
 * mapper implements the base case of a (non-recursive) substitution.
 *
 * The mapper will only be called with non-inverted and simplified
 * nodes as arguments.
 */
typedef BoolectorNode *(*BoolectorNodeMapper) (Btor *btor,
                                               void *state,
                                               BoolectorNode *n);

/* References returned by a 'BoolectorNodeMapper' are not restricted to be
 * allocated internally, hence we need a matching release operation.
 */
typedef void (*BoolectorNodeReleaser) (Btor *btor, BoolectorNode *n);

BoolectorNode *boolector_non_recursive_extended_substitute_node (
    Btor *btor,
    BoolectorNodeMap *map,  // share/cache substitution results
    void *state,            // for the mapper
    BoolectorNodeMapper,    // see above
    BoolectorNodeReleaser,  // see above
    BoolectorNode *root);

/*------------------------------------------------------------------------*/

#endif
