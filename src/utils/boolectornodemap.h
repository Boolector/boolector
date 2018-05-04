/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BOOLECTORNODEMAP_H_INCLUDED
#define BOOLECTORNODEMAP_H_INCLUDED

/*------------------------------------------------------------------------*/

#include "btortypes.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/
/* Simple map for expression nodes.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'boolector_nodemap_map'.  Succesful
 * look-up through 'boolector_nodemap_mapped' does not add a reference.  The
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

BoolectorNodeMap *boolector_nodemap_new (Btor *btor);
void boolector_nodemap_delete (BoolectorNodeMap *);

void boolector_nodemap_map (BoolectorNodeMap *map,
                            BoolectorNode *src,
                            BoolectorNode *dst);

BoolectorNode *boolector_nodemap_mapped (BoolectorNodeMap *map,
                                         const BoolectorNode *n);

uint32_t boolector_nodemap_count (const BoolectorNodeMap *map);

/*------------------------------------------------------------------------*/

BoolectorNode *boolector_nodemap_substitute_node (Btor *btor,
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

BoolectorNode *boolector_nodemap_extended_substitute_node (
    Btor *btor,
    BoolectorNodeMap *map,  // share/cache substitution results
    void *state,            // for the mapper
    BoolectorNodeMapper,    // see above
    BoolectorNodeReleaser,  // see above
    BoolectorNode *root);

/*------------------------------------------------------------------------*/

#endif
