/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013,2015 Aina Niemetz.
 *  Copyright (C) 2013 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORMAP_H_INCLUDED
#define BTORMAP_H_INCLUDED

#include "boolector.h"
#include "btoraig.h"

/*------------------------------------------------------------------------*/
/* Simple map for expression node.  The 'map' owns references to the non
 * zero 'src' and 'dst' nodes added in 'btor_map_node'.  Succesful look-up
 * through 'btor_mapped_node' does not add a reference.  The destructor
 * releases all the owned references.  Mapping is signed, e.g. if you map
 * 'a' to 'b', then '~a' is implicitely mapped to '~b', too.
 *
 * As long 'BoolectorNode' is the same as 'BtorNode' these mapping functions
 * can also be used to map 'BoolectorNode' objects (by casting).  The
 * alternative would be to implement all these mapping functions identically
 * through the external interface (replacing 'btor_and' by 'boolector_and'
 * etc. in the recursive versions).
 */
struct BtorNodeMap
{
  Btor *btor;  // For managing (owning) map memory
               // Otherwise src and dst can have different
               // Boolector instances (even != 'btor')!!!
  BtorPtrHashTable *table;

  // '0' for BtorNodeMap:	e.g. do not follow simplify pointers ...
  // '1' for BoolectorNodeMap:	pointer chasing on nodes enabled
  //
  int simplify;
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

/*========================================================================*/

// External version using external 'boolector_...' API calls internally.

typedef struct BoolectorNodeMap BoolectorNodeMap;

/*------------------------------------------------------------------------*/

BoolectorNodeMap *boolector_new_node_map (Btor *);
BoolectorNode *boolector_mapped_node (BoolectorNodeMap *, BoolectorNode *);
int boolector_count_map (BoolectorNodeMap *map);
void boolector_map_node (BoolectorNodeMap *, BoolectorNode *, BoolectorNode *);
void boolector_delete_node_map (BoolectorNodeMap *);

/*------------------------------------------------------------------------*/

BoolectorNode *boolector_non_recursive_substitute_node (Btor *,
                                                        BoolectorNodeMap *,
                                                        BoolectorNode *);

/*------------------------------------------------------------------------*/

typedef BoolectorNode *(*BoolectorNodeMapper) (Btor *,
                                               void *state,
                                               BoolectorNode *);

typedef void (*BoolectorNodeReleaser) (Btor *, BoolectorNode *);

BoolectorNode *boolector_non_recursive_extended_substitute_node (
    Btor *,
    BoolectorNodeMap *,
    void *state,
    BoolectorNodeMapper,
    BoolectorNodeReleaser,
    BoolectorNode *root);

/*========================================================================*/

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
