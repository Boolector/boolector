/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORUNIONFIND_H_INCLUDED
#define BTORUNIONFIND_H_INCLUDED

#include "btortypes.h"
#include "utils/btormem.h"

#include <stdbool.h>

typedef struct BtorUnionFind BtorUnionFind;

/* Create new union-find data structure */
BtorUnionFind *btor_ufind_new (BtorMemMgr *mm);

/* Delete union-find data structure. */
void btor_ufind_delete (BtorUnionFind *ufind);

/* Add a new set containing 'x'. */
void btor_ufind_add (BtorUnionFind *ufind, BtorNode *x);

/* Merge sets of 'x' and 'y'. */
void btor_ufind_merge (BtorUnionFind *ufind, BtorNode *x, BtorNode *y);

/* Get representative of 'x'. */
BtorNode *btor_ufind_get_repr (BtorUnionFind *ufind, BtorNode *x);

/* Check whether 'x' and 'y' belong to the same set. */
bool btor_ufind_is_equal (BtorUnionFind *ufind, BtorNode *x, BtorNode *y);

#endif
