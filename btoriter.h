/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORITER_H_INCLUDED
#define BTORITER_H_INCLUDED

#include "btorexp.h"

/*------------------------------------------------------------------------*/

struct BtorPartialParentIterator
{
  BtorNode *cur;
};

typedef struct BtorPartialParentIterator BtorPartialParentIterator;

struct BtorFullParentIterator
{
  BtorNode *cur;
  BtorNode *exp;
  int regular_parents_done;
};

typedef struct BtorFullParentIterator BtorFullParentIterator;

/*------------------------------------------------------------------------*/

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_NEXT_AEQ_ACOND_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_aeq_acond_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_PREV_AEQ_ACOND_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_aeq_acond_parent[BTOR_GET_TAG_NODE (exp)])

void init_read_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_write_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_aeq_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_acond_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_full_parent_iterator (BtorFullParentIterator *, BtorNode *);

BtorNode *next_parent_read_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_write_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_aeq_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_acond_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_full_parent_iterator (BtorFullParentIterator *);

int has_next_parent_read_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_write_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_aeq_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_acond_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_full_parent_iterator (BtorFullParentIterator *);

#endif
