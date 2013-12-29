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

#include "btorcore.h"
#include "btorhash.h"

/*------------------------------------------------------------------------*/

struct BtorFullParentIterator
{
  BtorNode *cur;
  BtorNode *exp;
  int regular_parents_done;
};

typedef struct BtorFullParentIterator BtorFullParentIterator;

struct BtorArgsIterator
{
  int pos;
  BtorNode *cur;
  BtorNode *exp;
};

typedef struct BtorArgsIterator BtorArgsIterator;

struct BtorParameterizedIterator
{
  BtorNode *cur;
  BtorPtrHashBucket *bucket;
  int num_params;
};

typedef struct BtorParameterizedIterator BtorParameterizedIterator;

struct BtorIterator
{
  BtorNode *cur;
};

typedef struct BtorIterator BtorIterator;
typedef struct BtorIterator BtorPartialParentIterator;

#define BTOR_HASH_TABLE_ITERATOR_STACK_SIZE 8

struct BtorHashTableIterator
{
  BtorPtrHashBucket *bucket;
  void *cur;
  char reversed;
  int num_queued;
  int pos;
  BtorPtrHashTable *stack[BTOR_HASH_TABLE_ITERATOR_STACK_SIZE];
};

typedef struct BtorHashTableIterator BtorHashTableIterator;

/*------------------------------------------------------------------------*/

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_NEXT_AEQ_ACOND_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_aeq_acond_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_PREV_AEQ_ACOND_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_aeq_acond_parent[BTOR_GET_TAG_NODE (exp)])

void init_apply_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_aeq_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_acond_parent_iterator (BtorPartialParentIterator *, BtorNode *);
void init_full_parent_iterator (BtorFullParentIterator *, BtorNode *);

BtorNode *next_parent_apply_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_aeq_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_acond_parent_iterator (BtorPartialParentIterator *);
BtorNode *next_parent_full_parent_iterator (BtorFullParentIterator *);

int has_next_parent_apply_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_aeq_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_acond_parent_iterator (BtorPartialParentIterator *);
int has_next_parent_full_parent_iterator (BtorFullParentIterator *);

void init_args_iterator (BtorArgsIterator *, BtorNode *);
BtorNode *next_args_iterator (BtorArgsIterator *);
int has_next_args_iterator (BtorArgsIterator *);

void init_lambda_iterator (BtorIterator *, BtorNode *);
BtorNode *next_lambda_iterator (BtorIterator *);
int has_next_lambda_iterator (BtorIterator *);

void init_parameterized_iterator (Btor *,
                                  BtorParameterizedIterator *,
                                  BtorNode *);
BtorNode *next_parameterized_iterator (BtorParameterizedIterator *);
int has_next_parameterized_iterator (BtorParameterizedIterator *);

void init_node_hash_table_iterator (Btor *,
                                    BtorHashTableIterator *,
                                    BtorPtrHashTable *);
void init_reversed_node_hash_table_iterator (Btor *,
                                             BtorHashTableIterator *,
                                             BtorPtrHashTable *);
BtorNode *next_node_hash_table_iterator (BtorHashTableIterator *);
int has_next_node_hash_table_iterator (BtorHashTableIterator *);
void queue_node_hash_table_iterator (BtorHashTableIterator *,
                                     BtorPtrHashTable *);

#endif
