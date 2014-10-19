/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2014 Aina Niemetz.
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
#include "btormap.h"

/*------------------------------------------------------------------------*/
/* node iterators                                                         */
/*------------------------------------------------------------------------*/

typedef struct BtorNodeIterator
{
  BtorNode *cur;
} BtorNodeIterator;

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_parent[BTOR_GET_TAG_NODE (exp)])

void init_apply_parent_iterator (BtorNodeIterator *, BtorNode *);
int has_next_parent_apply_parent_iterator (BtorNodeIterator *);
BtorNode *next_parent_apply_parent_iterator (BtorNodeIterator *);

void init_full_parent_iterator (BtorNodeIterator *, BtorNode *);
int has_next_parent_full_parent_iterator (BtorNodeIterator *);
BtorNode *next_parent_full_parent_iterator (BtorNodeIterator *);

void init_lambda_iterator (BtorNodeIterator *, BtorNode *);
int has_next_lambda_iterator (BtorNodeIterator *);
BtorNode *next_lambda_iterator (BtorNodeIterator *);

/*------------------------------------------------------------------------*/

typedef struct BtorArgsIterator
{
  int pos;
  BtorNode *cur;
  BtorNode *exp;
} BtorArgsIterator;

void init_args_iterator (BtorArgsIterator *, BtorNode *);
int has_next_args_iterator (BtorArgsIterator *);
BtorNode *next_args_iterator (BtorArgsIterator *);

/*------------------------------------------------------------------------*/

typedef struct BtorParameterizedIterator
{
  BtorNode *cur;
  BtorPtrHashBucket *bucket;
  int num_params;
} BtorParameterizedIterator;

void init_parameterized_iterator (Btor *,
                                  BtorParameterizedIterator *,
                                  BtorNode *);
int has_next_parameterized_iterator (BtorParameterizedIterator *);
BtorNode *next_parameterized_iterator (BtorParameterizedIterator *);

/*------------------------------------------------------------------------*/
/* hash table iterators					                  */
/*------------------------------------------------------------------------*/

#define BTOR_HASH_TABLE_ITERATOR_STACK_SIZE 8

typedef struct BtorHashTableIterator
{
  BtorPtrHashBucket *bucket;
  void *cur;
  char reversed;
  int num_queued;
  int pos;
  BtorPtrHashTable *stack[BTOR_HASH_TABLE_ITERATOR_STACK_SIZE];
} BtorHashTableIterator;

void init_hash_table_iterator (BtorHashTableIterator *, BtorPtrHashTable *);
void init_reversed_hash_table_iterator (BtorHashTableIterator *,
                                        BtorPtrHashTable *);
void queue_hash_table_iterator (BtorHashTableIterator *, BtorPtrHashTable *);
int has_next_hash_table_iterator (BtorHashTableIterator *);
void *next_hash_table_iterator (BtorHashTableIterator *);
BtorPtrHashData *next_data_hash_table_iterator (BtorHashTableIterator *);

void init_node_hash_table_iterator (BtorHashTableIterator *,
                                    BtorPtrHashTable *);
void init_reversed_node_hash_table_iterator (BtorHashTableIterator *,
                                             BtorPtrHashTable *);
void queue_node_hash_table_iterator (BtorHashTableIterator *,
                                     BtorPtrHashTable *);
int has_next_node_hash_table_iterator (BtorHashTableIterator *);
BtorNode *next_node_hash_table_iterator (BtorHashTableIterator *);
BtorPtrHashData *next_data_node_hash_table_iterator (BtorHashTableIterator *);

/*------------------------------------------------------------------------*/
/* map iterators						          */
/*------------------------------------------------------------------------*/

typedef struct BtorNodeMapIterator
{
  BtorHashTableIterator it;
} BtorNodeMapIterator;

void init_node_map_iterator (BtorNodeMapIterator *, BtorNodeMap *);
void init_reversed_node_map_iterator (BtorNodeMapIterator *, BtorNodeMap *);
void queue_node_map_iterator (BtorNodeMapIterator *, BtorNodeMap *);
int has_next_node_map_iterator (BtorNodeMapIterator *);
BtorNode *next_node_map_iterator (BtorNodeMapIterator *);
BtorPtrHashData *next_data_node_map_iterator (BtorNodeMapIterator *);

/*------------------------------------------------------------------------*/
#endif
