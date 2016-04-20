/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORITER_H_INCLUDED
#define BTORITER_H_INCLUDED

#include "btorcore.h"
#include "utils/btorhashptr.h"
#include "utils/btornodemap.h"

#include <stdbool.h>

/*------------------------------------------------------------------------*/
/* node iterators                                                         */
/*------------------------------------------------------------------------*/

typedef struct BtorNodeIterator
{
  const Btor *btor; /* required for unique table iterator */
  int pos;          /* required for unique table iterator */
#ifndef NDEBUG
  int num_elements;
#endif
  BtorNode *cur;
} BtorNodeIterator;

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_parent[BTOR_GET_TAG_NODE (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_parent[BTOR_GET_TAG_NODE (exp)])

void btor_init_apply_parent_iterator (BtorNodeIterator *, const BtorNode *);
bool btor_has_next_apply_parent_iterator (BtorNodeIterator *);
BtorNode *btor_next_apply_parent_iterator (BtorNodeIterator *);

void btor_init_parent_iterator (BtorNodeIterator *, const BtorNode *);
bool btor_has_next_parent_iterator (BtorNodeIterator *);
BtorNode *btor_next_parent_iterator (BtorNodeIterator *);

void btor_init_binder_iterator (BtorNodeIterator *, BtorNode *);
bool btor_has_next_binder_iterator (BtorNodeIterator *);
BtorNode *btor_next_binder_iterator (BtorNodeIterator *);

void btor_init_lambda_iterator (BtorNodeIterator *, BtorNode *);
bool btor_has_next_lambda_iterator (BtorNodeIterator *);
BtorNode *btor_next_lambda_iterator (BtorNodeIterator *);

void btor_init_param_iterator (BtorNodeIterator *, BtorNode *);
bool btor_has_next_param_iterator (BtorNodeIterator *);
BtorNode *btor_next_param_iterator (BtorNodeIterator *);

void btor_init_unique_table_iterator (BtorNodeIterator *, const Btor *);
bool btor_has_next_unique_table_iterator (BtorNodeIterator *);
BtorNode *btor_next_unique_table_iterator (BtorNodeIterator *);

/*------------------------------------------------------------------------*/

typedef struct BtorArgsIterator
{
  int pos;
  BtorNode *cur;
  const BtorNode *exp;
} BtorArgsIterator;

void btor_init_args_iterator (BtorArgsIterator *, const BtorNode *);
bool btor_has_next_args_iterator (BtorArgsIterator *);
BtorNode *btor_next_args_iterator (BtorArgsIterator *);

/*------------------------------------------------------------------------*/
/* hash table iterators					                  */
/*------------------------------------------------------------------------*/

#define BTOR_HASH_TABLE_ITERATOR_STACK_SIZE 8

typedef struct BtorHashTableIterator
{
  BtorPtrHashBucket *bucket;
  void *cur;
  bool reversed;
  uint8_t num_queued;
  uint8_t pos;
  const BtorPtrHashTable *stack[BTOR_HASH_TABLE_ITERATOR_STACK_SIZE];
} BtorHashTableIterator;

void btor_init_hash_table_iterator (BtorHashTableIterator *,
                                    const BtorPtrHashTable *);
void btor_init_reversed_hash_table_iterator (BtorHashTableIterator *,
                                             const BtorPtrHashTable *);
void btor_queue_hash_table_iterator (BtorHashTableIterator *,
                                     const BtorPtrHashTable *);
bool btor_has_next_hash_table_iterator (BtorHashTableIterator *);
void *btor_next_hash_table_iterator (BtorHashTableIterator *);
BtorPtrHashData *btor_next_data_hash_table_iterator (BtorHashTableIterator *);

void btor_init_node_hash_table_iterator (BtorHashTableIterator *,
                                         const BtorPtrHashTable *);
void btor_init_reversed_node_hash_table_iterator (BtorHashTableIterator *,
                                                  const BtorPtrHashTable *);
void btor_queue_node_hash_table_iterator (BtorHashTableIterator *,
                                          const BtorPtrHashTable *);
bool btor_has_next_node_hash_table_iterator (BtorHashTableIterator *);
BtorNode *btor_next_node_hash_table_iterator (BtorHashTableIterator *);
BtorPtrHashData *btor_next_data_node_hash_table_iterator (
    BtorHashTableIterator *);

/*------------------------------------------------------------------------*/
/* map iterators						          */
/*------------------------------------------------------------------------*/

typedef struct BtorNodeMapIterator
{
  BtorHashTableIterator it;
} BtorNodeMapIterator;

void btor_init_node_map_iterator (BtorNodeMapIterator *, const BtorNodeMap *);
void btor_init_reversed_node_map_iterator (BtorNodeMapIterator *,
                                           const BtorNodeMap *);
void btor_queue_node_map_iterator (BtorNodeMapIterator *, const BtorNodeMap *);
bool btor_has_next_node_map_iterator (BtorNodeMapIterator *);
BtorNode *btor_next_node_map_iterator (BtorNodeMapIterator *);
BtorPtrHashData *btor_next_data_node_map_iterator (BtorNodeMapIterator *);

/*------------------------------------------------------------------------*/
#endif
