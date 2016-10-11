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
#include "utils/btorhashptr2.h"
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

void btor_init_apply_parent_iterator (BtorNodeIterator *it,
                                      const BtorNode *exp);
bool btor_has_next_apply_parent_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_apply_parent_iterator (BtorNodeIterator *it);

void btor_init_parent_iterator (BtorNodeIterator *it, const BtorNode *exp);
bool btor_has_next_parent_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_parent_iterator (BtorNodeIterator *it);

void btor_init_lambda_iterator (BtorNodeIterator *it, BtorNode *exp);
bool btor_has_next_lambda_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_lambda_iterator (BtorNodeIterator *it);

void btor_init_param_iterator (BtorNodeIterator *it, BtorNode *exp);
bool btor_has_next_param_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_param_iterator (BtorNodeIterator *it);

void btor_init_unique_table_iterator (BtorNodeIterator *it, const Btor *exp);
bool btor_has_next_unique_table_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_unique_table_iterator (BtorNodeIterator *it);

/*------------------------------------------------------------------------*/

typedef struct BtorArgsIterator
{
  int pos;
  BtorNode *cur;
  const BtorNode *exp;
} BtorArgsIterator;

void btor_init_args_iterator (BtorArgsIterator *it, const BtorNode *exp);
bool btor_has_next_args_iterator (const BtorArgsIterator *it);
BtorNode *btor_next_args_iterator (BtorArgsIterator *it);

/*------------------------------------------------------------------------*/
/* ptr hash table iterators */
/*------------------------------------------------------------------------*/

#define BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE 8

typedef struct BtorPtrHashTableIterator
{
  BtorPtrHashBucket *bucket;
  void *cur;
  bool reversed;
  uint8_t num_queued;
  uint8_t pos;
  const BtorPtrHashTable *stack[BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE];

  // TODO: this replaces the above as soon as hashptrtable is replaced
  //       with the new implementation
  //  void *cur;
  size_t cur_pos;
  const BtorPtrHashTable2 *cur_table;

  /* queue fields */
  //  bool reversed;
  //  uint8_t num_queued;
  uint8_t queue_pos;
  const BtorPtrHashTable2 *stack2[BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE];
} BtorPtrHashTableIterator;

void btor_init_ptr_hash_table_iterator (BtorPtrHashTableIterator *it,
                                        const BtorPtrHashTable *t);
void btor_init_reversed_ptr_hash_table_iterator (BtorPtrHashTableIterator *it,
                                                 const BtorPtrHashTable *t);
void btor_queue_ptr_hash_table_iterator (BtorPtrHashTableIterator *it,
                                         const BtorPtrHashTable *t);
bool btor_has_next_ptr_hash_table_iterator (const BtorPtrHashTableIterator *it);
void *btor_next_ptr_hash_table_iterator (BtorPtrHashTableIterator *it);
BtorHashTableData *btor_next_data_ptr_hash_table_iterator (
    BtorPtrHashTableIterator *it);

void btor_init_node_ptr_hash_table_iterator (BtorPtrHashTableIterator *it,
                                             const BtorPtrHashTable *t);
void btor_init_reversed_node_ptr_hash_table_iterator (
    BtorPtrHashTableIterator *it, const BtorPtrHashTable *t);
void btor_queue_node_ptr_hash_table_iterator (BtorPtrHashTableIterator *it,
                                              const BtorPtrHashTable *t);
bool btor_has_next_node_ptr_hash_table_iterator (
    const BtorPtrHashTableIterator *it);
BtorNode *btor_next_node_ptr_hash_table_iterator (BtorPtrHashTableIterator *it);
BtorHashTableData *btor_next_data_node_ptr_hash_table_iterator (
    BtorPtrHashTableIterator *it);

struct BtorPtrHashTableIterator2
{
  void *cur;
  size_t cur_pos;
  const BtorPtrHashTable2 *cur_table;

  /* queue fields */
  bool reversed;
  uint8_t num_queued;
  uint8_t queue_pos;
  const BtorPtrHashTable2 *stack[BTOR_PTR_HASH_TABLE_ITERATOR_STACK_SIZE];
};

typedef struct BtorPtrHashTableIterator2 BtorPtrHashTableIterator2;

void btor_init_ptr_hash_table_iterator2 (BtorPtrHashTableIterator *it,
                                         const BtorPtrHashTable2 *t);
void btor_init_reversed_ptr_hash_table_iterator2 (BtorPtrHashTableIterator *it,
                                                  const BtorPtrHashTable2 *t);
void btor_queue_ptr_hash_table_iterator2 (BtorPtrHashTableIterator *it,
                                          const BtorPtrHashTable2 *t);
bool btor_has_next_ptr_hash_table_iterator2 (
    const BtorPtrHashTableIterator *it);
void *btor_next_ptr_hash_table_iterator2 (BtorPtrHashTableIterator *it);
BtorHashTableData *btor_next_data_ptr_hash_table_iterator2 (
    BtorPtrHashTableIterator *it);

void btor_init_node_ptr_hash_table_iterator2 (BtorPtrHashTableIterator *it,
                                              const BtorPtrHashTable2 *t);
void btor_init_reversed_node_ptr_hash_table_iterator2 (
    BtorPtrHashTableIterator *it, const BtorPtrHashTable2 *t);
void btor_queue_node_ptr_hash_table_iterator2 (BtorPtrHashTableIterator *it,
                                               const BtorPtrHashTable2 *t);
bool btor_has_next_node_ptr_hash_table_iterator2 (
    const BtorPtrHashTableIterator *it);
BtorNode *btor_next_node_ptr_hash_table_iterator2 (
    BtorPtrHashTableIterator *it);
BtorHashTableData *btor_next_data_node_ptr_hash_table_iterator2 (
    BtorPtrHashTableIterator *it);

/*------------------------------------------------------------------------*/
/* map iterators						          */
/*------------------------------------------------------------------------*/

typedef struct BtorNodeMapIterator
{
  BtorPtrHashTableIterator it;
} BtorNodeMapIterator;

void btor_init_node_map_iterator (BtorNodeMapIterator *it,
                                  const BtorNodeMap *map);
void btor_init_reversed_node_map_iterator (BtorNodeMapIterator *it,
                                           const BtorNodeMap *map);
void btor_queue_node_map_iterator (BtorNodeMapIterator *it,
                                   const BtorNodeMap *map);
bool btor_has_next_node_map_iterator (const BtorNodeMapIterator *it);
BtorNode *btor_next_node_map_iterator (BtorNodeMapIterator *it);
BtorHashTableData *btor_next_data_node_map_iterator (BtorNodeMapIterator *it);

/*------------------------------------------------------------------------*/
#endif
