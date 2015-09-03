/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2015 Armin Biere.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSORT_H_INCLUDED
#define BTORSORT_H_INCLUDED

#include <stdbool.h>
#include "utils/btormem.h"
#include "utils/btorstack.h"

typedef unsigned BtorSortId;

enum BtorSortKind
{
  BTOR_INVALID_SORT = 0,
  BTOR_BOOL_SORT    = 1,
  BTOR_BITVEC_SORT  = 2,
  BTOR_ARRAY_SORT   = 3,
  BTOR_LST_SORT     = 4,
  BTOR_FUN_SORT     = 5,
  BTOR_TUPLE_SORT   = 6
};

typedef enum BtorSortKind BtorSortKind;

typedef struct BtorSort BtorSort;
typedef struct BtorBitVecSort BtorBitVecSort;
typedef struct BtorArraySort BtorArraySort;
typedef struct BtorLstSort BtorLstSort;
typedef struct BtorFunSort BtorFunSort;
typedef struct BtorTupleSort BtorTupleSort;

struct BtorBitVecSort
{
  unsigned width;
};

struct BtorArraySort
{
  BtorSort *index;
  BtorSort *element;
};

struct BtorLstSort
{
  BtorSort *head;
  BtorSort *tail;
};

struct BtorFunSort
{
  unsigned arity;
  BtorSort *domain;
  BtorSort *codomain;
};

struct BtorTupleSort
{
  unsigned num_elements;
  BtorSort **elements;
};

typedef struct BtorSortUniqueTable BtorSortUniqueTable;

struct BtorSort
{
  BtorSortKind kind;  // what kind of sort
  unsigned id;        // fixed id
  int refs;           // reference counter
  int ext_refs;       // reference counter for API references
  BtorSort *next;     // collision chain for unique table
  BtorSortUniqueTable *table;
#ifndef NDEBUG
  int parents;
#endif
  union
  {
    BtorBitVecSort bitvec;
    BtorArraySort array;
    BtorLstSort lst;
    BtorFunSort fun;
    BtorTupleSort tuple;
  };
};

BTOR_DECLARE_STACK (BtorSortPtr, BtorSort *);
BTOR_DECLARE_STACK (BtorSortId, BtorSortId);

struct BtorSortUniqueTable
{
  int size;
  int num_elements;
  BtorSort **chains;
  BtorMemMgr *mm;
  BtorSortPtrStack id2sort;
};

BtorSortId btor_bool_sort (BtorSortUniqueTable *table);

BtorSortId btor_bitvec_sort (BtorSortUniqueTable *table, unsigned width);

BtorSortId btor_array_sort (BtorSortUniqueTable *table,
                            BtorSortId index_id,
                            BtorSortId element_id);

BtorSortId btor_lst_sort (BtorSortUniqueTable *table,
                          BtorSortId head_id,
                          BtorSortId tail_id);

BtorSortId btor_fun_sort (BtorSortUniqueTable *table,
                          BtorSortId domain_id,
                          BtorSortId codomain_id);

BtorSortId btor_tuple_sort (BtorSortUniqueTable *table,
                            BtorSortId *element_ids,
                            size_t num_elements);

BtorSortId btor_copy_sort (BtorSortUniqueTable *table, BtorSortId id);

void btor_release_sort (BtorSortUniqueTable *table, BtorSortId id);

BtorSort *btor_get_sort_by_id (const BtorSortUniqueTable *table, BtorSortId id);

unsigned btor_get_width_bitvec_sort (const BtorSortUniqueTable *table,
                                     BtorSortId id);

unsigned btor_get_arity_tuple_sort (const BtorSortUniqueTable *table,
                                    BtorSortId id);

BtorSortId btor_get_codomain_fun_sort (const BtorSortUniqueTable *table,
                                       BtorSortId id);

BtorSortId btor_get_domain_fun_sort (const BtorSortUniqueTable *table,
                                     BtorSortId id);

unsigned btor_get_arity_fun_sort (const BtorSortUniqueTable *table,
                                  BtorSortId id);

BtorSortId btor_get_index_array_sort (const BtorSortUniqueTable *table,
                                      BtorSortId id);

BtorSortId btor_get_element_array_sort (const BtorSortUniqueTable *table,
                                        BtorSortId id);

bool btor_is_bool_sort (BtorSortUniqueTable *table, BtorSortId id);

bool btor_is_bitvec_sort (BtorSortUniqueTable *table, BtorSortId id);

bool btor_is_array_sort (BtorSortUniqueTable *table, BtorSortId id);

bool btor_is_tuple_sort (BtorSortUniqueTable *table, BtorSortId id);

bool btor_is_fun_sort (BtorSortUniqueTable *table, BtorSortId id);

struct BtorTupleSortIterator
{
  size_t pos;
  BtorSort *tuple;
};

typedef struct BtorTupleSortIterator BtorTupleSortIterator;

void btor_init_tuple_sort_iterator (BtorTupleSortIterator *it,
                                    BtorSortUniqueTable *table,
                                    BtorSortId id);

bool btor_has_next_tuple_sort_iterator (BtorTupleSortIterator *it);
BtorSortId btor_next_tuple_sort_iterator (BtorTupleSortIterator *it);

#endif
