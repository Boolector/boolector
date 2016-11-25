/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2015 Armin Biere.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSORT_H_INCLUDED
#define BTORSORT_H_INCLUDED

#include "btortypes.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

#include <stdbool.h>
#include <stdint.h>

typedef uint32_t BtorSortId;
// typedef struct btorsortanon btorsortanon; // debug
// typedef btorsortanon* BtorSortId;

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
  uint32_t width;
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
  bool is_array;
  uint32_t arity;
  BtorSort *domain;
  BtorSort *codomain;
};

struct BtorTupleSort
{
  uint32_t num_elements;
  BtorSort **elements;
};

typedef struct BtorSortUniqueTable BtorSortUniqueTable;

struct BtorSort
{
  BtorSortKind kind;  // what kind of sort
  BtorSortId id;      // fixed id
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
  uint32_t size;
  uint32_t num_elements;
  BtorSort **chains;
  BtorMemMgr *mm;
  BtorSortPtrStack id2sort;
};

BtorSortId btor_bool_sort (Btor *btor);

BtorSortId btor_bitvec_sort (Btor *btor, uint32_t width);

BtorSortId btor_array_sort (Btor *btor,
                            BtorSortId index_id,
                            BtorSortId element_id);

BtorSortId btor_lst_sort (Btor *btor, BtorSortId head_id, BtorSortId tail_id);

BtorSortId btor_fun_sort (Btor *btor,
                          BtorSortId domain_id,
                          BtorSortId codomain_id);

BtorSortId btor_tuple_sort (Btor *btor,
                            BtorSortId *element_ids,
                            size_t num_elements);

BtorSortId btor_copy_sort (Btor *btor, BtorSortId id);

void btor_release_sort (Btor *btor, BtorSortId id);

BtorSort *btor_get_sort_by_id (Btor *btor, BtorSortId id);

uint32_t btor_get_width_bitvec_sort (Btor *btor, BtorSortId id);

uint32_t btor_get_arity_fun_sort (Btor *btor, BtorSortId id);
uint32_t btor_get_arity_tuple_sort (Btor *btor, BtorSortId id);

BtorSortId btor_get_codomain_fun_sort (Btor *btor, BtorSortId id);
BtorSortId btor_get_domain_fun_sort (Btor *btor, BtorSortId id);

BtorSortId btor_get_index_array_sort (Btor *btor, BtorSortId id);
BtorSortId btor_get_element_array_sort (Btor *btor, BtorSortId id);

bool btor_is_valid_sort (Btor *btor, BtorSortId id);

bool btor_is_bool_sort (Btor *btor, BtorSortId id);

bool btor_is_bitvec_sort (Btor *btor, BtorSortId id);

bool btor_is_array_sort (Btor *btor, BtorSortId id);

bool btor_is_tuple_sort (Btor *btor, BtorSortId id);

bool btor_is_fun_sort (Btor *btor, BtorSortId id);

struct BtorTupleSortIterator
{
  size_t pos;
  BtorSort *tuple;
};

typedef struct BtorTupleSortIterator BtorTupleSortIterator;

void btor_init_tuple_sort_iterator (BtorTupleSortIterator *it,
                                    Btor *btor,
                                    BtorSortId id);

bool btor_has_next_tuple_sort_iterator (const BtorTupleSortIterator *it);
BtorSortId btor_next_tuple_sort_iterator (BtorTupleSortIterator *it);

#endif
