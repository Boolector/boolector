/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2015 Armin Biere.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *  Copyright (C) 2014-2017 Aina Niemetz.
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
  BtorSortKind kind;
  BtorSortId id;
  uint32_t refs;     /* reference counter */
  uint32_t ext_refs; /* reference counter for API references */
  BtorSort *next;    /* collision chain for unique table */
  BtorSortUniqueTable *table;
#ifndef NDEBUG
  Btor *btor;
  uint32_t parents;
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

BtorSortId btor_sort_bool (Btor *btor);

BtorSortId btor_sort_bv (Btor *btor, uint32_t width);

BtorSortId btor_sort_array (Btor *btor,
                            BtorSortId index_id,
                            BtorSortId element_id);

#if 0
BtorSortId btor_sort_lst (Btor * btor,
                          BtorSortId head_id,
                          BtorSortId tail_id);
#endif

BtorSortId btor_sort_fun (Btor *btor,
                          BtorSortId domain_id,
                          BtorSortId codomain_id);

BtorSortId btor_sort_tuple (Btor *btor,
                            BtorSortId *element_ids,
                            size_t num_elements);

BtorSortId btor_sort_copy (Btor *btor, BtorSortId id);

void btor_sort_release (Btor *btor, BtorSortId id);

BtorSort *btor_sort_get_by_id (Btor *btor, BtorSortId id);

uint32_t btor_sort_bv_get_width (Btor *btor, BtorSortId id);

uint32_t btor_sort_fun_get_arity (Btor *btor, BtorSortId id);
uint32_t btor_sort_tuple_get_arity (Btor *btor, BtorSortId id);

BtorSortId btor_sort_fun_get_codomain (Btor *btor, BtorSortId id);
BtorSortId btor_sort_fun_get_domain (Btor *btor, BtorSortId id);

BtorSortId btor_sort_array_get_index (Btor *btor, BtorSortId id);
BtorSortId btor_sort_array_get_element (Btor *btor, BtorSortId id);

bool btor_sort_is_valid (Btor *btor, BtorSortId id);

bool btor_sort_is_bool (Btor *btor, BtorSortId id);

bool btor_sort_is_bv (Btor *btor, BtorSortId id);

bool btor_sort_is_array (Btor *btor, BtorSortId id);

bool btor_sort_is_tuple (Btor *btor, BtorSortId id);

bool btor_sort_is_fun (Btor *btor, BtorSortId id);

struct BtorTupleSortIterator
{
  size_t pos;
  BtorSort *tuple;
};

typedef struct BtorTupleSortIterator BtorTupleSortIterator;

void btor_iter_tuple_sort_init (BtorTupleSortIterator *it,
                                Btor *btor,
                                BtorSortId id);

bool btor_iter_tuple_sort_has_next (const BtorTupleSortIterator *it);
BtorSortId btor_iter_tuple_sort_next (BtorTupleSortIterator *it);

#endif
