/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSORT_H_INCLUDED
#define BTORSORT_H_INCLUDED

#include "btormem.h"
#include "btorstack.h"

typedef struct BtorNode BtorNode;

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
  int len;
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
  int arity;
  BtorSort *domain;
  BtorSort *codomain;
};

struct BtorTupleSort
{
  int num_elements;
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

struct BtorSortUniqueTable
{
  int size;
  int num_elements;
  BtorSort **chains;
  BtorMemMgr *mm;
  BtorSortPtrStack id2sort;
};

BtorSort *btor_bool_sort (BtorSortUniqueTable *);

BtorSort *btor_bitvec_sort (BtorSortUniqueTable *, int);

BtorSort *btor_array_sort (BtorSortUniqueTable *, BtorSort *, BtorSort *);

BtorSort *btor_lst_sort (BtorSortUniqueTable *, BtorSort *, BtorSort *);

BtorSort *btor_fun_sort (BtorSortUniqueTable *, BtorSort **, int, BtorSort *);

BtorSort *btor_fun_sort_from_fun (BtorSortUniqueTable *table, BtorNode *fun);

BtorSort *btor_tuple_sort (BtorSortUniqueTable *, BtorSort **, int);

BtorSort *btor_copy_sort (BtorSort *);

void btor_release_sort (BtorSortUniqueTable *, BtorSort *);

#define BTOR_IS_BOOL_SORT(sort) ((sort) && (sort->kind == BTOR_BOOL_SORT))

#define BTOR_IS_BITVEC_SORT(sort) ((sort) && (sort->kind == BTOR_BITVEC_SORT))

#define BTOR_IS_ARRAY_SORT(sort) ((sort) && (sort->kind == BTOR_ARRAY_SORT))

#define BTOR_IS_FUN_SORT(sort) ((sort) && (sort->kind == BTOR_FUN_SORT))

#endif
