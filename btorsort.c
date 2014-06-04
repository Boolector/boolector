/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsort.h"
#include "btorexit.h"
#include "btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>

#define BTOR_SORT_UNIQUE_TABLE_LIMIT 30

#define BTOR_FULL_SORT_UNIQUE_TABLE(table) \
  ((table)->num_elements >= (table)->size  \
   && btor_log_2_util ((table)->size) < BTOR_SORT_UNIQUE_TABLE_LIMIT)

#define BTOR_ABORT_SORT(cond, msg)                   \
  do                                                 \
  {                                                  \
    if (cond)                                        \
    {                                                \
      printf ("[btorsort] %s: %s\n", __func__, msg); \
      fflush (stdout);                               \
      exit (BTOR_ERR_EXIT);                          \
    }                                                \
  } while (0)

static int
compare_sorts (const void *p1, const void *p2)
{
  BtorSort *a, *b;
  a = *((BtorSort **) p1);
  b = *((BtorSort **) p2);
  return a->id - b->id;
}

static void
inc_sort_ref_counter (BtorSort *sort)
{
  assert (sort);
  BTOR_ABORT_SORT (sort->refs == INT_MAX, "Sort reference counter overflow");
  sort->refs++;
}

static unsigned
compute_hash_sort (BtorSort *sort, int table_size)
{
  assert (sort);
  assert (table_size);
  assert (btor_is_power_of_2_util (table_size));

  int i;
  unsigned res, tmp;

  tmp = 0;

  switch (sort->kind)
  {
    default:
    case BTOR_BOOL_SORT:
      assert (sort->kind == BTOR_BOOL_SORT);
      res = 0;
      break;

    case BTOR_BITVEC_SORT: res = (unsigned int) sort->bitvec.len; break;

    case BTOR_ARRAY_SORT:
      res = (unsigned int) sort->array.index->id;
      tmp = (unsigned int) sort->array.element->id;
      break;

    case BTOR_LST_SORT:
      res = (unsigned int) sort->lst.head->id;
      tmp = (unsigned int) sort->lst.tail->id;
      break;

    case BTOR_FUN_SORT:
      res = (unsigned int) sort->fun.domain->id;
      tmp = (unsigned int) sort->fun.codomain->id;
      break;

    case BTOR_TUPLE_SORT:
      res = 0;
      for (i = 0; i < sort->tuple.num_elements; i++)
      {
        if ((i & 1) == 0)
          res += (unsigned int) sort->tuple.elements[i]->id;
        else
          tmp += (unsigned int) sort->tuple.elements[i]->id;
      }
      break;
  }

  res *= 444555667u;

  if (tmp)
  {
    res += tmp;
    res *= 123123137u;
  }

  res &= table_size - 1;

  return res;
}

static void
remove_from_sorts_unique_table_sort (BtorSortUniqueTable *table, BtorSort *sort)
{
  assert (table);
  assert (sort);
  assert (!sort->refs);
  assert (table->num_elements > 0);

  unsigned int hash;
  BtorSort *prev, *cur;

  hash = compute_hash_sort (sort, table->size);
  prev = 0;
  cur  = table->chains[hash];

  while (cur != sort)
  {
    assert (cur);
    prev = cur;
    cur  = cur->next;
  }

  assert (cur);
  if (!prev)
    table->chains[hash] = cur->next;
  else
    prev->next = cur->next;

  table->num_elements--;
}

static int
equal_sort (const BtorSort *a, const BtorSort *b)
{
  assert (a);
  assert (b);

  int i;

  if (a->kind != b->kind) return 0;

  switch (a->kind)
  {
    case BTOR_BOOL_SORT:
    default: assert (a->kind == BTOR_BOOL_SORT); break;

    case BTOR_BITVEC_SORT:
      if (a->bitvec.len != b->bitvec.len) return 0;
      break;

    case BTOR_ARRAY_SORT:
      if (a->array.index->id != b->array.index->id) return 0;
      if (a->array.element->id != b->array.element->id) return 0;
      break;

    case BTOR_LST_SORT:
      if (a->lst.head->id != b->lst.head->id) return 0;
      if (a->lst.tail->id != b->lst.tail->id) return 0;
      break;

    case BTOR_FUN_SORT:
      if (a->fun.domain->id != b->fun.domain->id) return 0;
      if (a->fun.codomain->id != b->fun.codomain->id) return 0;
      break;

    case BTOR_TUPLE_SORT:
      if (a->tuple.num_elements != b->tuple.num_elements) return 0;
      for (i = 0; i < a->tuple.num_elements; i++)
        if (a->tuple.elements[i]->id != b->tuple.elements[i]->id) return 0;
      break;
  }

  return 1;
}

static BtorSort **
find_sort (BtorSortUniqueTable *table, BtorSort *pattern)
{
  assert (table);
  assert (pattern);

  BtorSort **res, *sort;
  unsigned int hash;
  hash = compute_hash_sort (pattern, table->size);
  assert (hash < (unsigned) table->size);
  for (res = table->chains + hash; (sort = *res) && !equal_sort (sort, pattern);
       res = &sort->next)
    assert (sort->refs > 0);
  return res;
}

static void
enlarge_sorts_unique_table (BtorSortUniqueTable *table)
{
  assert (table);

  BtorSort *cur, *temp, **new_chains;
  int size, new_size, i;
  unsigned int hash;
  BtorMemMgr *mm;

  mm       = table->mm;
  size     = table->size;
  new_size = size << 1;
  assert (new_size / size == 2);
  BTOR_CNEWN (mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = table->chains[i];
    while (cur)
    {
      temp             = cur->next;
      hash             = compute_hash_sort (cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BTOR_DELETEN (mm, table->chains, size);
  table->size   = new_size;
  table->chains = new_chains;
}

static void
release_sort (BtorSortUniqueTable *table, BtorSort *sort)
{
  assert (table);
  assert (sort);
  assert (sort->refs > 0);

  int i;

  if (--sort->refs > 0) return;

  remove_from_sorts_unique_table_sort (table, sort);

  switch (sort->kind)
  {
    default: break;

    case BTOR_LST_SORT:
      release_sort (table, sort->lst.head);
      release_sort (table, sort->lst.tail);
      break;

    case BTOR_ARRAY_SORT:
      release_sort (table, sort->array.index);
      release_sort (table, sort->array.element);
      break;

    case BTOR_FUN_SORT:
      release_sort (table, sort->fun.domain);
      release_sort (table, sort->fun.codomain);
      break;

    case BTOR_TUPLE_SORT:
      for (i = 0; i < sort->tuple.num_elements; i++)
        release_sort (table, sort->tuple.elements[i]);
      BTOR_DELETEN (table->mm, sort->tuple.elements, sort->tuple.num_elements);
      break;
  }

  BTOR_DELETE (table->mm, sort);
}

BtorSort *
btor_copy_sort (BtorSort *sort)
{
  inc_sort_ref_counter (sort);
  return sort;
}

void
btor_release_sort (BtorSortUniqueTable *table, BtorSort *sort)
{
  assert (table);
  assert (sort);
  assert (sort->refs > 0);
  release_sort (table, sort);
}

static BtorSort *
create_sort (BtorSortUniqueTable *table, BtorSort *pattern)
{
  assert (table);
  assert (pattern);

  int i;
  BtorSort *res;

  BTOR_CNEW (table->mm, res);

  switch (pattern->kind)
  {
    case BTOR_BOOL_SORT: res->kind = BTOR_BOOL_SORT; break;

    case BTOR_BITVEC_SORT:
      res->kind       = BTOR_BITVEC_SORT;
      res->bitvec.len = pattern->bitvec.len;
      break;

    case BTOR_ARRAY_SORT:
      res->kind          = BTOR_ARRAY_SORT;
      res->array.index   = pattern->array.index;
      res->array.element = pattern->array.element;
      inc_sort_ref_counter (pattern->array.index);
      inc_sort_ref_counter (pattern->array.element);
      break;

    case BTOR_LST_SORT:
      res->kind     = BTOR_LST_SORT;
      res->lst.head = pattern->lst.head;
      res->lst.tail = pattern->lst.tail;
      inc_sort_ref_counter (pattern->lst.head);
      inc_sort_ref_counter (pattern->lst.tail);
      break;

    case BTOR_FUN_SORT:
      res->kind         = BTOR_FUN_SORT;
      res->fun.domain   = pattern->fun.domain;
      res->fun.codomain = pattern->fun.codomain;
      inc_sort_ref_counter (pattern->fun.domain);
      inc_sort_ref_counter (pattern->fun.codomain);
      break;

    case BTOR_TUPLE_SORT:
      res->kind               = BTOR_TUPLE_SORT;
      res->tuple.num_elements = pattern->tuple.num_elements;
      BTOR_NEWN (table->mm, res->tuple.elements, res->tuple.num_elements);
      for (i = 0; i < res->tuple.num_elements; i++)
        res->tuple.elements[i] = btor_copy_sort (pattern->tuple.elements[i]);
      break;

    default: break;
  }
  assert (res->kind);
  res->id = table->id++;
  table->num_elements++;

  return res;
}

BtorSort *
btor_bool_sort (BtorSortUniqueTable *table)
{
  assert (table);

  BtorSort *res, **pos, pattern;

  BTOR_CLR (&pattern);
  pattern.kind = BTOR_BOOL_SORT;
  pos          = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    if (BTOR_FULL_SORT_UNIQUE_TABLE (table))
    {
      enlarge_sorts_unique_table (table);
      pos = find_sort (table, &pattern);
      assert (pos);
      res = *pos;
      assert (!res);
    }
    res  = create_sort (table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res;
}

BtorSort *
btor_bitvec_sort (BtorSortUniqueTable *table, int len)
{
  assert (table);
  assert (len > 0);

  BtorSort *res, **pos, pattern;

  BTOR_CLR (&pattern);
  pattern.kind       = BTOR_BITVEC_SORT;
  pattern.bitvec.len = len;
  pos                = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    if (BTOR_FULL_SORT_UNIQUE_TABLE (table))
    {
      enlarge_sorts_unique_table (table);
      pos = find_sort (table, &pattern);
      assert (pos);
      res = *pos;
      assert (!res);
    }
    res  = create_sort (table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res;
}

BtorSort *
btor_array_sort (BtorSortUniqueTable *table, BtorSort *index, BtorSort *element)
{
  assert (table);
  assert (index);
  assert (index->refs > 0);
  assert (element);
  assert (element->refs > 0);

  BtorSort *res, **pos, pattern;

  BTOR_CLR (&pattern);
  pattern.kind          = BTOR_ARRAY_SORT;
  pattern.array.index   = index;
  pattern.array.element = element;
  pos                   = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    if (BTOR_FULL_SORT_UNIQUE_TABLE (table))
    {
      enlarge_sorts_unique_table (table);
      pos = find_sort (table, &pattern);
      assert (pos);
      res = *pos;
      assert (!res);
    }
    res  = create_sort (table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res;
}

BtorSort *
btor_lst_sort (BtorSortUniqueTable *table, BtorSort *head, BtorSort *tail)
{
  assert (table);
  assert (head);
  assert (head->refs > 0);
  assert (tail);
  assert (tail->refs > 0);

  BtorSort *res, **pos, pattern;

  BTOR_CLR (&pattern);
  pattern.kind     = BTOR_LST_SORT;
  pattern.lst.head = head;
  pattern.lst.tail = tail;
  pos              = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    if (BTOR_FULL_SORT_UNIQUE_TABLE (table))
    {
      enlarge_sorts_unique_table (table);
      pos = find_sort (table, &pattern);
      assert (pos);
      res = *pos;
      assert (!res);
    }
    res  = create_sort (table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res;
}

BtorSort *
btor_fun_sort (BtorSortUniqueTable *table, BtorSort *domain, BtorSort *codomain)
{
  assert (table);
  assert (domain);
  assert (domain->refs > 0);
  assert (codomain);
  assert (codomain->refs > 0);

  BtorSort *res, **pos, pattern;

  BTOR_CLR (&pattern);
  pattern.kind         = BTOR_FUN_SORT;
  pattern.fun.domain   = domain;
  pattern.fun.codomain = codomain;
  pos                  = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    if (BTOR_FULL_SORT_UNIQUE_TABLE (table))
    {
      enlarge_sorts_unique_table (table);
      pos = find_sort (table, &pattern);
      assert (pos);
      res = *pos;
      assert (!res);
    }
    res  = create_sort (table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res;
}

BtorSort *
btor_tuple_sort (BtorSortUniqueTable *table,
                 BtorSort **elements,
                 int num_elements)
{
  assert (table);
  assert (elements);
  assert (num_elements > 1);

  BtorSort *res, **pos, pattern;

  BTOR_CLR (&pattern);
  pattern.kind               = BTOR_TUPLE_SORT;
  pattern.tuple.num_elements = num_elements;
  pattern.tuple.elements     = elements;
  pos                        = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res)
  {
    if (BTOR_FULL_SORT_UNIQUE_TABLE (table))
    {
      enlarge_sorts_unique_table (table);
      pos = find_sort (table, &pattern);
      assert (pos);
      res = *pos;
      assert (!res);
    }
    res  = create_sort (table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res;
}

void
btor_sorts_list_sort (BtorMemMgr *mm,
                      BtorSortUniqueTable *table,
                      BtorSortPtrStack *sorts)
{
  assert (table);
  assert (sorts);

  int i;
  BtorSort *sort;

  for (i = 0; i < table->size; i++)
  {
    if (!table->chains[i]) continue;
    for (sort = table->chains[i]; sort; sort = sort->next)
      BTOR_PUSH_STACK (mm, *sorts, sort);
  }

  qsort ((*sorts).start,
         BTOR_COUNT_STACK (*sorts),
         sizeof (BtorSort *),
         compare_sorts);
}
