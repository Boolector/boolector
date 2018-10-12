/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsort.h"

#include "btorabort.h"
#include "btorcore.h"
#include "btornode.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>

#define BTOR_SORT_UNIQUE_TABLE_LIMIT 30

#define BTOR_FULL_SORT_UNIQUE_TABLE(table) \
  ((table)->num_elements >= (table)->size  \
   && btor_util_log_2 ((table)->size) < BTOR_SORT_UNIQUE_TABLE_LIMIT)

static void
inc_sort_ref_counter (BtorSort *sort)
{
  assert (sort);
  BTOR_ABORT (sort->refs == INT32_MAX, "Sort reference counter overflow");
  sort->refs++;
}

static uint32_t
compute_hash_sort (const BtorSort *sort, uint32_t table_size)
{
  assert (sort);
  assert (table_size);
  assert (btor_util_is_power_of_2 (table_size));

  uint32_t i, res, tmp;

  tmp = 0;

  switch (sort->kind)
  {
    default:
#if 0
      case BTOR_BOOL_SORT:
	assert (sort->kind == BTOR_BOOL_SORT);
        res = 0;
	break;
#endif
    case BTOR_BITVEC_SORT: res = sort->bitvec.width; break;
#if 0
      case BTOR_ARRAY_SORT:
        res = sort->array.index->id;
        tmp = sort->array.element->id;
	break;

      case BTOR_LST_SORT:
        res = sort->lst.head->id;
        tmp = sort->lst.tail->id;
        break;
#endif
    case BTOR_FUN_SORT:
      res = sort->fun.domain->id;
      tmp = sort->fun.codomain->id;
      break;

    case BTOR_TUPLE_SORT:
      res = 0;
      for (i = 0; i < sort->tuple.num_elements; i++)
      {
        if ((i & 1) == 0)
          res += sort->tuple.elements[i]->id;
        else
          tmp += sort->tuple.elements[i]->id;
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

  uint32_t hash;
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

static int32_t
equal_sort (const BtorSort *a, const BtorSort *b)
{
  assert (a);
  assert (b);

  uint32_t i;

  if (a->kind != b->kind) return 0;

  switch (a->kind)
  {
    default:
#if 0
      case BTOR_BOOL_SORT:
      default:
        assert (a->kind == BTOR_BOOL_SORT);
        break;
#endif
    case BTOR_BITVEC_SORT:
      if (a->bitvec.width != b->bitvec.width) return 0;
      break;
#if 0
      case BTOR_ARRAY_SORT:
        if (a->array.index->id != b->array.index->id) return 0;
        if (a->array.element->id != b->array.element->id) return 0;
        break;

      case BTOR_LST_SORT:
        if (a->lst.head->id != b->lst.head->id) return 0;
        if (a->lst.tail->id != b->lst.tail->id) return 0;
        break;
#endif
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
find_sort (BtorSortUniqueTable *table, const BtorSort *pattern)
{
  assert (table);
  assert (pattern);

  BtorSort **res, *sort;
  uint32_t hash;
  hash = compute_hash_sort (pattern, table->size);
  assert (hash < (uint32_t) table->size);
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
  uint32_t size, new_size, i, hash;
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

  uint32_t i;

  if (--sort->refs > 0) return;

  remove_from_sorts_unique_table_sort (table, sort);

  switch (sort->kind)
  {
    default: break;
#if 0
      case BTOR_LST_SORT:
#ifndef NDEBUG
	sort->lst.head->parents--;
	sort->lst.tail->parents--;
#endif
        release_sort (table, sort->lst.head);
        release_sort (table, sort->lst.tail);
        break;

      case BTOR_ARRAY_SORT:
#ifndef NDEBUG
	sort->array.index->parents--;
	sort->array.element->parents--;
#endif
        release_sort (table, sort->array.index);
        release_sort (table, sort->array.element);
        break;
#endif
    case BTOR_FUN_SORT:
#ifndef NDEBUG
      sort->fun.domain->parents--;
      sort->fun.codomain->parents--;
#endif
      release_sort (table, sort->fun.domain);
      release_sort (table, sort->fun.codomain);
      break;

    case BTOR_TUPLE_SORT:
      for (i = 0; i < sort->tuple.num_elements; i++)
      {
#ifndef NDEBUG
        sort->tuple.elements[i]->parents--;
#endif
        release_sort (table, sort->tuple.elements[i]);
      }
      BTOR_DELETEN (table->mm, sort->tuple.elements, sort->tuple.num_elements);
      break;
  }

  assert (BTOR_PEEK_STACK (table->id2sort, sort->id) == sort);
  BTOR_POKE_STACK (table->id2sort, sort->id, 0);
  BTOR_DELETE (table->mm, sort);
}

BtorSort *
btor_sort_get_by_id (Btor *btor, BtorSortId id)
{
  assert (btor);
  assert (id < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort));
  return BTOR_PEEK_STACK (btor->sorts_unique_table.id2sort, id);
}

BtorSortId
btor_sort_copy (Btor *btor, BtorSortId id)
{
  assert (btor);
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  inc_sort_ref_counter (sort);
  return id;
}

void
btor_sort_release (Btor *btor, BtorSortId id)
{
  assert (btor);

  BtorSort *sort;

  sort = btor_sort_get_by_id (btor, id);
  assert (sort);
  assert (sort->refs > 0);
  release_sort (&btor->sorts_unique_table, sort);
}

static BtorSort *
copy_sort (BtorSort *sort)
{
  inc_sort_ref_counter (sort);
  return sort;
}

static BtorSort *
create_sort (Btor *btor, BtorSortUniqueTable *table, BtorSort *pattern)
{
  assert (table);
  assert (pattern);

  uint32_t i;
  BtorSort *res;

  BTOR_CNEW (table->mm, res);

#ifndef NDEBUG
  res->btor = btor;
#else
  (void) btor;
#endif

  switch (pattern->kind)
  {
#if 0
      case BTOR_BOOL_SORT:
	res->kind = BTOR_BOOL_SORT;
	break;
#endif
    case BTOR_BITVEC_SORT:
      res->kind         = BTOR_BITVEC_SORT;
      res->bitvec.width = pattern->bitvec.width;
      break;
#if 0
      case BTOR_ARRAY_SORT:
	res->kind = BTOR_ARRAY_SORT;
	res->array.index = copy_sort (pattern->array.index);
	res->array.element = copy_sort (pattern->array.element);
#ifndef NDEBUG
	res->array.index->parents++;
	res->array.element->parents++;
#endif
	break;

      case BTOR_LST_SORT:
	res->kind = BTOR_LST_SORT;
	res->lst.head = copy_sort (pattern->lst.head);
	res->lst.tail = copy_sort (pattern->lst.tail);
#ifndef NDEBUG
	res->lst.head->parents++;
	res->lst.tail->parents++;
#endif
	break;
#endif
    case BTOR_FUN_SORT:
      res->kind         = BTOR_FUN_SORT;
      res->fun.domain   = copy_sort (pattern->fun.domain);
      res->fun.codomain = copy_sort (pattern->fun.codomain);
#ifndef NDEBUG
      res->fun.domain->parents++;
      res->fun.codomain->parents++;
#endif
      break;

    case BTOR_TUPLE_SORT:
      res->kind               = BTOR_TUPLE_SORT;
      res->tuple.num_elements = pattern->tuple.num_elements;
      BTOR_NEWN (table->mm, res->tuple.elements, res->tuple.num_elements);
      for (i = 0; i < res->tuple.num_elements; i++)
      {
        res->tuple.elements[i] = copy_sort (pattern->tuple.elements[i]);
#ifndef NDEBUG
        res->tuple.elements[i]->parents++;
#endif
      }
      break;

    default: break;
  }
  assert (res->kind);
  res->id = BTOR_COUNT_STACK (table->id2sort);
  BTOR_PUSH_STACK (table->id2sort, res);
  assert (BTOR_COUNT_STACK (table->id2sort) == res->id + 1);
  assert (BTOR_PEEK_STACK (table->id2sort, res->id) == res);

  table->num_elements++;
  res->table = table;

  return res;
}

BtorSortId
btor_sort_bool (Btor *btor)
{
  return btor_sort_bv (btor, 1);
}

BtorSortId
btor_sort_bv (Btor *btor, uint32_t width)
{
  assert (btor);
  assert (width > 0);

  BtorSort *res, **pos, pattern;
  BtorSortUniqueTable *table;

  table = &btor->sorts_unique_table;

  BTOR_CLR (&pattern);
  pattern.kind         = BTOR_BITVEC_SORT;
  pattern.bitvec.width = width;
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
    res  = create_sort (btor, table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res->id;
}

BtorSortId
btor_sort_array (Btor *btor, BtorSortId index_id, BtorSortId element_id)
{
  assert (btor);
  assert (index_id < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort));
  assert (element_id < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort));

  BtorSortId tup, res;
  BtorSort *s;

  tup = btor_sort_tuple (btor, &index_id, 1);
  res = btor_sort_fun (btor, tup, element_id);
  btor_sort_release (btor, tup);
  s               = btor_sort_get_by_id (btor, res);
  s->fun.is_array = true;
  return res;
#if 0
  BtorSort * res, ** pos, pattern, *index, *element;
  BtorSortUniqueTable *table;

  table = &btor->sorts_unique_table;

  index = btor_sort_get_by_id (btor, index_id);
  assert (index);
  assert (index->refs > 0);
  assert (index->table == table);
  element = btor_sort_get_by_id (btor, element_id);
  assert (element);
  assert (element->refs > 0);
  assert (element->table == table);

  BTOR_CLR (&pattern);
  pattern.kind = BTOR_ARRAY_SORT;
  pattern.array.index = index;
  pattern.array.element = element;
  pos = find_sort (table, &pattern);
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
      res = create_sort (btor, table, &pattern);
      *pos = res;
    }
  inc_sort_ref_counter (res);
  return res->id;
#endif
}

#if 0
BtorSortId
btor_sort_lst (Btor * btor,
	       BtorSortId head_id,
	       BtorSortId tail_id)
{
  assert (btor);
  assert (head_id < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort));
  assert (tail_id < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort));

  BtorSort * res, ** pos, pattern, *head, *tail;
  BtorSortUniqueTable *table;

  table = &btor->sorts_unique_table;

  head = btor_sort_get_by_id (btor, head_id);
  assert (head);
  assert (head->refs > 0);
  assert (head->table == table);
  tail = btor_sort_get_by_id (btor, tail_id);
  assert (tail);
  assert (tail->refs > 0);
  assert (tail->table == table);

  BTOR_CLR (&pattern);
  pattern.kind = BTOR_LST_SORT;
  pattern.lst.head = head;
  pattern.lst.tail = tail;
  pos = find_sort (table, &pattern);
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
      res = create_sort (btor, table, &pattern);
      *pos = res;
    }
  inc_sort_ref_counter (res);
  return res->id;
}
#endif

BtorSortId
btor_sort_fun (Btor *btor, BtorSortId domain_id, BtorSortId codomain_id)
{
  assert (btor);
  assert (domain_id);

  BtorSort *domain, *codomain, *res, **pos, pattern;
  BtorSortUniqueTable *table;

  table = &btor->sorts_unique_table;

  domain = btor_sort_get_by_id (btor, domain_id);
  assert (domain);
  assert (domain->refs > 0);
  assert (domain->table == table);
  assert (domain->kind == BTOR_TUPLE_SORT);
  codomain = btor_sort_get_by_id (btor, codomain_id);
  assert (codomain);
  assert (codomain->refs > 0);
  assert (codomain->table == table);

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
    res            = create_sort (btor, table, &pattern);
    res->fun.arity = domain->tuple.num_elements;
    *pos           = res;
  }
  inc_sort_ref_counter (res);

  return res->id;
}

BtorSortId
btor_sort_tuple (Btor *btor, BtorSortId *element_ids, size_t num_elements)
{
  assert (btor);
  assert (element_ids);
  assert (num_elements > 0);

  size_t i;
  BtorSort *elements[num_elements], *res, **pos, pattern;
  BtorSortUniqueTable *table;

  table = &btor->sorts_unique_table;

  for (i = 0; i < num_elements; i++)
  {
    elements[i] = btor_sort_get_by_id (btor, element_ids[i]);
    assert (elements[i]);
    assert (elements[i]->table == table);
  }

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
    res  = create_sort (btor, table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter (res);
  return res->id;
}

uint32_t
btor_sort_bv_get_width (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind != BTOR_BOOL_SORT);
#if 0
  /* special case for Boolector as boolean are treated as bv of width 1 */
  if (sort->kind == BTOR_BOOL_SORT)
    return 1;
#endif
  assert (sort->kind == BTOR_BITVEC_SORT);
  return sort->bitvec.width;
}

uint32_t
btor_sort_tuple_get_arity (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind == BTOR_TUPLE_SORT);
  return sort->tuple.num_elements;
}

BtorSortId
btor_sort_fun_get_codomain (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind == BTOR_FUN_SORT);
  return sort->fun.codomain->id;
}

BtorSortId
btor_sort_fun_get_domain (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind == BTOR_FUN_SORT);
  return sort->fun.domain->id;
}

uint32_t
btor_sort_fun_get_arity (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind == BTOR_FUN_SORT);
  assert (sort->fun.domain->kind == BTOR_TUPLE_SORT);
  return sort->fun.domain->tuple.num_elements;
}

BtorSortId
btor_sort_array_get_index (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind != BTOR_ARRAY_SORT);
#if 0
  if (sort->kind == BTOR_ARRAY_SORT)
    return sort->array.index->id;
#endif
  assert (sort->kind == BTOR_FUN_SORT);
  assert (sort->fun.domain->tuple.num_elements == 1);
  return sort->fun.domain->tuple.elements[0]->id;
}

BtorSortId
btor_sort_array_get_element (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort->kind != BTOR_ARRAY_SORT);
#if 0
  if (sort->kind == BTOR_ARRAY_SORT)
    return sort->array.element->id;
#endif
  assert (sort->kind == BTOR_FUN_SORT);
  return sort->fun.codomain->id;
}

bool
btor_sort_is_valid (Btor *btor, BtorSortId id)
{
  return id < BTOR_COUNT_STACK (btor->sorts_unique_table.id2sort)
         && BTOR_PEEK_STACK (btor->sorts_unique_table.id2sort, id) != 0;
}

bool
btor_sort_is_bool (Btor *btor, BtorSortId id)
{
  return btor_sort_is_bv (btor, id) && btor_sort_bv_get_width (btor, id) == 1;
}

bool
btor_sort_is_bv (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort);
  return sort->kind == BTOR_BITVEC_SORT;
}

bool
btor_sort_is_array (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort);
  return btor_sort_is_fun (btor, id) && sort->fun.is_array;
}

bool
btor_sort_is_tuple (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort);
  return sort->kind == BTOR_TUPLE_SORT;
}

bool
btor_sort_is_fun (Btor *btor, BtorSortId id)
{
  BtorSort *sort;
  sort = btor_sort_get_by_id (btor, id);
  assert (sort);
  return sort->kind == BTOR_FUN_SORT;
}

void
btor_iter_tuple_sort_init (BtorTupleSortIterator *it, Btor *btor, BtorSortId id)
{
  assert (it);
  assert (btor);
  assert (btor_sort_is_tuple (btor, id));
  it->pos   = 0;
  it->tuple = btor_sort_get_by_id (btor, id);
}

bool
btor_iter_tuple_sort_has_next (const BtorTupleSortIterator *it)
{
  assert (it);
  return it->pos < it->tuple->tuple.num_elements;
}

BtorSortId
btor_iter_tuple_sort_next (BtorTupleSortIterator *it)
{
  assert (it);
  assert (it->pos < it->tuple->tuple.num_elements);

  BtorSortId result;
  result = it->tuple->tuple.elements[it->pos]->id;
  it->pos += 1;
  return result;
}
