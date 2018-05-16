/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorass.h"

#include <assert.h>
#include <stdbool.h>

/*------------------------------------------------------------------------*/

BtorBVAssList *
btor_ass_new_bv_list (BtorMemMgr *mm)
{
  assert (mm);

  BtorBVAssList *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BtorBVAssList *
btor_ass_clone_bv_list (BtorMemMgr *mm, BtorBVAssList *list)
{
  assert (mm);
  assert (list);

  BtorBVAssList *res;
  BtorBVAss *bvass;

  res = btor_ass_new_bv_list (mm);
  for (bvass = list->first; bvass; bvass = bvass->next)
    (void) btor_ass_new_bv (res, (char *) btor_ass_get_bv_str (bvass));

  return res;
}

void
btor_ass_delete_bv_list (BtorBVAssList *list, bool auto_cleanup)
{
  assert (list);

  BtorBVAss *bvass, *tmp;

  assert (auto_cleanup || list->count == 0);

  if (auto_cleanup)
  {
    bvass = list->first;
    while (bvass)
    {
      tmp   = bvass;
      bvass = bvass->next;
      btor_ass_release_bv (list, (char *) btor_ass_get_bv_str (tmp));
    }
  }
  BTOR_DELETE (list->mm, list);
}

BtorBVAss *
btor_ass_get_bv (const char *ass)
{
  assert (ass);
  return (BtorBVAss *) (ass - sizeof (BtorBVAss));
}

const char *
btor_ass_get_bv_str (BtorBVAss *ass)
{
  return (const char *) ((char *) ass + sizeof (BtorBVAss));
}

BtorBVAss *
btor_ass_new_bv (BtorBVAssList *list, char *ass)
{
  assert (list);
  assert (ass);

  BtorBVAss *res;
  uint32_t len;

  len = strlen (ass) + 1;
  res = btor_mem_calloc (list->mm, sizeof (BtorBVAss) + len, sizeof (char));
  strcpy ((char *) res + sizeof (BtorBVAss), ass);
  res->prev = list->last;
  if (list->first)
    list->last->next = res;
  else
    list->first = res;
  list->last = res;
  list->count += 1;

  return res;
}

bool
btor_find_bv_assignment_dbg (BtorBVAssList *list, BtorBVAss *ass)
{
  assert (list);
  assert (ass);

  bool res;
  BtorBVAss *b;

  for (res = false, b = list->first; b; b = b->next)
    if ((res = (b == ass))) break;
  return res;
}

void
btor_ass_release_bv (BtorBVAssList *list, const char *ass)
{
  assert (list);
  assert (ass);

  BtorBVAss *bvass;

  assert (list->count);
  list->count -= 1;

  bvass = btor_ass_get_bv (ass);
  assert (btor_find_bv_assignment_dbg (list, bvass));

  if (bvass->prev)
    bvass->prev->next = bvass->next;
  else
    list->first = bvass->next;

  if (bvass->next)
    bvass->next->prev = bvass->prev;
  else
    list->last = bvass->prev;
  btor_mem_free (list->mm, bvass, sizeof (BtorBVAss) + strlen (ass) + 1);
}

/*------------------------------------------------------------------------*/

BtorFunAssList *
btor_ass_new_fun_list (BtorMemMgr *mm)
{
  assert (mm);

  BtorFunAssList *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BtorFunAssList *
btor_ass_clone_fun_list (BtorMemMgr *mm, BtorFunAssList *list)
{
  assert (mm);
  assert (list);

  BtorFunAssList *res;
  BtorFunAss *funass;
  char **ind, **val, **cind, **cval;

  res = btor_ass_new_fun_list (mm);
  for (funass = list->first; funass; funass = funass->next)
  {
    btor_ass_get_fun_indices_values (funass, &ind, &val, funass->size);
    btor_ass_get_fun_indices_values (
        btor_ass_new_fun (res, ind, val, funass->size),
        &cind,
        &cval,
        funass->size);
    funass->cloned_indices = cind;
    funass->cloned_values  = cval;
  }

  return res;
}

void
btor_ass_delete_fun_list (BtorFunAssList *list, bool auto_cleanup)
{
  assert (list);

  BtorFunAss *funass, *next;
  char **ind, **val;

  assert (auto_cleanup || list->count == 0);

  if (auto_cleanup)
  {
    for (funass = list->first, next = 0; funass; funass = next)
    {
      next = funass->next;
      btor_ass_get_fun_indices_values (funass, &ind, &val, funass->size);
      btor_ass_release_fun (list, ind, val, funass->size);
    }
  }
  BTOR_DELETE (list->mm, list);
}

BtorFunAss *
btor_ass_get_fun (const char **indices, const char **values, uint32_t size)
{
  assert (indices);
  assert (values);
  (void) values;
  assert (size);
  (void) size;

  BtorFunAss *funass;

  funass = (BtorFunAss *) ((char *) indices - sizeof (BtorFunAss));
  assert (funass->size == size);
  return funass;
}

void
btor_ass_get_fun_indices_values (BtorFunAss *ass,
                                 char ***indices,
                                 char ***values,
                                 uint32_t size)
{
  assert (ass);
  assert (indices);
  assert (values);
  assert (size);
  (void) size;

  assert (size == ass->size);
  *indices = (char **) ((char *) ass + sizeof (BtorFunAss));
  *values  = (char **) ((char *) ass + sizeof (BtorFunAss)
                       + ass->size * sizeof (char *));
}

BtorFunAss *
btor_ass_new_fun (BtorFunAssList *list,
                  char **indices,
                  char **values,
                  uint32_t size)
{
  assert (list);
  assert (indices);
  assert (values);

  BtorFunAss *res;
  char **ind, **val;
  uint32_t i;

  res       = btor_mem_calloc (list->mm,
                         sizeof (BtorFunAss) + 2 * size * sizeof (char *),
                         sizeof (char));
  res->size = size;
  if (list->first)
    list->last->next = res;
  else
    list->first = res;
  list->last = res;

  btor_ass_get_fun_indices_values (res, &ind, &val, size);
  for (i = 0; i < size; i++)
  {
    ind[i] = btor_mem_strdup (list->mm, indices[i]);
    val[i] = btor_mem_strdup (list->mm, values[i]);
  }

  list->count += 1;

  return res;
}

bool
btor_find_array_assignment_dbg (BtorFunAssList *list, BtorFunAss *ass)
{
  assert (list);
  assert (ass);

  bool res;
  BtorFunAss *a;

  for (res = 0, a = list->first; a; a = a->next)
    if ((res = (a == ass))) break;
  return res;
}

void
btor_ass_release_fun (BtorFunAssList *list,
                      char **indices,
                      char **values,
                      uint32_t size)

{
  assert (list);
  assert (indices);
  assert (values);
  assert (size);

  uint32_t i;
  BtorFunAss *funass;

  assert (list->count);
  list->count -= 1;

  funass =
      btor_ass_get_fun ((const char **) indices, (const char **) values, size);
  assert (size == funass->size);
  assert (btor_find_array_assignment_dbg (list, funass));

  if (funass->prev)
    funass->prev->next = funass->next;
  else
    list->first = funass->next;

  if (funass->next)
    funass->next->prev = funass->prev;
  else
    list->last = funass->prev;

  for (i = 0; i < size; i++)
  {
    btor_mem_freestr (list->mm, indices[i]);
    btor_mem_freestr (list->mm, values[i]);
  }
  btor_mem_free (
      list->mm, funass, sizeof (BtorFunAss) + 2 * size * sizeof (char *));
}
