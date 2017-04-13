/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorass.h"

#include <assert.h>
#include <stdbool.h>

/*------------------------------------------------------------------------*/

BtorBVAssList *
btor_new_bv_assignment_list (BtorMemMgr *mm)
{
  assert (mm);

  BtorBVAssList *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BtorBVAssList *
btor_clone_bv_assignment_list (BtorMemMgr *mm, BtorBVAssList *list)
{
  assert (mm);
  assert (list);

  BtorBVAssList *res;
  BtorBVAss *bvass;

  res = btor_new_bv_assignment_list (mm);
  for (bvass = list->first; bvass; bvass = bvass->next)
    (void) btor_new_bv_assignment (res,
                                   (char *) btor_get_bv_assignment_str (bvass));

  return res;
}

void
btor_delete_bv_assignment_list (BtorBVAssList *list, bool auto_cleanup)
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
      btor_release_bv_assignment (list,
                                  (char *) btor_get_bv_assignment_str (tmp));
    }
  }
  BTOR_DELETE (list->mm, list);
}

BtorBVAss *
btor_get_bv_assignment (const char *ass)
{
  assert (ass);
  return (BtorBVAss *) (ass - sizeof (BtorBVAss));
}

const char *
btor_get_bv_assignment_str (BtorBVAss *ass)
{
  return (const char *) ((char *) ass + sizeof (BtorBVAss));
}

BtorBVAss *
btor_new_bv_assignment (BtorBVAssList *list, char *ass)
{
  assert (list);
  assert (ass);

  BtorBVAss *res;
  int len;

  len = strlen (ass) + 1;
  res = btor_calloc (list->mm, sizeof (BtorBVAss) + len, sizeof (char));
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
btor_release_bv_assignment (BtorBVAssList *list, const char *ass)
{
  assert (list);
  assert (ass);

  BtorBVAss *bvass;

  assert (list->count);
  list->count -= 1;

  bvass = btor_get_bv_assignment (ass);
  assert (btor_find_bv_assignment_dbg (list, bvass));

  if (bvass->prev)
    bvass->prev->next = bvass->next;
  else
    list->first = bvass->next;

  if (bvass->next)
    bvass->next->prev = bvass->prev;
  else
    list->last = bvass->prev;
  btor_free (list->mm, bvass, sizeof (BtorBVAss) + strlen (ass) + 1);
}

/*------------------------------------------------------------------------*/

BtorFunAssList *
btor_new_array_assignment_list (BtorMemMgr *mm)
{
  assert (mm);

  BtorFunAssList *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BtorFunAssList *
btor_clone_array_assignment_list (BtorMemMgr *mm, BtorFunAssList *list)
{
  assert (mm);
  assert (list);

  BtorFunAssList *res;
  BtorFunAss *funass;
  char **ind, **val, **cind, **cval;

  res = btor_new_array_assignment_list (mm);
  for (funass = list->first; funass; funass = funass->next)
  {
    btor_get_array_assignment_indices_values (funass, &ind, &val, funass->size);
    btor_get_array_assignment_indices_values (
        btor_new_array_assignment (res, ind, val, funass->size),
        &cind,
        &cval,
        funass->size);
    funass->cloned_indices = cind;
    funass->cloned_values  = cval;
  }

  return res;
}

void
btor_delete_array_assignment_list (BtorFunAssList *list, int auto_cleanup)
{
  assert (list);

  BtorFunAss *funass;
  char **ind, **val;

  assert (auto_cleanup || list->count == 0);

  for (funass = list->first; auto_cleanup && funass; funass = funass->next)
  {
    btor_get_array_assignment_indices_values (funass, &ind, &val, funass->size);
    btor_release_array_assignment (list, ind, val, funass->size);
  }
  BTOR_DELETE (list->mm, list);
}

BtorFunAss *
btor_get_array_assignment (const char **indices, const char **values, int size)
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
btor_get_array_assignment_indices_values (BtorFunAss *ass,
                                          char ***indices,
                                          char ***values,
                                          int size)
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
btor_new_array_assignment (BtorFunAssList *list,
                           char **indices,
                           char **values,
                           int size)
{
  assert (list);
  assert (indices);
  assert (values);

  BtorFunAss *res;
  char **ind, **val;
  int i;

  res       = btor_calloc (list->mm,
                     sizeof (BtorFunAss) + 2 * size * sizeof (char *),
                     sizeof (char));
  res->size = size;
  if (list->first)
    list->last->next = res;
  else
    list->first = res;
  list->last = res;

  btor_get_array_assignment_indices_values (res, &ind, &val, size);
  for (i = 0; i < size; i++)
  {
    ind[i] = btor_strdup (list->mm, indices[i]);
    val[i] = btor_strdup (list->mm, values[i]);
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
btor_release_array_assignment (BtorFunAssList *list,
                               char **indices,
                               char **values,
                               int size)

{
  assert (list);
  assert (indices);
  assert (values);
  assert (size);

  int i;
  BtorFunAss *funass;

  assert (list->count);
  list->count -= 1;

  funass = btor_get_array_assignment (
      (const char **) indices, (const char **) values, size);
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
    btor_freestr (list->mm, indices[i]);
    btor_freestr (list->mm, values[i]);
  }
  btor_free (
      list->mm, funass, sizeof (BtorFunAss) + 2 * size * sizeof (char *));
}
