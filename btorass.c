/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorass.h"
#include "assert.h"

BtorBVAssignmentList *
btor_new_bv_assignment_list (BtorMemMgr *mm)
{
  assert (mm);

  BtorBVAssignmentList *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BtorBVAssignmentList *
btor_clone_bv_assignment_list (BtorMemMgr *mm, BtorBVAssignmentList *list)
{
  BtorBVAssignmentList *res;
  BtorBVAssignment *bvass;

  res = btor_new_bv_assignment_list (mm);
  for (bvass = list->first; bvass; bvass = bvass->next)
    bvass->cloned_assignment =
        btor_get_bv_assignment_str (btor_new_bv_assignment (
            res, (char *) btor_get_bv_assignment_str (bvass)));

  return res;
}

void
btor_delete_bv_assignment_list (BtorBVAssignmentList *list)
{
  assert (list);

  BtorBVAssignment *bvass;

  for (bvass = list->first; bvass; bvass = bvass->next)
    btor_release_bv_assignment (list,
                                (char *) btor_get_bv_assignment_str (bvass));
  BTOR_DELETE (list->mm, list);
}

BtorBVAssignment *
btor_get_bv_assignment (const char *ass)
{
  return (BtorBVAssignment *) (ass - sizeof (BtorBVAssignment));
}

const char *
btor_get_bv_assignment_str (BtorBVAssignment *ass)
{
  return (const char *) ((char *) ass + sizeof (BtorBVAssignment));
}

BtorBVAssignment *
btor_new_bv_assignment (BtorBVAssignmentList *list, char *ass)
{
  assert (list);
  assert (ass);

  BtorBVAssignment *res;
  int len;

  len = strlen (ass) + 1;
  res = btor_calloc (list->mm, sizeof (BtorBVAssignment) + len, sizeof (char));
  strcpy ((char *) res + sizeof (BtorBVAssignment), ass);
  res->prev = list->last;
  if (list->first)
    list->last->next = res;
  else
    list->first = res;
  list->last = res;
  list->count += 1;

  return res;
}

void
btor_release_bv_assignment (BtorBVAssignmentList *list, const char *ass)
{
  assert (list);
  assert (ass);

  BtorBVAssignment *bvass;

  bvass = btor_get_bv_assignment (ass);

  if (bvass->prev)
    bvass->prev->next = bvass->next;
  else
    list->first = bvass->next;

  if (bvass->next)
    bvass->next->prev = bvass->prev;
  else
    list->last = bvass->prev;

  btor_free (list->mm, bvass, sizeof (BtorBVAssignment) + strlen (ass) + 1);
}

BtorArrayAssignmentList *
btor_new_array_assignment_list (BtorMemMgr *mm)
{
  assert (mm);

  BtorArrayAssignmentList *res;

  BTOR_CNEW (mm, res);
  res->mm   = mm;
  res->last = res->first;
  res->count += 1;
  return res;
}

BtorArrayAssignmentList *
btor_clone_array_assignment_list (BtorMemMgr *mm, BtorArrayAssignmentList *list)
{
  BtorArrayAssignmentList *res;
  BtorArrayAssignment *arrass;
  char **ind, **val, **cind, **cval;

  res = btor_new_array_assignment_list (mm);
  for (arrass = list->first; arrass; arrass = arrass->next)
  {
    btor_get_array_assignment_indices_values (arrass, &ind, &val, arrass->size);
    btor_get_array_assignment_indices_values (
        btor_new_array_assignment (res, ind, val, arrass->size),
        &cind,
        &cval,
        arrass->size);
    arrass->cloned_indices = cind;
    arrass->cloned_values  = cval;
  }

  return res;
}

void
btor_delete_array_assignment_list (BtorArrayAssignmentList *list)
{
  assert (list);

  BtorArrayAssignment *arrass;
  char **ind, **val;

  for (arrass = list->first; arrass; arrass = arrass->next)
  {
    btor_get_array_assignment_indices_values (arrass, &ind, &val, arrass->size);
    btor_release_array_assignment (list, ind, val, arrass->size);
  }
  BTOR_DELETE (list->mm, list);
}

BtorArrayAssignment *
btor_get_array_assignment (const char **indices, const char **values, int size)
{
  assert (indices);
  assert (values);
  assert (size);

  BtorArrayAssignment *arrass;

  arrass =
      (BtorArrayAssignment *) ((char *) indices - sizeof (BtorArrayAssignment));
  assert (arrass->size == size);
  (void) size;
  return arrass;
}

void
btor_get_array_assignment_indices_values (BtorArrayAssignment *ass,
                                          char ***indices,
                                          char ***values,
                                          int size)
{
  assert (size == ass->size);
  *indices = (char **) ((char *) ass + sizeof (BtorArrayAssignment));
  *values  = (char **) ((char *) ass + sizeof (BtorArrayAssignment)
                       + ass->size * sizeof (char *));
}

BtorArrayAssignment *
btor_new_array_assignment (BtorArrayAssignmentList *list,
                           char **indices,
                           char **values,
                           int size)
{
  assert (list);
  assert (indices);
  assert (values);

  BtorArrayAssignment *res;
  char **ind, **val;
  int i;

  res       = btor_calloc (list->mm,
                     sizeof (BtorArrayAssignment) + 2 * size * sizeof (char *),
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

void
btor_release_array_assignment (BtorArrayAssignmentList *list,
                               char **indices,
                               char **values,
                               int size)

{
  assert (list);
  assert (indices);
  assert (values);
  assert (size);

  int i;
  BtorArrayAssignment *arrass;

  arrass = btor_get_array_assignment (
      (const char **) indices, (const char **) values, size);
  assert (size == arrass->size);

  if (arrass->prev)
    arrass->prev->next = arrass->next;
  else
    list->first = arrass->next;

  if (arrass->next)
    arrass->next->prev = arrass->prev;
  else
    list->last = arrass->prev;

  for (i = 0; i < size; i++)
  {
    btor_freestr (list->mm, indices[i]);
    btor_freestr (list->mm, values[i]);
  }

  btor_free (list->mm,
             arrass,
             sizeof (BtorArrayAssignment) + 2 * size * sizeof (char *));
}
