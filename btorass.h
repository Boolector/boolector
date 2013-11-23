/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORASS_H_INCLUDED
#define BTORASS_H_INCLUDED

#include "btormem.h"

typedef struct BtorBVAssignment BtorBVAssignment;

struct BtorBVAssignment
{
  // TODO shadow clone flag
  const char *cloned_assignment;
  BtorBVAssignment *prev;
  BtorBVAssignment *next;
};

typedef struct BtorArrayAssignment BtorArrayAssignment;

struct BtorBVAssignmentList
{
  BtorMemMgr *mm;
  unsigned count;
  BtorBVAssignment *first;
  BtorBVAssignment *last;
};

typedef struct BtorBVAssignmentList BtorBVAssignmentList;

BtorBVAssignmentList *btor_new_bv_assignment_list (BtorMemMgr *);

BtorBVAssignmentList *btor_clone_bv_assignment_list (BtorMemMgr *,
                                                     BtorBVAssignmentList *);
void btor_delete_bv_assignment_list (BtorBVAssignmentList *);

BtorBVAssignment *btor_get_bv_assignment (const char *);

const char *btor_get_bv_assignment_str (BtorBVAssignment *);

BtorBVAssignment *btor_new_bv_assignment (BtorBVAssignmentList *, char *);

void btor_release_bv_assignment (BtorBVAssignmentList *, char *);

struct BtorArrayAssignment
{
  // TODO shadow clone flag
  char **cloned_indices;
  char **cloned_values;
  int size;
  BtorArrayAssignment *prev;
  BtorArrayAssignment *next;
};

struct BtorArrayAssignmentList
{
  BtorMemMgr *mm;
  unsigned count;
  BtorArrayAssignment *first;
  BtorArrayAssignment *last;
};

typedef struct BtorArrayAssignmentList BtorArrayAssignmentList;

BtorArrayAssignmentList *btor_new_array_assignment_list (BtorMemMgr *);

BtorArrayAssignmentList *btor_clone_array_assignment_list (
    BtorMemMgr *, BtorArrayAssignmentList *);

void btor_delete_array_assignment_list (BtorArrayAssignmentList *);

BtorArrayAssignment *btor_get_array_assignment (const char **,
                                                const char **,
                                                int);

void btor_get_array_assignment_indices_values (BtorArrayAssignment *,
                                               char ***,
                                               char ***,
                                               int size);

BtorArrayAssignment *btor_new_array_assignment (BtorArrayAssignmentList *,
                                                char **,
                                                char **,
                                                int);

void btor_release_array_assignment (BtorArrayAssignmentList *,
                                    char **,
                                    char **,
                                    int);

#endif
