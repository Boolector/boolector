/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORASS_H_INCLUDED
#define BTORASS_H_INCLUDED

#include "utils/btormem.h"

/*------------------------------------------------------------------------*/

typedef struct BtorBVAssignment BtorBVAssignment;
typedef struct BtorBVAssignmentList BtorBVAssignmentList;

struct BtorBVAssignment
{
  const char *cloned_assignment; /* needed for shadow clone only */
  BtorBVAssignment *prev;
  BtorBVAssignment *next;
};

struct BtorBVAssignmentList
{
  BtorMemMgr *mm;
  unsigned count;
  BtorBVAssignment *first;
  BtorBVAssignment *last;
};

/* Create new bv assignment list. */
BtorBVAssignmentList *btor_new_bv_assignment_list (BtorMemMgr *);

/* Clone bv assignment list. */
BtorBVAssignmentList *btor_clone_bv_assignment_list (BtorMemMgr *,
                                                     BtorBVAssignmentList *);

/* Delete bv assignment list. */
void btor_delete_bv_assignment_list (BtorBVAssignmentList *, int);

/* Get BtorBVAssignment bucket reference from bv assignment string. */
BtorBVAssignment *btor_get_bv_assignment (const char *);

/* Get bv assignment string from BtorBVAssignment bucket. */
const char *btor_get_bv_assignment_str (BtorBVAssignment *);

/* Create new bv assignment and add it to the list. */
BtorBVAssignment *btor_new_bv_assignment (BtorBVAssignmentList *, char *);

/* Release bv assignment and remove it from the list. */
void btor_release_bv_assignment (BtorBVAssignmentList *, const char *);

/*------------------------------------------------------------------------*/

typedef struct BtorArrayAssignment BtorArrayAssignment;
typedef struct BtorArrayAssignmentList BtorArrayAssignmentList;

struct BtorArrayAssignment
{
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

/* Create new array assignment list. */
BtorArrayAssignmentList *btor_new_array_assignment_list (BtorMemMgr *);

/* Clone array assignment list. */
BtorArrayAssignmentList *btor_clone_array_assignment_list (
    BtorMemMgr *, BtorArrayAssignmentList *);

/* Delete array assignment list. */
void btor_delete_array_assignment_list (BtorArrayAssignmentList *, int);

/* Get BtorArrayAssignment bucket reference from indices reference. */
BtorArrayAssignment *btor_get_array_assignment (const char **,
                                                const char **,
                                                int);

/* Get indices and values references from BtorArrayAssignment bucket. */
void btor_get_array_assignment_indices_values (BtorArrayAssignment *,
                                               char ***,
                                               char ***,
                                               int size);

/* Create new array assignment and add it to the list. */
BtorArrayAssignment *btor_new_array_assignment (BtorArrayAssignmentList *,
                                                char **,
                                                char **,
                                                int);

/* Release array assignment and remove it from the list. */
void btor_release_array_assignment (BtorArrayAssignmentList *,
                                    char **,
                                    char **,
                                    int);

#endif
