/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORASS_H_INCLUDED
#define BTORASS_H_INCLUDED

#include <stdbool.h>
#include "utils/btormem.h"

/*------------------------------------------------------------------------*/

typedef struct BtorBVAss BtorBVAss;
typedef struct BtorBVAssList BtorBVAssList;

struct BtorBVAss
{
#ifndef NDEBUG
  const char *cloned_assignment; /* needed for shadow clone only */
#endif
  BtorBVAss *prev;
  BtorBVAss *next;
};

struct BtorBVAssList
{
  BtorMemMgr *mm;
  unsigned count;
  BtorBVAss *first;
  BtorBVAss *last;
};

/* Create new bv assignment list. */
BtorBVAssList *btor_new_bv_assignment_list (BtorMemMgr *mm);

/* Clone bv assignment list. */
BtorBVAssList *btor_clone_bv_assignment_list (BtorMemMgr *mm,
                                              BtorBVAssList *list);

/* Delete bv assignment list. */
void btor_delete_bv_assignment_list (BtorBVAssList *list, bool auto_cleanup);

/* Get BtorBVAss bucket reference from bv assignment string. */
BtorBVAss *btor_get_bv_assignment (const char *ass);

/* Get bv assignment string from BtorBVAss bucket. */
const char *btor_get_bv_assignment_str (BtorBVAss *ass);

/* Create new bv assignment and add it to the list. */
BtorBVAss *btor_new_bv_assignment (BtorBVAssList *list, char *ass);

/* Release bv assignment and remove it from the list. */
void btor_release_bv_assignment (BtorBVAssList *list, const char *ass);

/*------------------------------------------------------------------------*/

typedef struct BtorFunAss BtorFunAss;
typedef struct BtorFunAssList BtorFunAssList;

struct BtorFunAss
{
  char **cloned_indices;
  char **cloned_values;
  int size;
  BtorFunAss *prev;
  BtorFunAss *next;
};

struct BtorFunAssList
{
  BtorMemMgr *mm;
  unsigned count;
  BtorFunAss *first;
  BtorFunAss *last;
};

/* Create new array assignment list. */
BtorFunAssList *btor_new_array_assignment_list (BtorMemMgr *);

/* Clone array assignment list. */
BtorFunAssList *btor_clone_array_assignment_list (BtorMemMgr *,
                                                  BtorFunAssList *);

/* Delete array assignment list. */
void btor_delete_array_assignment_list (BtorFunAssList *, int);

/* Get BtorFunAss bucket reference from indices reference. */
BtorFunAss *btor_get_array_assignment (const char **, const char **, int);

/* Get indices and values references from BtorFunAss bucket. */
void btor_get_array_assignment_indices_values (BtorFunAss *,
                                               char ***,
                                               char ***,
                                               int size);

/* Create new array assignment and add it to the list. */
BtorFunAss *btor_new_array_assignment (BtorFunAssList *, char **, char **, int);

/* Release array assignment and remove it from the list. */
void btor_release_array_assignment (BtorFunAssList *, char **, char **, int);

#endif
