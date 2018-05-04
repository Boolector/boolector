/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORASS_H_INCLUDED
#define BTORASS_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
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
  uint32_t count;
  BtorBVAss *first;
  BtorBVAss *last;
};

/* Create new bv assignment list. */
BtorBVAssList *btor_ass_new_bv_list (BtorMemMgr *mm);

/* Clone bv assignment list. */
BtorBVAssList *btor_ass_clone_bv_list (BtorMemMgr *mm, BtorBVAssList *list);

/* Delete bv assignment list. */
void btor_ass_delete_bv_list (BtorBVAssList *list, bool auto_cleanup);

/* Get BtorBVAss bucket reference from bv assignment string. */
BtorBVAss *btor_ass_get_bv (const char *ass);

/* Get bv assignment string from BtorBVAss bucket. */
const char *btor_ass_get_bv_str (BtorBVAss *ass);

/* Create new bv assignment and add it to the list. */
BtorBVAss *btor_ass_new_bv (BtorBVAssList *list, char *ass);

/* Release bv assignment and remove it from the list. */
void btor_ass_release_bv (BtorBVAssList *list, const char *ass);

/*------------------------------------------------------------------------*/

typedef struct BtorFunAss BtorFunAss;
typedef struct BtorFunAssList BtorFunAssList;

struct BtorFunAss
{
  char **cloned_indices;
  char **cloned_values;
  uint32_t size;
  BtorFunAss *prev;
  BtorFunAss *next;
};

struct BtorFunAssList
{
  BtorMemMgr *mm;
  uint32_t count;
  BtorFunAss *first;
  BtorFunAss *last;
};

/* Create new array assignment list. */
BtorFunAssList *btor_ass_new_fun_list (BtorMemMgr *mm);

/* Clone array assignment list. */
BtorFunAssList *btor_ass_clone_fun_list (BtorMemMgr *mm, BtorFunAssList *list);

/* Delete array assignment list. */
void btor_ass_delete_fun_list (BtorFunAssList *list, bool auto_cleanup);

/* Get BtorFunAss bucket reference from indices reference. */
BtorFunAss *btor_ass_get_fun (const char **indices,
                              const char **values,
                              uint32_t size);

/* Get indices and values references from BtorFunAss bucket. */
void btor_ass_get_fun_indices_values (BtorFunAss *ass,
                                      char ***indices,
                                      char ***values,
                                      uint32_t size);

/* Create new array assignment and add it to the list. */
BtorFunAss *btor_ass_new_fun (BtorFunAssList *list,
                              char **indices,
                              char **values,
                              uint32_t size);

/* Release array assignment and remove it from the list. */
void btor_ass_release_fun (BtorFunAssList *list,
                           char **indices,
                           char **values,
                           uint32_t size);

#endif
