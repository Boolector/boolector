/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORCHKCLONE_H_INCLUDED
#define BTORCHKCLONE_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "btorcore.h"
#include "btoropt.h"

void btor_chkclone (Btor *btor);
void btor_chkclone_exp (BtorNode *exp, BtorNode *clone);
void btor_chkclone_sort (const BtorSort *sort, const BtorSort *clone);

#define BTOR_CHKCLONE_NORES(fun, args...)  \
  do                                       \
  {                                        \
    if (!btor->clone) break;               \
    boolector_##fun (btor->clone, ##args); \
    btor_chkclone (btor);                  \
  } while (0)

#define BTOR_CHKCLONE_RES(res, fun, args...)              \
  do                                                      \
  {                                                       \
    if (!btor->clone) break;                              \
    int cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                      \
    assert (cloneres == res);                             \
    btor_chkclone (btor);                                 \
  } while (0)

#define BTOR_CHKCLONE_RES_PTR(res, fun, args...)                            \
  do                                                                        \
  {                                                                         \
    if (!btor->clone) break;                                                \
    BtorNode *cloneres =                                                    \
        BTOR_IMPORT_BOOLECTOR_NODE (boolector_##fun (btor->clone, ##args)); \
    (void) cloneres;                                                        \
    btor_chkclone_exp (res, cloneres);                                      \
    btor_chkclone (btor);                                                   \
  } while (0)

#define BTOR_CHKCLONE_RES_STR(res, fun, args...)                  \
  do                                                              \
  {                                                               \
    if (!btor->clone) break;                                      \
    const char *cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                              \
    assert (!strcmp (cloneres, res));                             \
    btor_chkclone (btor);                                         \
  } while (0)

#define BTOR_CHKCLONE_RES_SORT(res, fun, args...)                           \
  do                                                                        \
  {                                                                         \
    if (!btor->clone) break;                                                \
    const BtorSortId cloneres =                                             \
        BTOR_IMPORT_BOOLECTOR_SORT (boolector_##fun (btor->clone, ##args)); \
    const BtorSort *s0, *s1;                                                \
    s0 = btor_get_sort_by_id (&btor->sorts_unique_table, res);              \
    s1 = btor_get_sort_by_id (&btor->sorts_unique_table, cloneres);         \
    btor_chkclone_sort (s0, s1);                                            \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
