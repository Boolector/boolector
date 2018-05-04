/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
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
#include "btorsat.h"

void btor_chkclone (Btor *btor, Btor *clone);

void btor_chkclone_exp (Btor *btor,
                        Btor *clone,
                        const BtorNode *exp,
                        const BtorNode *cexp);

void btor_chkclone_sort (Btor *btor,
                         Btor *clone,
                         const BtorSort *sort,
                         const BtorSort *cexp);

#define BTOR_CHKCLONE_NORES(fun, args...)  \
  do                                       \
  {                                        \
    if (!btor->clone) break;               \
    boolector_##fun (btor->clone, ##args); \
    btor_chkclone (btor, btor->clone);     \
  } while (0)

#define BTOR_CHKCLONE_RES_INT(res, fun, args...)              \
  do                                                          \
  {                                                           \
    if (!btor->clone) break;                                  \
    int32_t cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                          \
    assert (cloneres == res);                                 \
    btor_chkclone (btor, btor->clone);                        \
  } while (0)

#define BTOR_CHKCLONE_RES_UINT(res, fun, args...)              \
  do                                                           \
  {                                                            \
    if (!btor->clone) break;                                   \
    uint32_t cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                           \
    assert (cloneres == res);                                  \
    btor_chkclone (btor, btor->clone);                         \
  } while (0)

#define BTOR_CHKCLONE_RES_BOOL(res, fun, args...)          \
  do                                                       \
  {                                                        \
    if (!btor->clone) break;                               \
    bool cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                       \
    assert (cloneres == res);                              \
    btor_chkclone (btor, btor->clone);                     \
  } while (0)

#define BTOR_CHKCLONE_RES_PTR(res, fun, args...)                            \
  do                                                                        \
  {                                                                         \
    if (!btor->clone) break;                                                \
    BtorNode *cloneres =                                                    \
        BTOR_IMPORT_BOOLECTOR_NODE (boolector_##fun (btor->clone, ##args)); \
    (void) cloneres;                                                        \
    btor_chkclone_exp (btor, btor->clone, res, cloneres);                   \
    btor_chkclone (btor, btor->clone);                                      \
  } while (0)

#define BTOR_CHKCLONE_RES_STR(res, fun, args...)                  \
  do                                                              \
  {                                                               \
    if (!btor->clone) break;                                      \
    const char *cloneres = boolector_##fun (btor->clone, ##args); \
    (void) cloneres;                                              \
    if (!res)                                                     \
      assert (!cloneres);                                         \
    else                                                          \
      assert (!strcmp (cloneres, res));                           \
    btor_chkclone (btor, btor->clone);                            \
  } while (0)

#define BTOR_CHKCLONE_RES_SORT(res, fun, args...)                           \
  do                                                                        \
  {                                                                         \
    if (!btor->clone) break;                                                \
    const BtorSortId cloneres =                                             \
        BTOR_IMPORT_BOOLECTOR_SORT (boolector_##fun (btor->clone, ##args)); \
    const BtorSort *s0, *s1;                                                \
    s0 = btor_sort_get_by_id (btor, res);                                   \
    s1 = btor_sort_get_by_id (btor->clone, cloneres);                       \
    btor_chkclone_sort (btor, btor->clone, s0, s1);                         \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
