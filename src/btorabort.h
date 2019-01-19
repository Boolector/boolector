/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2018 Aina Niemetz
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORABORT_H_INCLUDED
#define BTORABORT_H_INCLUDED

#include "btortypes.h"

#include <stdbool.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/

#define BTOR_WARN(cond, msg...)                                       \
  do                                                                  \
  {                                                                   \
    if (cond) btor_abort_warn (false, __FILE__, __FUNCTION__, ##msg); \
  } while (0)

#define BTOR_WARN_DEPRECATED(msg...)                              \
  do                                                              \
  {                                                               \
    fprintf (stderr,                                              \
             "[%s] function %s is deprecated, use %s instead \n", \
             __FILE__,                                            \
             __FUNCTION__,                                        \
             ##msg);                                              \
    fflush (stderr);                                              \
  } while (0)

/*------------------------------------------------------------------------*/

void btor_abort_fun (const char* msg);

void btor_abort_warn (
    bool abort, const char* filename, const char* fun, const char* fmt, ...);

#define BTOR_ABORT(cond, msg...)                                     \
  do                                                                 \
  {                                                                  \
    if (cond) btor_abort_warn (true, __FILE__, __FUNCTION__, ##msg); \
  } while (0)

#define BTOR_ABORT_ARG_NULL(arg)                              \
  do                                                          \
  {                                                           \
    BTOR_ABORT ((arg) == 0, "'%s' must not be NULL\n", #arg); \
  } while (0)

#define BTOR_ABORT_REFS_NOT_POS(arg)                           \
  do                                                           \
  {                                                            \
    BTOR_ABORT (btor_node_real_addr (arg)->ext_refs < 1,       \
                "reference counter of '%s' must not be < 1\n", \
                #arg);                                         \
  } while (0)

#define BTOR_ABORT_BTOR_MISMATCH(argbtor, argnode)                         \
  do                                                                       \
  {                                                                        \
    BTOR_ABORT (btor_node_real_addr (argnode)->btor != (argbtor),          \
                "argument '%s' belongs to different Boolector instance\n", \
                #argnode);                                                 \
  } while (0)

#define BTOR_ABORT_IS_NOT_BV(arg)                                     \
  do                                                                  \
  {                                                                   \
    BTOR_ABORT (!btor_sort_is_bv (btor, btor_node_get_sort_id (arg)), \
                "'%s' must be a bit-vector\n",                        \
                #arg);                                                \
  } while (0)

#define BTOR_ABORT_IS_NOT_ARRAY(arg)                                         \
  do                                                                         \
  {                                                                          \
    BTOR_ABORT (!btor_node_is_array (arg), "'%s' must be an array\n", #arg); \
  } while (0)

#define BTOR_ABORT_IS_NOT_FUN(arg)                                     \
  do                                                                   \
  {                                                                    \
    BTOR_ABORT (!btor_sort_is_fun (btor, btor_node_get_sort_id (arg)), \
                "'%s' must be a function\n",                           \
                #arg);                                                 \
  } while (0)

#define BTOR_ABORT_SORT_MISMATCH(argbw1, argbw2)                          \
  do                                                                      \
  {                                                                       \
    BTOR_ABORT (                                                          \
        btor_node_get_sort_id (argbw1) != btor_node_get_sort_id (argbw2), \
        "sorts of '%s' and '%s' must match\n",                            \
        #argbw1,                                                          \
        #argbw2);                                                         \
  } while (0)

/*------------------------------------------------------------------------*/

#endif
