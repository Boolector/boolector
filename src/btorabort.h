/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORABORT_H_INCLUDED
#define BTORABORT_H_INCLUDED

#include "btortypes.h"

#include <stdlib.h>

/*------------------------------------------------------------------------*/

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

void btor_abort (const char* filename, const char* fun, const char* fmt, ...);

#define BTOR_ABORT(cond, msg...)                          \
  do                                                      \
  {                                                       \
    if (cond) btor_abort (__FILE__, __FUNCTION__, ##msg); \
  } while (0)

#define BTOR_ABORT_ARG_NULL(arg)                              \
  do                                                          \
  {                                                           \
    BTOR_ABORT ((arg) == 0, "'%s' must not be NULL\n", #arg); \
  } while (0)

#define BTOR_ABORT_REFS_NOT_POS(arg)                           \
  do                                                           \
  {                                                            \
    BTOR_ABORT (BTOR_REAL_ADDR_NODE ((arg))->ext_refs < 1,     \
                "reference counter of '%s' must not be < 1\n", \
                #arg);                                         \
  } while (0)

#define BTOR_ABORT_BTOR_MISMATCH(argbtor, argnode)                         \
  do                                                                       \
  {                                                                        \
    BTOR_ABORT (BTOR_REAL_ADDR_NODE (argnode)->btor != (argbtor),          \
                "argument '%s' belongs to different Boolector instance\n", \
                #argnode);                                                 \
  } while (0)

#define BTOR_ABORT_IS_BV(arg)                                             \
  do                                                                      \
  {                                                                       \
    BTOR_ABORT (btor_is_bitvec_sort (&btor->sorts_unique_table,           \
                                     BTOR_REAL_ADDR_NODE (arg)->sort_id), \
                "'%s' must not be a bit-vector\n",                        \
                #arg);                                                    \
  } while (0)

#define BTOR_ABORT_IS_NOT_BV(arg)                                          \
  do                                                                       \
  {                                                                        \
    BTOR_ABORT (!btor_is_bitvec_sort (&btor->sorts_unique_table,           \
                                      BTOR_REAL_ADDR_NODE (arg)->sort_id), \
                "'%s' must be a bit-vector\n",                             \
                #arg);                                                     \
  } while (0)

#define BTOR_ABORT_BW_MISMATCH(argbw1, argbw2)                  \
  do                                                            \
  {                                                             \
    BTOR_ABORT (BTOR_REAL_ADDR_NODE ((argbw1))->sort_id         \
                    != BTOR_REAL_ADDR_NODE ((argbw2))->sort_id, \
                "bit-width of '%s' and '%s' must match\n",      \
                #argbw1,                                        \
                #argbw2);                                       \
  } while (0)

/*------------------------------------------------------------------------*/

#endif
