/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORABORT_H_INCLUDED
#define BTORABORT_H_INCLUDED

/*------------------------------------------------------------------------*/

#include "btorexit.h"

/*------------------------------------------------------------------------*/

#define BTOR_ABORT_BOOLECTOR(cond, msg)                      \
  do                                                         \
  {                                                          \
    if (cond)                                                \
    {                                                        \
      printf ("[%s] %s: %s\n", __FILE__, __FUNCTION__, msg); \
      fflush (stdout);                                       \
      exit (BTOR_ERR_EXIT);                                  \
    }                                                        \
  } while (0)

#define BTOR_ABORT_ARG_NULL_BOOLECTOR(arg)          \
  do                                                \
  {                                                 \
    if ((arg) == NULL)                              \
    {                                               \
      printf ("[%s] %s: ", __FILE__, __FUNCTION__); \
      printf ("'%s' must not be NULL\n", #arg);     \
      fflush (stdout);                              \
      exit (BTOR_ERR_EXIT);                         \
    }                                               \
  } while (0)

#define BTOR_ABORT_REFS_NOT_POS_BOOLECTOR(arg)                      \
  do                                                                \
  {                                                                 \
    if (BTOR_REAL_ADDR_NODE ((arg))->refs < 1)                      \
    {                                                               \
      printf ("[%s] %s: ", __FILE__, __FUNCTION__);                 \
      printf ("reference counter of '%s' must not be < 1\n", #arg); \
      fflush (stdout);                                              \
      exit (BTOR_ERR_EXIT);                                         \
    }                                                               \
  } while (0)

#define BTOR_ABORT_ARRAY_BOOLECTOR(arg)                   \
  do                                                      \
  {                                                       \
    if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE ((arg)))) \
    {                                                     \
      printf ("[%s] %s: ", __FILE__, __FUNCTION__);       \
      printf ("'%s' must not be an array\n", #arg);       \
      fflush (stdout);                                    \
      exit (BTOR_ERR_EXIT);                               \
    }                                                     \
  } while (0)

#define BTOR_ABORT_BV_BOOLECTOR(arg)                       \
  do                                                       \
  {                                                        \
    if (!BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE ((arg)))) \
    {                                                      \
      printf ("[%s] %s: ", __FILE__, __FUNCTION__);        \
      printf ("'%s' must not be a bit-vector\n", #arg);    \
      fflush (stdout);                                     \
      exit (BTOR_ERR_EXIT);                                \
    }                                                      \
  } while (0)

#define BTOR_ABORT_NE_BW(arg1, arg2)                                         \
  do                                                                         \
  {                                                                          \
    if (BTOR_REAL_ADDR_NODE ((arg1))->len                                    \
        != BTOR_REAL_ADDR_NODE ((arg2))->len)                                \
    {                                                                        \
      printf ("[%s] %s: ", __FILE__, __FUNCTION__);                          \
      printf (                                                               \
          "bit-width of '%s' and '%s' must not be unequal\n", #arg1, #arg2); \
      exit (BTOR_ERR_EXIT);                                                  \
    }                                                                        \
  } while (0)

/*------------------------------------------------------------------------*/

#endif
