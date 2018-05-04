/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORLOG_H_INCLUDED
#define BTORLOG_H_INCLUDED

#include "btorcore.h"
#include "btormsg.h"
#include "btoropt.h"

/*------------------------------------------------------------------------*/
#ifndef NBTORLOG
/*------------------------------------------------------------------------*/

#define BTORLOG(LEVEL, FMT, ARGS...)                           \
  do                                                           \
  {                                                            \
    if (btor_opt_get (btor, BTOR_OPT_LOGLEVEL) < LEVEL) break; \
    btor_msg (btor->msg, true, __FILE__, FMT, ##ARGS);         \
  } while (0)

#define BTORLOG_TIMESTAMP(start)     \
  do                                 \
  {                                  \
    start = btor_util_time_stamp (); \
  } while (0)

/*------------------------------------------------------------------------*/
#else
/*------------------------------------------------------------------------*/

#define BTORLOG(...) \
  do                 \
  {                  \
    (void) btor;     \
  } while (0)
#define BTORLOG_TIMESTAMP(start) \
  do                             \
  {                              \
    (void) start;                \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
