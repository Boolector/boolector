/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  All rights reserved.

 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORLOG_H_INCLUDED
#define BTORLOG_H_INCLUDED

#include "btormsg.h"

/*------------------------------------------------------------------------*/
#ifndef NBTORLOG
/*------------------------------------------------------------------------*/

#define BTORLOG(LEVEL, FMT, ARGS...)                   \
  do                                                   \
  {                                                    \
    if (btor->options.loglevel.val < LEVEL) break;     \
    btor_msg (btor->msg, true, __FILE__, FMT, ##ARGS); \
  } while (0)

#define BTORLOG_TIMESTAMP(start) \
  do                             \
  {                              \
    start = btor_time_stamp ();  \
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
