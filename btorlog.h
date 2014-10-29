/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Armin Biere.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *
 *  All rights reserved.

 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORLOG_H_INCLUDED
#define BTORLOG_H_INCLUDED

int btor_log_start (Btor *, const char *, ...);
void btor_log_end (Btor *);

/*------------------------------------------------------------------------*/
#ifndef NBTORLOG
/*------------------------------------------------------------------------*/

#define BTORLOG_LEVEL_MAX 1 /* at the moment we support en/disabling only */

#define BTORLOG(FMT, ARGS...)                   \
  do                                            \
  {                                             \
    if (btor->options.loglevel.val <= 0) break; \
    (void) btor_log_start (btor, FMT, ##ARGS);  \
    btor_log_end (btor);                        \
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
