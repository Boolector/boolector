/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Armin Biere.
 *  Copyright (C) 2013-2015 Aina Niemetz.
 *  Copyright (C) 2014 Mathias Preiner.
 *
 *  All rights reserved.

 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORLOG_H_INCLUDED
#define BTORLOG_H_INCLUDED

int btor_log_start (Btor *, const char *filename, const char *, ...);
void btor_log_end (Btor *);

/*------------------------------------------------------------------------*/
#ifndef NBTORLOG
/*------------------------------------------------------------------------*/

#define BTORLOG(LEVEL, FMT, ARGS...)                     \
  do                                                     \
  {                                                      \
    if (btor->options.loglevel.val < LEVEL) break;       \
    (void) btor_log_start (btor, __FILE__, FMT, ##ARGS); \
    btor_log_end (btor);                                 \
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
