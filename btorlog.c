/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef NBTORLOG

#include "btorlog.h"
#include "btorcore.h"

#include <stdarg.h>

int
btor_log_start (Btor* btor, const char* fmt, ...)
{
  va_list ap;
  if (btor->options.loglevel.val <= 0) return 0;
  fputs ("[btorlog] ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  return 1;
}

void
btor_log_end (Btor* btor)
{
  (void) btor;
  assert (btor->options.loglevel.val > 0);
  fputc ('\n', stdout);
  fflush (stdout);
}

#endif
