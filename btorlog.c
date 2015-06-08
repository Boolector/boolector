/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2014 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
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
btor_log_start (Btor *btor, const char *filename, const char *fmt, ...)
{
  size_t len;
  va_list ap;
  char *fname, *c;

  if (btor->options.loglevel.val <= 0) return 0;

  len = strlen (filename) + 1;
  BTOR_NEWN (btor->mm, fname, len);
  strcpy (fname, filename);
  if ((c = strrchr (fname, '.'))) *c = 0;
  while ((c = strrchr (fname, '/'))) *c = ':';
  fputs ("[", stdout);
  fputs (fname, stdout);
  fputs (":", stdout);
  fputs ("log] ", stdout);
  BTOR_DELETEN (btor->mm, fname, len);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  return 1;
}

void
btor_log_end (Btor *btor)
{
  (void) btor;
  assert (btor->options.loglevel.val > 0);
  fputc ('\n', stdout);
  fflush (stdout);
}

#endif
