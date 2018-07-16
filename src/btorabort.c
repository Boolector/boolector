/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorabort.h"

#include "btorexit.h"
#include "btortypes.h"
#include "utils/btormem.h"

#include <stdio.h>

void
btor_abort (void)
{
  if (btor_abort_callback.abortfun)
    btor_abort_callback.abortfun ();
  else
    exit (BTOR_ERR_EXIT);
}

void
btor_abort_warn (
    bool abort, const char *filename, const char *fun, const char *fmt, ...)
{
  char *s, *e, *p;
  va_list list;

  e = strrchr (filename, '.');
  s = strrchr (filename, '/');
  s = s ? s + 1 : (char *) filename;

  fputc ('[', stderr);
  for (p = s; p < e; p++) fputc (*p, stderr);

  fprintf (stderr, "] %s: %s", fun, abort ? "" : "WARNING: ");
  va_start (list, fmt);
  vfprintf (stderr, fmt, list);
  va_end (list);
  fprintf (stderr, "\n");
  fflush (stderr);
  if (abort) btor_abort();
}
