/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorabort.h"

#include "btorexit.h"
#include "utils/btormem.h"

#include <stdio.h>

void
btor_abort (const char *filename, const char *fun, const char *fmt, ...)
{
  va_list list;
  char *s, *e, *p;

  e = strrchr (filename, '.');
  s = strrchr (filename, '/');
  s = s ? s + 1 : (char *) filename;

  fputc ('[', stderr);
  for (p = s; p < e; p++) fputc (*p, stderr);

  fprintf (stderr, "] %s: ", fun);

  va_start (list, fmt);
  vfprintf (stderr, fmt, list);
  va_end (list);
  fprintf (stderr, "\n");
  fflush (stderr);
  exit (BTOR_ERR_EXIT);
}
