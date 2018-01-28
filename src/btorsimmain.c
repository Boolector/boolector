/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <assert.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "btorfmt/btorfmt.h"

static void
die (char *m, ...)
{
  va_list list;
  va_start (list, m);
  fputs ("btorsim: ", stderr);
  vfprintf (stderr, m, list);
  fprintf (stderr, "\n");
  va_end (list);
  exit (1);
}

static void
msg (char *m, ...)
{
  assert (m);

  va_list list;
  va_start (list, m);
  fprintf (stdout, "[btorsim");
  vfprintf (stdout, m, list);
  fprintf (stdout, "\n");
  va_end (list);
}

int
main (int argc, char **argv)
{
  int res = 0;
  return res;
}
