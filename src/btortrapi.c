/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btortrapi.h"

void
btor_trapi_print (Btor *btor, const char *msg, ...)
{
  assert (btor);
  assert (btor->apitrace);

  va_list args;
  va_start (args, msg);
  vfprintf (btor->apitrace, msg, args);
  va_end (args);
  fflush (btor->apitrace);
}

void
btor_trapi (Btor *btor, const char *fname, const char *msg, ...)
{
  assert (btor);
  assert (btor->apitrace);

  va_list args;

  if (fname)
  {
    /* skip boolector_ prefix */
    fprintf (btor->apitrace, "%s", fname + 10);
    /* skip functions that do not have 'btor' as argument */
    if (strcmp (fname, "boolector_new") && strcmp (fname, "boolector_get_btor"))
      fprintf (btor->apitrace, " %p", btor);
  }
  else
    fputs ("return", btor->apitrace);

  if (strlen (msg) > 0) fputc (' ', btor->apitrace);

  va_start (args, msg);
  vfprintf (btor->apitrace, msg, args);
  va_end (args);
  fputc ('\n', btor->apitrace);
  fflush (btor->apitrace);
}

void
btor_trapi_open_trace (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);

  FILE *file;
  char *cmd;
  uint32_t len = strlen (name);

  if (len >= 3 && !strcmp (name + len - 3, ".gz"))
  {
    len += 20;
    BTOR_NEWN (btor->mm, cmd, len);
    sprintf (cmd, "gzip -c > %s", name);
    if ((file = popen (cmd, "w"))) btor->close_apitrace = 2;
    BTOR_DELETEN (btor->mm, cmd, len);
  }
  else
  {
    if ((file = fopen (name, "w"))) btor->close_apitrace = 1;
  }

  if (file)
    btor->apitrace = file;
  else
    printf ("[boolector] WARNING failed to write API trace file to '%s'", name);
}
