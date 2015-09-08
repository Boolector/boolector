/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormsg.h"
#include <stdio.h>
#include "assert.h"

BtorMsg *
btor_new_btor_msg (BtorMemMgr *mm, int *verbosity)
{
  assert (mm);
  assert (verbosity);

  BtorMsg *res;

  BTOR_CNEW (mm, res);
  res->mm        = mm;
  res->verbosity = verbosity;
  return res;
}

void
btor_delete_btor_msg (BtorMsg *msg)
{
  assert (msg);

  btor_freestr (msg->mm, msg->prefix);
  BTOR_DELETE (msg->mm, msg);
}

void
btor_msg (BtorMsg *msg, bool log, char *filename, char *fmt, ...)
{
  va_list ap;
  char *path, *fname, *c, *p;
  int len;

  len = strlen (filename) + 1;
  BTOR_NEWN (msg->mm, path, len);
  strcpy (path, filename);
  /* cut-off file extension */
  if ((c = strrchr (path, '.'))) *c = 0;
  fname = strrchr (path, '/');
  if (!fname)
    fname = path;
  else
    fname += 1;

  fputs ("[", stdout);
  if (log) fputs ("log:", stdout);
  if (msg->prefix) fprintf (stdout, "%s>", msg->prefix);
  p = path;
  while ((c = strchr (p, '/')))
  {
    *c = 0;
    /* print at most 4 chars per directory */
    if (c - p > 4)
    {
      p[4] = 0;
      fprintf (stdout, "%s>", p);
    }
    p = c;
  }
  /* cut-off btor prefix from file name */
  fputs (fname + 4, stdout);
  fputs ("] ", stdout);
  BTOR_DELETEN (msg->mm, path, len);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}
