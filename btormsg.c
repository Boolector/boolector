/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2012-2014 Aina Niemetz.
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
btor_msg (BtorMsg *msg, char *filename, int level, char *fmt, ...)
{
  va_list ap;
  char *fname, *c;
  int len;

  if (*msg->verbosity < level) return;

  len = strlen (filename) + 1;
  BTOR_NEWN (msg->mm, fname, len);
  strcpy (fname, filename);
  if ((c = strrchr (fname, '.'))) *c = 0;
  while ((c = strrchr (fname, '/'))) *c = ':';
  fputs ("[", stdout);
  fputs (fname, stdout);
  fputs ("] ", stdout);
  BTOR_DELETEN (msg->mm, fname, len);
  if (msg->prefix) printf ("%s : ", msg->prefix);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}
