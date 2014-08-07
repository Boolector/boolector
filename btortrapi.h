/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORTRAPI_H_INCLUDED
#define BTORTRAPI_H_INCLUDED

#include <btorcore.h>
#include <stdio.h>

#define NODE_FMT "e%d "
#define SORT_FMT "s%d "

#define BTOR_TRAPI_NODE_ID(exp) \
  (BTOR_IS_INVERTED_NODE (exp) ? -BTOR_REAL_ADDR_NODE (exp)->id : exp->id)

#define BTOR_TRAPI_SORT_ID(sort) (sort)->id

#define BTOR_TRAPI(args...)                  \
  do                                         \
  {                                          \
    if (!btor->apitrace) break;              \
    btor_trapi (btor, __FUNCTION__, ##args); \
  } while (0)

#define BTOR_TRAPI_RETURN(args...) \
  do                               \
  {                                \
    if (!btor->apitrace) break;    \
    btor_trapi (btor, 0, ##args);  \
  } while (0)

#define BTOR_TRAPI_UNFUN_EXT(exp, fmt, args...) \
  BTOR_TRAPI (NODE_FMT fmt, BTOR_TRAPI_NODE_ID (exp), ##args)

#define BTOR_TRAPI_UNFUN(exp) BTOR_TRAPI (NODE_FMT, BTOR_TRAPI_NODE_ID (exp))

#define BTOR_TRAPI_BINFUN(e0, e1) \
  BTOR_TRAPI (                    \
      NODE_FMT NODE_FMT, BTOR_TRAPI_NODE_ID (e0), BTOR_TRAPI_NODE_ID (e1))

#define BTOR_TRAPI_TERFUN(e0, e1, e2)     \
  BTOR_TRAPI (NODE_FMT NODE_FMT NODE_FMT, \
              BTOR_TRAPI_NODE_ID (e0),    \
              BTOR_TRAPI_NODE_ID (e1),    \
              BTOR_TRAPI_NODE_ID (e2))

#define BTOR_TRAPI_RETURN_NODE(res) \
  BTOR_TRAPI_RETURN (NODE_FMT, BTOR_TRAPI_NODE_ID (res))

#define BTOR_TRAPI_RETURN_PTR(res) BTOR_TRAPI_RETURN ("%p", res)

#define BTOR_TRAPI_RETURN_STR(res) BTOR_TRAPI_RETURN ("%s", res)

#define BTOR_TRAPI_RETURN_INT(res) BTOR_TRAPI_RETURN ("%d", res)

#define BTOR_TRAPI_RETURN_SORT(sort) \
  BTOR_TRAPI_RETURN (SORT_FMT, BTOR_TRAPI_SORT_ID (sort))

static void
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

static void
btor_open_apitrace (Btor *btor, const char *name)
{
  assert (btor);
  assert (name);

  FILE *file;
  char *cmd;
  int len = strlen (name);

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

#endif
