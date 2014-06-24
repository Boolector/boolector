/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Aina Niemetz.
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

#define NODE_FMT " e%d"

#define BTOR_TRAPI_NODE_ID(exp) \
  (BTOR_IS_INVERTED_NODE (exp) ? -BTOR_REAL_ADDR_NODE (exp)->id : exp->id)

#define BTOR_TRAPI(msg, args...)    \
  do                                \
  {                                 \
    if (!btor->apitrace) break;     \
    btor_trapi (btor, msg, ##args); \
  } while (0)

#define BTOR_TRAPI_UNFUN_EXT(name, exp, fmt, args...) \
  BTOR_TRAPI (name NODE_FMT " " fmt, BTOR_TRAPI_NODE_ID (exp), ##args)

#define BTOR_TRAPI_UNFUN(name, exp) \
  BTOR_TRAPI (name NODE_FMT, BTOR_TRAPI_NODE_ID (exp))

#define BTOR_TRAPI_BINFUN(name, e0, e1) \
  BTOR_TRAPI (name NODE_FMT NODE_FMT,   \
              BTOR_TRAPI_NODE_ID (e0),  \
              BTOR_TRAPI_NODE_ID (e1))

#define BTOR_TRAPI_TERFUN(name, e0, e1, e2)    \
  BTOR_TRAPI (name NODE_FMT NODE_FMT NODE_FMT, \
              BTOR_TRAPI_NODE_ID (e0),         \
              BTOR_TRAPI_NODE_ID (e1),         \
              BTOR_TRAPI_NODE_ID (e2))

#define BTOR_TRAPI_RETURN(res)     \
  do                               \
  {                                \
    BTOR_TRAPI ("return %d", res); \
  } while (0)

#define BTOR_TRAPI_RETURN_NODE(res)                           \
  do                                                          \
  {                                                           \
    BTOR_TRAPI ("return" NODE_FMT, BTOR_TRAPI_NODE_ID (res)); \
  } while (0)

#define BTOR_TRAPI_RETURN_PTR(res) \
  do                               \
  {                                \
    BTOR_TRAPI ("return %p", res); \
  } while (0)

#define BTOR_TRAPI_RETURN_STR(res) \
  do                               \
  {                                \
    BTOR_TRAPI ("return %s", res); \
  } while (0)

static void
btor_trapi (Btor *btor, const char *msg, ...)
{
  assert (btor);
  assert (btor->apitrace);

  va_list args;

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
    if ((file = popen (cmd, "w"))) btor->closeapitrace = 2;
    BTOR_DELETEN (btor->mm, cmd, len);
  }
  else
  {
    if ((file = fopen (name, "w"))) btor->closeapitrace = 1;
  }

  if (file)
    btor->apitrace = file;
  else
    printf ("[boolector] WARNING failed to write API trace file to '%s'", name);
}

#endif
