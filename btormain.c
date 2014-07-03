/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormain.h"
#include "boolector.h"
#include "btorexit.h"
#include "btoropt.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

static void
print_err (char *msg)
{
  assert (msg);
  fputs ("boolector: ", stdout);
  fputs (msg, stdout);
}

static void
print_err_va_args (char *msg, ...)
{
  va_list list;
  assert (msg);
  fputs ("boolector: ", stdout);
  va_start (list, msg);
  vprintf (msg, list);
  va_end (list);
}

/*------------------------------------------------------------------------*/

typedef struct BtorMainMemMgr
{
  size_t allocated;
} BtorMainMemMgr;

static BtorMainMemMgr *
btormain_new_mem_mgr (void)
{
  BtorMainMemMgr *mm = (BtorMainMemMgr *) malloc (sizeof (BtorMainMemMgr));
  if (!mm)
  {
    print_err ("out of memory in 'btormain_new_mem_mgr'");
    exit (BTOR_ERR_EXIT);
  }
  mm->allocated = 0;
  return mm;
}

static void *
btormain_malloc (BtorMainMemMgr *mm, size_t size)
{
  void *result;
  if (!size) return 0;
  assert (mm);
  if (!(result = malloc (size)))
  {
    print_err ("out of memory in 'btormain_malloc'");
    exit (BTOR_ERR_EXIT);
  }
  mm->allocated += size;
  return result;
}

void *
btormain_calloc (BtorMainMemMgr *mm, size_t nobj, size_t size)
{
  size_t bytes = nobj * size;
  void *result;
  assert (mm);
  result = calloc (nobj, size);
  if (!mm)
  {
    print_err ("out of memory in 'btor_calloc'");
    exit (BTOR_ERR_EXIT);
  }
  mm->allocated += bytes;
  return result;
}

#define BTORMAIN_NEWN(mm, ptr, nelems)                                      \
  do                                                                        \
  {                                                                         \
    (ptr) = (typeof(ptr)) btormain_malloc ((mm), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BTORMAIN_CNEWN(mm, ptr, nelems)                                    \
  do                                                                       \
  {                                                                        \
    (ptr) = (typeof(ptr)) btormain_calloc ((mm), (nelems), sizeof *(ptr)); \
  } while (0)

void
btormain_free (BtorMainMemMgr *mm, void *p, size_t freed)
{
  assert (mm);
  assert (!p == !freed);
  assert (mm->allocated >= freed);
  mm->allocated -= freed;
  free (p);
}

void
btormain_delete_mem_mgr (BtorMainMemMgr *mm)
{
  assert (mm);
  assert (!mm->allocated);
  free (mm);
}

#define BTORMAIN_DELETEN(mm, ptr, nelems)                  \
  do                                                       \
  {                                                        \
    btormain_free ((mm), (ptr), (nelems) * sizeof *(ptr)); \
  } while (0)

/*------------------------------------------------------------------------*/

typedef struct BtorMainGenOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorOpt help;
  BtorOpt copyright;
  BtorOpt version;
  BtorOpt timelimit;
  /* ------------------------------------ */
  BtorOpt last; /* dummy for iteration */
} BtorMainGenOpts;

typedef struct BtorMainInputOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorOpt btor;
  BtorOpt smt1;
  BtorOpt smt2;
  /* ------------------------------------ */
  BtorOpt last; /* dummy for iteration */
} BtorMainInputOpts;

typedef struct BtorMainOutputOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorOpt output;
  BtorOpt hex;
  BtorOpt decimal;
  BtorOpt dump_btor;
  BtorOpt dump_smt1;
  BtorOpt dump_smt2;
  /* ------------------------------------ */
  BtorOpt last; /* dummy for iteration */
} BtorMainOutputOpts;

typedef struct BtorMainIncOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorOpt all;
  BtorOpt look_ahead;
  BtorOpt in_depth;
  BtorOpt interval;
  /* ------------------------------------ */
  BtorOpt last; /* dummy for iteration */
} BtorMainIncOpts;

typedef struct BtorMainOpts
{
  BtorMainGenOpts gen_opts;
  BtorMainInputOpts input_opts;
  BtorMainOutputOpts output_opts;
  BtorMainIncOpts inc_opts;
} BtorMainOpts;

#define BTORMAIN_FIRST_OPT(OPTS) (&OPTS.first + 1)
#define BTORMAIN_LAST_OPT(OPTS) (&OPTS.last - 1)

#define BTORMAIN_INIT_OPT(OPT, INTL, SHRT, LNG, VAL, MIN, MAX, DESC) \
  do                                                                 \
  {                                                                  \
    OPT.internal = INTL;                                             \
    OPT.shrt     = SHRT;                                             \
    OPT.lng      = LNG;                                              \
    OPT.dflt = OPT.val = VAL;                                        \
    OPT.min            = MIN;                                        \
    OPT.max            = MAX;                                        \
    OPT.desc           = DESC;                                       \
  } while (0)

/*------------------------------------------------------------------------*/

typedef struct BtorMainApp
{
  Btor *btor;
  BtorMainMemMgr *mm;
  BtorMainOpts opts;
} BtorMainApp;

static BtorMainApp *
btormain_new_btormain (Btor *btor)
{
  assert (btor);

  BtorMainApp *res;
  BtorMainMemMgr *mm;

  mm = btormain_new_mem_mgr ();
  BTORMAIN_CNEWN (mm, res, 1);
  res->mm   = mm;
  res->btor = btor;
  return res;
}

static void
btormain_delete_btormain (BtorMainApp *app)
{
  assert (app);
  BtorMainMemMgr *mm = app->mm;

  btor_delete_btor (app->btor);
  BTORMAIN_DELETEN (mm, app, 1);
  btormain_delete_mem_mgr (mm);
}

/*------------------------------------------------------------------------*/

static void
init_main_opts (BtorMainApp *app)
{
  assert (app);

  BtorMainOpts *opts = &app->opts;

  /* Note: we use BtorOpt flag 'internal' to identify non-btor opts here. */

  BTORMAIN_INIT_OPT (opts->gen_opts.help,
                     1,
                     "h",
                     "help",
                     0,
                     0,
                     1,
                     "print this message and exit");
  BTORMAIN_INIT_OPT (opts->gen_opts.copyright,
                     1,
                     "c",
                     "copyright",
                     0,
                     0,
                     1,
                     "print copyright and exit");
  BTORMAIN_INIT_OPT (opts->gen_opts.version,
                     1,
                     "V",
                     "version",
                     0,
                     0,
                     1,
                     "print version and exit");
  BTORMAIN_INIT_OPT (
      opts->gen_opts.timelimit, 1, "t", "time", 0, 0, -1, "set time limit");

  BTORMAIN_INIT_OPT (
      opts->input_opts.btor, 1, 0, "btor", 0, 0, 1, "force BTOR input");
  BTORMAIN_INIT_OPT (opts->input_opts.smt1,
                     1,
                     0,
                     "smt1",
                     0,
                     0,
                     1,
                     "force SMT-LIB version 1 input");
  BTORMAIN_INIT_OPT (opts->input_opts.smt2,
                     1,
                     0,
                     "smt2",
                     0,
                     0,
                     1,
                     "force SMT-LIB version 2 input");

  BTORMAIN_INIT_OPT (opts->output_opts.output,
                     1,
                     "o",
                     "output",
                     0,
                     0,
                     -1,
                     "set output file for dumping");
  BTORMAIN_INIT_OPT (
      opts->output_opts.hex, 1, "x", "hex", 0, 0, 1, "hexadecimal output");
  BTORMAIN_INIT_OPT (
      opts->output_opts.decimal, 1, "d", "dec", 0, 0, 1, "decimal output");
  BTORMAIN_INIT_OPT (opts->output_opts.dump_btor,
                     1,
                     "db",
                     "dump_btor",
                     0,
                     0,
                     1,
                     "dump formula in BTOR format");
  BTORMAIN_INIT_OPT (opts->output_opts.dump_smt2,
                     1,
                     "ds",
                     "dump_smt",
                     0,
                     0,
                     1,
                     "dump formula in SMT-LIB v2 format");
  BTORMAIN_INIT_OPT (opts->output_opts.dump_smt1,
                     1,
                     "ds1",
                     "dump_smt1",
                     0,
                     0,
                     1,
                     "dump formula in SMT-LIB v1 format");

  BTORMAIN_INIT_OPT (opts->inc_opts.all,
                     1,
                     "I",
                     "incremental_all",
                     0,
                     0,
                     1,
                     "same as '-i' but solve all formulas");
  BTORMAIN_INIT_OPT (opts->inc_opts.look_ahead,
                     1,
                     0,
                     "look_ahead",
                     0,
                     0,
                     -1,
                     "incremental lookahead mode width <w>");
  BTORMAIN_INIT_OPT (opts->inc_opts.in_depth,
                     1,
                     0,
                     "in_depth",
                     0,
                     0,
                     -1,
                     "incremental in-depth mode width <w>");
  BTORMAIN_INIT_OPT (opts->inc_opts.interval,
                     1,
                     0,
                     "interval",
                     0,
                     0,
                     -1,
                     "incremental interval mode width <w>");
}

static void
print_opt (BtorMainApp *app, BtorOpt *opt)
{
  assert (app);
  assert (opt);

  char optstr[35], paramstr[10], *lngstr;
  int i, len;

  memset (optstr, ' ', 35 * sizeof (char));
  optstr[34] = '\0';

  if (!strcmp (opt->lng, "look_ahead") || !strcmp (opt->lng, "in_depth")
      || !strcmp (opt->lng, "interval"))
    sprintf (paramstr, "<w>");
  else if (!strcmp (opt->lng, "timelimit"))
    sprintf (paramstr, "<seconds>");
  else if (!strcmp (opt->lng, "output"))
    sprintf (paramstr, "<file>");
  else if (!strcmp (opt->lng, "rewrite_level"))
    sprintf (paramstr, "<n>");
  else
    paramstr[0] = '\0';

  assert (
      (opt->shrt
       && 2 * strlen (paramstr) + strlen (opt->shrt) + strlen (opt->lng) + 7
              <= 35)
      || (!opt->shrt && 2 * strlen (paramstr) + strlen (opt->lng) + 7 <= 35));

  len = strlen (opt->lng);
  BTORMAIN_NEWN (app->mm, lngstr, len + 1);
  for (i = 0; i < len; i++) lngstr[i] = opt->lng[i] == '_' ? '-' : opt->lng[i];
  lngstr[len] = '\0';

  sprintf (optstr,
           "  %s%s%s%s%s--%s%s%s",
           opt->shrt ? "-" : "",
           opt->shrt ? opt->shrt : "",
           opt->shrt && strlen (paramstr) > 0 ? " " : "",
           opt->shrt ? paramstr : "",
           opt->shrt ? ", " : "",
           lngstr,
           strlen (paramstr) > 0 ? "=" : "",
           paramstr);

  BTORMAIN_DELETEN (app->mm, lngstr, len + 1);

  len = strlen (optstr);
  for (i = len; i < 34; i++) optstr[i] = ' ';
  optstr[34] = '\0';

  printf ("%s %s\n", optstr, opt->desc);
  // TODO default values
}

static void
print_help (BtorMainApp *app)
{
  assert (app);

  BtorOpt *o, *oo;
  BtorMainOpts *opts = &app->opts;

  printf ("usage: boolector [<option>...][<input>]\n");
  printf ("\n");
  printf ("where <option> is one of the following:\n");
  printf ("\n");

  for (o = BTORMAIN_FIRST_OPT (opts->gen_opts);
       o <= BTORMAIN_LAST_OPT (opts->gen_opts);
       o++)
    print_opt (app, o);
  printf ("\n");

  for (o = BTORMAIN_FIRST_OPT (opts->input_opts);
       o <= BTORMAIN_LAST_OPT (opts->input_opts);
       o++)
    print_opt (app, o);
  printf ("\n");

  for (o = btor_first_opt (app->btor); o <= btor_last_opt (app->btor); o++)
  {
    if (o->internal) continue;
    if (!strcmp (o->lng, "incremental") || !strcmp (o->lng, "pretty_print"))
      printf ("\n");
    print_opt (app, o);
    if (!strcmp (o->lng, "incremental"))
    {
      for (oo = BTORMAIN_FIRST_OPT (opts->inc_opts);
           oo <= BTORMAIN_LAST_OPT (opts->inc_opts);
           oo++)
        print_opt (app, oo);
      printf ("\n");
    }
    else if (!strcmp (o->lng, "pretty_print"))
    {
      for (oo = BTORMAIN_FIRST_OPT (opts->output_opts);
           oo <= BTORMAIN_LAST_OPT (opts->output_opts);
           oo++)
        print_opt (app, oo);
      printf ("\n");
    }
    else if (!strcmp (o->lng, "rewrite_level_pbr"))
      printf ("\n");
  }
}

int
boolector_main (int argc, char **argv)
{
  BtorMainApp *app;

  app = btormain_new_btormain (boolector_new ());

  init_main_opts (app);
  print_help (app);

  btormain_delete_btormain (app);
}
