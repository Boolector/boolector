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
#include "btorsat.h"

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

typedef struct BtorMainApp BtorMainApp;

typedef struct BtorMainOpt
{
  BtorOpt opts;
  void (*fun) (BtorMainApp *app);
} BtorMainOpt;

typedef struct BtorMainGenOpts
{
  BtorMainOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorMainOpt help;
  BtorMainOpt copyright;
  BtorMainOpt version;
  BtorMainOpt timelimit;
  /* ------------------------------------ */
  BtorMainOpt last; /* dummy for iteration */
} BtorMainGenOpts;

typedef struct BtorMainInputOpts
{
  BtorMainOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorMainOpt btor;
  BtorMainOpt smt1;
  BtorMainOpt smt2;
  /* ------------------------------------ */
  BtorMainOpt last; /* dummy for iteration */
} BtorMainInputOpts;

typedef struct BtorMainOutputOpts
{
  BtorMainOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorMainOpt output;
  BtorMainOpt hex;
  BtorMainOpt decimal;
  BtorMainOpt dump_btor;
  BtorMainOpt dump_smt1;
  BtorMainOpt dump_smt2;
  /* ------------------------------------ */
  BtorMainOpt last; /* dummy for iteration */
} BtorMainOutputOpts;

typedef struct BtorMainIncOpts
{
  BtorMainOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorMainOpt all;
  BtorMainOpt look_ahead;
  BtorMainOpt in_depth;
  BtorMainOpt interval;
  /* ------------------------------------ */
  BtorMainOpt last; /* dummy for iteration */
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

#define BTORMAIN_INIT_OPT(OPT, INTL, SHRT, LNG, VAL, MIN, MAX, DESC, FUN) \
  do                                                                      \
  {                                                                       \
    OPT.opts.internal = INTL;                                             \
    OPT.opts.shrt     = SHRT;                                             \
    OPT.opts.lng      = LNG;                                              \
    OPT.opts.dflt = OPT.opts.val = VAL;                                   \
    OPT.opts.min                 = MIN;                                   \
    OPT.opts.max                 = MAX;                                   \
    OPT.opts.desc                = DESC;                                  \
    OPT.fun                      = FUN;                                   \
  } while (0)

/*------------------------------------------------------------------------*/

typedef struct BtorMainApp
{
  Btor *btor;
  BtorMainMemMgr *mm;
  BtorMainOpts opts;
  int done;
  int err;
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

  boolector_delete (app->btor);
  BTORMAIN_DELETEN (mm, app, 1);
  btormain_delete_mem_mgr (mm);
}

/*------------------------------------------------------------------------*/

static void
set_gen_help (BtorMainApp *app)
{
}

static void
set_gen_copyright (BtorMainApp *app)
{
}

static void
set_gen_version (BtorMainApp *app)
{
}

static void
set_gen_time (BtorMainApp *app)
{
}

static void
set_input_btor (BtorMainApp *app)
{
}

static void
set_input_smt1 (BtorMainApp *app)
{
}

static void
set_input_smt2 (BtorMainApp *app)
{
}

static void
set_output_output (BtorMainApp *app)
{
}

static void
set_output_hex (BtorMainApp *app)
{
}

static void
set_output_decimal (BtorMainApp *app)
{
}

static void
set_output_dump_btor (BtorMainApp *app)
{
}

static void
set_output_dump_smt1 (BtorMainApp *app)
{
}

static void
set_output_dump_smt2 (BtorMainApp *app)
{
}

static void
set_inc_all (BtorMainApp *app)
{
}

static void
set_inc_look_ahead (BtorMainApp *app)
{
}

static void
set_inc_in_depth (BtorMainApp *app)
{
}

static void
set_inc_interval (BtorMainApp *app)
{
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
                     "print this message and exit",
                     set_gen_help);
  BTORMAIN_INIT_OPT (opts->gen_opts.copyright,
                     1,
                     "c",
                     "copyright",
                     0,
                     0,
                     1,
                     "print copyright and exit",
                     set_gen_copyright);
  BTORMAIN_INIT_OPT (opts->gen_opts.version,
                     1,
                     "V",
                     "version",
                     0,
                     0,
                     1,
                     "print version and exit",
                     set_gen_version);
  BTORMAIN_INIT_OPT (opts->gen_opts.timelimit,
                     1,
                     "t",
                     "time",
                     0,
                     0,
                     -1,
                     "set time limit",
                     set_gen_time);

  BTORMAIN_INIT_OPT (opts->input_opts.btor,
                     1,
                     0,
                     "btor",
                     0,
                     0,
                     1,
                     "force BTOR input",
                     set_input_btor);
  BTORMAIN_INIT_OPT (opts->input_opts.smt1,
                     1,
                     0,
                     "smt1",
                     0,
                     0,
                     1,
                     "force SMT-LIB version 1 input",
                     set_input_smt1);
  BTORMAIN_INIT_OPT (opts->input_opts.smt2,
                     1,
                     0,
                     "smt2",
                     0,
                     0,
                     1,
                     "force SMT-LIB version 2 input",
                     set_input_smt2);

  BTORMAIN_INIT_OPT (opts->output_opts.output,
                     1,
                     "o",
                     "output",
                     0,
                     0,
                     -1,
                     "set output file for dumping",
                     set_output_output);
  BTORMAIN_INIT_OPT (opts->output_opts.hex,
                     1,
                     "x",
                     "hex",
                     0,
                     0,
                     1,
                     "hexadecimal output",
                     set_output_hex);
  BTORMAIN_INIT_OPT (opts->output_opts.decimal,
                     1,
                     "d",
                     "dec",
                     0,
                     0,
                     1,
                     "decimal output",
                     set_output_decimal);
  BTORMAIN_INIT_OPT (opts->output_opts.dump_btor,
                     1,
                     "db",
                     "dump_btor",
                     0,
                     0,
                     1,
                     "dump formula in BTOR format",
                     set_output_dump_btor);
  BTORMAIN_INIT_OPT (opts->output_opts.dump_smt1,
                     1,
                     "ds1",
                     "dump_smt1",
                     0,
                     0,
                     1,
                     "dump formula in SMT-LIB v1 format",
                     set_output_dump_smt1);
  BTORMAIN_INIT_OPT (opts->output_opts.dump_smt2,
                     1,
                     "ds",
                     "dump_smt",
                     0,
                     0,
                     1,
                     "dump formula in SMT-LIB v2 format",
                     set_output_dump_smt2);

  BTORMAIN_INIT_OPT (opts->inc_opts.all,
                     1,
                     "I",
                     "incremental_all",
                     0,
                     0,
                     1,
                     "same as '-i' but solve all formulas",
                     set_inc_all);
  BTORMAIN_INIT_OPT (opts->inc_opts.look_ahead,
                     1,
                     0,
                     "look_ahead",
                     0,
                     0,
                     -1,
                     "incremental lookahead mode width <w>",
                     set_inc_look_ahead);
  BTORMAIN_INIT_OPT (opts->inc_opts.in_depth,
                     1,
                     0,
                     "in_depth",
                     0,
                     0,
                     -1,
                     "incremental in-depth mode width <w>",
                     set_inc_in_depth);
  BTORMAIN_INIT_OPT (opts->inc_opts.interval,
                     1,
                     0,
                     "interval",
                     0,
                     0,
                     -1,
                     "incremental interval mode width <w>",
                     set_inc_interval);
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
  else if (!strcmp (opt->lng, "time"))
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

  BtorOpt *bo;
  BtorMainOpt *o;
  BtorMainOpts *opts = &app->opts;

  printf ("usage: boolector [<option>...][<input>]\n");
  printf ("\n");
  printf ("where <option> is one of the following:\n");
  printf ("\n");

  for (o = BTORMAIN_FIRST_OPT (opts->gen_opts);
       o <= BTORMAIN_LAST_OPT (opts->gen_opts);
       o++)
    print_opt (app, &o->opts);
  printf ("\n");

  for (o = BTORMAIN_FIRST_OPT (opts->input_opts);
       o <= BTORMAIN_LAST_OPT (opts->input_opts);
       o++)
    print_opt (app, &o->opts);
  printf ("\n");

  for (bo = btor_first_opt (app->btor); bo <= btor_last_opt (app->btor); bo++)
  {
    if (bo->internal) continue;
    if (!strcmp (bo->lng, "incremental") || !strcmp (bo->lng, "pretty_print"))
      printf ("\n");
    print_opt (app, bo);
    if (!strcmp (bo->lng, "incremental"))
    {
      for (o = BTORMAIN_FIRST_OPT (opts->inc_opts);
           o <= BTORMAIN_LAST_OPT (opts->inc_opts);
           o++)
        print_opt (app, &o->opts);
      printf ("\n");
    }
    else if (!strcmp (bo->lng, "pretty_print"))
    {
      for (o = BTORMAIN_FIRST_OPT (opts->output_opts);
           o <= BTORMAIN_LAST_OPT (opts->output_opts);
           o++)
        print_opt (app, &o->opts);
      printf ("\n");
    }
    else if (!strcmp (bo->lng, "rewrite_level_pbr"))
      printf ("\n");
  }
}

int
boolector_main (int argc, char **argv)
{
  int i, res;
  BtorMainApp *app;

  res = BTOR_UNKNOWN_EXIT;

  app = btormain_new_btormain (boolector_new ());

  init_main_opts (app);

  //  for (i = 1; i < argc; i++)
  //    {
  //      if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
  //	{
  print_help (app);
  res = BTOR_SUCC_EXIT;
  goto DONE;
  //	}
  //
  //
  //    }

DONE:
  assert (res == BTOR_ERR_EXIT || res == BTOR_SUCC_EXIT || res == BTOR_SAT
          || res == BTOR_UNSAT || res == BTOR_UNKNOWN);
  btormain_delete_btormain (app);
  return res;
}
