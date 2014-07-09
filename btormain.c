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
#include "btorconfig.h"
#include "btorexit.h"
#include "btoropt.h"
#include "btorparse.h"
#include "btorsat.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int static_set_alarm;
static void print_error (char *msg, ...);

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
    print_error ("out of memory in 'btormain_new_mem_mgr'");
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
    print_error ("out of memory in 'btormain_malloc'");
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
    print_error ("out of memory in 'btor_calloc'");
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

typedef struct BtorMainOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorOpt help;
  BtorOpt copyright;
  BtorOpt version;
  BtorOpt time;
  BtorOpt output;
  /* ------------------------------------ */
  BtorOpt last; /* dummy for iteration */
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

typedef struct BtorMainApp
{
  Btor *btor;
  BtorMainMemMgr *mm;
  BtorMainOpts opts;
  int done;
  int err;
  char *infile_name;
  FILE *infile;
  int close_infile;
  FILE *outfile;
  int close_outfile;
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

static void
btormain_init_opts (BtorMainApp *app)
{
  assert (app);

  BTORMAIN_INIT_OPT (
      app->opts.help, 0, "h", "help", 0, 0, 1, "print this message and exit");
  BTORMAIN_INIT_OPT (app->opts.copyright,
                     0,
                     "c",
                     "copyright",
                     0,
                     0,
                     1,
                     "print copyright and exit");
  BTORMAIN_INIT_OPT (
      app->opts.version, 0, "V", "version", 0, 0, 1, "print version and exit");
  BTORMAIN_INIT_OPT (
      app->opts.time, 0, "t", "time", 0, 0, -1, "set time limit");
  BTORMAIN_INIT_OPT (app->opts.output,
                     0,
                     "o",
                     "output",
                     0,
                     0,
                     0,
                     "set output file for dumping");
}

/*------------------------------------------------------------------------*/

static void
vprint_error (char *msg, va_list list)
{
  assert (list);

  fputs ("boolector: ", stderr);
  vfprintf (stderr, msg, list);
  fprintf (stderr, "\n");
}

static void
print_error (char *msg, ...)
{
  assert (msg);

  va_list list;
  va_start (list, msg);
  vprint_error (msg, list);
  va_end (list);
}

static void
btormain_error (BtorMainApp *app, char *msg, ...)
{
  assert (app);

  va_list list;
  va_start (list, msg);
  vprint_error (msg, list);
  va_end (list);
  app->err = BTOR_ERR_EXIT;
}

/*------------------------------------------------------------------------*/

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

  fprintf (app->outfile, "%s %s\n", optstr, opt->desc);
  // TODO default values
}

static void
print_help (BtorMainApp *app)
{
  assert (app);

  BtorOpt to;
  BtorOpt *o;
  FILE *out = app->outfile;

  fprintf (out, "usage: boolector [<option>...][<input>]\n");
  fprintf (out, "\n");
  fprintf (out, "where <option> is one of the following:\n");
  fprintf (out, "\n");

  for (o = BTORMAIN_FIRST_OPT (app->opts); o <= BTORMAIN_LAST_OPT (app->opts);
       o++)
  {
    if (!strcmp (o->lng, "time") || !strcmp (o->lng, "output"))
      fprintf (out, "\n");
    print_opt (app, o);
  }
  fprintf (out, "\n");

  for (o = btor_first_opt (app->btor); o <= btor_last_opt (app->btor); o++)
  {
    if (o->internal) continue;
    if (!strcmp (o->lng, "incremental") || !strcmp (o->lng, "beta_reduce_all")
        || !strcmp (o->lng, "no_pretty_print"))
      fprintf (out, "\n");
    if (!strcmp (o->lng, "input_format"))
    {
      fprintf (app->outfile, "\n");
      to.shrt = 0;
      to.lng  = "btor";
      to.desc = "force BTOR input format";
      print_opt (app, &to);
      to.shrt = 0;
      to.lng  = "smt";
      to.desc = "force SMT-LIB v2 input format";
      print_opt (app, &to);
      to.shrt = 0;
      to.lng  = "smt1";
      to.desc = "force SMT-LIB v1 input format";
      print_opt (app, &to);
      fprintf (app->outfile, "\n");
    }
    else if (!strcmp (o->lng, "output_number_format"))
    {
      fprintf (app->outfile, "\n");
      to.shrt = "x";
      to.lng  = "hex";
      to.desc = "force hexadecimal number output";
      print_opt (app, &to);
      to.shrt = "d";
      to.lng  = "dec";
      to.desc = "force decimal number output";
      print_opt (app, &to);
    }
    else if (!strcmp (o->lng, "output_format"))
    {
      fprintf (app->outfile, "\n");
      to.shrt = "db";
      to.lng  = "dump_btor";
      to.desc = "dump formula in BTOR format";
      print_opt (app, &to);
      to.shrt = "ds";
      to.lng  = "dump_smt";
      to.desc = "dump formula in SMT-LIB v2 format";
      print_opt (app, &to);
      to.shrt = "ds1";
      to.lng  = "dump_smt1";
      to.desc = "dump formula in SMT-LIB v1 format";
      print_opt (app, &to);
      fprintf (app->outfile, "\n");
    }
    else
      print_opt (app, o);
  }
  app->done = 1;
}

static void
print_copyright (BtorMainApp *app)
{
  assert (app);

  FILE *out = app->outfile;

  fprintf (out, "This software is\n");
  fprintf (out, "Copyright (c) 2007-2009 Robert Brummayer\n");
  fprintf (out, "Copyright (c) 2007-2014 Armin Biere\n");
  fprintf (out, "Copyright (c) 2012-2014 Aina Niemetz, Mathias Preiner\n");
  fprintf (out, "Copyright (c) 2013 Christian Reisenberger\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#ifdef BTOR_USE_LINGELING
  fprintf (out, "\n");
  fprintf (out, "This software is linked against Lingeling\n");
  fprintf (out, "Copyright (c) 2010-2014 Armin Biere\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#endif
#ifdef BTOR_USE_PICOSAT
  fprintf (out, "\n");
  fprintf (out, "This software is linked against PicoSAT\n");
  fprintf (out, "Copyright (c) 2006-2014 Armin Biere\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#endif
#ifdef BTOR_USE_MINISAT
  fprintf (out, "\n");
  fprintf (out, "This software is linked against MiniSAT\n");
  fprintf (out, "Copyright (c) 2003-2013, Niklas Een, Niklas Sorensson\n");
#endif
  app->done = 1;
}

static void
print_version (BtorMainApp *app)
{
  assert (app);
  fprintf (app->outfile, "%s\n", BTOR_VERSION);
  app->done = 1;
}

/*------------------------------------------------------------------------*/

static int
has_suffix (const char *str, const char *suffix)
{
  int l, k, d;
  l = strlen (str);
  k = strlen (suffix);
  d = l - k;
  if (d < 0) return 0;
  return !strcmp (str + d, suffix);
}

/*------------------------------------------------------------------------*/

int
boolector_main (int argc, char **argv)
{
  int i, j, k, len, shrt, res, val, log, verb;
  char opt[50], *cmd;
  BtorMainApp *app;
  BtorOpt *o;

  res = BTOR_UNKNOWN_EXIT;

  app = btormain_new_btormain (boolector_new ());

  btormain_init_opts (app);

  for (i = 1; i < argc; i++)
  {
    if (argv[i][0] != '-')
    {
      if (app->close_infile)
      {
        btormain_error (app, "multiple input files");
        goto DONE;
      }
      app->infile_name = argv[i];
      if (!boolector_file_exists (app->btor, app->infile_name))
        app->infile = 0;
      else if (has_suffix (app->infile_name, ".gz")
               || has_suffix (app->infile_name, ".bz2")
               || has_suffix (app->infile_name, "7z"))
      {
        BTORMAIN_NEWN (app->mm, cmd, strlen (app->infile_name + 40));
        if (has_suffix (app->infile_name, ".gz"))
          sprintf (cmd, "gunzip -c %s", app->infile_name);
        else if (has_suffix (app->infile_name, ".bz2"))
          sprintf (cmd, "bzcat %s", app->infile_name);
        else if (has_suffix (app->infile_name, ".7z"))
          sprintf (cmd, "7z x -so %s 2>/dev/null", app->infile_name);
        if ((app->infile = popen (cmd, "r"))) app->close_infile = 2;
        BTORMAIN_DELETEN (app->mm, cmd, strlen (app->infile_name + 40));
      }
      else if ((app->infile = fopen (app->infile_name, "r")))
        app->close_infile = 1;

      if (!app->infile)
      {
        btormain_error (app, "can not read '%s'", app->infile_name);
        goto DONE;
      }

      continue;
    }

    k    = 0;
    val  = -1;
    len  = strlen (argv[i]);
    shrt = argv[i][1] == '-' ? 0 : 1;
    for (j = shrt ? 1 : 2; j < len && argv[i][j] != '='; j++, k++)
      opt[k] = argv[i][j] == '-' ? '_' : argv[i][j];
    opt[k] = '\0';
    if (argv[i][j] == '=') val = atoi (argv[i] + j + 1);

    if ((shrt && !strcmp (opt, app->opts.help.shrt))
        || !strcmp (opt, app->opts.help.lng))
    {
      print_help (app);
      goto DONE;
    }
    else if ((shrt && !strcmp (opt, app->opts.copyright.shrt))
             || !strcmp (opt, app->opts.copyright.lng))
    {
      print_copyright (app);
      goto DONE;
    }
    else if ((shrt && !strcmp (opt, app->opts.version.shrt))
             || !strcmp (opt, app->opts.version.lng))
    {
      print_version (app);
      goto DONE;
    }
    else if ((shrt && !strcmp (opt, app->opts.time.shrt))
             || !strcmp (opt, app->opts.time.lng))
    {
      if (++i < argc)
      {
        static_set_alarm = atoi (argv[i]);
        if (static_set_alarm <= 0)
        {
          btormain_error (
              app, "invalid argument for '%s'", app->opts.time.shrt);
          goto DONE;
        }
        boolector_set_opt (app->btor, "time", static_set_alarm);
      }
      else
      {
        btormain_error (app,
                        "missing argument for '-%s', '--%s'",
                        app->opts.time.shrt,
                        app->opts.time.lng);
        goto DONE;
      }
    }
    else if ((shrt && !strcmp (opt, app->opts.output.shrt))
             || !strcmp (opt, app->opts.output.lng))
    {
      if (++i < argc)
      {
        if (app->close_outfile)
        {
          btormain_error (app, "multiple output files");
          goto DONE;
        }
        app->outfile = fopen (argv[i], "w");
        if (!app->outfile)
        {
          btormain_error (app, "can not create '%s'", argv[i]);
          goto DONE;
        }
        app->close_outfile = 1;
      }
      else
      {
        btormain_error (app,
                        "missing argument for '-%s', '--%s'",
                        app->opts.output.shrt,
                        app->opts.output.lng);
        goto DONE;
      }
    }
    else
    {
      if (!strcmp (opt, "btor"))
        boolector_set_opt (app->btor, "input_format", BTOR_INPUT_FORMAT_BTOR);
      else if (!strcmp (opt, "smt"))
        boolector_set_opt (app->btor, "input_format", BTOR_INPUT_FORMAT_SMT2);
      else if (!strcmp (opt, "smt1"))
        boolector_set_opt (app->btor, "input_format", BTOR_INPUT_FORMAT_SMT1);
      else if (!strcmp (opt, "x") || !strcmp (opt, "hex"))
        boolector_set_opt (
            app->btor, "output_number_format", BTOR_OUTPUT_BASE_HEX);
      else if (!strcmp (opt, "d") || !strcmp (opt, "dec"))
        boolector_set_opt (
            app->btor, "output_number_format", BTOR_OUTPUT_BASE_DEC);
      else if (!strcmp (opt, "db") || !strcmp (opt, "dump_btor"))
        boolector_set_opt (app->btor, "output_format", BTOR_OUTPUT_FORMAT_BTOR);
      else if (!strcmp (opt, "ds") || !strcmp (opt, "dump_smt"))
        boolector_set_opt (app->btor, "output_format", BTOR_OUTPUT_FORMAT_SMT2);
      else if (!strcmp (opt, "ds1") || !strcmp (opt, "dump_smt1"))
        boolector_set_opt (app->btor, "output_format", BTOR_OUTPUT_FORMAT_SMT1);
      else
      {
        for (o = btor_first_opt (app->btor); o <= btor_last_opt (app->btor);
             o++)
        {
          if ((shrt && o->shrt && !strcmp (o->shrt, opt))
              || !strcmp (o->lng, opt))
            break;
        }

        if (o > btor_last_opt (app->btor))
        {
          btormain_error (app, "invalid option '%s%s'", shrt ? "-" : "--", opt);
          goto DONE;
        }

        if ((o->shrt && !strcmp (o->shrt, app->btor->options.dual_prop.shrt))
            || !strcmp (o->lng, app->btor->options.dual_prop.lng))
        {
          if (boolector_get_opt (app->btor, app->btor->options.just.lng)->val)
          {
            btormain_error (
                app, "multiple exclusive optimization techniques enabled");
            goto DONE;
          }
          boolector_set_opt (app->btor, o->lng, 1);
        }
        else if ((o->shrt && !strcmp (o->shrt, app->btor->options.just.shrt))
                 || !strcmp (o->lng, app->btor->options.just.lng))
        {
          if (boolector_get_opt (app->btor, app->btor->options.dual_prop.lng)
                  ->val)
          {
            btormain_error (
                app, "multiple exclusive optimization techniques enabled");
            goto DONE;
          }
          boolector_set_opt (app->btor, o->lng, 1);
        }
        else if ((o->shrt
                  && !strcmp (o->shrt, app->btor->options.rewrite_level.shrt))
                 || !strcmp (o->lng, app->btor->options.rewrite_level.lng))
        {
          if (val < 0 && ++i > argc)
          {
            btormain_error (app,
                            "missing argument for '-%s', '--%s'",
                            app->btor->options.rewrite_level.shrt,
                            app->btor->options.rewrite_level.lng);
            goto DONE;
          }
          else if (val < 0)
            val = atoi (argv[i]);

          if (val > 3 || val < 0)
          {
            btormain_error (app, "rewrite level not in [0,3]");
            goto DONE;
          }

          boolector_set_opt (app->btor, o->lng, val);
        }
        else if (!strcmp (o->lng, app->btor->options.rewrite_level_pbr.lng))
        {
          if (++i < argc)
          {
            val = atoi (argv[i]);
            if (val > 3 || val < 0)
            {
              btormain_error (app, "rewrite level not in [0,3]");
              goto DONE;
            }
            boolector_set_opt (app->btor, o->lng, val);
          }
          else
          {
            btormain_error (app,
                            "missing argument for '-%s', '--%s'",
                            app->btor->options.rewrite_level_pbr.shrt,
                            app->btor->options.rewrite_level_pbr.lng);
            goto DONE;
          }
        }
#ifndef NBTORLOG
        else if ((o->shrt
                  && !strcmp (o->shrt, app->btor->options.loglevel.shrt))
                 || !strcmp (o->lng, app->btor->options.loglevel.lng))
        {
          log += 1;
        }
#endif
        else if ((o->shrt
                  && !strcmp (o->shrt, app->btor->options.verbosity.shrt))
                 || !strcmp (o->lng, app->btor->options.verbosity.lng))
        {
          verb += 1;
        }
        else
          boolector_set_opt (app->btor, o->lng, 1);
      }
    }
  }

#ifndef NBTORLOG
  boolector_set_opt (app->btor, "loglevel", log);
#endif
  boolector_set_opt (app->btor, "verbosity", verb);

DONE:
  if (app->done)
    res = BTOR_SUCC_EXIT;
  else if (app->err)
    res = BTOR_ERR_EXIT;

  assert (res == BTOR_ERR_EXIT || res == BTOR_SUCC_EXIT || res == BTOR_SAT
          || res == BTOR_UNSAT || res == BTOR_UNKNOWN);
  btormain_delete_btormain (app);
  return res;
}
