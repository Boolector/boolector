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
#include "btormem.h"
#include "btoropt.h"
#include "btorparse.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int static_set_alarm;

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
#ifdef BTOR_USE_LINGELING
  BtorOpt lingeling;
  BtorOpt lgl_no_fork;
  BtorOpt lgl_opts;
#endif
#ifdef BTOR_USE_PICOSAT
  BtorOpt picosat;
#endif
#ifdef BTOR_USE_MINISAT
  BtorOpt minisat;
#endif
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
  BtorMemMgr *mm;
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
  BtorMemMgr *mm;

  mm = btor_new_mem_mgr ();
  BTOR_CNEWN (mm, res, 1);
  res->mm      = mm;
  res->btor    = btor;
  res->infile  = stdin;
  res->outfile = stdout;
  return res;
}

static void
btormain_delete_btormain (BtorMainApp *app)
{
  assert (app);
  BtorMemMgr *mm = app->mm;

  boolector_delete (app->btor);
  BTOR_DELETEN (mm, app, 1);
  btor_delete_mem_mgr (mm);
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
                     1,
                     "o",
                     "output",
                     0,
                     0,
                     0,
                     "set output file for dumping");
#if defined(BTOR_USE_LINGELING)
  BTORMAIN_INIT_OPT (app->opts.lingeling,
                     1,
                     0,
                     "lingeling",
                     0,
                     0,
                     1,
                     "force Lingeling as SAT solver");
  BTORMAIN_INIT_OPT (app->opts.lgl_opts,
                     1,
                     0,
                     "lgl_opts",
                     0,
                     0,
                     0,
                     "set lingeling option(s) '--<opt>=<val>'");
  BTORMAIN_INIT_OPT (app->opts.lgl_no_fork,
                     1,
                     0,
                     "lgl_no_fork",
                     0,
                     0,
                     0,
                     "do not use 'fork/clone' for Lingeling");
#endif
#ifdef BTOR_USE_PICOSAT
  BTORMAIN_INIT_OPT (app->opts.picosat,
                     1,
                     0,
                     "picosat",
                     0,
                     0,
                     1,
                     "force PicoSAT as SAT solver");
#endif
#ifdef BTOR_USE_MINISAT
  BTORMAIN_INIT_OPT (app->opts.minisat,
                     1,
                     0,
                     "minisat",
                     0,
                     0,
                     1,
                     "force MiniSAT as SAT solver");
#endif
}

/*------------------------------------------------------------------------*/

static void
btormain_error (BtorMainApp *app, char *msg, ...)
{
  assert (app);

  va_list list;
  va_start (list, msg);
  fputs ("boolector: ", stderr);
  vfprintf (stderr, msg, list);
  fprintf (stderr, "\n");
  va_end (list);
  app->err = BTOR_ERR_EXIT;
}

static void
btormain_msg (BtorMainApp *app, char *msg, ...)
{
  assert (app);

  va_list list;
  va_start (list, msg);
  vfprintf (app->outfile, msg, list);
  fprintf (app->outfile, "\n");
  va_end (list);
}

/*------------------------------------------------------------------------*/

#define LEN_OPTSTR 35
#define LEN_PARAMSTR 16

static void
print_opt (BtorMainApp *app, BtorOpt *opt)
{
  assert (app);
  assert (opt);

  char optstr[LEN_OPTSTR], paramstr[LEN_PARAMSTR], *lngstr;
  int i, len;

  memset (optstr, ' ', LEN_OPTSTR * sizeof (char));
  optstr[LEN_OPTSTR - 1] = '\0';

  if (!strcmp (opt->lng, "look_ahead") || !strcmp (opt->lng, "in_depth")
      || !strcmp (opt->lng, "interval"))
    sprintf (paramstr, "<w>");
  else if (!strcmp (opt->lng, "time"))
    sprintf (paramstr, "<seconds>");
  else if (!strcmp (opt->lng, "output"))
    sprintf (paramstr, "<file>");
  else if (!strcmp (opt->lng, "rewrite_level"))
    sprintf (paramstr, "<n>");
  else if (!strcmp (opt->lng, "lgl_opts"))
    sprintf (paramstr, "[,<opt>=<val>]+");
  else
    paramstr[0] = '\0';

  assert (
      !strcmp (opt->lng, "lgl_opts")
      || (opt->shrt
          && 2 * strlen (paramstr) + strlen (opt->shrt) + strlen (opt->lng) + 7
                 <= LEN_OPTSTR)
      || (!opt->shrt
          && 2 * strlen (paramstr) + strlen (opt->lng) + 7 <= LEN_OPTSTR));

  len = strlen (opt->lng);
  BTOR_NEWN (app->mm, lngstr, len + 1);
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

  BTOR_DELETEN (app->mm, lngstr, len + 1);

  len = strlen (optstr);
  for (i = len; i < LEN_OPTSTR - 1; i++) optstr[i] = ' ';
  optstr[LEN_OPTSTR - 1] = '\0';

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
    if (o->internal) continue;
    if (!strcmp (o->lng, "time") || !strcmp (o->lng, "output"))
      fprintf (out, "\n");
    print_opt (app, o);
  }
  fprintf (out, "\n");

  for (o = (BtorOpt *) boolector_first_opt (app->btor);
       o <= (BtorOpt *) boolector_last_opt (app->btor);
       o++)
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
      print_opt (app, &app->opts.output);
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

#if defined(BTOR_USE_LINGELING)
  fprintf (app->outfile, "\n");
  print_opt (app, &app->opts.lingeling);
  print_opt (app, &app->opts.lgl_no_fork);
  print_opt (app, &app->opts.lgl_opts);
#elif defined(BTOR_USE_PICOSAT)
  print_opt (app, &app->opts.picosat);
#elif defined(BTOR_USE_MINISAT)
  print_opt (app, &app->opts.minisat);
#else
#error "no SAT solver configured"
#endif
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
  int res;
  int i, j, k, len, shrt, readval, val, log, verb, forced_sat_solver;
  char opt[50], *cmd, *valstr, *lgl_opts;
  BtorMainApp *app;
  BtorOpt *o;

  lgl_opts = 0;
  verb     = 0;
  log      = 0;
  res      = BTOR_UNKNOWN_EXIT;

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
        BTOR_NEWN (app->mm, cmd, strlen (app->infile_name + 40));
        if (has_suffix (app->infile_name, ".gz"))
          sprintf (cmd, "gunzip -c %s", app->infile_name);
        else if (has_suffix (app->infile_name, ".bz2"))
          sprintf (cmd, "bzcat %s", app->infile_name);
        else if (has_suffix (app->infile_name, ".7z"))
          sprintf (cmd, "7z x -so %s 2>/dev/null", app->infile_name);
        if ((app->infile = popen (cmd, "r"))) app->close_infile = 2;
        BTOR_DELETEN (app->mm, cmd, strlen (app->infile_name + 40));
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

    k       = 0;
    val     = 0;
    readval = 0;
    len     = strlen (argv[i]);
    shrt    = argv[i][1] == '-' ? 0 : 1;
    for (j = shrt ? 1 : 2; j < len && argv[i][j] != '='; j++, k++)
      opt[k] = argv[i][j] == '-' ? '_' : argv[i][j];
    opt[k] = '\0';
    valstr = argv[i] + j + 1;
    if (argv[i][j] == '=')
    {
      val     = atoi (valstr);
      readval = 1;
    }

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
      if (!readval && ++i >= argc)
      {
        btormain_error (app,
                        "missing argument for '-%s', '--%s'",
                        app->opts.time.shrt,
                        app->opts.time.lng);
        goto DONE;
      }
      else if (!readval)
        val = atoi (argv[i]);

      static_set_alarm = val;
      if (static_set_alarm <= 0)
      {
        btormain_error (app,
                        "invalid argument for '-%s', '--%s'",
                        app->opts.time.shrt,
                        app->opts.time.lng);
        goto DONE;
      }
      boolector_set_opt (app->btor, "time", static_set_alarm);
    }
    else if ((shrt && !strcmp (opt, app->opts.output.shrt))
             || !strcmp (opt, app->opts.output.lng))
    {
      if (!readval && ++i > argc)
      {
        btormain_error (app,
                        "missing argument for '-%s', '--%s'",
                        app->opts.output.shrt,
                        app->opts.output.lng);
        goto DONE;
      }

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
#ifdef BTOR_USE_LINGELING
    else if ((shrt && !strcmp (opt, app->opts.lgl_opts.shrt))
             || !strcmp (opt, app->opts.lgl_opts.lng))
    {
      if (!readval && ++i > argc)
      {
        btormain_error (app,
                        "missing argument for '-%s', '--%s'",
                        app->opts.lgl_opts.shrt,
                        app->opts.lgl_opts.lng);
        goto DONE;
      }

      lgl_opts = valstr;
    }
#endif
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

        if (!strcmp (o->shrt, "i") || !strcmp (o->lng, "incremental"))
        {
          boolector_set_opt (
              app->btor, o->lng, BTOR_PARSE_MODE_BASIC_INCREMENTAL);
        }
        else if (!strcmp (o->shrt, "I") || !strcmp (o->lng, "incremental_all"))
        {
          boolector_set_opt (
              app->btor, o->lng, BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE);
        }
        else if (!strcmp (o->lng, "incremental_in_depth"))
        {
          if (boolector_get_opt (app->btor, "incremental_look_ahead")->val
              || boolector_get_opt (app->btor, "incremental_interval")->val)
          {
            btormain_error (app,
                            "Can only use one out of '--%s', '--%s', or '--%s'",
                            "incremental-in-depth",
                            "incremental-look-ahead",
                            "incremental-interval");
            goto DONE;
          }

          if (!readval && ++i >= argc)
          {
            btormain_error (
                app, "missing argument for '-%s', '--%s'", o->shrt, o->lng);
            goto DONE;
          }
          else if (!readval)
            val = atoi (argv[i]);

          if (val < 1)
          {
            btormain_error (app, "incremental in-depth width must be >= 1");
            goto DONE;
          }

          boolector_set_opt (app->btor, o->lng, val);
        }
        else if (!strcmp (o->lng, "incremental_look_ahead"))
        {
          if (boolector_get_opt (app->btor, "incremental_in_depth")->val
              || boolector_get_opt (app->btor, "incremental_interval")->val)
          {
            btormain_error (app,
                            "Can only use one out of '--%s', '--%s', or '--%s'",
                            "incremental-in-depth",
                            "incremental-look-ahead",
                            "incremental-interval");
            goto DONE;
          }

          if (!readval && ++i >= argc)
          {
            btormain_error (
                app, "missing argument for '-%s', '--%s'", o->shrt, o->lng);
            goto DONE;
          }
          else if (!readval)
            val = atoi (argv[i]);

          if (val < 1)
          {
            btormain_error (app, "incremental look-ahead width must be >= 1");
            goto DONE;
          }

          boolector_set_opt (app->btor, o->lng, val);
        }
        else if (!strcmp (o->lng, "incremental_inverval"))
        {
          if (boolector_get_opt (app->btor, "incremental_in_depth")->val
              || boolector_get_opt (app->btor, "incremental_look_ahead")->val)
          {
            btormain_error (app,
                            "Can only use one out of '--%s', '--%s', or '--%s'",
                            "incremental-in-depth",
                            "incremental-look-ahead",
                            "incremental-interval");
            goto DONE;
          }

          if (!readval && ++i >= argc)
          {
            btormain_error (
                app, "missing argument for '-%s', '--%s'", o->shrt, o->lng);
            goto DONE;
          }
          else if (!readval)
            val = atoi (argv[i]);

          if (val < 1)
          {
            btormain_error (app, "incremental interval width must be >= 1");
            goto DONE;
          }

          boolector_set_opt (app->btor, o->lng, val);
        }
        else if (!strcmp (o->shrt, "dp") || !strcmp (o->lng, "dual_prop"))
        {
          if (boolector_get_opt (app->btor, "just")->val)
          {
            btormain_error (
                app, "multiple exclusive optimization techniques enabled");
            goto DONE;
          }
          boolector_set_opt (app->btor, o->lng, 1);
        }
        else if (!strcmp (o->shrt, "ju") || !strcmp (o->lng, "just"))
        {
          if (boolector_get_opt (app->btor, "dual_prop")->val)
          {
            btormain_error (
                app, "multiple exclusive optimization techniques enabled");
            goto DONE;
          }
          boolector_set_opt (app->btor, o->lng, 1);
        }
        else if (!strcmp (o->shrt, "rwl") || !strcmp (o->lng, "rewrite_level"))
        {
          if (!readval && ++i >= argc)
          {
            btormain_error (
                app, "missing argument for '-%s', '--%s'", o->shrt, o->lng);
            goto DONE;
          }
          else if (!readval)
            val = atoi (argv[i]);

          if (val > 3 || val < 0)
          {
            btormain_error (app, "rewrite level not in [0,3]");
            goto DONE;
          }

          boolector_set_opt (app->btor, o->lng, val);
        }
        else if (!strcmp (o->lng, "rewrite_level_pbr"))
        {
          if (!readval && ++i >= argc)
          {
            btormain_error (app, "missing argument for '--%s'", o->lng);
            goto DONE;
          }
          else if (!readval)
            val = atoi (argv[i]);

          if (val > 3 || val < 0)
          {
            btormain_error (app, "rewrite level not in [0,3]");
            goto DONE;
          }

          boolector_set_opt (app->btor, o->lng, val);
        }
#ifndef NBTORLOG
        else if (!strcmp (o->shrt, "l") || !strcmp (o->lng, "loglevel"))
        {
          log += 1;
        }
#endif
        else if (!strcmp (o->shrt, "v") || !strcmp (o->lng, "verbosity"))
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

  if (!boolector_get_opt (app->btor, "incremental")->val
      && (boolector_get_opt (app->btor, "incremental_in_depth")->val
          || boolector_get_opt (app->btor, "incremental_look_ahead")->val
          || boolector_get_opt (app->btor, "incremental_interval")->val))
    boolector_set_opt (
        app->btor, "incremental", BTOR_PARSE_MODE_BASIC_INCREMENTAL);

  forced_sat_solver = 0;
#ifdef BTOR_USE_LINGELING
  if (app->opts.lingeling.val)
  {
    if (forced_sat_solver++)
    {
      btormain_error (app, "multiple sat solvers forced");
      goto DONE;
    }
    if (!boolector_set_sat_solver (
            app->btor, app->opts.lingeling.lng, lgl_opts))
      btormain_error (app, "invalid options to Lingeling: '%s'", lgl_opts);
  }
#endif
#ifdef BTOR_USE_PICOSAT
  if (app->opts.picosat.val)
  {
    if (forced_sat_solver++)
    {
      btormain_error (app, "multiple sat solvers forced");
      goto DONE;
    }
    boolector_set_sat_solver (app->btor, app->opts.picosat.lng, 0);
  }
#endif
#ifdef BTOR_USE_MINISAT
  if (app->opts.minisat.val)
  {
    if (forced_sat_solver++)
    {
      btormain_error (app, "multiple sat solvers forced");
      goto DONE;
    }
    boolector_set_sat_solver (app->btor, app->opts.minisat.lng, 0);
  }
#endif
  if (!forced_sat_solver)
  {
#if defined(BTOR_USE_LINGELING)
    if (!boolector_set_sat_solver (
            app->btor, app->opts.lingeling.lng, lgl_opts))
      btormain_error (app, "invalid options to Lingeling: '%s'", lgl_opts);
#elif defined(BTOR_USE_PICOSAT)
    boolector_set_sat_solver (app->btor, app->opts.picosat.lng, 0);
#elif defined(BTOR_USE_MINISAT)
    boolector_set_sat_solver (app->btor, app->opts.minisat.lng, 0);
#else
#error "no SAT solver configured"
#endif
  }

  if (boolector_get_opt (app->btor, "verbosity")->val > 0)
  {
    if (boolector_get_opt (app->btor, "incremental")->val)
      btormain_msg (app, "incremental mode through command line option");
    if (boolector_get_opt (app->btor, "incremental_in_depth")->val)
      btormain_msg (app,
                    "incremental in-depth window of %d",
                    boolector_get_opt (app->btor, "incremental_in_depth")->val);
    if (boolector_get_opt (app->btor, "incremental_look_ahead")->val)
      btormain_msg (
          app,
          "incremental look-ahead window of %d",
          boolector_get_opt (app->btor, "incremental_look_ahead")->val);
    if (boolector_get_opt (app->btor, "incremental_interval")->val)
      btormain_msg (app,
                    "incremental interval window of %d",
                    boolector_get_opt (app->btor, "incremental_interval")->val);
  }

DONE:
  if (app->done)
    res = BTOR_SUCC_EXIT;
  else if (app->err)
    res = BTOR_ERR_EXIT;

  assert (res == BTOR_ERR_EXIT || res == BTOR_SUCC_EXIT || res == BOOLECTOR_SAT
          || res == BOOLECTOR_UNSAT || res == BOOLECTOR_UNKNOWN);
  btormain_delete_btormain (app);
  return res;
}
