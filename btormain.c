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
#include "btoropt.h"

#include <assert.h>
#include <stdio.h>
#include <string.h>

typedef struct BtorMainGenOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ----------------------------------------------------------------------- */
  BtorOpt help;
  BtorOpt copyright;
  BtorOpt version;
  BtorOpt timelimit;
  /* ----------------------------------------------------------------------- */
  BtorOpt last; /* dummy for iteration */
} BtorMainGenOpts;

typedef struct BtorMainInputOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ----------------------------------------------------------------------- */
  BtorOpt btor;
  BtorOpt smt1;
  BtorOpt smt2;
  /* ----------------------------------------------------------------------- */
  BtorOpt last; /* dummy for iteration */
} BtorMainInputOpts;

typedef struct BtorMainOutputOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ----------------------------------------------------------------------- */
  BtorOpt output;
  BtorOpt hex;
  BtorOpt decimal;
  BtorOpt dump_btor;
  BtorOpt dump_smt1;
  BtorOpt dump_smt2;
  /* ----------------------------------------------------------------------- */
  BtorOpt last; /* dummy for iteration */
} BtorMainOutputOpts;

typedef struct BtorMainIncOpts
{
  BtorOpt first; /* dummy for iteration */
  /* ----------------------------------------------------------------------- */
  BtorOpt all;
  BtorOpt look_ahead;
  BtorOpt in_depth;
  BtorOpt interval;
  /* ----------------------------------------------------------------------- */
  BtorOpt last; /* dummy for iteration */
} BtorMainIncOpts;

typedef struct BtorMainOpts
{
  BtorMainGenOpts gen_opts;
  BtorMainInputOpts input_opts;
  BtorMainOutputOpts output_opts;
  BtorMainIncOpts inc_opts;
} BtorMainOpts;

#define FIRST_OPT(OPTS) (&OPTS.first + 1)
#define LAST_OPT(OPTS) (&OPTS.last - 1)

#define INIT_OPT(OPT, INTL, SHRT, LNG, VAL, MIN, MAX, DESC) \
  do                                                        \
  {                                                         \
    OPT.internal = INTL;                                    \
    OPT.shrt     = SHRT;                                    \
    OPT.lng      = LNG;                                     \
    OPT.dflt = OPT.val = VAL;                               \
    OPT.min            = MIN;                               \
    OPT.max            = MAX;                               \
    OPT.desc           = DESC;                              \
  } while (0)

static void
init_main_opts (BtorMainOpts *main_opts)
{
  assert (main_opts);

  /* Note: we use BtorOpt flag 'internal' to identify non-btor opts here. */

  INIT_OPT (main_opts->gen_opts.help,
            1,
            "h",
            "help",
            0,
            0,
            1,
            "print this message and exit");
  INIT_OPT (main_opts->gen_opts.copyright,
            1,
            "c",
            "copyright",
            0,
            0,
            1,
            "print copyright and exit");
  INIT_OPT (main_opts->gen_opts.version,
            1,
            "V",
            "version",
            0,
            0,
            1,
            "print version and exit");
  INIT_OPT (main_opts->gen_opts.timelimit,
            1,
            "t",
            "time",
            0,
            0,
            -1,
            "set time limit");

  INIT_OPT (
      main_opts->input_opts.btor, 1, 0, "btor", 0, 0, 1, "force BTOR input");
  INIT_OPT (main_opts->input_opts.smt1,
            1,
            0,
            "smt1",
            0,
            0,
            1,
            "force SMT-LIB version 1 input");
  INIT_OPT (main_opts->input_opts.smt2,
            1,
            0,
            "smt2",
            0,
            0,
            1,
            "force SMT-LIB version 2 input");

  INIT_OPT (main_opts->output_opts.output,
            1,
            "o",
            "output",
            0,
            0,
            -1,
            "set output file for dumping");
  INIT_OPT (
      main_opts->output_opts.hex, 1, "x", "hex", 0, 0, 1, "hexadecimal output");
  INIT_OPT (
      main_opts->output_opts.decimal, 1, "d", "dec", 0, 0, 1, "decimal output");
  INIT_OPT (main_opts->output_opts.dump_btor,
            1,
            "db",
            "dump_btor",
            0,
            0,
            1,
            "dump formula in BTOR format");
  INIT_OPT (main_opts->output_opts.dump_smt2,
            1,
            "ds",
            "dump_smt",
            0,
            0,
            1,
            "dump formula in SMT-LIB v2 format");
  INIT_OPT (main_opts->output_opts.dump_smt1,
            1,
            "ds1",
            "dump_smt1",
            0,
            0,
            1,
            "dump formula in SMT-LIB v1 format");

  INIT_OPT (main_opts->inc_opts.all,
            1,
            "I",
            "incremental_all",
            0,
            0,
            1,
            "same as '-i' but solve all formulas");
  INIT_OPT (main_opts->inc_opts.look_ahead,
            1,
            0,
            "look_ahead",
            0,
            0,
            -1,
            "incremental lookahead mode width <w>");
  INIT_OPT (main_opts->inc_opts.in_depth,
            1,
            0,
            "in_depth",
            0,
            0,
            -1,
            "incremental in-depth mode width <w>");
  INIT_OPT (main_opts->inc_opts.interval,
            1,
            0,
            "interval",
            0,
            0,
            -1,
            "incremental interval mode width <w>");
}

static void
print_opt (BtorOpt *opt)
{
  assert (opt);

  char optstr[35], paramstr[10];
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

  sprintf (optstr,
           "  %s%s%s%s%s--%s%s%s",
           opt->shrt ? "-" : "",
           opt->shrt ? opt->shrt : "",
           opt->shrt && strlen (paramstr) > 0 ? " " : "",
           opt->shrt ? paramstr : "",
           opt->shrt ? ", " : "",
           opt->lng,
           strlen (paramstr) > 0 ? "=" : "",
           paramstr);

  len = strlen (optstr);
  for (i = len; i < 34; i++) optstr[i] = ' ';
  optstr[34] = '\0';
  printf ("%s %s\n", optstr, opt->desc);
  // TODO default values
}

static void
print_help (Btor *btor, BtorMainOpts *mo)
{
  assert (btor);
  assert (mo);

  BtorOpt *o, *oo;

  printf ("usage: boolector [<option>...][<input>]\n");
  printf ("\n");
  printf ("where <option> is one of the following:\n");
  printf ("\n");

  for (o = FIRST_OPT (mo->gen_opts); o <= LAST_OPT (mo->gen_opts); o++)
    print_opt (o);
  printf ("\n");

  for (o = FIRST_OPT (mo->input_opts); o <= LAST_OPT (mo->input_opts); o++)
    print_opt (o);
  printf ("\n");

  for (o = btor_first_opt (btor); o <= btor_last_opt (btor); o++)
  {
    if (o->internal) continue;
    if (!strcmp (o->lng, "incremental") || !strcmp (o->lng, "pretty_print"))
      printf ("\n");
    print_opt (o);
    if (!strcmp (o->lng, "incremental"))
    {
      for (oo = FIRST_OPT (mo->inc_opts); oo <= LAST_OPT (mo->inc_opts); oo++)
        print_opt (oo);
      printf ("\n");
    }
    else if (!strcmp (o->lng, "pretty_print"))
    {
      for (oo = FIRST_OPT (mo->output_opts); oo <= LAST_OPT (mo->output_opts);
           oo++)
        print_opt (oo);
      printf ("\n");
    }
    else if (!strcmp (o->lng, "rewrite_level_pbr"))
      printf ("\n");
  }
}

int
boolector_main (int argc, char **argv)
{
  Btor *btor;
  BtorMainOpts main_opts;

  btor = boolector_new ();

  init_main_opts (&main_opts);
  print_help (btor, &main_opts);
}
