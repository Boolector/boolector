/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2015 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
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
#include "btorutil.h"

#include <assert.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct BtorMainApp BtorMainApp;
static BtorMainApp *g_app;

static int g_verbosity;
static int g_set_alarm;
static int g_caught_sig;
#ifdef BTOR_HAVE_GETRUSAGE
static int g_start_time;
#endif

static void (*sig_int_handler) (int);
static void (*sig_segv_handler) (int);
static void (*sig_abrt_handler) (int);
static void (*sig_term_handler) (int);
static void (*sig_bus_handler) (int);

static void (*sig_alrm_handler) (int);

/*------------------------------------------------------------------------*/

typedef struct BtorMainOpt
{
  int general;      /* general option? */
  const char *shrt; /* short option identifier (may be 0) */
  const char *lng;  /* long option identifier */
  const char *desc; /* description */
  int val;          /* value */
  int dflt;         /* default value */
  int min;          /* min value */
  int max;          /* max value */
} BtorMainOpt;

typedef struct BtorMainOpts
{
  BtorMainOpt first; /* dummy for iteration */
  /* ------------------------------------ */
  BtorMainOpt help;
  BtorMainOpt copyright;
  BtorMainOpt version;
  BtorMainOpt time;
  BtorMainOpt output;
  BtorMainOpt smt2_model;
#ifdef BTOR_USE_LINGELING
  BtorMainOpt lingeling;
  BtorMainOpt lingeling_nofork;
  BtorMainOpt lingeling_opts;
#endif
#ifdef BTOR_USE_PICOSAT
  BtorMainOpt picosat;
#endif
#ifdef BTOR_USE_MINISAT
  BtorMainOpt minisat;
#endif
  /* ------------------------------------ */
  BtorMainOpt last; /* dummy for iteration */
} BtorMainOpts;

#define BTORMAIN_FIRST_OPT(OPTS) (&OPTS.first + 1)
#define BTORMAIN_LAST_OPT(OPTS) (&OPTS.last - 1)

#define BTORMAIN_INIT_OPT(OPT, GEN, SHRT, LNG, VAL, MIN, MAX, DESC) \
  do                                                                \
  {                                                                 \
    OPT.general = GEN;                                              \
    OPT.shrt    = SHRT;                                             \
    OPT.lng     = LNG;                                              \
    OPT.dflt = OPT.val = VAL;                                       \
    OPT.min            = MIN;                                       \
    OPT.max            = MAX;                                       \
    OPT.desc           = DESC;                                      \
  } while (0)

struct BtorMainApp
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
  char *outfile_name;
  int close_outfile;
};

static BtorMainApp *
btormain_new_btormain (Btor *btor)
{
  assert (btor);

  BtorMainApp *res;
  BtorMemMgr *mm;

  mm = btor_new_mem_mgr ();
  BTOR_CNEWN (mm, res, 1);
  res->mm          = mm;
  res->btor        = btor;
  res->infile      = stdin;
  res->infile_name = "<stdin>";
  res->outfile     = stdout;
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
      app->opts.help, 1, "h", "help", 0, 0, 1, "print this message and exit");
  BTORMAIN_INIT_OPT (app->opts.copyright,
                     1,
                     "c",
                     "copyright",
                     0,
                     0,
                     1,
                     "print copyright and exit");
  BTORMAIN_INIT_OPT (
      app->opts.version, 1, "V", "version", 0, 0, 1, "print version and exit");
  BTORMAIN_INIT_OPT (
      app->opts.time, 1, "t", "time", 0, 0, -1, "set time limit");
  BTORMAIN_INIT_OPT (app->opts.output,
                     1,
                     "o",
                     "output",
                     0,
                     0,
                     0,
                     "set output file for dumping");
  BTORMAIN_INIT_OPT (
      app->opts.smt2_model,
      0,
      0,
      "smt2_model",
      0,
      0,
      1,
      "print model in SMT-LIB v2 format if model generation is enabled");
#ifdef BTOR_USE_LINGELING
  BTORMAIN_INIT_OPT (app->opts.lingeling,
                     0,
                     0,
                     "lingeling",
                     0,
                     0,
                     1,
                     "force Lingeling as SAT solver");
  BTORMAIN_INIT_OPT (app->opts.lingeling_opts,
                     0,
                     0,
                     "lingeling_opts",
                     0,
                     0,
                     0,
                     "set lingeling option(s) '--<opt>=<val>'");
  BTORMAIN_INIT_OPT (app->opts.lingeling_nofork,
                     0,
                     0,
                     "lingeling_nofork",
                     0,
                     0,
                     0,
                     "do not use 'fork/clone' for Lingeling");
#endif
#ifdef BTOR_USE_PICOSAT
  BTORMAIN_INIT_OPT (app->opts.picosat,
                     0,
                     0,
                     "picosat",
                     0,
                     0,
                     1,
                     "force PicoSAT as SAT solver");
#endif
#ifdef BTOR_USE_MINISAT
  BTORMAIN_INIT_OPT (app->opts.minisat,
                     0,
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
btormain_msg (char *msg, ...)
{
  assert (msg);

  va_list list;
  va_start (list, msg);
  fprintf (stdout, "[btormain] ");
  vfprintf (stdout, msg, list);
  fprintf (stdout, "\n");
  va_end (list);
}

/*------------------------------------------------------------------------*/

#define LEN_OPTSTR 35
#define LEN_PARAMSTR 16
#define LEN_HELPSTR 80

static void
print_opt (BtorMainApp *app,
           const char *lng,
           const char *shrt,
           int dflt,
           const char *desc)
{
  assert (app);
  assert (lng);
  assert (desc);

  char optstr[LEN_OPTSTR], paramstr[LEN_PARAMSTR];
  char *descstr, descstrline[LEN_HELPSTR], *lngstr, *word;
  int i, j, len;
  BtorCharPtrStack words;

  if (!strcmp (lng, BTOR_OPT_INCREMENTAL_LOOK_AHEAD)
      || !strcmp (lng, BTOR_OPT_INCREMENTAL_IN_DEPTH)
      || !strcmp (lng, BTOR_OPT_INCREMENTAL_INTERVAL))
    sprintf (paramstr, "<w>");
  else if (!strcmp (lng, "time"))
    sprintf (paramstr, "<seconds>");
  else if (!strcmp (lng, "output"))
    sprintf (paramstr, "<file>");
  else if (!strcmp (lng, BTOR_OPT_REWRITE_LEVEL)
           || !strcmp (lng, BTOR_OPT_REWRITE_LEVEL_PBR)
           || !strcmp (lng, BTOR_OPT_PBRA_LOD_LIMIT)
           || !strcmp (lng, BTOR_OPT_PBRA_SAT_LIMIT)
           || !strcmp (lng, BTOR_OPT_PBRA_OPS_FACTOR)
           || !strcmp (lng, BTOR_OPT_SLS_MOVE_RAND_WALK_PROB))
    sprintf (paramstr, "<n>");
  else if (!strcmp (lng, "lingeling_opts"))
    sprintf (paramstr, "[,<opt>=<val>]+");
  else
    paramstr[0] = '\0';

  assert (!strcmp (lng, "lingeling_opts")
          || (shrt
              && (2 * strlen (paramstr) + strlen (shrt) + strlen (lng) + 7
                  <= LEN_OPTSTR))
          || (!shrt && (strlen (paramstr) + strlen (lng) + 7 <= LEN_OPTSTR)));

  /* option string ------------------------------------------ */
  memset (optstr, ' ', LEN_OPTSTR * sizeof (char));
  optstr[LEN_OPTSTR - 1] = '\0';
  len                    = strlen (lng);
  BTOR_NEWN (app->mm, lngstr, (len + 1) * sizeof (char));
  for (i = 0; i < len; i++) lngstr[i] = lng[i] == '_' ? '-' : lng[i];
  lngstr[len] = '\0';
  sprintf (optstr,
           "  %s%s%s%s%s--%s%s%s",
           shrt ? "-" : "",
           shrt ? shrt : "",
           shrt && strlen (paramstr) > 0 ? " " : "",
           shrt ? paramstr : "",
           shrt ? ", " : "",
           lngstr,
           strlen (paramstr) > 0 ? "=" : "",
           paramstr);
  BTOR_DELETEN (app->mm, lngstr, len + 1);
  len = strlen (optstr);
  for (i = len; i < LEN_OPTSTR - 1; i++) optstr[i] = ' ';
  optstr[LEN_OPTSTR - 1] = '\0';

  /* formatted description ---------------------------------- */
  /* append default value to description */
  if (!strcmp (lng, BTOR_OPT_REWRITE_LEVEL)
      || !strcmp (lng, BTOR_OPT_REWRITE_LEVEL_PBR)
      || !strcmp (lng, BTOR_OPT_PBRA_LOD_LIMIT)
      || !strcmp (lng, BTOR_OPT_PBRA_SAT_LIMIT)
      || !strcmp (lng, BTOR_OPT_PBRA_OPS_FACTOR)
      || !strcmp (lng, BTOR_OPT_DUAL_PROP) || !strcmp (lng, BTOR_OPT_JUST)
      || !strcmp (lng, BTOR_OPT_JUST_HEURISTIC) || !strcmp (lng, BTOR_OPT_UCOPT)
      || !strcmp (lng, BTOR_OPT_LAZY_SYNTHESIZE)
      || !strcmp (lng, BTOR_OPT_ELIMINATE_SLICES)
      || !strcmp (lng, BTOR_OPT_PRETTY_PRINT)
      || !strcmp (lng, BTOR_OPT_VERBOSITY) || !strcmp (lng, BTOR_OPT_LOGLEVEL)
      || !strcmp (lng, BTOR_OPT_SEED)
      || !strcmp (lng, BTOR_OPT_SLS_MOVE_RAND_WALK_PROB))
  {
    len = strlen (desc) + 3 + btor_num_digits_util (dflt);
    BTOR_CNEWN (app->mm, descstr, len + 1);
    sprintf (descstr, "%s [%d]", desc, dflt);
  }
  else
  {
    len = strlen (desc);
    BTOR_CNEWN (app->mm, descstr, len + 1);
    sprintf (descstr, "%s", desc);
  }
  BTOR_INIT_STACK (words);
  word = strtok (descstr, " ");
  while (word)
  {
    BTOR_PUSH_STACK (app->mm, words, btor_strdup (app->mm, word));
    word = strtok (0, " ");
  }
  BTOR_DELETEN (app->mm, descstr, len + 1);

  BTOR_CLRN (descstrline, LEN_HELPSTR);
  sprintf (descstrline, "%s ", optstr);
  i = 0;
  do
  {
    j = LEN_OPTSTR;
    for (; i < BTOR_COUNT_STACK (words); i++)
    {
      word = BTOR_PEEK_STACK (words, i);
      len  = strlen (word);

      /* word does not fit into remaining line */
      if (j + 1 + len >= LEN_HELPSTR) break;

      strcpy (descstrline + j, word);
      j += len;
      descstrline[j++] = ' ';
    }
    descstrline[j] = 0;
    fprintf (app->outfile, "%s\n", descstrline);
    BTOR_CLRN (descstrline, LEN_HELPSTR);
    memset (descstrline, ' ', LEN_OPTSTR * sizeof (char));
  } while (i < BTOR_COUNT_STACK (words));

  /* cleanup */
  while (!BTOR_EMPTY_STACK (words))
    btor_freestr (app->mm, BTOR_POP_STACK (words));
  BTOR_RELEASE_STACK (app->mm, words);
}

#define PRINT_MAIN_OPT(app, opt)                                        \
  do                                                                    \
  {                                                                     \
    print_opt (app, (opt)->lng, (opt)->shrt, (opt)->dflt, (opt)->desc); \
  } while (0)

#define BOOLECTOR_OPTS_INFO_MSG                                                \
  "All of the following options can also be used in the form '-<short "        \
  "name>=<int>'\n"                                                             \
  "and '--<long name>=<int>'. Flags are disabled with 0 and enabled with a "   \
  "pos.\n"                                                                     \
  "integer. Alternatively, use '-no-<short name>' and '--no-<long name>' "     \
  "for\n"                                                                      \
  "disabling, and '-<short name>' and '--<long name>' for enabling flags.\n"   \
  "Note that all of the following options can also be set via env. variables " \
  "of\n"                                                                       \
  "the form 'BTOR<capitalized long name without '-'>=<int>'.\n\n"

static void
print_help (BtorMainApp *app)
{
  assert (app);

  char *o;
  BtorMainOpt to;
  BtorMainOpt *mo;
  FILE *out = app->outfile;

  fprintf (out, "usage: boolector [<option>...][<input>]\n");
  fprintf (out, "\n");
  fprintf (out, "where <option> is one of the following:\n");
  fprintf (out, "\n");

  for (mo = BTORMAIN_FIRST_OPT (app->opts); mo <= BTORMAIN_LAST_OPT (app->opts);
       mo++)
  {
    if (!mo->general) continue;
    if (!strcmp (mo->lng, "time")) fprintf (out, "\n");
    PRINT_MAIN_OPT (app, mo);
  }

  fprintf (app->outfile, "\n");
  to.dflt = 0;
  to.shrt = "x";
  to.lng  = "hex";
  to.desc = "force hexadecimal number output";
  PRINT_MAIN_OPT (app, &to);
  to.shrt = "d";
  to.lng  = "dec";
  to.desc = "force decimal number output";
  PRINT_MAIN_OPT (app, &to);

  fprintf (app->outfile, "\n");
  to.shrt = 0;
  to.lng  = "btor";
  to.desc = "force BTOR input format";
  PRINT_MAIN_OPT (app, &to);
  to.shrt = 0;
  to.lng  = "smt2";
  to.desc = "force SMT-LIB v2 input format";
  PRINT_MAIN_OPT (app, &to);
  to.shrt = 0;
  to.lng  = "smt1";
  to.desc = "force SMT-LIB v1 input format";
  PRINT_MAIN_OPT (app, &to);
  fprintf (app->outfile, "\n");

  to.shrt = "db";
  to.lng  = "dump_btor";
  to.desc = "dump formula in BTOR format";
  PRINT_MAIN_OPT (app, &to);
#if 0
  to.shrt = "db2"; to.lng = "dump_btor2";
  to.desc = "dump formula in BTOR 2.0 format";
  PRINT_MAIN_OPT (app, &to);
#endif
  to.shrt = "ds";
  to.lng  = "dump_smt2";
  to.desc = "dump formula in SMT-LIB v2 format";
  PRINT_MAIN_OPT (app, &to);
  to.shrt = "ds1";
  to.lng  = "dump_smt1";
  to.desc = "dump formula in SMT-LIB v1 format";
  PRINT_MAIN_OPT (app, &to);
  fprintf (out, "\n");

  for (mo = BTORMAIN_FIRST_OPT (app->opts); mo <= BTORMAIN_LAST_OPT (app->opts);
       mo++)
  {
    if (mo->general) continue;
    PRINT_MAIN_OPT (app, mo);
    if (!strcmp (mo->lng, "smt2_model")) fprintf (out, "\n");
  }

  fprintf (out, "\n");

  fprintf (out, BOOLECTOR_OPTS_INFO_MSG);

  for (o = (char *) boolector_first_opt (app->btor); o;
       o = (char *) boolector_next_opt (app->btor, o))
  {
    if (!strcmp (o, BTOR_OPT_INPUT_FORMAT)
        || !strcmp (o, BTOR_OPT_OUTPUT_NUMBER_FORMAT)
        || !strcmp (o, BTOR_OPT_OUTPUT_FORMAT))
      continue;
    if (!strcmp (o, BTOR_OPT_INCREMENTAL) || !strcmp (o, BTOR_OPT_REWRITE_LEVEL)
        || !strcmp (o, BTOR_OPT_BETA_REDUCE_ALL)
        || !strcmp (o, BTOR_OPT_AUTO_CLEANUP) || !strcmp (o, BTOR_OPT_DUAL_PROP)
        || !strcmp (o, BTOR_OPT_LAZY_SYNTHESIZE))
      fprintf (out, "\n");
    print_opt (app,
               o,
               boolector_get_opt_shrt (app->btor, o),
               boolector_get_opt_dflt (app->btor, o),
               boolector_get_opt_desc (app->btor, o));
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
  fprintf (out, "Copyright (c) 2007-2015 Armin Biere\n");
  fprintf (out, "Copyright (c) 2012-2015 Aina Niemetz, Mathias Preiner\n");
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

static void
print_static_stats (int sat_res)
{
#ifdef BTOR_HAVE_GETRUSAGE
  double delta_time = delta_time = btor_time_stamp () - g_start_time;
  btormain_msg ("%.1f seconds", delta_time);
  btormain_msg ("%s",
                sat_res == BOOLECTOR_SAT
                    ? "sat"
                    : (sat_res == BOOLECTOR_UNSAT ? "unsat" : "unknown"));
#else
  btormain_msg ("can not determine run-time in seconds (no getrusage)");
#endif
}

static void
print_sat_result (BtorMainApp *app, int sat_result)
{
  assert (app);
  if (sat_result == BOOLECTOR_UNSAT)
    fprintf (app->outfile, "unsat\n");
  else if (sat_result == BOOLECTOR_SAT)
    fprintf (app->outfile, "sat\n");
  else
  {
    assert (sat_result == BOOLECTOR_UNKNOWN);
    fprintf (app->outfile, "unknown\n");
  }
}

/*------------------------------------------------------------------------*/

static void
reset_sig_handlers (void)
{
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
  (void) signal (SIGBUS, sig_bus_handler);
}

static void
catch_sig (int sig)
{
  if (!g_caught_sig)
  {
    g_caught_sig = 1;
    btormain_msg ("CAUGHT SIGNAL %d", sig);
    fputs ("unknown\n", stdout);
    fflush (stdout);
    if (g_verbosity > 0)
    {
      boolector_print_stats (g_app->btor);
      print_static_stats (0);
      btormain_msg ("CAUGHT SIGNAL %d", sig);
    }
  }
  reset_sig_handlers ();
  raise (sig);
  exit (sig);
}

static void
set_sig_handlers (void)
{
  sig_int_handler  = signal (SIGINT, catch_sig);
  sig_segv_handler = signal (SIGSEGV, catch_sig);
  sig_abrt_handler = signal (SIGABRT, catch_sig);
  sig_term_handler = signal (SIGTERM, catch_sig);
  sig_bus_handler  = signal (SIGBUS, catch_sig);
}

static void
reset_alarm (void)
{
  alarm (0);
  (void) signal (SIGALRM, sig_alrm_handler);
}

static void
catch_alarm (int sig)
{
  (void) sig;
  assert (sig == SIGALRM);
  if (g_set_alarm > 0)
  {
    btormain_msg ("ALARM TRIGGERED: time limit %d seconds reached",
                  g_set_alarm);
    fputs ("unknown\n", stdout);
    fflush (stdout);
    if (g_verbosity > 0)
    {
      boolector_print_stats (g_app->btor);
      print_static_stats (0);
    }
  }
  reset_alarm ();
  exit (0);
}

static void
set_alarm (void)
{
  sig_alrm_handler = signal (SIGALRM, catch_alarm);
  assert (g_set_alarm > 0);
  alarm (g_set_alarm);
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

#define IS_MAIN_OPT(lng_opt)                          \
  ((isshrt && g_app->opts.lng_opt.shrt                \
    && !strcmp (opt.start, g_app->opts.lng_opt.shrt)) \
   || (!isshrt && !strcmp (opt.start, g_app->opts.lng_opt.lng)))

#define IS_BTOR_OPT(shrt_opt, lng_opt)            \
  ((isshrt && oshrt && !strcmp (oshrt, shrt_opt)) \
   || (!isshrt && !strcmp (o, lng_opt)))

#define HAS_UNEXPECTED_ARGUMENT ((readval == 2 || (readval == 1 && isint)))
#define HAS_MISSING_ARGUMENT ((!readval || (readval == 1 && !isint)))
#define HAS_INVALID_ARGUMENT ((readval == 2 && !isint))

int
boolector_main (int argc, char **argv)
{
  int i, j, len, readval, val, format;
  int isshrt, isdisable, isint;
  int res, parse_res, parse_status, sat_res;
  int mgen, pmodel, inc, dump, force_sat;
  char *arg, *cmd, *valstr, *tmp, *parse_err_msg;
  char *o;
  const char *oshrt;
#ifdef BTOR_USE_LINGELING
  char *lglopts = 0;
#endif
  BtorCharStack opt, errarg;

#ifdef BTOR_HAVE_GETRUSAGE
  g_start_time = btor_time_stamp ();
#endif

  g_app = btormain_new_btormain (boolector_new ());
  btormain_init_opts (g_app);

  res          = BTOR_UNKNOWN_EXIT;
  parse_res    = BOOLECTOR_UNKNOWN;
  parse_status = BOOLECTOR_UNKNOWN;
  sat_res      = BOOLECTOR_UNKNOWN;
  inc          = 0;
  mgen         = 0;
  pmodel       = 0;
  dump         = 0;
  force_sat    = 0;

  mgen = boolector_get_opt_val (g_app->btor, BTOR_OPT_MODEL_GEN);

  BTOR_INIT_STACK (opt);
  BTOR_INIT_STACK (errarg);

  for (i = 1; i < argc; i++)
  {
    arg       = argv[i];
    len       = strlen (argv[i]);
    isshrt    = 0;
    isdisable = 0;
    isint     = 0;
    readval   = 0;
    val       = 0;
    valstr    = 0;

    /* input file */

    if (arg[0] != '-')
    {
      if (g_app->close_infile)
      {
        btormain_error (g_app, "multiple input files");
        goto DONE;
      }

      g_app->infile_name = arg;

      if (!btor_file_exists (g_app->infile_name))
      {
        g_app->infile = 0;
      }
      else if (has_suffix (g_app->infile_name, ".gz")
               || has_suffix (g_app->infile_name, ".bz2")
               || has_suffix (g_app->infile_name, ".7z"))
      {
        BTOR_NEWN (g_app->mm, cmd, len + 40);
        if (has_suffix (g_app->infile_name, ".gz"))
          sprintf (cmd, "gunzip -c %s", g_app->infile_name);
        else if (has_suffix (g_app->infile_name, ".bz2"))
          sprintf (cmd, "bzcat %s", g_app->infile_name);
        else if (has_suffix (g_app->infile_name, ".7z"))
          sprintf (cmd, "7z x -so %s > /dev/null", g_app->infile_name);

        if ((g_app->infile = popen (cmd, "r"))) g_app->close_infile = 2;

        BTOR_DELETEN (g_app->mm, cmd, len + 40);
      }
      else if ((g_app->infile = fopen (g_app->infile_name, "r")))
      {
        g_app->close_infile = 1;
      }

      if (!g_app->infile)
      {
        btormain_error (g_app, "can not read '%s'", g_app->infile_name);
        goto DONE;
      }

      continue;
    }

    /* options */

    BTOR_RESET_STACK (errarg);
    BTOR_RESET_STACK (opt);

    /* save original option string (without arguments) for error messages */
    for (j = 0; j < len && arg[j] != '='; j++)
      BTOR_PUSH_STACK (g_app->mm, errarg, arg[j]);
    BTOR_PUSH_STACK (g_app->mm, errarg, '\0');

    /* extract option name */
    isshrt = arg[1] == '-' ? 0 : 1;
    j      = isshrt ? 1 : 2;
    isdisable =
        len > 3 && arg[j] == 'n' && arg[j + 1] == 'o' && arg[j + 2] == '-';
    for (j = isdisable ? j + 3 : j; j < len && arg[j] != '='; j++)
      BTOR_PUSH_STACK (g_app->mm, opt, arg[j] == '-' ? '_' : arg[j]);
    BTOR_PUSH_STACK (g_app->mm, opt, '\0');

    /* extract option argument (if any) */
    if (arg[j] == '=')
    {
      valstr = arg + j + 1;
      if (valstr[0] != 0)
      {
        readval = 2;
        val     = (int) strtol (valstr, &tmp, 10);
        isint   = tmp[0] == 0;
      }
    }
    else if ((readval = i + 1 < argc && argv[i + 1][0] != '-'))
    {
      valstr = argv[i + 1];
      val    = (int) strtol (valstr, &tmp, 10);
      if (tmp[0] == 0)
      {
        isint = 1;
        i += 1;
      }
    }

    /* set options */
    /* >> main options */
    if (IS_MAIN_OPT (help))
    {
      if (isdisable)
      {
      ERR_INVALID_OPTION:
        btormain_error (g_app, "invalid option '%s'", errarg.start);
        goto DONE;
      }

      if (HAS_UNEXPECTED_ARGUMENT)
      {
      ERR_UNEXPECTED_ARGUMENT:
        btormain_error (
            g_app, "option '%s' does not expect an argument", errarg.start);
        goto DONE;
      }

      print_help (g_app);
      goto DONE;
    }
    else if (IS_MAIN_OPT (copyright))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      print_copyright (g_app);
      goto DONE;
    }
    else if (IS_MAIN_OPT (version))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      print_version (g_app);
      goto DONE;
    }
    else if (IS_MAIN_OPT (time))
    {
      if (isdisable) goto ERR_INVALID_OPTION;

      if (HAS_MISSING_ARGUMENT)
      {
      ERR_MISSING_ARGUMENT:
        btormain_error (g_app, "missing argument for '%s'", errarg.start);
        goto DONE;
      }

      if (HAS_INVALID_ARGUMENT)
      {
      ERR_INVALID_ARGUMENT:
        btormain_error (
            g_app, "invalid argument for '%s', expected int", errarg.start);
        goto DONE;
      }

      g_set_alarm = val;
    }
    else if (IS_MAIN_OPT (output))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (!readval) goto ERR_MISSING_ARGUMENT;

      if (g_app->close_outfile)
      {
        btormain_error (g_app, "multiple output files");
        goto DONE;
      }

      g_app->outfile_name = valstr;
      if (readval == 1) i += 1;
    }
    else if (IS_MAIN_OPT (smt2_model))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      g_app->opts.smt2_model.val += 1;
    }
    /* >> sat solver options */
#ifdef BTOR_USE_LINGELING
    else if (IS_MAIN_OPT (lingeling))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      g_app->opts.lingeling.val = 1;
    }
    else if (IS_MAIN_OPT (lingeling_nofork))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      g_app->opts.lingeling_nofork.val = 1;
    }
    else if (IS_MAIN_OPT (lingeling_opts))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (!readval) goto ERR_MISSING_ARGUMENT;

      lglopts = valstr;
    }
#endif
#ifdef BTOR_USE_PICOSAT
    else if (IS_MAIN_OPT (picosat))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;
      g_app->opts.picosat.val = 1;
    }
#endif
#ifdef BTOR_USE_MINISAT
    else if (IS_MAIN_OPT (minisat))
    {
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;
      g_app->opts.minisat.val = 1;
    }
#endif

    /* >> meta options */
    else if (!strcmp (opt.start, "btor"))
    {
      format = BTOR_INPUT_FORMAT_BTOR;
    SET_INPUT_FORMAT:
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      boolector_set_opt (g_app->btor, BTOR_OPT_INPUT_FORMAT, format);
    }
    else if (!strcmp (opt.start, "smt2"))
    {
      format = BTOR_INPUT_FORMAT_SMT2;
      goto SET_INPUT_FORMAT;
    }
    else if (!strcmp (opt.start, "smt1"))
    {
      format = BTOR_INPUT_FORMAT_SMT1;
      goto SET_INPUT_FORMAT;
    }
    else if (!strcmp (opt.start, "x") || !strcmp (opt.start, "hex"))
    {
      format = BTOR_OUTPUT_BASE_HEX;
    SET_OUTPUT_NUMBER_FORMAT:
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      boolector_set_opt (g_app->btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, format);
    }
    else if (!strcmp (opt.start, "d") || !strcmp (opt.start, "dec"))
    {
      format = BTOR_OUTPUT_BASE_DEC;
      goto SET_OUTPUT_NUMBER_FORMAT;
    }
    else if (!strcmp (opt.start, "db") || !strcmp (opt.start, "dump_btor"))
    {
      dump = BTOR_OUTPUT_FORMAT_BTOR;
    SET_OUTPUT_FORMAT:
      if (isdisable) goto ERR_INVALID_OPTION;
      if (HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

      boolector_set_opt (g_app->btor, BTOR_OPT_OUTPUT_FORMAT, dump);
      boolector_set_opt (g_app->btor, BTOR_OPT_PARSE_INTERACTIVE, 0);
    }
#if 0
      else if (!strcmp (opt.start, "db2") || !strcmp (opt.start, "dump_btor2"))
	{
	  dump = BTOR_OUTPUT_FORMAT_BTOR2;
	  goto SET_OUTPUT_FORMAT;
	}
#endif
    else if (!strcmp (opt.start, "ds") || !strcmp (opt.start, "dump_smt2"))
    {
      dump = BTOR_OUTPUT_FORMAT_SMT2;
      goto SET_OUTPUT_FORMAT;
    }
    else if (!strcmp (opt.start, "ds1") || !strcmp (opt.start, "dump_smt1"))
    {
      dump = BTOR_OUTPUT_FORMAT_SMT1;
      goto SET_OUTPUT_FORMAT;
    }

    /* >> btor options */
    else
    {
      for (o = (char *) boolector_first_opt (g_app->btor); o;
           o = (char *) boolector_next_opt (g_app->btor, o))
      {
        oshrt = boolector_get_opt_shrt (g_app->btor, o);
        if ((isshrt && oshrt && !strcmp (oshrt, opt.start))
            || (!isshrt && !strcmp (o, opt.start)))
          break;
      }

      if (!o) goto ERR_INVALID_OPTION;

      /* flags */
      if (IS_BTOR_OPT ("i", BTOR_OPT_INCREMENTAL))
      {
        if (readval == 2 && !isint) goto ERR_INVALID_ARGUMENT;

        inc = isdisable || (readval && isint && val == 0)
                  ? 0
                  : inc | BTOR_PARSE_MODE_BASIC_INCREMENTAL;
        boolector_set_opt (g_app->btor, o, inc);
      }
      else if (IS_BTOR_OPT ("I", BTOR_OPT_INCREMENTAL_ALL))
      {
        if (readval == 2 && !isint) goto ERR_INVALID_ARGUMENT;

        if (isdisable || (readval && isint && val == 0))
          boolector_set_opt (g_app->btor, o, 0);
        else
        {
          boolector_set_opt (
              g_app->btor, o, BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE);
          inc |= BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE;
          boolector_set_opt (g_app->btor, BTOR_OPT_INCREMENTAL, inc);
        }
      }
      else if (IS_BTOR_OPT ("m", BTOR_OPT_MODEL_GEN))
      {
        if (readval == 2 && !isint) goto ERR_INVALID_ARGUMENT;

        if (isdisable || (readval && isint && val == 0))
        {
          mgen   = 0;
          pmodel = 0;
        }
        else
        {
          mgen += 1;
          pmodel = 1;
        }
      }
      /* options requiring an integer argument */
      else if (IS_BTOR_OPT ("rwl", BTOR_OPT_REWRITE_LEVEL)
               || IS_BTOR_OPT ("", BTOR_OPT_REWRITE_LEVEL_PBR)
               || IS_BTOR_OPT ("", BTOR_OPT_PBRA_LOD_LIMIT)
               || IS_BTOR_OPT ("", BTOR_OPT_PBRA_SAT_LIMIT)
               || IS_BTOR_OPT ("", BTOR_OPT_PBRA_OPS_FACTOR))
      {
        if (!readval) goto ERR_MISSING_ARGUMENT;
        if (!isint) goto ERR_INVALID_ARGUMENT;
        boolector_set_opt (g_app->btor, o, val);
      }
      /* options that can be used as a flag or with an argument */
      else
      {
        if (isdisable && HAS_UNEXPECTED_ARGUMENT) goto ERR_UNEXPECTED_ARGUMENT;

        if ((IS_BTOR_OPT ("dp", BTOR_OPT_DUAL_PROP)
             && boolector_get_opt_val (g_app->btor, BTOR_OPT_JUST))
            || (IS_BTOR_OPT ("ju", BTOR_OPT_JUST)
                && boolector_get_opt_val (g_app->btor, BTOR_OPT_DUAL_PROP)))
        {
          btormain_error (g_app,
                          "can only set one out of '--%s' and '--%s'",
                          BTOR_OPT_DUAL_PROP,
                          BTOR_OPT_JUST);
          goto DONE;
        }

        if (isdisable || (readval && isint && val == 0))
          boolector_set_opt (g_app->btor, o, 0);
        else if (readval && isint)
          boolector_set_opt (g_app->btor, o, val);
        else
          boolector_set_opt (
              g_app->btor, o, boolector_get_opt_val (g_app->btor, o) + 1);
      }
    }
  }

  assert (!g_app->done && !g_app->err);

  g_verbosity = boolector_get_opt_val (g_app->btor, BTOR_OPT_VERBOSITY);

  /* open output file */
  if (g_app->outfile_name)
  {
    if (!strcmp (g_app->outfile_name, g_app->infile_name))
    {
      btormain_error (g_app, "input and output file must not be the same");
      goto DONE;
    }

    g_app->outfile = fopen (g_app->outfile_name, "w");
    if (!g_app->outfile)
    {
      btormain_error (g_app, "can not create '%s'", g_app->outfile_name);
      goto DONE;
    }
    g_app->close_outfile = 1;
  }

  /* automatically enable model generation if smt2 models are forced */
  mgen =
      !mgen && g_app->opts.smt2_model.val ? g_app->opts.smt2_model.val : mgen;

  // TODO: disabling model generation not yet supported (ma)
  if (mgen > 0) boolector_set_opt (g_app->btor, BTOR_OPT_MODEL_GEN, mgen);

    /* force sat solver */
#ifdef BTOR_USE_LINGELING
  if (g_app->opts.lingeling.val)
  {
    if (force_sat++)
    {
      btormain_error (g_app, "multiple sat solvers forced");
      goto DONE;
    }
    if (!boolector_set_sat_solver_lingeling (
            g_app->btor, lglopts, g_app->opts.lingeling_nofork.val))
      btormain_error (g_app, "invalid options to Lingeling: '%s'", lglopts);
  }
#endif
#ifdef BTOR_USE_PICOSAT
  if (g_app->opts.picosat.val)
  {
    if (force_sat++)
    {
      btormain_error (g_app, "multiple sat solvers forced");
      goto DONE;
    }
    boolector_set_sat_solver_picosat (g_app->btor);
  }
#endif
#ifdef BTOR_USE_MINISAT
  if (g_app->opts.minisat.val)
  {
    if (force_sat++)
    {
      btormain_error (g_app, "multiple sat solvers forced");
      goto DONE;
    }
    boolector_set_sat_solver_minisat (g_app->btor);
  }
#endif
#ifdef BTOR_USE_LINGELING
  if (g_app->opts.lingeling_nofork.val && !g_app->opts.lingeling.val)
  {
    btormain_error (g_app,
                    "option '%s' is invalid if Lingeling is not "
                    "configured as SAT solver",
                    errarg.start);
    goto DONE;
  }
#endif

  /* print verbose info and set signal handlers */
  if (g_verbosity)
  {
    if (inc) btormain_msg ("incremental mode through command line option");
    btormain_msg ("Boolector Version %s %s", BTOR_VERSION, BTOR_ID);
    btormain_msg ("%s", BTOR_CFLAGS);
    btormain_msg ("released %s", BTOR_RELEASED);
    btormain_msg ("compiled %s", BTOR_COMPILED);
    if (*BTOR_CC) btormain_msg ("%s", BTOR_CC);
    btormain_msg ("setting signal handlers");
  }
  set_sig_handlers ();

  /* set alarm */
  if (g_set_alarm)
  {
    if (g_verbosity)
      btormain_msg ("setting time limit to %d seconds", g_set_alarm);
    set_alarm ();
  }
  else if (g_verbosity)
    btormain_msg ("no time limit given");

  if (inc && g_verbosity) btormain_msg ("starting incremental mode");

  /* parse */
  if ((val = boolector_get_opt_val (g_app->btor, "input_format")))
  {
    switch (val)
    {
      case BTOR_INPUT_FORMAT_BTOR:
        if (g_verbosity)
          btormain_msg ("BTOR input forced through cmd line options");
        parse_res = boolector_parse_btor (g_app->btor,
                                          g_app->infile,
                                          g_app->infile_name,
                                          g_app->outfile,
                                          &parse_err_msg,
                                          &parse_status);
        break;
      case BTOR_INPUT_FORMAT_SMT1:
        if (g_verbosity)
          btormain_msg ("SMT-LIB v1 input forced through cmd line options");
        parse_res = boolector_parse_smt1 (g_app->btor,
                                          g_app->infile,
                                          g_app->infile_name,
                                          g_app->outfile,
                                          &parse_err_msg,
                                          &parse_status);
        break;
      case BTOR_INPUT_FORMAT_SMT2:
        if (g_verbosity)
          btormain_msg ("SMT-LIB v2 input forced through cmd line options");
        parse_res = boolector_parse_smt2 (g_app->btor,
                                          g_app->infile,
                                          g_app->infile_name,
                                          g_app->outfile,
                                          &parse_err_msg,
                                          &parse_status);
        break;
    }
  }
  else
    parse_res = boolector_parse (g_app->btor,
                                 g_app->infile,
                                 g_app->infile_name,
                                 g_app->outfile,
                                 &parse_err_msg,
                                 &parse_status);

  /* verbosity may have been increased via input (set-option) */
  g_verbosity = boolector_get_opt_val (g_app->btor, BTOR_OPT_VERBOSITY);

  if (parse_res == BOOLECTOR_PARSE_ERROR)
  {
    /* NOTE: do not use btormain_error here as 'parse_err_msg' must not be
     * treated as format string --- it might contain unescaped '%' due to
     * invalid user input. */
    fprintf (stderr, "boolector: %s\n", parse_err_msg);
    g_app->err = BTOR_ERR_EXIT;
    goto DONE;
  }

  /* incremental mode */
  if (inc)
  {
    if (parse_res == BOOLECTOR_SAT)
    {
      if (g_verbosity) btormain_msg ("one formula SAT in incremental mode");
      sat_res = BOOLECTOR_SAT;
    }
    else if (parse_res == BOOLECTOR_UNSAT)
    {
      if (g_verbosity) btormain_msg ("all formulas UNSAT in incremental mode");
      sat_res = BOOLECTOR_UNSAT;
    }

    if (g_verbosity) boolector_print_stats (g_app->btor);

    if (pmodel && sat_res == BOOLECTOR_SAT)
    {
      assert (boolector_get_opt_val (g_app->btor, BTOR_OPT_MODEL_GEN));
      boolector_print_model (g_app->btor,
                             g_app->opts.smt2_model.val ? "smt2" : "btor",
                             g_app->outfile);
    }

    goto DONE;
  }
  /* we don't dump formula(s) in incremental mode */
  else if (dump)
  {
    switch (dump)
    {
      case BTOR_OUTPUT_FORMAT_BTOR:
        if (g_verbosity) btormain_msg ("dumping BTOR expressions");
        boolector_dump_btor (g_app->btor, g_app->outfile);
        break;
#if 0
	  case BTOR_OUTPUT_FORMAT_BTOR2:
	    if (g_verbosity) btormain_msg ("dumping BTOR 2.0 expressions");
	    boolector_dump_btor2 (g_app->btor, g_app->outfile);
	    break;
#endif
      case BTOR_OUTPUT_FORMAT_SMT1:
        if (g_verbosity) btormain_msg ("dumping in SMT-LIB v1 format");
        boolector_dump_smt1 (g_app->btor, g_app->outfile);
        break;
      default:
        assert (dump == BTOR_OUTPUT_FORMAT_SMT2);
        if (g_verbosity) btormain_msg ("dumping in SMT 2.0 format");
        boolector_dump_smt2 (g_app->btor, g_app->outfile);
    }

    if (g_verbosity) boolector_print_stats (g_app->btor);

    goto DONE;
  }

  /* call sat (if not in incremental mode) */
  if (parse_res != BOOLECTOR_SAT && parse_res != BOOLECTOR_UNSAT
      && !boolector_terminate (g_app->btor))
  {
    sat_res = boolector_sat (g_app->btor);
    print_sat_result (g_app, sat_res);
  }
  else
    sat_res = parse_res;

  assert (boolector_terminate (g_app->btor) || sat_res != BOOLECTOR_UNKNOWN);

  /* check if status is equal to benchmark status (if provided) */
  if (sat_res == BOOLECTOR_SAT && parse_status == BOOLECTOR_UNSAT)
    btormain_error (g_app,
                    "'sat' but status of benchmark in '%s' is 'unsat'",
                    g_app->infile_name);
  else if (sat_res == BOOLECTOR_UNSAT && parse_status == BOOLECTOR_SAT)
    btormain_error (g_app,
                    "'unsat' but status of benchmark in '%s' is 'sat'",
                    g_app->infile_name);

  /* print stats */
  if (g_verbosity)
  {
    boolector_print_stats (g_app->btor);
    print_static_stats (sat_res);
  }

  /* print model */
  if (pmodel && sat_res == BOOLECTOR_SAT)
  {
    assert (boolector_get_opt_val (g_app->btor, BTOR_OPT_MODEL_GEN));
    boolector_print_model (g_app->btor,
                           g_app->opts.smt2_model.val ? "smt2" : "btor",
                           g_app->outfile);
  }

DONE:
  if (g_app->done)
    res = BTOR_SUCC_EXIT;
  else if (g_app->err)
    res = BTOR_ERR_EXIT;
  else if (sat_res == BOOLECTOR_UNSAT)
    res = BTOR_UNSAT_EXIT;
  else if (sat_res == BOOLECTOR_SAT)
    res = BTOR_SAT_EXIT;

  assert (res == BTOR_ERR_EXIT || res == BTOR_SUCC_EXIT || res == BTOR_SAT_EXIT
          || res == BTOR_UNSAT_EXIT || res == BTOR_UNKNOWN_EXIT);

  if (g_app->close_infile == 1)
    fclose (g_app->infile);
  else if (g_app->close_infile == 2)
    pclose (g_app->infile);
  if (g_app->close_outfile) fclose (g_app->outfile);

  BTOR_RELEASE_STACK (g_app->mm, errarg);
  BTOR_RELEASE_STACK (g_app->mm, opt);
  btormain_delete_btormain (g_app);
  reset_sig_handlers ();

  return res;
}
