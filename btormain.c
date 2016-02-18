/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2016 Aina Niemetz.
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
#include "btoropt.h"
#include "btorparse.h"
#include "utils/btorhashptr.h"
#include "utils/btoriter.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
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

enum BtorMainOptArg
{
  BTORMAIN_OPT_ARG_NONE,
  BTORMAIN_OPT_ARG_INT,
  BTORMAIN_OPT_ARG_STR,
};
typedef enum BtorMainOptArg BtorMainOptArg;

typedef struct BtorMainOpt
{
  bool general;       /* general option? */
  const char *shrt;   /* short option identifier (may be 0) */
  const char *lng;    /* long option identifier */
  const char *desc;   /* description */
  uint32_t val;       /* value */
  uint32_t dflt;      /* default value */
  uint32_t min;       /* min value */
  uint32_t max;       /* max value */
  bool candisable;    /* can be disabled via '-(-)no-XX'? */
  BtorMainOptArg arg; /* expects argument? */
} BtorMainOpt;

static void
init_main_opt (BtorPtrHashTable *options,
               bool general,
               char *lng,
               char *shrt,
               uint32_t val,
               uint32_t min,
               uint32_t max,
               bool candisable,
               BtorMainOptArg arg,
               char *desc)
{
  assert (options);
  assert (lng);
  assert (desc);
  assert (max <= UINT_MAX);
  assert (min <= val);
  assert (val <= max);

  BtorMainOpt *opt;

  assert (!btor_get_ptr_hash_table (options, lng));
  BTOR_CNEW (options->mm, opt);
  opt->general    = general;
  opt->lng        = lng;
  opt->shrt       = shrt;
  opt->val        = val;
  opt->dflt       = val;
  opt->min        = min;
  opt->max        = max;
  opt->desc       = desc;
  opt->candisable = candisable;
  opt->arg        = arg;

  btor_add_ptr_hash_table (options, lng)->data.as_ptr = opt;
}

static void
btormain_init_opts (BtorPtrHashTable *options)
{
  assert (options);

  init_main_opt (options,
                 true,
                 "help",
                 "h",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print this message and exit");
  init_main_opt (options,
                 true,
                 "copyright",
                 "c",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print copyright and exit");
  init_main_opt (options,
                 true,
                 "version",
                 "V",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print version and exit");
  init_main_opt (options,
                 true,
                 "time",
                 "t",
                 0,
                 0,
                 UINT_MAX,
                 false,
                 BTORMAIN_OPT_ARG_INT,
                 "set time limit");
  init_main_opt (options,
                 true,
                 "output",
                 "o",
                 0,
                 0,
                 0,
                 false,
                 BTORMAIN_OPT_ARG_STR,
                 "set output file for dumping");
  init_main_opt (options,
                 true,
                 BTOR_OPT_ENGINE,
                 "E",
                 BTOR_ENGINE_DFLT,
                 BTOR_ENGINE_MIN,
                 BTOR_ENGINE_MAX,
                 false,
                 BTORMAIN_OPT_ARG_STR,
                 "set engine (core sls) [core]");
  init_main_opt (options,
                 true,
                 BTOR_OPT_SAT_ENGINE,
                 "SE",
                 BTOR_SAT_ENGINE_DFLT,
                 BTOR_SAT_ENGINE_MIN + 1,
                 BTOR_SAT_ENGINE_MAX - 1,
                 false,
                 BTORMAIN_OPT_ARG_STR,
                 "set sat solver");
#ifdef BTOR_USE_LINGELING
  init_main_opt (options,
                 true,
                 "lingeling_nofork",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "do not use 'fork/clone' for Lingeling");
  init_main_opt (options,
                 true,
                 "lingeling_opts",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_STR,
                 "set lingeling option(s) '--<opt>=<val>'");
#endif
  init_main_opt (options,
                 true,
                 "hex",
                 "x",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force hexadecimal number output");
  init_main_opt (options,
                 true,
                 "dec",
                 "d",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force decimal number output");
  init_main_opt (options,
                 true,
                 "btor",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force BTOR input format");
  init_main_opt (options,
                 true,
                 "smt2",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force SMT-LIB v2 input format");
  init_main_opt (options,
                 true,
                 "smt1",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force SMT-LIB v1 input format");
  init_main_opt (options,
                 true,
                 "dump_btor",
                 "db",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump formula in BTOR format");
#if 0
  init_main_opt (options, true, "dump_btor2", "db2", 0, 0, 1,
		 false, BTORMAIN_OPT_ARG_NONE,
		 "dump formula in BTOR 2.0 format");
#endif
  init_main_opt (options,
                 true,
                 "dump_smt",
                 "ds",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump formula in SMT-LIB v2 format");
  init_main_opt (options,
                 true,
                 "dump_aag",
                 "daa",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump QF_BV formula in ascii AIGER format");
  init_main_opt (options,
                 true,
                 "dump_aig",
                 "dai",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump QF_BV formula in binary AIGER format");
  init_main_opt (options,
                 true,
                 "dump_aiger_merge",
                 "dam",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "merge all roots of AIG [0]");

  init_main_opt (options,
                 false,
                 "smt2_model",
                 0,
                 0,
                 0,
                 1,
                 true,
                 BTORMAIN_OPT_ARG_INT,
                 "print model in SMT-LIB v2 format "
                 "if model generation is enabled");
}

/*------------------------------------------------------------------------*/

struct BtorMainApp
{
  Btor *btor;
  BtorMemMgr *mm;
  BtorPtrHashTable *opts;
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
  res->opts        = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_str, (BtorCmpPtr) strcmp);
  btormain_init_opts (res->opts);
  return res;
}

static void
btormain_delete_btormain (BtorMainApp *app)
{
  assert (app);

  BtorMemMgr *mm;
  BtorHashTableIterator it;

  mm = app->mm;
  assert (app->opts);
  btor_init_hash_table_iterator (&it, app->opts);
  while (btor_has_next_hash_table_iterator (&it))
    BTOR_DELETE (
        mm, (BtorMainOpt *) btor_next_data_hash_table_iterator (&it)->as_ptr);
  btor_delete_ptr_hash_table (app->opts);
  boolector_delete (app->btor);
  BTOR_DELETE (mm, app);
  btor_delete_mem_mgr (mm);
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
  fprintf (stdout, "[btor>main] ");
  vfprintf (stdout, msg, list);
  fprintf (stdout, "\n");
  va_end (list);
}

/*------------------------------------------------------------------------*/

#define LEN_OPTSTR 38
#define LEN_PARAMSTR 16
#define LEN_HELPSTR 80

#define IS_OPT(optlng, lng) (!strcmp (optlng, lng))

static void
print_opt (BtorMainApp *app,
           const char *lng,
           const char *shrt,
           int dflt,
           const char *desc,
           int print_dflt)
{
  assert (app);
  assert (lng);
  assert (desc);

  char optstr[LEN_OPTSTR], paramstr[LEN_PARAMSTR];
  char *descstr, descstrline[LEN_HELPSTR], *lngstr, *word;
  int i, j, len;
  BtorCharPtrStack words;

  if (!strcmp (lng, "time"))
    sprintf (paramstr, "<seconds>");
  else if (!strcmp (lng, "output"))
    sprintf (paramstr, "<file>");
  else if (!strcmp (lng, BTOR_OPT_ENGINE) || !strcmp (lng, BTOR_OPT_SAT_ENGINE))
    sprintf (paramstr, "<engine>");
  else if (!strcmp (lng, BTOR_OPT_REWRITE_LEVEL)
           || !strcmp (lng, BTOR_OPT_SLS_MOVE_RAND_WALK_PROB)
           || !strcmp (lng, BTOR_OPT_SLS_MOVE_PROP_FLIP_COND_PROB))
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
  if (print_dflt)
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

#define PRINT_MAIN_OPT(app, opt)                                           \
  do                                                                       \
  {                                                                        \
    print_opt (app, (opt)->lng, (opt)->shrt, (opt)->dflt, (opt)->desc, 0); \
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
  "the form 'BTOR<capitalized long name without '-' and ':'>=<int>'.\n\n"

static void
print_help (BtorMainApp *app)
{
  assert (app);

  char *o;
  BtorMainOpt *mo;
  BtorHashTableIterator it;
  FILE *out = app->outfile;

  fprintf (out, "usage: boolector [<option>...][<input>]\n");
  fprintf (out, "\n");
  fprintf (out, "where <option> is one of the following:\n");
  fprintf (out, "\n");

  btor_init_hash_table_iterator (&it, app->opts);
  while (btor_has_next_hash_table_iterator (&it))
  {
    mo = btor_next_data_hash_table_iterator (&it)->as_ptr;
    if (!mo->general) continue;
    if (IS_OPT (mo->lng, "time") || IS_OPT (mo->lng, BTOR_OPT_ENGINE)
        || IS_OPT (mo->lng, "lingeling_opts") || IS_OPT (mo->lng, "hex")
        || IS_OPT (mo->lng, "btor") || IS_OPT (mo->lng, "dump_btor"))
      fprintf (out, "\n");
    PRINT_MAIN_OPT (app, mo);
  }

  fprintf (out, "\n");

  btor_init_hash_table_iterator (&it, app->opts);
  while (btor_has_next_hash_table_iterator (&it))
  {
    mo = btor_next_data_hash_table_iterator (&it)->as_ptr;
    if (mo->general) continue;
    PRINT_MAIN_OPT (app, mo);
    if (!strcmp (mo->lng, "smt2_model")) fprintf (out, "\n");
  }

  fprintf (out, "\n");

  fprintf (out, BOOLECTOR_OPTS_INFO_MSG);

  for (o = (char *) boolector_first_opt (app->btor); o;
       o = (char *) boolector_next_opt (app->btor, o))
  {
    if (!strcmp (o, BTOR_OPT_ENGINE) || !strcmp (o, BTOR_OPT_SAT_ENGINE)
        || !strcmp (o, BTOR_OPT_INPUT_FORMAT)
        || !strcmp (o, BTOR_OPT_OUTPUT_NUMBER_FORMAT)
        || !strcmp (o, BTOR_OPT_OUTPUT_FORMAT))
      continue;
    if (!strcmp (o, BTOR_OPT_INCREMENTAL) || !strcmp (o, BTOR_OPT_REWRITE_LEVEL)
        || !strcmp (o, BTOR_OPT_BETA_REDUCE_ALL)
        || !strcmp (o, BTOR_OPT_AUTO_CLEANUP)
        || !strcmp (o, BTOR_OPT_FUN_DUAL_PROP)
        || !strcmp (o, BTOR_OPT_SLS_STRATEGY) || !strcmp (o, BTOR_OPT_SORT_EXP))
      fprintf (out, "\n");
    print_opt (app,
               o,
               boolector_get_opt_shrt (app->btor, o),
               boolector_get_opt_dflt (app->btor, o),
               boolector_get_opt_desc (app->btor, o),
               1);
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
  fprintf (out, "Copyright (c) 2012-2016 Aina Niemetz, Mathias Preiner\n");
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
    if (g_verbosity > 0)
    {
      boolector_print_stats (g_app->btor);
      print_static_stats (0);
    }
    btormain_msg ("CAUGHT SIGNAL %d", sig);
    fputs ("unknown\n", stdout);
    fflush (stdout);
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

#define NO_VALUE_READ(val) (readval == 0 || readval == 3)

#define HAS_UNEXPECTED_ARGUMENT(arg)               \
  ((arg == BTORMAIN_OPT_ARG_NONE                   \
    || (arg == BTORMAIN_OPT_ARG_INT && isdisable)) \
   && (readval == 2 || (readval == 1 && isint)))

#define HAS_MISSING_ARGUMENT(arg, candisable)                 \
  ((arg == BTORMAIN_OPT_ARG_STR && NO_VALUE_READ (readval))   \
   || (arg == BTORMAIN_OPT_ARG_INT                            \
       && (((!candisable && (NO_VALUE_READ (val) || !isint))) \
           || (readval == 3))))

#define HAS_INVALID_ARGUMENT(arg, candisable) \
  (arg == BTORMAIN_OPT_ARG_INT && readval == 2 && !isint)

int
boolector_main (int argc, char **argv)
{
  bool dump_merge;
  int i, j, len, readval, val, format;
  int isshrt, isdisable, isint;
  int res, parse_res, parse_status, sat_res;
  int mgen, pmodel, inc, dump;
  char *arg, *cmd, *valstr, *tmp, *parse_err_msg;
  BtorCharStack opt, errarg;
  BtorHashTableIterator it;
  BtorOpt *o;
  BtorMainOpt *mo;

#ifdef BTOR_HAVE_GETRUSAGE
  g_start_time = btor_time_stamp ();
#endif

  g_app = btormain_new_btormain (boolector_new ());

  res          = BTOR_UNKNOWN_EXIT;
  parse_res    = BOOLECTOR_UNKNOWN;
  parse_status = BOOLECTOR_UNKNOWN;
  sat_res      = BOOLECTOR_UNKNOWN;
  inc          = 0;
  mgen         = 0;
  pmodel       = 0;
  dump         = 0;
  dump_merge   = false;

  mgen = boolector_get_opt (g_app->btor, BTOR_OPT_MODEL_GEN);

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

    /* options ========================================================== */

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
      readval = 3;
      valstr  = arg + j + 1;
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

    /* main options ----------------------------------------------------- */
    mo = 0;
    btor_init_hash_table_iterator (&it, g_app->opts);
    while (btor_has_next_hash_table_iterator (&it))
    {
      mo = btor_next_data_hash_table_iterator (&it)->as_ptr;
      if ((isshrt && mo->shrt && !strcmp (mo->shrt, opt.start))
          || (!isshrt && !strcmp (mo->lng, opt.start)))
        break;
      mo = 0;
    }
    if (mo)
    {
      /* check opt */
      if (isdisable && !mo->candisable)
      {
        btormain_error (g_app, "invalid option '%s'", errarg.start);
        goto DONE;
      }
      if (mo->arg == BTORMAIN_OPT_ARG_NONE)
      {
        if (HAS_UNEXPECTED_ARGUMENT (mo->arg))
        {
          btormain_error (
              g_app, "option '%s' does not expect an argument", errarg.start);
          goto DONE;
        }
      }
      else
      {
        if (HAS_MISSING_ARGUMENT (mo->arg, mo->candisable))
        {
          btormain_error (g_app, "missing argument for '%s'", errarg.start);
          goto DONE;
        }
        if (HAS_INVALID_ARGUMENT (mo->arg, mo->candisable))
        {
          btormain_error (
              g_app, "invalid argument for '%s', expected int", errarg.start);
          goto DONE;
        }
      }
      /* set opt */
      if (IS_OPT (mo->lng, "help"))
      {
        print_help (g_app);
        goto DONE;
      }
      else if (IS_OPT (mo->lng, "copyright"))
      {
        print_copyright (g_app);
        goto DONE;
      }
      else if (IS_OPT (mo->lng, "version"))
      {
        print_version (g_app);
        goto DONE;
      }
      else if (IS_OPT (mo->lng, "time"))
      {
        g_set_alarm = val;
      }
      else if (IS_OPT (mo->lng, "output"))
      {
        if (g_app->close_outfile)
        {
          btormain_error (g_app, "multiple output files");
          goto DONE;
        }
        g_app->outfile_name = valstr;
        if (readval == 1) i += 1;
      }
      else if (IS_OPT (mo->lng, "smt2_model"))
      {
        ((BtorMainOpt *) btor_get_ptr_hash_table (g_app->opts, "smt2_model")
             ->data.as_ptr)
            ->val += 1;
      }
      else if (IS_OPT (mo->lng, BTOR_OPT_ENGINE))
      {
        if (!strcasecmp (valstr, "core"))
          boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_CORE);
        else if (!strcasecmp (valstr, "sls"))
          boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);
        else if (!strcasecmp (valstr, "ef"))
          boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_EF);
        else
        {
          btormain_error (
              g_app, "invalid engine '%s' for '%s'", valstr, errarg.start);
          goto DONE;
        }
      }
      else if (IS_OPT (mo->lng, BTOR_OPT_SAT_ENGINE))
      {
#ifdef BTOR_USE_LINGELING
        if (!strcasecmp (valstr, "lingeling"))
        {
          boolector_set_opt (
              g_app->btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_LINGELING);
        }
        else
#endif
#ifdef BTOR_USE_PICOSAT
            if (!strcasecmp (valstr, "picosat"))
        {
          boolector_set_opt (
              g_app->btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_PICOSAT);
        }
        else
#endif
#ifdef BTOR_USE_MINISAT
            if (!strcasecmp (valstr, "minisat"))
          boolector_set_opt (
              g_app->btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_MINISAT);
        else
#endif
        {
          btormain_error (
              g_app, "invalid sat solver '%s' for '%s'", valstr, errarg.start);
          goto DONE;
        }
      }
#ifdef BTOR_USE_LINGELING
      else if (IS_OPT (opt.start, "lingeling_nofork"))
      {
        boolector_set_opt (g_app->btor, BTOR_OPT_SAT_ENGINE_LGL_FORK, 0);
      }
      else if (IS_OPT (mo->lng, "lingeling_opts"))
      {
        btor_set_opt_str (g_app->btor, BTOR_OPT_SAT_ENGINE, valstr);
      }
#endif
      else if (IS_OPT (mo->lng, "hex"))
      {
        format = BTOR_OUTPUT_BASE_HEX;
      SET_OUTPUT_NUMBER_FORMAT:
        boolector_set_opt (g_app->btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, format);
      }
      else if (IS_OPT (mo->lng, "dec"))
      {
        format = BTOR_OUTPUT_BASE_DEC;
        goto SET_OUTPUT_NUMBER_FORMAT;
      }
      else if (IS_OPT (mo->lng, "btor"))
      {
        format = BTOR_INPUT_FORMAT_BTOR;
      SET_INPUT_FORMAT:
        boolector_set_opt (g_app->btor, BTOR_OPT_INPUT_FORMAT, format);
      }
      else if (IS_OPT (mo->lng, "smt2"))
      {
        format = BTOR_INPUT_FORMAT_SMT2;
        goto SET_INPUT_FORMAT;
      }
      else if (IS_OPT (mo->lng, "smt1"))
      {
        format = BTOR_INPUT_FORMAT_SMT1;
        goto SET_INPUT_FORMAT;
      }
      else if (IS_OPT (mo->lng, "dump_btor"))
      {
        dump = BTOR_OUTPUT_FORMAT_BTOR;
      SET_OUTPUT_FORMAT:
        boolector_set_opt (g_app->btor, BTOR_OPT_OUTPUT_FORMAT, dump);
        boolector_set_opt (g_app->btor, BTOR_OPT_PARSE_INTERACTIVE, 0);
      }
#if 0
	  else if (IS_OPT (mo->lng, "dump_btor2"))
	    {
	      dump = BTOR_OUTPUT_FORMAT_BTOR2;
	      goto SET_OUTPUT_FORMAT;
	    }
#endif
      else if (IS_OPT (mo->lng, "dump_smt2"))
      {
        dump = BTOR_OUTPUT_FORMAT_SMT2;
        goto SET_OUTPUT_FORMAT;
      }
      else if (IS_OPT (mo->lng, "dump_aag"))
      {
        dump = BTOR_OUTPUT_FORMAT_AIGER_ASCII;
        goto SET_OUTPUT_FORMAT;
      }
      else if (IS_OPT (mo->lng, "dump_aig"))
      {
        dump = BTOR_OUTPUT_FORMAT_AIGER_BINARY;
        goto SET_OUTPUT_FORMAT;
      }
      else if (IS_OPT (mo->lng, "dump_aiger_merge"))
      {
        dump_merge = true;
      }
    }

    /* >> btor options ------------------------------------------------ */
    else
    {
      o = 0;
      btor_init_hash_table_iterator (&it, g_app->btor->options);
      while (btor_has_next_hash_table_iterator (&it))
      {
        o = (BtorOpt *) btor_next_data_hash_table_iterator (&it)->as_ptr;
        if ((isshrt && o->shrt && !strcmp (o->shrt, opt.start))
            || (!isshrt && !strcmp (o->lng, opt.start)))
          break;
        o = 0;
      }
      /* check opt */
      if (!o)
      {
        btormain_error (g_app, "invalid option '%s'", errarg.start);
        goto DONE;
      }
      if (HAS_MISSING_ARGUMENT (BTORMAIN_OPT_ARG_INT, o->isflag))
      {
        btormain_error (g_app, "missing argument for '%s'", errarg.start);
        goto DONE;
      }
      if (HAS_INVALID_ARGUMENT (BTORMAIN_OPT_ARG_INT, o->isflag))
      {
        btormain_error (
            g_app, "invalid argument for '%s', expected int", errarg.start);
        goto DONE;
      }
      if (o->isflag)
      {
        if (isdisable)
        {
          if (IS_OPT (o->lng, BTOR_OPT_MODEL_GEN))
          {
            mgen   = 0;
            pmodel = 0;
          }
          else
            boolector_set_opt (g_app->btor, o->lng, 0);
        }
        else
        {
          if (IS_OPT (o->lng, BTOR_OPT_INCREMENTAL))
          {
            inc = (readval && isint && val == 0)
                      ? 0
                      : inc | BTOR_PARSE_MODE_BASIC_INCREMENTAL;
            boolector_set_opt (g_app->btor, BTOR_OPT_INCREMENTAL, inc);
          }
          else if (IS_OPT (o->lng, BTOR_OPT_INCREMENTAL_ALL))
          {
            boolector_set_opt (
                g_app->btor, o->lng, BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE);
            inc = (readval && isint && val == 0)
                      ? 0
                      : inc | BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE;
            boolector_set_opt (g_app->btor, BTOR_OPT_INCREMENTAL, inc);
          }
          else if (IS_OPT (o->lng, BTOR_OPT_MODEL_GEN))
          {
            if (readval && isint && val == 0)
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
          else if ((IS_OPT (o->lng, BTOR_OPT_FUN_DUAL_PROP)
                    && boolector_get_opt (g_app->btor, BTOR_OPT_FUN_JUST))
                   || (IS_OPT (o->lng, BTOR_OPT_FUN_JUST)
                       && boolector_get_opt (g_app->btor,
                                             BTOR_OPT_FUN_DUAL_PROP)))
          {
            btormain_error (g_app,
                            "can only set one out of '--%s' and '--%s'",
                            BTOR_OPT_FUN_DUAL_PROP,
                            BTOR_OPT_FUN_JUST);
            goto DONE;
          }
          else
          {
            if (readval && isint)
              boolector_set_opt (g_app->btor, o->lng, val);
            else
              boolector_set_opt (g_app->btor, o->lng, 1);
          }
        }
      }
      else
      {
#ifndef NBTORLOG
        if (IS_OPT (o->lng, BTOR_OPT_VERBOSITY)
            || IS_OPT (o->lng, BTOR_OPT_LOGLEVEL))
#else
        if (IS_OPT (o->lng, BTOR_OPT_VERBOSITY))
#endif
        {
          if (readval && isint)
            boolector_set_opt (g_app->btor, o->lng, val);
          else
            boolector_set_opt (g_app->btor,
                               o->lng,
                               boolector_get_opt (g_app->btor, o->lng) + 1);
        }
        else
        {
          assert (readval);
          assert (isint);
          boolector_set_opt (g_app->btor, o->lng, val);
        }
      }
    }
  }

  assert (!g_app->done && !g_app->err);

  g_verbosity = boolector_get_opt (g_app->btor, BTOR_OPT_VERBOSITY);

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
  val = ((BtorMainOpt *) btor_get_ptr_hash_table (g_app->opts, "smt2_model")
             ->data.as_ptr)
            ->val;
  mgen = !mgen && val ? val : mgen;

  // TODO: disabling model generation not yet supported (ma)
  if (mgen > 0) boolector_set_opt (g_app->btor, BTOR_OPT_MODEL_GEN, mgen);

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
  if ((val = boolector_get_opt (g_app->btor, "input_format")))
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
  g_verbosity = boolector_get_opt (g_app->btor, BTOR_OPT_VERBOSITY);

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
      assert (boolector_get_opt (g_app->btor, BTOR_OPT_MODEL_GEN));
      val = ((BtorMainOpt *) btor_get_ptr_hash_table (g_app->opts, "smt2_model")
                 ->data.as_ptr)
                ->val;
      boolector_print_model (
          g_app->btor, val ? "smt2" : "btor", g_app->outfile);
    }

#ifdef BTOR_HAVE_GETRUSAGE
    if (g_verbosity)
    {
      double delta_time = delta_time = btor_time_stamp () - g_start_time;
      btormain_msg ("%.1f seconds", delta_time);
    }
#endif
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
      case BTOR_OUTPUT_FORMAT_SMT2:
        if (g_verbosity) btormain_msg ("dumping in SMT 2.0 format");
        boolector_dump_smt2 (g_app->btor, g_app->outfile);
        break;
      case BTOR_OUTPUT_FORMAT_AIGER_ASCII:
        if (g_verbosity) btormain_msg ("dumping in ascii AIGER format");
        boolector_dump_aiger_ascii (g_app->btor, g_app->outfile, dump_merge);
        break;
      default:
        assert (dump == BTOR_OUTPUT_FORMAT_AIGER_BINARY);
        if (g_verbosity) btormain_msg ("dumping in binary AIGER format");
        boolector_dump_aiger_binary (g_app->btor, g_app->outfile, dump_merge);
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
    assert (boolector_get_opt (g_app->btor, BTOR_OPT_MODEL_GEN));
    val = ((BtorMainOpt *) btor_get_ptr_hash_table (g_app->opts, "smt2_model")
               ->data.as_ptr)
              ->val;
    boolector_print_model (g_app->btor, val ? "smt2" : "btor", g_app->outfile);
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

  if (!boolector_get_opt (g_app->btor, BTOR_OPT_EXIT_CODES))
  {
    switch (res)
    {
      case BTOR_UNSAT_EXIT:
      case BTOR_SAT_EXIT: res = BTOR_SUCC_EXIT; break;
      default: res = BTOR_ERR_EXIT;
    }
  }

  BTOR_RELEASE_STACK (g_app->mm, errarg);
  BTOR_RELEASE_STACK (g_app->mm, opt);
  btormain_delete_btormain (g_app);
  reset_sig_handlers ();

  return res;
}
