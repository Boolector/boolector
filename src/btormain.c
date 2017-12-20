/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2016 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormain.h"
#include "boolector.h"
#include "btorconfig.h"
#include "btorcore.h"
#include "btorexit.h"
#include "btoropt.h"
#include "btorparse.h"
#include "utils/btorhashptr.h"
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

bool g_dual_threads;
static double g_start_time_real;
static uint32_t g_verbosity;
static uint32_t g_set_alarm;
static bool g_caught_sig;

static void (*sig_int_handler) (int32_t);
static void (*sig_segv_handler) (int32_t);
static void (*sig_abrt_handler) (int32_t);
static void (*sig_term_handler) (int32_t);
static void (*sig_bus_handler) (int32_t);

static void (*sig_alrm_handler) (int32_t);

/*------------------------------------------------------------------------*/

enum BtorMainOption
{
  BTORMAIN_OPT_HELP,
  BTORMAIN_OPT_COPYRIGHT,
  BTORMAIN_OPT_VERSION,
  BTORMAIN_OPT_TIME,
  BTORMAIN_OPT_OUTPUT,
  BTORMAIN_OPT_ENGINE,
  BTORMAIN_OPT_SAT_ENGINE,
  BTORMAIN_OPT_LGL_NOFORK,
  BTORMAIN_OPT_HEX,
  BTORMAIN_OPT_DEC,
  BTORMAIN_OPT_BIN,
  BTORMAIN_OPT_BTOR,
  BTORMAIN_OPT_SMT2,
  BTORMAIN_OPT_SMT1,
  BTORMAIN_OPT_DUMP_BTOR,
#if 0
  BTORMAIN_OPT_DUMP_BTOR2,
#endif
  BTORMAIN_OPT_DUMP_SMT,
  BTORMAIN_OPT_DUMP_AAG,
  BTORMAIN_OPT_DUMP_AIG,
  BTORMAIN_OPT_DUMP_AIGER_MERGE,
  BTORMAIN_OPT_SMT2_MODEL,
  /* this MUST be the last entry! */
  BTORMAIN_OPT_NUM_OPTS,
};
typedef enum BtorMainOption BtorMainOption;

enum BtorMainOptArg
{
  BTORMAIN_OPT_ARG_NONE,
  BTORMAIN_OPT_ARG_INT,
  BTORMAIN_OPT_ARG_STR,
};
typedef enum BtorMainOptArg BtorMainOptArg;

enum BtorMainReadArg
{
  BTORMAIN_READ_ARG_NONE,
  BTORMAIN_READ_ARG_NONE_VIA_EQ,
  BTORMAIN_READ_ARG_STR,
  BTORMAIN_READ_ARG_STR_VIA_EQ,
  BTORMAIN_READ_ARG_INT,
  BTORMAIN_READ_ARG_INT_VIA_EQ,
};
typedef enum BtorMainReadArg BtorMainReadArg;

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
  bool isflag;        /* is option flag? */
  BtorMainOptArg arg; /* expects argument? */
} BtorMainOpt;

/*------------------------------------------------------------------------*/

struct BtorMainApp
{
  Btor *btor;
  BtorMemMgr *mm;
  BtorMainOpt *options;
  bool done;
  int32_t err;
  char *infile_name;
  FILE *infile;
  int32_t close_infile;
  FILE *outfile;
  char *outfile_name;
  bool close_outfile;
};

/*------------------------------------------------------------------------*/

static void
init_main_opt (BtorMainApp *app,
               BtorMainOption opt,
               bool general,
               bool isflag,
               char *lng,
               char *shrt,
               uint32_t val,
               uint32_t min,
               uint32_t max,
               bool candisable,
               BtorMainOptArg arg,
               char *desc)
{
  assert (app);
  assert (lng);
  assert (desc);
  assert (max <= UINT_MAX);
  assert (min <= val);
  assert (val <= max);

  app->options[opt].general    = general;
  app->options[opt].lng        = lng;
  app->options[opt].shrt       = shrt;
  app->options[opt].val        = val;
  app->options[opt].dflt       = val;
  app->options[opt].min        = min;
  app->options[opt].max        = max;
  app->options[opt].desc       = desc;
  app->options[opt].candisable = candisable;
  app->options[opt].isflag     = isflag;
  app->options[opt].arg        = arg;
}

static void
btormain_init_opts (BtorMainApp *app)
{
  assert (app);

  BTOR_CNEWN (app->mm, app->options, BTORMAIN_OPT_NUM_OPTS);

  init_main_opt (app,
                 BTORMAIN_OPT_HELP,
                 true,
                 true,
                 "help",
                 "h",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print this message and exit");
  init_main_opt (app,
                 BTORMAIN_OPT_COPYRIGHT,
                 true,
                 true,
                 "copyright",
                 "c",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print copyright and exit");
  init_main_opt (app,
                 BTORMAIN_OPT_VERSION,
                 true,
                 true,
                 "version",
                 "V",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print version and exit");
  init_main_opt (app,
                 BTORMAIN_OPT_TIME,
                 true,
                 false,
                 "time",
                 "t",
                 0,
                 0,
                 UINT_MAX,
                 false,
                 BTORMAIN_OPT_ARG_INT,
                 "set time limit");
  init_main_opt (app,
                 BTORMAIN_OPT_OUTPUT,
                 true,
                 false,
                 "output",
                 "o",
                 0,
                 0,
                 0,
                 false,
                 BTORMAIN_OPT_ARG_STR,
                 "set output file for dumping");
  init_main_opt (app,
                 BTORMAIN_OPT_ENGINE,
                 true,
                 false,
                 (char *) boolector_get_opt_lng (app->btor, BTOR_OPT_ENGINE),
                 (char *) boolector_get_opt_shrt (app->btor, BTOR_OPT_ENGINE),
                 BTOR_ENGINE_DFLT,
                 BTOR_ENGINE_MIN,
                 BTOR_ENGINE_MAX,
                 false,
                 BTORMAIN_OPT_ARG_STR,
                 "set engine (core sls prop aigprop) [core]");
  init_main_opt (
      app,
      BTORMAIN_OPT_SAT_ENGINE,
      true,
      false,
      (char *) boolector_get_opt_lng (app->btor, BTOR_OPT_SAT_ENGINE),
      (char *) boolector_get_opt_shrt (app->btor, BTOR_OPT_SAT_ENGINE),
      BTOR_SAT_ENGINE_DFLT,
      BTOR_SAT_ENGINE_MIN + 1,
      BTOR_SAT_ENGINE_MAX - 1,
      false,
      BTORMAIN_OPT_ARG_STR,
      "set sat solver");
#ifdef BTOR_USE_LINGELING
  init_main_opt (app,
                 BTORMAIN_OPT_LGL_NOFORK,
                 true,
                 true,
                 "lingeling-nofork",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "do not use 'fork/clone' for Lingeling");
#endif
  init_main_opt (app,
                 BTORMAIN_OPT_HEX,
                 true,
                 true,
                 "hex",
                 "x",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force hexadecimal number output");
  init_main_opt (app,
                 BTORMAIN_OPT_DEC,
                 true,
                 true,
                 "dec",
                 "d",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force decimal number output");
  init_main_opt (app,
                 BTORMAIN_OPT_BIN,
                 true,
                 true,
                 "bin",
                 "b",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force binary number output");
  init_main_opt (app,
                 BTORMAIN_OPT_BTOR,
                 true,
                 true,
                 "btor",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force BTOR input format");
  init_main_opt (app,
                 BTORMAIN_OPT_SMT2,
                 true,
                 true,
                 "smt2",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force SMT-LIB v2 input format");
  init_main_opt (app,
                 BTORMAIN_OPT_SMT1,
                 true,
                 true,
                 "smt1",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "force SMT-LIB v1 input format");
  init_main_opt (app,
                 BTORMAIN_OPT_DUMP_BTOR,
                 true,
                 true,
                 "dump-btor",
                 "db",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump formula in BTOR format");
#if 0
  init_main_opt (app, BTORMAIN_OPT_DUMP_BTOR2, true, true,
	         "dump-btor2", "db2", 0, 0, 1,
		 false, BTORMAIN_OPT_ARG_NONE,
		 "dump formula in BTOR 2.0 format");
#endif
  init_main_opt (app,
                 BTORMAIN_OPT_DUMP_SMT,
                 true,
                 true,
                 "dump-smt",
                 "ds",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump formula in SMT-LIB v2 format");
  init_main_opt (app,
                 BTORMAIN_OPT_DUMP_AAG,
                 true,
                 true,
                 "dump-aag",
                 "daa",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump QF_BV formula in ascii AIGER format");
  init_main_opt (app,
                 BTORMAIN_OPT_DUMP_AIG,
                 true,
                 true,
                 "dump-aig",
                 "dai",
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "dump QF_BV formula in binary AIGER format");
  init_main_opt (app,
                 BTORMAIN_OPT_DUMP_AIGER_MERGE,
                 true,
                 true,
                 "dump-aiger-merge",
                 "dam",
                 0,
                 0,
                 1,
                 true,
                 BTORMAIN_OPT_ARG_NONE,
                 "merge all roots of AIG [0]");
  init_main_opt (app,
                 BTORMAIN_OPT_SMT2_MODEL,
                 false,
                 true,
                 "smt2-model",
                 0,
                 0,
                 0,
                 1,
                 false,
                 BTORMAIN_OPT_ARG_NONE,
                 "print model in SMT-LIB v2 format "
                 "if model generation is enabled");
}

/*------------------------------------------------------------------------*/

static BtorMainApp *
btormain_new_btormain (Btor *btor)
{
  assert (btor);

  BtorMainApp *res;
  BtorMemMgr *mm;

  mm = btor_mem_mgr_new ();
  BTOR_CNEWN (mm, res, 1);
  res->mm          = mm;
  res->btor        = btor;
  res->infile      = stdin;
  res->infile_name = "<stdin>";
  res->outfile     = stdout;
  btormain_init_opts (res);
  return res;
}

static void
btormain_delete_btormain (BtorMainApp *app)
{
  assert (app);

  BtorMemMgr *mm;

  mm = app->mm;
  BTOR_DELETEN (mm, app->options, BTORMAIN_OPT_NUM_OPTS);
  boolector_delete (app->btor);
  BTOR_DELETE (mm, app);
  btor_mem_mgr_delete (mm);
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
           bool isflag,
           uint32_t dflt,
           const char *desc,
           bool print_dflt)
{
  assert (app);
  assert (lng);
  assert (desc);

  char optstr[LEN_OPTSTR], paramstr[LEN_PARAMSTR];
  char *descstr, descstrline[LEN_HELPSTR], *word;
  int32_t i, j, len;
  BtorCharPtrStack words;

  if (!strcmp (lng, "time"))
    sprintf (paramstr, "<seconds>");
  else if (!strcmp (lng, "output"))
    sprintf (paramstr, "<file>");
  else if (!strcmp (lng, boolector_get_opt_lng (app->btor, BTOR_OPT_ENGINE))
           || !strcmp (lng,
                       boolector_get_opt_lng (app->btor, BTOR_OPT_SAT_ENGINE)))
    sprintf (paramstr, "<engine>");
  else if (!isflag)
    sprintf (paramstr, "<n>");
  else
    paramstr[0] = '\0';

  /* option string ------------------------------------------ */
  memset (optstr, ' ', LEN_OPTSTR * sizeof (char));
  optstr[LEN_OPTSTR - 1] = '\0';
  len                    = strlen (lng);
  sprintf (optstr,
           "  %s%s%s%s%s--%s%s%s",
           shrt ? "-" : "",
           shrt ? shrt : "",
           shrt && strlen (paramstr) > 0 ? " " : "",
           shrt ? paramstr : "",
           shrt ? ", " : "",
           lng,
           strlen (paramstr) > 0 ? "=" : "",
           paramstr);
  len = strlen (optstr);
  for (i = len; i < LEN_OPTSTR - 1; i++) optstr[i] = ' ';
  optstr[LEN_OPTSTR - 1] = '\0';

  /* formatted description ---------------------------------- */
  /* append default value to description */
  if (print_dflt)
  {
    len = strlen (desc) + 3 + btor_util_num_digits (dflt);
    BTOR_CNEWN (app->mm, descstr, len + 1);
    sprintf (descstr, "%s [%u]", desc, dflt);
  }
  else
  {
    len = strlen (desc);
    BTOR_CNEWN (app->mm, descstr, len + 1);
    sprintf (descstr, "%s", desc);
  }
  BTOR_INIT_STACK (app->mm, words);
  word = strtok (descstr, " ");
  while (word)
  {
    BTOR_PUSH_STACK (words, btor_mem_strdup (app->mm, word));
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
    btor_mem_freestr (app->mm, BTOR_POP_STACK (words));
  BTOR_RELEASE_STACK (words);
}

#define PRINT_MAIN_OPT(app, opt) \
  do                             \
  {                              \
    print_opt (app,              \
               (opt)->lng,       \
               (opt)->shrt,      \
               (opt)->isflag,    \
               (opt)->dflt,      \
               (opt)->desc,      \
               false);           \
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

  BtorOption o;
  BtorMainOption mo;
  FILE *out;

  out = app->outfile;

  fprintf (out, "usage: boolector [<option>...][<input>]\n");
  fprintf (out, "\n");
  fprintf (out, "where <option> is one of the following:\n");
  fprintf (out, "\n");

  for (mo = 0; mo < BTORMAIN_OPT_NUM_OPTS; mo++)
  {
    if (!app->options[mo].general) continue;
    if (mo == BTORMAIN_OPT_TIME || mo == BTORMAIN_OPT_ENGINE
        || mo == BTORMAIN_OPT_HEX || mo == BTORMAIN_OPT_BTOR
        || mo == BTORMAIN_OPT_DUMP_BTOR)
      fprintf (out, "\n");
    PRINT_MAIN_OPT (app, &app->options[mo]);
  }

  fprintf (out, "\n");

  for (mo = 0; mo < BTORMAIN_OPT_NUM_OPTS; mo++)
  {
    if (app->options[mo].general) continue;
    PRINT_MAIN_OPT (app, &app->options[mo]);
    if (mo == BTORMAIN_OPT_SMT2_MODEL) fprintf (out, "\n");
  }

  fprintf (out, "\n");

  fprintf (out, BOOLECTOR_OPTS_INFO_MSG);

  for (o = boolector_first_opt (app->btor); boolector_has_opt (app->btor, o);
       o = boolector_next_opt (app->btor, o))
  {
    if (app->btor->options[o].internal) continue;
    if (o == BTOR_OPT_ENGINE || o == BTOR_OPT_SAT_ENGINE
        || o == BTOR_OPT_INPUT_FORMAT || o == BTOR_OPT_OUTPUT_NUMBER_FORMAT
        || o == BTOR_OPT_OUTPUT_FORMAT)
      continue;
    if (o == BTOR_OPT_INCREMENTAL || o == BTOR_OPT_REWRITE_LEVEL
        || o == BTOR_OPT_BETA_REDUCE_ALL || o == BTOR_OPT_AUTO_CLEANUP
        || o == BTOR_OPT_FUN_DUAL_PROP || o == BTOR_OPT_SLS_STRATEGY
        || o == BTOR_OPT_SORT_EXP)
      fprintf (out, "\n");
    print_opt (app,
               app->btor->options[o].lng,
               app->btor->options[o].shrt,
               app->btor->options[o].isflag,
               app->btor->options[o].dflt,
               app->btor->options[o].desc,
               true);
  }

  app->done = true;
}

static void
print_copyright (BtorMainApp *app)
{
  assert (app);

  FILE *out = app->outfile;

  fprintf (out, "This software is\n");
  fprintf (out, "Copyright (c) 2007-2009 Robert Brummayer\n");
  fprintf (out, "Copyright (c) 2007-2016 Armin Biere\n");
  fprintf (out, "Copyright (c) 2012-2017 Aina Niemetz, Mathias Preiner\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#ifdef BTOR_USE_LINGELING
  fprintf (out, "\n");
  fprintf (out, "This software is linked against Lingeling\n");
  fprintf (out, "Copyright (c) 2010-2016 Armin Biere\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#endif
#ifdef BTOR_USE_PICOSAT
  fprintf (out, "\n");
  fprintf (out, "This software is linked against PicoSAT\n");
  fprintf (out, "Copyright (c) 2006-2016 Armin Biere\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#endif
#ifdef BTOR_USE_MINISAT
  fprintf (out, "\n");
  fprintf (out, "This software is linked against MiniSAT\n");
  fprintf (out, "Copyright (c) 2003-2013, Niklas Een, Niklas Sorensson\n");
#endif
#ifdef BTOR_USE_CADICAL
  fprintf (out, "\n");
  fprintf (out, "This software is linked against CaDiCaL\n");
  fprintf (out, "Copyright (c) 2016-2017 Armin Biere\n");
  fprintf (out, "Institute for Formal Models and Verification\n");
  fprintf (out, "Johannes Kepler University, Linz, Austria\n");
#endif
  app->done = true;
}

static void
print_version (BtorMainApp *app)
{
  assert (app);
  fprintf (app->outfile, "%s\n", BTOR_VERSION);
  app->done = true;
}

static void
print_static_stats (int32_t sat_res)
{
  double real = btor_util_current_time () - g_start_time_real;
#ifdef BTOR_HAVE_GETRUSAGE
  double process = btor_util_time_stamp ();
  if (g_dual_threads)
    btormain_msg ("%.1f seconds process, %.0f%% utilization",
                  process,
                  real > 0 ? (100 * process) / real / 2 : 0.0);
  else
    btormain_msg ("%.1f seconds process", process);
#else
  btormain_msg ("can not determine run-time in seconds (no getrusage)");
#endif
  btormain_msg ("%.1f seconds real", real);
  btormain_msg ("%s",
                sat_res == BOOLECTOR_SAT
                    ? "sat"
                    : (sat_res == BOOLECTOR_UNSAT ? "unsat" : "unknown"));
}

static void
print_sat_result (BtorMainApp *app, int32_t sat_result)
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
catch_sig (int32_t sig)
{
  if (!g_caught_sig)
  {
    g_caught_sig = true;
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
catch_alarm (int32_t sig)
{
  (void) sig;
  assert (sig == SIGALRM);
  if (g_set_alarm > 0)
  {
    btormain_msg ("ALARM TRIGGERED: time limit %d seconds reached",
                  g_set_alarm);
    if (g_verbosity > 0)
    {
      boolector_print_stats (g_app->btor);
      print_static_stats (0);
    }
    fputs ("unknown\n", stdout);
    fflush (stdout);
  }
  reset_alarm ();
  _exit (0);
}

static void
set_alarm (void)
{
  sig_alrm_handler = signal (SIGALRM, catch_alarm);
  assert (g_set_alarm > 0);
  alarm (g_set_alarm);
}

/*------------------------------------------------------------------------*/

static bool
has_suffix (const char *str, const char *suffix)
{
  int32_t l, k, d;
  l = strlen (str);
  k = strlen (suffix);
  d = l - k;
  if (d < 0) return 0;
  return !strcmp (str + d, suffix);
}

/*------------------------------------------------------------------------*/

#define NO_VALUE_READ(val) \
  (val == BTORMAIN_READ_ARG_NONE || val == BTORMAIN_READ_ARG_NONE_VIA_EQ)

#define READ_ARG_IS_INT(val) \
  (val == BTORMAIN_READ_ARG_INT || val == BTORMAIN_READ_ARG_INT_VIA_EQ)

#define HAS_UNEXPECTED_ARGUMENT(arg)               \
  ((arg == BTORMAIN_OPT_ARG_NONE                   \
    || (arg == BTORMAIN_OPT_ARG_INT && isdisable)) \
   && (readval == BTORMAIN_READ_ARG_STR_VIA_EQ     \
       || readval == BTORMAIN_READ_ARG_INT_VIA_EQ  \
       || readval == BTORMAIN_READ_ARG_INT))

#define HAS_MISSING_ARGUMENT(arg, candisable)                             \
  ((arg == BTORMAIN_OPT_ARG_STR && NO_VALUE_READ (readval))               \
   || (arg == BTORMAIN_OPT_ARG_INT                                        \
       && (((!candisable                                                  \
             && (NO_VALUE_READ (readval) || !READ_ARG_IS_INT (readval)))) \
           || (readval == BTORMAIN_READ_ARG_NONE_VIA_EQ))))

#define HAS_INVALID_ARGUMENT(arg, candisable) \
  (arg == BTORMAIN_OPT_ARG_INT && readval == BTORMAIN_READ_ARG_STR_VIA_EQ)

int32_t
boolector_main (int32_t argc, char **argv)
{
  bool dump_merge;
  int32_t i, j, len, format;
  uint32_t val;
  BtorMainReadArg readval;
  bool isshrt, isdisable;
  int32_t res, parse_res, parse_status, sat_res;
  uint32_t mgen, pmodel, inc, dump;
  char *arg, *cmd, *valstr, *tmp, *parse_err_msg;
  BtorCharStack opt, errarg;
  BtorOption k;
  BtorMainOption l;
  BtorMainOpt *mo;
  BtorOpt *o;

  g_start_time_real = btor_util_current_time ();

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

  BTOR_INIT_STACK (g_app->mm, opt);
  BTOR_INIT_STACK (g_app->mm, errarg);

  for (i = 1; i < argc; i++)
  {
    arg       = argv[i];
    len       = strlen (argv[i]);
    isshrt    = false;
    isdisable = false;
    readval   = BTORMAIN_READ_ARG_NONE;
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

      if (!btor_util_file_exists (g_app->infile_name))
      {
        g_app->infile = 0;
      }
      else if (has_suffix (g_app->infile_name, ".gz")
               || has_suffix (g_app->infile_name, ".bz2")
               || has_suffix (g_app->infile_name, ".7z")
               || has_suffix (g_app->infile_name, ".zip"))
      {
        BTOR_NEWN (g_app->mm, cmd, len + 40);
        if (has_suffix (g_app->infile_name, ".gz"))
          sprintf (cmd, "gunzip -c %s", g_app->infile_name);
        else if (has_suffix (g_app->infile_name, ".bz2"))
          sprintf (cmd, "bzcat %s", g_app->infile_name);
        else if (has_suffix (g_app->infile_name, ".7z"))
          sprintf (cmd, "7z x -so %s 2> /dev/null", g_app->infile_name);
        else if (has_suffix (g_app->infile_name, ".zip"))
          sprintf (cmd, "unzip -p %s", g_app->infile_name);

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
    for (j = 0; j < len && arg[j] != '='; j++) BTOR_PUSH_STACK (errarg, arg[j]);
    BTOR_PUSH_STACK (errarg, '\0');

    /* extract option name */
    isshrt = arg[1] != '-';
    j      = isshrt ? 1 : 2;
    isdisable =
        len > 3 && arg[j] == 'n' && arg[j + 1] == 'o' && arg[j + 2] == '-';
    for (j = isdisable ? j + 3 : j; j < len && arg[j] != '='; j++)
      BTOR_PUSH_STACK (opt, arg[j]);
    BTOR_PUSH_STACK (opt, '\0');

    /* extract option argument (if any) */
    if (arg[j] == '=')
    {
      readval = BTORMAIN_READ_ARG_NONE_VIA_EQ;
      valstr  = arg + j + 1;
      if (valstr[0] != 0)
      {
        readval = BTORMAIN_READ_ARG_STR_VIA_EQ;
        val     = (uint32_t) strtol (valstr, &tmp, 10);
        if (tmp[0] == 0) readval = BTORMAIN_READ_ARG_INT_VIA_EQ;
      }
    }
    else
    {
      if (i + 1 < argc && argv[i + 1][0] != '-')
      {
        readval = BTORMAIN_READ_ARG_STR;
        valstr  = argv[i + 1];
        val     = (uint32_t) strtol (valstr, &tmp, 10);
        if (tmp[0] == 0) readval = BTORMAIN_READ_ARG_INT;
      }
    }

    /* main options ----------------------------------------------------- */
    for (l = 0, mo = 0; l < BTORMAIN_OPT_NUM_OPTS; l++)
    {
      mo = &g_app->options[l];
      if ((isshrt && mo->shrt && !strcmp (mo->shrt, opt.start))
          || (!isshrt && !strcmp (mo->lng, opt.start)))
        break;
      mo = 0;
    }
    if (mo)
    {
      if (mo->arg != BTORMAIN_OPT_ARG_NONE
          && (readval == BTORMAIN_READ_ARG_STR
              || readval == BTORMAIN_READ_ARG_INT))
        i += 1;

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
      switch (l)
      {
        case BTORMAIN_OPT_HELP: print_help (g_app); goto DONE;

        case BTORMAIN_OPT_COPYRIGHT: print_copyright (g_app); goto DONE;

        case BTORMAIN_OPT_VERSION: print_version (g_app); goto DONE;

        case BTORMAIN_OPT_TIME: g_set_alarm = val; break;

        case BTORMAIN_OPT_OUTPUT:
          if (g_app->close_outfile)
          {
            btormain_error (g_app, "multiple output files");
            goto DONE;
          }
          g_app->outfile_name = valstr;
          break;

        case BTORMAIN_OPT_SMT2_MODEL:
          g_app->options[BTORMAIN_OPT_SMT2_MODEL].val += 1;
          break;

        case BTORMAIN_OPT_ENGINE:
          if (!strcasecmp (valstr, "core"))
            boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_FUN);
          else if (!strcasecmp (valstr, "sls"))
            boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_SLS);
          else if (!strcasecmp (valstr, "prop"))
            boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_PROP);
          else if (!strcasecmp (valstr, "aigprop"))
            boolector_set_opt (
                g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_AIGPROP);
          else if (!strcasecmp (valstr, "ef"))
            boolector_set_opt (g_app->btor, BTOR_OPT_ENGINE, BTOR_ENGINE_EF);
          else
          {
            btormain_error (
                g_app, "invalid engine '%s' for '%s'", valstr, errarg.start);
            goto DONE;
          }
          break;

        case BTORMAIN_OPT_SAT_ENGINE:
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
#ifdef BTOR_USE_CADICAL
              if (!strcasecmp (valstr, "cadical"))
            boolector_set_opt (
                g_app->btor, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_CADICAL);
          else
#endif
          {
            btormain_error (g_app,
                            "invalid sat solver '%s' for '%s'",
                            valstr,
                            errarg.start);
            goto DONE;
          }
          break;

#ifdef BTOR_USE_LINGELING
        case BTORMAIN_OPT_LGL_NOFORK:
          boolector_set_opt (g_app->btor, BTOR_OPT_SAT_ENGINE_LGL_FORK, 0);
          break;
#endif

        case BTORMAIN_OPT_HEX:
          format = BTOR_OUTPUT_BASE_HEX;
        SET_OUTPUT_NUMBER_FORMAT:
          boolector_set_opt (
              g_app->btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, format);
          break;

        case BTORMAIN_OPT_DEC:
          format = BTOR_OUTPUT_BASE_DEC;
          goto SET_OUTPUT_NUMBER_FORMAT;

        case BTORMAIN_OPT_BIN:
          format = BTOR_OUTPUT_BASE_BIN;
          goto SET_OUTPUT_NUMBER_FORMAT;

        case BTORMAIN_OPT_BTOR:
          format = BTOR_INPUT_FORMAT_BTOR;
        SET_INPUT_FORMAT:
          boolector_set_opt (g_app->btor, BTOR_OPT_INPUT_FORMAT, format);
          break;

        case BTORMAIN_OPT_SMT2:
          format = BTOR_INPUT_FORMAT_SMT2;
          goto SET_INPUT_FORMAT;

        case BTORMAIN_OPT_SMT1:
          format = BTOR_INPUT_FORMAT_SMT1;
          goto SET_INPUT_FORMAT;

        case BTORMAIN_OPT_DUMP_BTOR:
          dump = BTOR_OUTPUT_FORMAT_BTOR;
        SET_OUTPUT_FORMAT:
          boolector_set_opt (g_app->btor, BTOR_OPT_OUTPUT_FORMAT, dump);
          boolector_set_opt (g_app->btor, BTOR_OPT_PARSE_INTERACTIVE, 0);
          break;
#if 0
	      case BTORMAIN_OPT_DUMP_BTOR2:
		dump = BTOR_OUTPUT_FORMAT_BTOR2;
		goto SET_OUTPUT_FORMAT;
#endif
        case BTORMAIN_OPT_DUMP_SMT:
          dump = BTOR_OUTPUT_FORMAT_SMT2;
          goto SET_OUTPUT_FORMAT;

        case BTORMAIN_OPT_DUMP_AAG:
          dump = BTOR_OUTPUT_FORMAT_AIGER_ASCII;
          goto SET_OUTPUT_FORMAT;

        case BTORMAIN_OPT_DUMP_AIG:
          dump = BTOR_OUTPUT_FORMAT_AIGER_BINARY;
          goto SET_OUTPUT_FORMAT;

        case BTORMAIN_OPT_DUMP_AIGER_MERGE: dump_merge = true; break;

        default:
          /* get rid of compiler warnings, should be unreachable */
          assert (l == BTORMAIN_OPT_NUM_OPTS);
      }
    }

    /* >> btor options ------------------------------------------------ */
    else
    {
      if (readval == BTORMAIN_READ_ARG_INT) i += 1;

      for (k = boolector_first_opt (g_app->btor), o = 0;
           boolector_has_opt (g_app->btor, k);
           k = btor_opt_next (g_app->btor, k))
      {
        o = &g_app->btor->options[k];
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
          if (k == BTOR_OPT_MODEL_GEN)
          {
            mgen   = 0;
            pmodel = 0;
          }
          else
            boolector_set_opt (g_app->btor, k, 0);
        }
        else
        {
          switch (k)
          {
            case BTOR_OPT_MODEL_GEN:
              if (READ_ARG_IS_INT (readval) && val == 0)
              {
                mgen   = 0;
                pmodel = 0;
              }
              else
              {
                mgen += 1;
                pmodel = 1;
              }
              break;
#ifndef NBTORLOG
            case BTOR_OPT_VERBOSITY:
            case BTOR_OPT_LOGLEVEL:
#else
            case BTOR_OPT_VERBOSITY:
#endif
              if (READ_ARG_IS_INT (readval))
                boolector_set_opt (g_app->btor, k, val);
              else
                boolector_set_opt (
                    g_app->btor, k, boolector_get_opt (g_app->btor, k) + 1);
              break;
            default:
              assert (k != BTOR_OPT_NUM_OPTS);
              if (READ_ARG_IS_INT (readval))
                boolector_set_opt (g_app->btor, k, val);
              else
                boolector_set_opt (g_app->btor, k, 1);
          }
        }
      }
      else
      {
        assert (READ_ARG_IS_INT (readval));
        boolector_set_opt (g_app->btor, k, val);
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
    g_app->close_outfile = true;
  }

  /* automatically enable model generation if smt2 models are forced */
  val  = g_app->options[BTORMAIN_OPT_SMT2_MODEL].val;
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
  val = boolector_get_opt (g_app->btor, BTOR_OPT_INPUT_FORMAT);
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

    default:
      parse_res = boolector_parse (g_app->btor,
                                   g_app->infile,
                                   g_app->infile_name,
                                   g_app->outfile,
                                   &parse_err_msg,
                                   &parse_status);
  }

  /* verbosity may have been increased via input (set-option) */
  g_verbosity = boolector_get_opt (g_app->btor, BTOR_OPT_VERBOSITY);

  g_dual_threads = boolector_get_opt (g_app->btor, BTOR_OPT_EF_DUAL_SOLVER) == 1
                   && g_app->btor->quantifiers->count > 0;

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
      val = g_app->options[BTORMAIN_OPT_SMT2_MODEL].val;
      boolector_print_model (
          g_app->btor, val ? "smt2" : "btor", g_app->outfile);
    }

#ifdef BTOR_HAVE_GETRUSAGE
    if (g_verbosity) btormain_msg ("%.1f seconds", btor_util_time_stamp ());
#endif
    goto DONE;
  }
  /* we don't dump formula(s) in incremental mode */
  else if (dump)
  {
    (void) boolector_simplify (g_app->btor);

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

  /* call sat (if not yet called) */
  if (parse_res == BOOLECTOR_PARSE_UNKNOWN
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
    val = g_app->options[BTORMAIN_OPT_SMT2_MODEL].val;
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

  BTOR_RELEASE_STACK (errarg);
  BTOR_RELEASE_STACK (opt);
  btormain_delete_btormain (g_app);
  reset_sig_handlers ();

  return res;
}
