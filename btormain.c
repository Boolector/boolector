/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btormain.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbtor.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btordump.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorhash.h"
#include "btorlog.h"
#include "btorlogic.h"
#include "btormem.h"
#include "btorparse.h"
#include "btorsat.h"
#include "btorsmt.h"
#include "btorsmt2.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

enum BtorBasis
{
  BTOR_BINARY_BASIS = 0,
  BTOR_DECIMAL_BASIS,
  BTOR_HEXADECIMAL_BASIS
};

typedef enum BtorBasis BtorBasis;

typedef enum BtorPrintModel BtorPrintModel;

struct BtorMainApp
{
  FILE *output_file;
  int close_output_file;
  FILE *input_file;
  char *input_file_name;
  int close_input_file;
  int verbosity;
#ifndef NBTORLOG
  int loglevel;
#endif
  int incremental;
  int beta_reduce_all;
  int pprint;
#ifdef BTOR_USE_LINGELING
  int nofork;
#endif
  int indepth;
  int lookahead;
  int interval;
  int done;
  int err;
  int argpos;
  int argc;
  char **argv;
  BtorBasis basis;
  int dump_exp;
  int dump_smt;
  int rewrite_level;
  int force_smt_input;
  int print_model;
  const char *forced_sat_solver_name;
  int forced_sat_solvers;
#ifdef BTOR_USE_PICOSAT
  int force_picosat;
#endif
#ifdef BTOR_USE_LINGELING
  int force_lingeling;
  const char *lingeling_options;
#endif
#ifdef BTOR_USE_MINISAT
  int force_minisat;
#endif
};

typedef struct BtorMainApp BtorMainApp;

/*------------------------------------------------------------------------*/

static const char *g_usage =
    "usage: boolector [<option>...][<input>]\n"
    "\n"
    "where <option> is one of the following:\n"
    "\n"
    "  -h, --help                       print usage information and exit\n"
    "  -c, --copyright                  print copyright and exit\n"
    "  -V, --version                    print version and exit\n"
    "\n"
    "  -m|--model                       print model in the SAT case\n"
    "  -v|--verbose                     increase verbosity (0 default, 4 max)\n"
#ifndef NBTORLOG
    "  -l|--log                         increase loglevel (0 default)\n"
#endif
    "\n"
    "  -i, --inc[remental]              incremental mode (SMT1 only)\n"
    "  -I                               same as '-i' but solve all formulas\n"
    "  -look-ahead=<w>                  incremental lookahead mode width <w>\n"
    "  -in-depth=<w>                    incremental in-depth mode width <w>\n"
    "  -interval=<w>                    incremental interval mode width <w>\n"
    "\n"
#ifdef BTOR_USE_LINGELING
    "  --no-fork                        do not use 'fork/clone' for Lingeling\n"
#endif
    "\n"
    "  -t <time out in seconds>         set time limit\n"
    "\n"
    "  --btor                           force BTOR format input\n"
    "  --smt, --smt1                    force SMTLIB version 1 format input\n"
    "  --smt2                           force SMTLIB version 2 format input\n"
    "\n"
    "  -x, --hex                        hexadecimal output\n"
    "  -d, --dec                        decimal output\n"
    "  -de, --dump-exp                  dump expression in BTOR format\n"
    "  -ds                              dump expression in SMT 1.2 format\n"
    "  -d1, -ds1, --dump-smt            dump expression in SMT 1.2 format\n"
    "  -d2, -ds2, --dump-smt2           dump expression in SMT 2.0 format\n"
    "  -d2fun, -ds2fun, --dump-smt2-fun dump expression in SMT 2.0 format "
    "using\n"
    "                                   define-fun instead of let\n"
    "  -o, --output <file>              set output file for dumping\n"
    "\n"
    "  -rwl<n>, --rewrite-level<n>      set rewrite level [0,3] (default 3)\n"
    "  -bra, --beta-reduce-all          eliminate lambda expressions\n"
    // TODO: -npp|--no-pretty-print ? (debug only?)
    "\n"
#ifdef BTOR_USE_PICOSAT
    "  -picosat                         enforce usage of PicoSAT as SAT "
    "solver\n"
#endif
#ifdef BTOR_USE_LINGELING
    "  -lingeling                       enforce usage of Lingeling as SAT "
    "solver\n"
    "  -l[,<opt>=<val>]*                set lingeling option(s) "
    "'--<opt>=<val>'\n"
#endif
#ifdef BTOR_USE_MINISAT
    "  -minisat                         enforce usage of MiniSAT as SAT "
    "solver\n"
#endif
    ;

static const char *g_copyright =
    "This software is\n"
    "Copyright (c) 2007-2009 Robert Brummayer\n"
    "Copyright (c) 2007-2013 Armin Biere\n"
    "Copyright (c) 2012-2013 Aina Niemetz, Mathias Preiner\n"
    "Copyright (c) 2013 Christian Reisenberger\n"
    "Institute for Formal Models and Verification\n"
    "Johannes Kepler University, Linz, Austria\n"
#ifdef BTOR_USE_LINGELING
    "\n"
    "This software is linked against Lingeling\n"
    "Copyright (c) 2010-2013 Armin Biere\n"
    "Institute for Formal Models and Verification\n"
    "Johannes Kepler University, Linz, Austria\n"
#endif
#ifdef BTOR_USE_PICOSAT
    "\n"
    "This software is linked against PicoSAT\n"
    "Copyright (c) 2006-2013 Armin Biere\n"
    "Institute for Formal Models and Verification\n"
    "Johannes Kepler University, Linz, Austria\n"
#endif
#ifdef BTOR_USE_MINISAT
    "\n"
    "This software is linked against MiniSAT\n"
    "Copyright (c) 2003-2013, Niklas Een, Niklas Sorensson\n"
    "Copyright (c) 2007-2013  Niklas Sorensson\n"
#endif
    ;

static int btor_static_verbosity;
static BtorSATMgr *btor_static_smgr;
static Btor *btor_static_btor;
static int btor_static_catched_sig;
static int btor_static_set_alarm;
#ifdef BTOR_HAVE_GETRUSAGE
static double btor_static_start_time;
#endif

static void (*btor_sig_int_handler) (int);
static void (*btor_sig_segv_handler) (int);
static void (*btor_sig_abrt_handler) (int);
static void (*btor_sig_term_handler) (int);
static void (*btor_sig_bus_handler) (int);

/*------------------------------------------------------------------------*/

static void
btor_reset_sig_handlers (void)
{
  (void) signal (SIGINT, btor_sig_int_handler);
  (void) signal (SIGSEGV, btor_sig_segv_handler);
  (void) signal (SIGABRT, btor_sig_abrt_handler);
  (void) signal (SIGTERM, btor_sig_term_handler);
  (void) signal (SIGBUS, btor_sig_bus_handler);
}

static void
btor_catched_sig_msg (int sig)
{
  printf ("[btormain] CAUGHT SIGNAL %d\n", sig);
  fflush (stdout);
}

static void
btor_msg_main (char *msg)
{
  assert (msg);
  fprintf (stdout, "[btormain] %s", msg);
  fflush (stdout);
}

static void
btor_msg_main_va_args (char *msg, ...)
{
  va_list list;
  assert (msg);
  va_start (list, msg);
  fprintf (stdout, "[btormain] ");
  vfprintf (stdout, msg, list);
  va_end (list);
}

static void
btor_print_static_stats (void)
{
  size_t maxallocated;
#ifdef BTOR_HAVE_GETRUSAGE
  double delta_time = delta_time = btor_time_stamp () - btor_static_start_time;
  btor_msg_main_va_args ("%.1f seconds\n", delta_time);
#else
  btor_msg_main ("can not determine run-time in seconds (no getrusage)");
#endif
  maxallocated = btor_static_btor ? btor_static_btor->mm->maxallocated : 0;
  btor_msg_main_va_args ("%.1f MB\n", maxallocated / (double) (1 << 20));
}

static void
btor_catch_sig (int sig)
{
  if (!btor_static_catched_sig)
  {
    btor_static_catched_sig = 1;
    btor_catched_sig_msg (sig);
    fputs ("unknown\n", stdout);
    fflush (stdout);
    if (btor_static_verbosity > 0)
    {
      if (btor_static_smgr) btor_print_stats_sat (btor_static_smgr);
      if (btor_static_btor) btor_print_stats_btor (btor_static_btor);
      btor_print_static_stats ();
      btor_catched_sig_msg (sig);
    }
  }
  btor_reset_sig_handlers ();
  raise (sig);
  exit (sig);
}

static void
btor_set_sig_handlers (void)
{
  btor_sig_int_handler  = signal (SIGINT, btor_catch_sig);
  btor_sig_segv_handler = signal (SIGSEGV, btor_catch_sig);
  btor_sig_abrt_handler = signal (SIGABRT, btor_catch_sig);
  btor_sig_term_handler = signal (SIGTERM, btor_catch_sig);
  btor_sig_bus_handler  = signal (SIGBUS, btor_catch_sig);
}

static void (*btor_sig_alrm_handler) (int);

static void
btor_reset_alarm (void)
{
  alarm (0);
  (void) signal (SIGALRM, btor_sig_alrm_handler);
}

static void
btor_catch_alarm (int sig)
{
  (void) sig;
  assert (sig == SIGALRM);
  if (btor_static_set_alarm > 0)
  {
    printf ("[btormain] ALARM TRIGGERED: time limit %d seconds reached\n",
            btor_static_set_alarm);
    fputs ("unknown\n", stdout);
    fflush (stdout);
    if (btor_static_verbosity > 0)
    {
      if (btor_static_smgr) btor_print_stats_sat (btor_static_smgr);
      if (btor_static_btor) btor_print_stats_btor (btor_static_btor);
      btor_print_static_stats ();
    }
  }
  btor_reset_alarm ();
  exit (0);
}

static void
btor_set_alarm (void)
{
  btor_sig_alrm_handler = signal (SIGALRM, btor_catch_alarm);
  assert (btor_static_set_alarm > 0);
  alarm (btor_static_set_alarm);
}

static void
print_err (BtorMainApp *app, char *msg)
{
  assert (msg);
  if (app->verbosity >= 0)
  {
    fputs ("boolector: ", stdout);
    fputs (msg, stdout);
  }
}

static void
print_err_va_args (BtorMainApp *app, char *msg, ...)
{
  va_list list;
  assert (msg);
  if (app->verbosity >= 0)
  {
    fputs ("boolector: ", stdout);
    va_start (list, msg);
    vprintf (msg, list);
    va_end (list);
  }
}

static int
has_suffix (const char *str, const char *suffix)
{
  int l = strlen (str), k = strlen (suffix), d = l - k;
  if (d < 0) return 0;
  return !strcmp (str + d, suffix);
}

static int
file_name_has_suffix (const char *str, const char *suffix)
{
  int l = strlen (str), k = strlen (suffix), d = l - k;
  if (d < 0) return 0;
  if (!strcmp (str + d, suffix)) return 1;
  if (d - 3 >= 0 && !strcmp (str + l - 3, ".gz")
      && !strncmp (str + d - 3, suffix, k))
    return 1;
  return 0;
}

static char *
format_assignment (BtorMainApp *app, Btor *btor, char *assignment)
{
  char *pretty, *grounded;
  BtorBasis basis;
  int not_binary;
  BtorMemMgr *mm;

  assert (app);
  assert (btor);
  assert (assignment);

  basis = app->basis;
  not_binary =
      (basis == BTOR_HEXADECIMAL_BASIS) || (basis == BTOR_DECIMAL_BASIS);
  mm = btor->mm;

  if (not_binary)
  {
    grounded = btor_ground_const_3vl (mm, assignment);

    if (basis == BTOR_HEXADECIMAL_BASIS)
      pretty = btor_const_to_hex (mm, grounded);
    else
    {
      assert (basis == BTOR_DECIMAL_BASIS);
      pretty = btor_const_to_decimal (mm, grounded);
    }

    btor_delete_const (mm, grounded);
  }
  else
    pretty = btor_copy_const (mm, assignment);

  return pretty;
}

static void
print_bv_assignment (BtorMainApp *app, Btor *btor, BtorNode *exp)
{
  char *pretty, *assignment;

  assert (app);
  assert (btor);
  assert (exp);
  assert (!BTOR_IS_INVERTED_NODE (exp));

  assignment = btor_bv_assignment_exp (btor, exp);
  assert (assignment);

  pretty = format_assignment (app, btor, assignment);
  fprintf (
      app->output_file, "%s %s\n", btor_get_symbol_exp (btor, exp), pretty);
  btor_free_bv_assignment_exp (btor, pretty);
  btor_free_bv_assignment_exp (btor, assignment);
}

static void
print_array_assignment (BtorMainApp *app, Btor *btor, BtorNode *exp)
{
  char **indices, **values;
  char *pretty_index, *pretty_value;
  int i, size;

  assert (app);
  assert (btor);
  assert (exp);
  assert (!BTOR_IS_INVERTED_NODE (exp));
  btor_array_assignment_exp (btor, exp, &indices, &values, &size);
  if (size > 0)
  {
    for (i = 0; i < size; i++)
    {
      pretty_index = format_assignment (app, btor, indices[i]);
      pretty_value = format_assignment (app, btor, values[i]);
      fprintf (app->output_file,
               "%s[%s] %s\n",
               exp->symbol,
               pretty_index,
               pretty_value);
      btor_free_bv_assignment_exp (btor, pretty_index);
      btor_free_bv_assignment_exp (btor, pretty_value);
      btor_free_bv_assignment_exp (btor, indices[i]);
      btor_free_bv_assignment_exp (btor, values[i]);
    }
    BTOR_DELETEN (btor->mm, indices, size);
    BTOR_DELETEN (btor->mm, values, size);
  }
}

static void
print_assignment (BtorMainApp *app, Btor *btor, BtorParseResult *parse_res)
{
  BtorNode *var, *temp;
  int i;

  for (i = 0; i < parse_res->ninputs; i++)
  {
    var  = parse_res->inputs[i];
    temp = btor_simplify_exp (btor, var);
    if (BTOR_IS_ARRAY_NODE (temp))
      print_array_assignment (app, btor, var);
    else
      print_bv_assignment (app, btor, var);
  }
}

static int
parse_option_with_int_value (BtorMainApp *app, const char *name, int *resptr)
{
  const char *p, *q;
  p = app->argv[app->argpos];
  if (*p++ != '-') return 0;
  for (q = name; *q; q++, p++)
    if (*p != *q) return 0;
  if (*p++ != '=') return 0;
  if (!*p) return 0;
  assert (resptr);
  *resptr = atoi (p);
  return 1;
}

static const char *
match_long_opt (const char *opt, const char *pattern)
{
  const char *p, *q;

  assert (opt);
  assert (pattern);

  if (opt[0] != '-' || opt[1] != '-') return 0;

  for (p = opt + 2, q = pattern; *q && (*p == *q); p++, q++)
    ;

  if (*q || p[0] != '=' || !p[1]) return 0;

  return p + 1;
}

static void
inc_forced_sat_solver (BtorMainApp *app)
{
  if (app->forced_sat_solvers++)
  {
    print_err (app, "can not force more than one SAT solver");
    app->err = 1;
  }
}

static void
parse_commandline_arguments (BtorMainApp *app)
{
  const char *matched_arg_str;
  FILE *temp_file;

  for (app->argpos = 1; !app->done && !app->err && app->argpos < app->argc;
       app->argpos++)
  {
    if (!strcmp (app->argv[app->argpos], "-h")
        || !strcmp (app->argv[app->argpos], "--help"))
    {
      fprintf (app->output_file, "%s\n", g_usage);
      app->done = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-c")
             || !strcmp (app->argv[app->argpos], "--copyright"))
    {
      fprintf (app->output_file, "%s", g_copyright);
      app->done = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-de")
             || !strcmp (app->argv[app->argpos], "--dump-exp"))
      app->dump_exp = 1;
    else if (!strcmp (app->argv[app->argpos], "-ds")
             || !strcmp (app->argv[app->argpos], "-d1")
             || !strcmp (app->argv[app->argpos], "-ds1")
             || !strcmp (app->argv[app->argpos], "--dump-smt")
             || !strcmp (app->argv[app->argpos], "--dump-smt1"))
      app->dump_smt = 1;
    else if (!strcmp (app->argv[app->argpos], "-d2")
             || !strcmp (app->argv[app->argpos], "-ds2")
             || !strcmp (app->argv[app->argpos], "--dump-smt2"))
      app->dump_smt = 2;
    else if (!strcmp (app->argv[app->argpos], "-d2fun")
             || !strcmp (app->argv[app->argpos], "-ds2fun")
             || !strcmp (app->argv[app->argpos], "--dump-smt2-fun"))
      app->dump_smt = 3;
    else if (!strcmp (app->argv[app->argpos], "-m")
             || !strcmp (app->argv[app->argpos], "--model"))
      app->print_model = 1;
    else if (!strcmp (app->argv[app->argpos], "--btor"))
      app->force_smt_input = -1;
    else if (!strcmp (app->argv[app->argpos], "--smt")
             || !strcmp (app->argv[app->argpos], "--smt1"))
      app->force_smt_input = 1;
    else if (!strcmp (app->argv[app->argpos], "--smt2"))
      app->force_smt_input = 2;
#ifdef BTOR_USE_LINGELING
    else if (!strcmp (app->argv[app->argpos], "--no-fork"))
      app->nofork = 1;
#endif
    else if ((strstr (app->argv[app->argpos], "-rwl") == app->argv[app->argpos]
              && strlen (app->argv[app->argpos]) == strlen ("-rlw") + 1)
             || (strstr (app->argv[app->argpos], "--rewrite-level")
                     == app->argv[app->argpos]
                 && strlen (app->argv[app->argpos])
                        == strlen ("--rewrite-level") + 1))
    {
      app->rewrite_level =
          (int)
              app->argv[app->argpos][(int) strlen (app->argv[app->argpos]) - 1]
          - 48;
      if (app->rewrite_level > 3 || app->rewrite_level < 0)
      {
        print_err (app, "rewrite level has to be in [0,3]\n");
        app->err = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-bra")
             || !strcmp (app->argv[app->argpos], "--beta-reduce-all"))
    {
      app->beta_reduce_all = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-npp")
             || !strcmp (app->argv[app->argpos], "--no-pretty-print"))
    {
      app->pprint = 0;
    }
    else if (!strcmp (app->argv[app->argpos], "-v")
             || !strcmp (app->argv[app->argpos], "--verbose"))
    {
      if (app->verbosity < 0)
      {
        print_err (app, "'-q' and '-v' can not be combined\n");
        app->err = 1;
      }
      else if (app->verbosity == 4)
      {
        print_err (app, "can not increase verbosity beyond '4'\n");
        app->err = 1;
      }
      else
        app->verbosity++;
    }
#ifndef NBTORLOG
    else if (!strcmp (app->argv[app->argpos], "-l")
             || !strcmp (app->argv[app->argpos], "--log"))
    {
      app->loglevel++;
    }
#endif
    else if (!strcmp (app->argv[app->argpos], "-i")
             || !strcmp (app->argv[app->argpos], "-inc")
             || !strcmp (app->argv[app->argpos], "--inc")
             || !strcmp (app->argv[app->argpos], "-incremental")
             || !strcmp (app->argv[app->argpos], "--incremental"))
    {
      app->incremental |= BTOR_PARSE_MODE_BASIC_INCREMENTAL;
    }
    else if (!strcmp (app->argv[app->argpos], "-I"))
    {
      app->incremental |= BTOR_PARSE_MODE_INCREMENTAL_BUT_CONTINUE;
    }
    else if (parse_option_with_int_value (app, "in-depth", &app->indepth))
    {
      if (app->indepth < 1)
      {
        print_err (app, "argument to '-in-depth' smaller than 1\n");
        app->err = 1;
      }
    }
    else if (parse_option_with_int_value (app, "look-ahead", &app->lookahead))
    {
      if (app->lookahead < 1)
      {
        print_err (app, "argument to '-look-ahead' smaller than 1\n");
        app->err = 1;
      }
    }
    else if (parse_option_with_int_value (app, "interval", &app->interval))
    {
      if (app->interval < 1)
      {
        print_err (app, "argument to '-interval' smaller than 1\n");
        app->err = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-t"))
    {
      if (app->argpos + 1 < app->argc)
      {
        btor_static_set_alarm = atoi (app->argv[++app->argpos]);
        if (btor_static_set_alarm <= 0)
        {
          print_err (app, "argument to '-t' invalid (should be positive)");
          app->err = 1;
        }
      }
      else
      {
        print_err (app, "argument to '-t' option missing");
        app->err = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-V")
             || !strcmp (app->argv[app->argpos], "--version"))
    {
      fprintf (app->output_file, "%s\n", BTOR_VERSION);
      app->done = 1;
    }
    else if ((matched_arg_str =
                  match_long_opt (app->argv[app->argpos], "solver")))
    {
      inc_forced_sat_solver (app);
      app->forced_sat_solver_name = matched_arg_str;
    }
#ifdef BTOR_USE_PICOSAT
    else if (!strcmp (app->argv[app->argpos], "-picosat")
             || !strcmp (app->argv[app->argpos], "--picosat"))
    {
      inc_forced_sat_solver (app);
      app->force_picosat = 1;
    }
#endif
#ifdef BTOR_USE_LINGELING
    else if (!strcmp (app->argv[app->argpos], "-lingeling")
             || !strcmp (app->argv[app->argpos], "--lingeling"))
    {
      inc_forced_sat_solver (app);
      app->force_lingeling = 1;
    }
#endif
#ifdef BTOR_USE_MINISAT
    else if (!strcmp (app->argv[app->argpos], "-minisat")
             || !strcmp (app->argv[app->argpos], "--minisat"))
    {
      inc_forced_sat_solver (app);
      app->force_minisat = 1;
    }
#endif
    else if (!strcmp (app->argv[app->argpos], "-x")
             || !strcmp (app->argv[app->argpos], "--hex"))
    {
      if (app->basis == BTOR_DECIMAL_BASIS)
      {
      HEXANDDECIMAL:
        print_err (app, "can not force hexadecimal and decimal output");
        app->err = 1;
      }
      else
        app->basis = BTOR_HEXADECIMAL_BASIS;
    }
    else if (!strcmp (app->argv[app->argpos], "-d")
             || !strcmp (app->argv[app->argpos], "--decimal"))
    {
      if (app->basis == BTOR_HEXADECIMAL_BASIS) goto HEXANDDECIMAL;

      app->basis = BTOR_DECIMAL_BASIS;
    }
    else if (!strcmp (app->argv[app->argpos], "-o")
             || !strcmp (app->argv[app->argpos], "--output"))
    {
      if (app->argpos < app->argc - 1)
      {
        if (app->close_output_file)
        {
          print_err_va_args (app, "multiple output files\n");
          app->err = 1;
        }
        else
        {
          app->output_file = fopen (app->argv[++app->argpos], "w");
          if (!app->output_file)
          {
            print_err_va_args (
                app, "can not create '%s'\n", app->argv[app->argpos]);
            app->err = 1;
          }
          else
            app->close_output_file = 1;
        }
      }
    }
    else if (app->argv[app->argpos][0] == '-'
             && app->argv[app->argpos][1] == 'l')
    {
#ifndef BTOR_USE_LINGELING
      print_err (app, "can not use '-l' without Lingeling support\n");
      app->err = 1;
#else
      if (app->lingeling_options)
      {
        print_err (app, "multiple '-l'\n");
        app->err = 1;
      }
      else
        app->lingeling_options = app->argv[app->argpos] + 2;
#endif
    }
    else if (app->argv[app->argpos][0] == '-')
    {
      print_err_va_args (app, "invalid option '%s'\n", app->argv[app->argpos]);
      app->err = 1;
    }
    else if (app->close_input_file)
    {
      print_err_va_args (app, "multiple input files\n");
      app->err = 1;
    }
    else
    {
      char *name = app->argv[app->argpos];
      if (!btor_file_exists (name))
      {
        temp_file = 0;
      }
      else if (has_suffix (name, ".gz"))
      {
        char *cmd = malloc (strlen (name) + 40);
        sprintf (cmd, "gunzip -c %s", name);
        if ((temp_file = popen (cmd, "r"))) app->close_input_file = 2;
        free (cmd);
      }
      else if (has_suffix (name, ".bz2"))
      {
        char *cmd = malloc (strlen (name) + 40);
        sprintf (cmd, "bzcat %s", name);
        if ((temp_file = popen (cmd, "r"))) app->close_input_file = 2;
        free (cmd);
      }
      else if (has_suffix (name, ".7z"))
      {
        char *cmd = malloc (strlen (name) + 40);
        sprintf (cmd, "7z x -so %s 2>/dev/null", name);
        if ((temp_file = popen (cmd, "r"))) app->close_input_file = 2;
        free (cmd);
      }
      else
      {
        if ((temp_file = fopen (name, "r"))) app->close_input_file = 1;
      }

      if (temp_file)
      {
        app->input_file_name = name;
        app->input_file      = temp_file;
      }
      else
      {
        print_err_va_args (app, "can not read '%s'\n", name);
        app->err = 1;
      }
    }
  }

  if (!app->err && !app->incremental
      && (app->indepth || app->lookahead || app->interval))
  {
    app->incremental = BTOR_PARSE_MODE_BASIC_INCREMENTAL;
  }

  if (!app->err
      && (app->indepth != 0) + (app->lookahead != 0) + (app->interval != 0)
             >= 2)
  {
    print_err_va_args (
        app,
        "Can only use one out of '-in-depth', '-look-ahead', or '-interval'");
    app->err = 1;
  }

  if (!app->err && app->verbosity > 0 && app->incremental)
    btor_msg_main ("incremental mode through command line option\n");
  if (!app->err && app->verbosity > 0 && app->indepth)
    btor_msg_main_va_args ("incremental in-depth window of %d\n", app->indepth);
  if (!app->err && app->verbosity > 0 && app->lookahead)
    btor_msg_main_va_args ("incremental look-ahead window of %d\n",
                           app->lookahead);
  if (!app->err && app->verbosity > 0 && app->interval)
    btor_msg_main_va_args ("incremental interval window of %d\n",
                           app->interval);
}

static void
print_sat_result (BtorMainApp *app, int sat_result)
{
  assert (app);
  if (sat_result == BTOR_UNSAT)
    fprintf (app->output_file, "unsat\n");
  else if (sat_result == BTOR_SAT)
    fprintf (app->output_file, "sat\n");
  else
  {
    assert (sat_result == BTOR_UNKNOWN);
    fprintf (app->output_file, "unknown\n");
  }
}

#ifdef BTOR_USE_LINGELING
static int
setup_lingeling (BtorMainApp *app, BtorSATMgr *smgr)
{
  if (btor_enable_lingeling_sat (smgr, app->lingeling_options, app->nofork))
    return 1;

  print_err_va_args (
      app, "invalid Lingeling options '-l%s'\n", app->lingeling_options);
  app->err = 1;
  return 0;
}
#endif

static int
setup_sat (BtorMainApp *app, BtorSATMgr *smgr)
{
  int forced_solvers = 0, used_solvers = 0;
#ifdef BTOR_USE_PICOSAT
  int use_picosat = 0;
#endif
#ifdef BTOR_USE_MINISAT
  int use_minisat = 0;
#endif
#ifdef BTOR_USE_LINGELING
  int use_lingeling = 0;
#endif
#ifdef BTOR_USE_PICOSAT
  if (app->force_picosat)
  {
    forced_solvers++;
    use_picosat = 1;
    used_solvers++;
  }
#endif
#ifdef BTOR_USE_MINISAT
  if (app->force_minisat)
  {
    forced_solvers++;
    use_minisat = 1;
    used_solvers++;
  }
#endif
#ifdef BTOR_USE_LINGELING
  if (app->force_lingeling)
  {
    forced_solvers++;
    use_lingeling = 1;
    used_solvers++;
  }
#endif
  assert (forced_solvers <= 1);

  // TODO remove the following defensive programming idiom.

  if (forced_solvers >= 2)
  {
    print_err (app, "can not force more than two SAT solvers\n");
    app->err = 1;
    return 0;
  }

#ifdef BTOR_USE_LINGELING
  if (!used_solvers)
  {
    use_lingeling = 1;
    used_solvers++;
  }
#endif
#ifdef BTOR_USE_MINISAT
  if (!used_solvers)
  {
    use_minisat = 1;
    used_solvers++;
  }
#endif
#ifdef BTOR_USE_PICOSAT
  if (!used_solvers)
  {
    use_picosat = 1;
    used_solvers++;
  }
#endif
  assert (used_solvers <= 1);

  if (!used_solvers)  // TODO make this a compile time error
  {
    print_err (app, "no usable SAT solver compiled in");
    app->err = 1;
    return 0;
  }

  assert (used_solvers == 1);
#ifdef BTOR_USE_PICOSAT
  if (use_picosat) btor_enable_picosat_sat (smgr);
#endif
#ifdef BTOR_USE_MINISAT
  if (use_minisat) btor_enable_minisat_sat (smgr);
#endif
#ifdef BTOR_USE_LINGELING
  if (use_lingeling) return setup_lingeling (app, smgr);
#endif
  return 1;
}

int
boolector_main (int argc, char **argv)
{
  BtorMainApp app;
  int return_val = 0;
  int sat_result = 0;
  int i          = 0;
  int root_len;
  const char *parse_error = 0;
  Btor *btor              = 0;
  BtorAIGMgr *amgr        = 0;
  BtorAIGVecMgr *avmgr    = 0;
  BtorSATMgr *smgr        = 0;
  BtorParseResult parse_res;
  const BtorParserAPI *parser_api = 0;
  BtorParser *parser              = 0;
  BtorParseOpt parse_opt;
  BtorMemMgr *mem = 0;
  BtorNode *root, *tmp, *all;
  BtorCharStack prefix;

  btor_static_start_time = btor_time_stamp ();

  memset (&app, 0, sizeof app);

  app.verbosity              = 0;
  app.incremental            = 0;
  app.indepth                = 0;
  app.lookahead              = 0;
  app.interval               = 0;
  app.output_file            = stdout;
  app.close_output_file      = 0;
  app.input_file             = stdin;
  app.input_file_name        = "<stdin>";
  app.close_input_file       = 0;
  app.argc                   = argc;
  app.argv                   = argv;
  app.argpos                 = 0;
  app.done                   = 0;
  app.err                    = 0;
  app.basis                  = BTOR_BINARY_BASIS;
  app.dump_exp               = 0;
  app.dump_smt               = 0;
  app.rewrite_level          = 3;
  app.force_smt_input        = 0;
  app.print_model            = 0;
  app.beta_reduce_all        = 0;
  app.pprint                 = 1;
  app.forced_sat_solver_name = 0;
  app.forced_sat_solvers     = 0;
#ifdef BTOR_USE_PICOSAT
  app.force_picosat = 0;
#endif
#ifdef BTOR_USE_LINGELING
  app.force_lingeling   = 0;
  app.lingeling_options = 0;
#endif
#ifdef BTOR_USE_MINISAT
  app.force_minisat = 0;
#endif
  btor_static_set_alarm = 0;

  parse_commandline_arguments (&app);

  if (app.verbosity > 0)
  {
    btor_msg_main_va_args ("Boolector Version %s %s\n", BTOR_VERSION, BTOR_ID);
    btor_msg_main_va_args ("%s\n", BTOR_CC);
    btor_msg_main_va_args ("%s\n", BTOR_CFLAGS);
    btor_msg_main_va_args ("released %s\n", BTOR_RELEASED);
    btor_msg_main_va_args ("compiled %s\n", BTOR_COMPILED);
    if (*BTOR_CC) btor_msg_main_va_args ("%s\n", BTOR_CC);
  }

  if (!app.done && !app.err)
  {
    parse_opt.verbosity   = app.verbosity;
    parse_opt.incremental = app.incremental;
    if (app.indepth)
    {
      parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_IN_DEPTH;
      parse_opt.window = app.indepth;
    }
    else if (app.lookahead)
    {
      parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_LOOK_AHEAD;
      parse_opt.window = app.lookahead;
    }
    else if (app.interval)
    {
      parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_INTERVAL;
      parse_opt.window = app.interval;
    }
    parse_opt.need_model = app.print_model;

    BTOR_INIT_STACK (prefix);

    // btor_static_btor = btor = btor_new_btor ();
    btor_static_btor = btor = boolector_new ();
    btor_static_verbosity   = app.verbosity;
    btor_set_rewrite_level_btor (btor, app.rewrite_level);

    if (app.beta_reduce_all) btor_enable_beta_reduce_all (btor);

    if (!app.pprint) btor_disable_pretty_print (btor);

    if (app.print_model) btor_enable_model_gen (btor);

    btor_set_verbosity_btor (btor, app.verbosity);
#ifndef NBTORLOG
    if (!app.loglevel && getenv ("BTORLOG")) app.loglevel = 1;
    btor_set_loglevel_btor (btor, app.loglevel);
#endif
    mem = btor->mm;

    avmgr            = btor->avmgr;
    amgr             = btor_get_aig_mgr_aigvec_mgr (avmgr);
    btor_static_smgr = smgr = btor_get_sat_mgr_aig_mgr (amgr);

    if (app.verbosity > 0) btor_msg_main ("setting signal handlers\n");
    btor_set_sig_handlers ();
    if (btor_static_set_alarm)
    {
      assert (btor_static_set_alarm > 0);
      if (app.verbosity > 0)
        btor_msg_main_va_args ("setting time limit to %d seconds\n",
                               btor_static_set_alarm);
      btor_set_alarm ();
    }
    else if (app.verbosity > 0)
      btor_msg_main ("no time limit\n");

    if (app.force_smt_input == -1)
    {
      parser_api = btor_btor_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main ("forced BTOR parsing through command line option\n");
    }
    else if (app.force_smt_input == 1)
    {
      parser_api = btor_smt_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main (
            "forced SMTLIB version 1 parsing through command line option\n");
    }
    else if (app.force_smt_input == 2)
    {
      parser_api = btor_smt2_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main (
            "forced SMTLIB version 2 parsing through command line option\n");
    }
    else if (app.close_input_file
             && file_name_has_suffix (app.input_file_name, ".btor"))
    {
      parser_api = btor_btor_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "assuming BTOR parsing because of '.btor' suffix\n");
    }
    else if (app.close_input_file
             && file_name_has_suffix (app.input_file_name, ".smt2"))
    {
      parser_api = btor_smt2_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "assuming SMTLIB version 2 parsing because of '.smt2' suffix\n");
    }
    else
    {
      int ch, first, second;
      parser_api = btor_btor_parser_api ();
      first = second = 0;
      for (;;)
      {
        ch = getc (app.input_file);
        BTOR_PUSH_STACK (mem, prefix, ch);
        if (!ch || ch == EOF) break;
        if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')
        {
          BTOR_PUSH_STACK (mem, prefix, ch);
        }
        else if (ch == ';')
        {
          BTOR_PUSH_STACK (mem, prefix, ';');
          do
          {
            ch = getc (app.input_file);
            if (ch == EOF) break;
            BTOR_PUSH_STACK (mem, prefix, ch);
          } while (ch != '\n');
          if (ch == EOF) break;
        }
        else if (!first)
          first = ch;
        else
        {
          second = ch;
          break;
        }
      }
      if (ch != EOF && ch)
      {
        assert (first && second);
        if (first == '(')
        {
          if (second == 'b')
          {
            parser_api = btor_smt_parser_api ();
            if (app.verbosity > 0)
              btor_msg_main_va_args (
                  "assuming SMTLIB version 1 "
                  "parsing because of '(b' "
                  "prefix\n");
          }
          else
          {
            parser_api = btor_smt2_parser_api ();
            if (app.verbosity > 0)
            {
              if (isprint (second))
                btor_msg_main_va_args (
                    "assuming SMTLIB version 2 "
                    "parsing because of '(%c' "
                    "prefix\n",
                    second);
              else
                btor_msg_main_va_args (
                    "assuming SMTLIB version 2 "
                    "parsing because of '(' "
                    "but not '(b' prefix\n");
            }
          }
        }
        else if (app.verbosity > 0)
          btor_msg_main_va_args (
              "assuming BTOR parsing because first "
              "character differs from '('\n");
      }
      else if (app.verbosity > 0)
      {
        if (ch == EOF)
          btor_msg_main_va_args (
              "assuming BTOR parsing because "
              "end-of-file found\n");
        else
        {
          assert (!ch);
          btor_msg_main_va_args (
              "assuming BTOR parsing because "
              "zero byte found\n");
        }
      }
    }
    parser = parser_api->init (btor, &parse_opt);

    if (app.forced_sat_solver_name)
    {
#ifdef BTOR_USE_LINGELING
      if (!strcasecmp (app.forced_sat_solver_name, "lingeling"))
      {
        if (!setup_lingeling (&app, smgr)) goto DONE;
      }
      else
#endif
          if (!boolector_set_sat_solver (btor, app.forced_sat_solver_name))
      {
        print_err_va_args (&app,
                           "invalid SAT solver in '--solver=%s'\n",
                           app.forced_sat_solver_name);
        app.err = 1;
        goto DONE;
      }
      // else SAT solver properly set up ...
    }
    else if (!setup_sat (&app, smgr))
      goto DONE;

    btor_init_sat (smgr);
    btor_set_output_sat (smgr, stdout);
    btor_enable_verbosity_sat (smgr, app.verbosity);

    if (app.incremental)
    {
      btor_enable_inc_usage (btor);

      if (app.verbosity > 0) btor_msg_main ("starting incremental BTOR mode\n");

      sat_result = BTOR_UNKNOWN;

      if (app.err)
      {
        /* do nothing */
      }
      else if ((parse_error = parser_api->parse (parser,
                                                 &prefix,
                                                 app.input_file,
                                                 app.input_file_name,
                                                 &parse_res)))
      {
        fprintf (app.output_file, "%s\n", parse_error);
        app.err = 1;
      }
      else
      {
        if (parse_res.result == BTOR_PARSE_SAT_STATUS_SAT)
        {
          if (app.verbosity > 0)
            btor_msg_main ("one formula SAT in incremental mode\n");

          sat_result = BTOR_SAT;
        }
        else if (parse_res.result == BTOR_PARSE_SAT_STATUS_UNSAT)
        {
          if (app.verbosity > 0)
            btor_msg_main ("all formulas UNSAT in incremental mode\n");

          sat_result = BTOR_UNSAT;
        }
        else
          sat_result = BTOR_UNKNOWN;

        print_sat_result (&app, sat_result);

        if (app.print_model && sat_result == BTOR_SAT)
          print_assignment (&app, btor, &parse_res);

        if (app.verbosity > 0)
        {
          btor_print_stats_sat (smgr);
          btor_print_stats_btor (btor);
        }
      }
    }
    else if ((parse_error = parser_api->parse (parser,
                                               &prefix,
                                               app.input_file,
                                               app.input_file_name,
                                               &parse_res)))
    {
      fprintf (app.output_file, "%s\n", parse_error);
      app.err = 1;
    }
    else if (app.dump_exp)
    {
      if (app.verbosity > 0)
        btor_msg_main_va_args ("dumping BTOR expressions\n");

      assert (app.rewrite_level >= 0);
      assert (app.rewrite_level <= 3);
      if (app.rewrite_level >= 2)
      {
        for (i = 0; i < parse_res.noutputs; i++)
        {
          root     = parse_res.outputs[i];
          root_len = btor_get_exp_len (btor, root);
          assert (root_len >= 1);
          if (root_len > 1)
            root = btor_redor_exp (btor, root);
          else
            root = btor_copy_exp (btor, root);
          btor_add_constraint_exp (btor, root);
          btor_release_exp (btor, root);
        }
        parser_api->reset (parser);
        parser_api = 0;
        btor_dump_exps_after_global_rewriting (btor, app.output_file);
      }
      else
        btor_dump_exps (
            btor, app.output_file, parse_res.outputs, parse_res.noutputs);
      app.done = 1;
    }
    else if (app.dump_smt)
    {
      if (app.verbosity > 0)
      {
        if (app.dump_smt < 2)
          btor_msg_main_va_args ("dumping in SMT 1.2 format\n");
        else
          btor_msg_main_va_args ("dumping in SMT 2.0 format\n");
      }

      assert (app.rewrite_level >= 0);
      assert (app.rewrite_level <= 3);
      if (app.rewrite_level >= 2)
      {
        for (i = 0; i < parse_res.noutputs; i++)
        {
          root     = parse_res.outputs[i];
          root_len = btor_get_exp_len (btor, root);
          assert (root_len >= 1);
          if (root_len > 1)
            root = btor_redor_exp (btor, root);
          else
            root = btor_copy_exp (btor, root);
          btor_add_constraint_exp (btor, root);
          btor_release_exp (btor, root);
        }
        parser_api->reset (parser);
        parser_api = 0;

        if (app.dump_smt <= 1)
          btor_dump_smt1_after_global_rewriting (btor, app.output_file);
        else if (app.dump_smt == 2)
          btor_dump_smt2_after_global_rewriting (btor, app.output_file);
        else
          btor_dump_smt2_fun_after_global_rewriting (btor, app.output_file);
      }
      else
      {
        all = 0;
        for (i = 0; i < parse_res.noutputs; i++)
        {
          root     = parse_res.outputs[i];
          root_len = btor_get_exp_len (btor, root);
          assert (root_len >= 1);
          if (root_len > 1)
            root = btor_redor_exp (btor, root);
          else
            root = btor_copy_exp (btor, root);
          if (all)
          {
            tmp = btor_and_exp (btor, all, root);
            btor_release_exp (btor, root);
            btor_release_exp (btor, all);
            all = tmp;
          }
          else
            all = root;
        }

        if (app.dump_smt <= 1)
          btor_dump_smt1 (btor, app.output_file, &all, parse_res.noutputs);
        else if (app.dump_smt == 2)
          btor_dump_smt2 (btor, app.output_file, &all, parse_res.noutputs);
        else
          btor_dump_smt2_fun (btor, app.output_file, &all, parse_res.noutputs);

        if (all) btor_release_exp (btor, all);
      }

      app.done = 1;
    }
    else
    {
      assert (!app.incremental);
      if (app.verbosity > 0)
      {
        btor_msg_main_va_args ("parsed %d inputs and %d outputs\n",
                               parse_res.ninputs,
                               parse_res.noutputs);
        if (parse_res.logic == BTOR_LOGIC_QF_BV)
        {
          btor_msg_main ("logic QF_BV\n");
        }
        else
        {
          assert (parse_res.logic == BTOR_LOGIC_QF_AUFBV);
          btor_msg_main ("logic QF_AUFBV\n");
        }

        if (parse_res.status == BTOR_PARSE_SAT_STATUS_SAT)
          btor_msg_main ("status sat\n");
        else if (parse_res.status == BTOR_PARSE_SAT_STATUS_UNSAT)
          btor_msg_main ("status unsat\n");
        else
        {
          assert (parse_res.status == BTOR_PARSE_SAT_STATUS_UNKNOWN);
          btor_msg_main ("status unknown\n");
        }
      }

      if (parse_res.logic == BTOR_LOGIC_QF_BV)
      {
        if (app.verbosity)
          btor_msg_main ("no need for incremental SAT solving\n");
        smgr->inc_required = 0;
      }
      else
      {
        assert (parse_res.logic == BTOR_LOGIC_QF_AUFBV);
        assert (smgr->inc_required);
        if (app.verbosity)
          btor_msg_main ("requiring incremental SAT solving\n");
        smgr->inc_required = 1;
      }

      if (app.verbosity > 0) btor_msg_main ("generating SAT instance\n");

      for (i = 0; i < parse_res.noutputs; i++)
      {
        root     = parse_res.outputs[i];
        root_len = btor_get_exp_len (btor, root);
        assert (root_len >= 1);
        if (root_len > 1)
          root = btor_redor_exp (btor, root);
        else
          root = btor_copy_exp (btor, root);
        btor_add_constraint_exp (btor, root);
        btor_release_exp (btor, root);
      }

      if (!app.print_model)
      {
        parser_api->reset (parser);
        parser_api = 0;
      }

      if (app.verbosity > 1)
        btor_msg_main_va_args ("added %d outputs (100%)\n", parse_res.noutputs);

      sat_result = btor_sat_btor (btor);
      assert (sat_result != BTOR_UNKNOWN);

      /* check if status is equal to benchmark status */
      if (sat_result == BTOR_SAT
          && parse_res.status == BTOR_PARSE_SAT_STATUS_UNSAT)
      {
        fprintf (app.output_file,
                 "[btormain] ERROR: "
                 "'sat' but status of benchmark in '%s' is 'unsat'\n",
                 app.input_file_name);
      }
      else if (sat_result == BTOR_UNSAT
               && parse_res.status == BTOR_PARSE_SAT_STATUS_SAT)
      {
        fprintf (app.output_file,
                 "[btormain] ERROR: "
                 "'unsat' but status of benchmark in '%s' is 'sat'\n",
                 app.input_file_name);
      }
      else
        print_sat_result (&app, sat_result);

      if (sat_result == BTOR_SAT && app.print_model)
        print_assignment (&app, btor, &parse_res);

      if (app.verbosity > 0)
      {
        btor_print_stats_sat (smgr);
        btor_print_stats_btor (btor);
      }
    }

    btor_static_smgr = 0;
    btor_reset_sat (smgr);
  DONE:
    if (parser_api)
    {
      assert (parser);
      parser_api->reset (parser);
    }

    if (!app.err && !app.done && app.verbosity > 0) btor_print_static_stats ();

    btor_static_btor      = 0;
    btor_static_verbosity = 0;
    BTOR_RELEASE_STACK (mem, prefix);
    btor_delete_btor (btor);

    btor_reset_sig_handlers ();
  }

  if (app.close_input_file == 1) fclose (app.input_file);
  if (app.close_input_file == 2) pclose (app.input_file);
  if (app.close_output_file) fclose (app.output_file);
  if (app.err)
    return_val = BTOR_ERR_EXIT;
  else if (app.done)
    return_val = BTOR_SUCC_EXIT;
  else if (sat_result == BTOR_UNSAT)
    return_val = BTOR_UNSAT_EXIT;
  else if (sat_result == BTOR_SAT)
    return_val = BTOR_SAT_EXIT;
  else
  {
    assert (sat_result == BTOR_UNKNOWN);
    return_val = BTOR_UNKNOWN_EXIT;
  }
  return return_val;
}
