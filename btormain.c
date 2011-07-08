/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010-2011 Armin Biere, FMV, JKU.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "btormain.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbtor.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btorhash.h"
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

#define BTOR_HAVE_STAT
#define BTOR_HAVE_ISATTY

#ifdef BTOR_HAVE_STAT
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

#ifdef BTOR_HAVE_ISATTY
#include <unistd.h>
#endif

#define BTOR_MAIN_DEFAULT_MAXK 32

enum BtorBasis
{
  BTOR_BINARY_BASIS = 0,
  BTOR_DECIMAL_BASIS,
  BTOR_HEXADECIMAL_BASIS
};

typedef enum BtorBasis BtorBasis;

enum BtorAppMode
{
  BTOR_APP_REGULAR_MODE = 0,
  BTOR_APP_BMC_MODE
};

typedef enum BtorAppMode BtorAppMode;

enum BtorAppBMCMode
{
  BTOR_APP_BMC_MODE_BASE_INDUCT = 0,
  BTOR_APP_BMC_MODE_BASE_ONLY,
  BTOR_APP_BMC_MODE_INDUCT_ONLY
};

typedef enum BtorAppBMCMode BtorAppBMCMode;

enum BtorAppReplayMode
{
  BTOR_APP_REPLAY_MODE_NONE = 0,
  BTOR_APP_REPLAY_MODE_FULL,
};

typedef enum BtorAppReplayMode BtorAppReplayMode;

enum BtorPrintModel
{
  BTOR_APP_PRINT_MODEL_NONE = 0,
  BTOR_APP_PRINT_MODEL_PARTIAL,
  BTOR_APP_PRINT_MODEL_FULL
};

typedef enum BtorPrintModel BtorPrintModel;

struct BtorMainApp
{
  FILE *output_file;
  int close_output_file;
  FILE *input_file;
  char *input_file_name;
  int close_input_file;
  FILE *replay_file;
  int close_replay_file;
  BtorAppReplayMode replay_mode;
  int verbosity;
  int incremental;
  int force;
  int done;
  int err;
  int argpos;
  int argc;
  char **argv;
  BtorBasis basis;
  BtorAppMode app_mode;
  BtorAppBMCMode bmc_mode;
  int dump_exp;
  FILE *exp_file;
  int close_exp_file;
  int dump_smt;
  FILE *smt_file;
  int close_smt_file;
  int rewrite_level;
  int ua;
  int ua_initial_eff_width;
  BtorUAMode ua_mode;
  BtorUARef ua_ref;
  BtorUAEnc ua_enc;
  int bmcmaxk;
  int bmcadc;
  BtorCNFEnc cnf_enc;
  int force_smt_input;
  BtorPrintModel print_model;
#ifdef BTOR_USE_PICOSAT
  int force_picosat;
#endif
#ifdef BTOR_USE_PRECOSAT
  int force_precosat;
#endif
#ifdef BTOR_USE_LINGELING
  int force_lingeling;
#endif
#ifdef BTOR_USE_MINISAT
  int force_minisat;
#endif
};

typedef struct BtorMainApp BtorMainApp;

static const char *g_usage =
    "usage: boolector [<option>...][<input>]\n"
    "\n"
    "where <option> is one of the following:\n"
    "\n"
    "  -h|--help                        print usage information and exit\n"
    "  -c|--copyright                   print copyright and exit\n"
    "  -V|--version                     print version and exit\n"
    "\n"
    "  -[p]m|--[partial-]model          print partial model in the SAT case\n"
    "  -fm|--full-model                 print full model (BV) in the SAT case\n"
    "  -q|--quiet                       do not print any output\n"
    "  -v|--verbose                     increase verbosity (0 default, 3 max)\n"
    "\n"
    "  -i|--inc[remental]               incremental mode (SMT only)\n"
    "  -I                               same but solve all\n"
    "\n"
    "  --btor                           force BTOR format input\n"
    "  --smt|--smt1                     force SMTLIB version 1 format input\n"
    "  --smt2                           force SMTLIB version 2 format input\n"
    "\n"
    "  -x|--hex                         hexadecimal output\n"
    "  -d|--dec                         decimal output\n"
    "  -o|--output <file>               set output file\n"
    "  -de|--dump-exp <file>            dump expression in BTOR format\n"
    "  -ds|--dump-smt <file>            dump expression in SMT format\n"
    "  -f|--force                       overwrite existing output file\n"
    "\n"
    "  -rwl<n>|--rewrite-level<n>       set rewrite level [0,3] (default 3)\n"
    "  -tcnf|--tseitin-cnf              Tseitin CNF encoding\n"
    "  -pgcnf|--plaisted-greenbaum-cnf  Plaisted-Greenbaum CNF encoding "
    "(default)\n"

    "\n"
    "  -picosat                         enforce usage of PicoSAT as SAT "
    "solver\n"
#ifdef BTOR_USE_PRECOSAT
    "  -precosat                        enforce usage of PrecoSAT as SAT "
    "solver\n"
#endif
#ifdef BTOR_USE_LINGELING
    "  -lingeling                       enforce usage of Lingeling as SAT "
    "solver\n"
#endif
#ifdef BTOR_USE_MINISAT
    "  -minisat                         enforce usage of MiniSAT as SAT "
    "solver\n"
#endif
    "\n"
    "Under-approximation options:\n"
    "  -ua                              enable under-approximation (UA)\n"
    "  -uaw=<n>                         initial effecitve bit-width (default "
    "n=1)\n"
    "\n"
    "  -uai                             eff. width refinement by incrementing\n"
    "  -uad                             eff. width refinement by doubling "
    "(default)\n"
    "\n"
    "  -ual                             local refinement strategy\n"
    "  -uali                            local individual refinement strategy\n"
    "  -uag                             global refinement strategy (default)\n"
    "\n"
    "  -uaz                             UA encoding by zero-extension\n"
    "  -uao                             UA encoding by one-extension\n"
    "  -uac                             UA encoding by equivalence classes\n"
    "  -uas                             UA encoding by sign-extension "
    "(default)\n"
    "\n"
    "\n"
    "BMC options:\n"
    "  -bmc-maxk=<k>                    sets maximum bound for model checking\n"
    "  -bmc-adc                         use all different constraints "
    "(default)\n"
    "  -bmc-no-adc                      disable all different constraints\n"
    "  -bmc-base-only                   base case (search for wittnesses, no "
    "adc)\n"
    "  -bmc-induct-only                 inductive case only\n"
    "  -bmc-replay <file>               turn replay on\n";

static const char *g_copyright =
    "Copyright (c) 2007 - 2008, Robert Brummayer, Armin Biere\n"
    "Institute for Formal Models and Verification\n"
    "Johannes Kepler University, Linz, Austria\n"
    "Licensed under the GNU Public License Version 3\n";

static int btor_static_verbosity;
static BtorSATMgr *btor_static_smgr;
static Btor *btor_static_btor;
static int btor_static_catched_sig;

static void (*btor_sig_int_handler) (int);
static void (*btor_sig_segv_handler) (int);
static void (*btor_sig_abrt_handler) (int);
static void (*btor_sig_term_handler) (int);
static void (*btor_sig_bus_handler) (int);

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
  printf ("[boolector] CAUGHT SIGNAL %d\n", sig);
  fflush (stdout);
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
    if (btor_static_verbosity)
    {
      if (btor_static_smgr) btor_print_stats_sat (btor_static_smgr);
      if (btor_static_btor) btor_print_stats_btor (btor_static_btor);
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

static void
btor_msg_main (char *msg)
{
  assert (msg != NULL);
  fprintf (stdout, "[btrmain] %s", msg);
  fflush (stdout);
}

static void
btor_msg_main_va_args (char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  va_start (list, msg);
  fprintf (stdout, "[btrmain] ");
  vfprintf (stdout, msg, list);
  va_end (list);
}

static void
print_msg (BtorMainApp *app, const char *msg)
{
  assert (msg != NULL);
  if (app->verbosity >= 0)
    fputs (msg, app->output_file); /* no 'fprintf' to avoid warning */
}

static void
print_msg_va_args (BtorMainApp *app, char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  if (app->verbosity >= 0)
  {
    va_start (list, msg);
    vfprintf (app->output_file, msg, list);
    va_end (list);
  }
}

static void
print_err (BtorMainApp *app, char *msg)
{
  assert (msg != NULL);
  if (app->verbosity >= 0)
  {
    fputs ("boolector: ", app->output_file);
    fputs (msg, app->output_file); /* no 'fprintf' to avoid warning */
  }
}

static void
print_err_va_args (BtorMainApp *app, char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  if (app->verbosity >= 0)
  {
    fputs ("boolector: ", app->output_file);
    va_start (list, msg);
    vfprintf (app->output_file, msg, list);
    va_end (list);
  }
}

static int
file_already_exists (const char *file_name)
{
#ifdef BTOR_HAVE_STAT
  struct stat buf;
  return !stat (file_name, &buf);
#else
  FILE *file = fopen (file_name, "r");
  int res;
  if (file)
  {
    fclose (file);
    res = 1;
  }
  else
    res = 1;
  return res;
#endif
}

static void
handle_dump_file (BtorMainApp *app,
                  int *dump_file,
                  int *close_file,
                  const char *file_kind,
                  FILE **file)
{
  const char *file_name;

  assert (dump_file != NULL);
  assert (close_file != NULL);
  assert (file_kind != NULL);
  assert (file != NULL);

  *dump_file = 1;

  if (app->argpos < app->argc - 1)
  {
    if (*close_file)
    {
      assert (*file != NULL);
      fclose (*file);
      *close_file = 0;
      print_err_va_args (app, "multiple %s files\n", file_kind);
      app->err = 1;
    }
    else
    {
      file_name = app->argv[++app->argpos];

      if (file_already_exists (file_name) && !app->force)
      {
        print_err_va_args (
            app,
            "will not overwrite existing %s file '%s' without '-f'\n",
            file_kind,
            file_name);

        app->err = 1;
      }
      else
      {
        *file = fopen (file_name, "w");
        if (*file == NULL)
        {
          print_err_va_args (
              app, "can not create '%s'\n", app->argv[app->argpos]);
          app->err = 1;
        }
        else
          *close_file = 1;
      }
    }
  }
}

static int
has_suffix (const char *str, const char *suffix)
{
  const char *p;

  for (p = str; *p; p++)
    if (!strcmp (p, suffix)) return 1;

  return 0;
}

static int
has_only_x (const char *str)
{
  const char *cur = NULL;
  assert (str != NULL);
  for (cur = str; *cur; cur++)
    if (*cur != 'x') return 0;
  return 1;
}

static void
convert_to_full_assignment (char *assignment)
{
  char *p;

  assert (assignment != NULL);

  for (p = assignment; *p; p++)
  {
    assert (*p == 'x' || *p == '0' || *p == '1');
    if (*p == 'x') *p = '0';
  }
}

static char *
format_assignment (BtorMainApp *app, Btor *btor, char *assignment)
{
  BtorBasis basis;
  char *pretty, *grounded;
  int not_binary;
  BtorMemMgr *mm;

  assert (app != NULL);
  assert (btor != NULL);
  assert (assignment != NULL);

  basis = app->basis;
  not_binary =
      (basis == BTOR_HEXADECIMAL_BASIS) || (basis == BTOR_DECIMAL_BASIS);
  mm = btor->mm;

  if (app->print_model == BTOR_APP_PRINT_MODEL_FULL)
    convert_to_full_assignment (assignment);

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
print_bv_assignment (BtorMainApp *app, Btor *btor, BtorExp *exp)
{
  char *pretty, *assignment;
  BtorMemMgr *mm = NULL;

  assert (app != NULL);
  assert (btor != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));

  mm = btor->mm;

  assignment = btor_bv_assignment_exp (btor, exp);
  assert (assignment != NULL);

  if (app->print_model == BTOR_APP_PRINT_MODEL_FULL || !has_only_x (assignment))
  {
    pretty = format_assignment (app, btor, assignment);
    print_msg_va_args (app, "%s %s\n", btor_get_symbol_exp (btor, exp), pretty);
    btor_free_bv_assignment_exp (btor, pretty);
  }

  btor_free_bv_assignment_exp (btor, assignment);
}

static void
print_variable_assignments (BtorMainApp *app,
                            Btor *btor,
                            BtorExp **vars,
                            int nvars)
{
  int i;

  assert (app != NULL);
  assert (btor != NULL);
  assert (vars != NULL);
  assert (nvars >= 0);

  for (i = 0; i < nvars; i++) print_bv_assignment (app, btor, vars[i]);
}

static void
print_array_assignment (BtorMainApp *app, Btor *btor, BtorExp *exp)
{
  char **indices, **values;
  char *pretty_index, *pretty_value;
  int i, size;

  assert (app != NULL);
  assert (btor != NULL);
  assert (exp != NULL);
  assert (!BTOR_IS_INVERTED_EXP (exp));
  btor_array_assignment_exp (btor, exp, &indices, &values, &size);
  if (size > 0)
  {
    for (i = 0; i < size; i++)
    {
      pretty_index = format_assignment (app, btor, indices[i]);
      pretty_value = format_assignment (app, btor, values[i]);
      print_msg_va_args (
          app, "%s[%s] %s\n", exp->symbol, pretty_index, pretty_value);
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
print_array_assignments (BtorMainApp *app,
                         Btor *btor,
                         BtorExp **arrays,
                         int narrays)
{
  int i;

  assert (app != NULL);
  assert (btor != NULL);
  assert (arrays != NULL);
  assert (narrays >= 0);

  for (i = 0; i < narrays; i++) print_array_assignment (app, btor, arrays[i]);
}

static void
parse_commandline_arguments (BtorMainApp *app)
{
  FILE *temp_file;
  for (app->argpos = 1; !app->done && !app->err && app->argpos < app->argc;
       app->argpos++)
  {
    if (!strcmp (app->argv[app->argpos], "-h")
        || !strcmp (app->argv[app->argpos], "--help"))
    {
      print_msg_va_args (app, "%s\n", g_usage);
      app->done = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-c")
             || !strcmp (app->argv[app->argpos], "--copyright"))
    {
      print_msg_va_args (app, "%s", g_copyright);
      app->done = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-f")
             || !strcmp (app->argv[app->argpos], "--force"))
      app->force = 1;
    else if (!strcmp (app->argv[app->argpos], "-de")
             || !strcmp (app->argv[app->argpos], "--dump-exp"))
      handle_dump_file (app,
                        &app->dump_exp,
                        &app->close_exp_file,
                        "expression",
                        &app->exp_file);
    else if (!strcmp (app->argv[app->argpos], "-m")
             || (!strcmp (app->argv[app->argpos], "-pm")
                 || !strcmp (app->argv[app->argpos], "--model"))
             || !strcmp (app->argv[app->argpos], "--partial-model"))
      app->print_model = BTOR_APP_PRINT_MODEL_PARTIAL;
    else if (!strcmp (app->argv[app->argpos], "-fm")
             || !strcmp (app->argv[app->argpos], "--full-model"))
      app->print_model = BTOR_APP_PRINT_MODEL_FULL;
    else if (!strcmp (app->argv[app->argpos], "-ds")
             || !strcmp (app->argv[app->argpos], "--dump-smt"))
      handle_dump_file (
          app, &app->dump_smt, &app->close_smt_file, "SMT", &app->smt_file);
    else if (!strcmp (app->argv[app->argpos], "--btor"))
      app->force_smt_input = -1;
    else if (!strcmp (app->argv[app->argpos], "--smt")
             || !strcmp (app->argv[app->argpos], "--smt1"))
      app->force_smt_input = 1;
    else if (!strcmp (app->argv[app->argpos], "--smt2"))
      app->force_smt_input = 2;
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
    else if (strstr (app->argv[app->argpos], "-bmc-maxk=")
             == app->argv[app->argpos])
    {
      app->bmcmaxk = atoi (app->argv[app->argpos] + 10);
      if (app->bmcmaxk < 0)
      {
        print_err (app, "invalid k\n");
        app->err = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-bmc-adc"))
      app->bmcadc = 1;
    else if (!strcmp (app->argv[app->argpos], "-bmc-no-adc"))
      app->bmcadc = 0;
    else if (!strcmp (app->argv[app->argpos], "-bmc-base-only"))
    {
      app->bmc_mode = BTOR_APP_BMC_MODE_BASE_ONLY;
      app->bmcadc   = 0;
    }
    else if (!strcmp (app->argv[app->argpos], "-bmc-induct-only"))
      app->bmc_mode = BTOR_APP_BMC_MODE_INDUCT_ONLY;
    else if (!strcmp (app->argv[app->argpos], "-v")
             || !strcmp (app->argv[app->argpos], "--verbose"))
    {
      if (app->verbosity < 0)
      {
        print_err (app, "'-q' and '-v' can not be combined\n");
        app->err = 1;
      }
      else if (app->verbosity == 3)
      {
        print_err (app, "can not increase verbosity beyond '3'\n");
        app->err = 1;
      }
      else
        app->verbosity++;
    }
    else if (!strcmp (app->argv[app->argpos], "-i")
             || !strcmp (app->argv[app->argpos], "-inc")
             || !strcmp (app->argv[app->argpos], "--inc")
             || !strcmp (app->argv[app->argpos], "-incremental")
             || !strcmp (app->argv[app->argpos], "--incremental"))
    {
      app->incremental = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-I"))
    {
      app->incremental = 2;
    }
    else if (!strcmp (app->argv[app->argpos], "-V")
             || !strcmp (app->argv[app->argpos], "--version"))
    {
      print_msg_va_args (app, "%s\n", BTOR_VERSION);
      app->done = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-q")
             || !strcmp (app->argv[app->argpos], "--quiet"))
    {
      if (app->verbosity > 0)
      {
        print_err (app, "'-q' and '-v' can not be combined\n");
        app->err = 1;
      }
      else
        app->verbosity = -1;
    }
#ifdef BTOR_USE_PICOSAT
    else if (!strcmp (app->argv[app->argpos], "-picosat")
             || !strcmp (app->argv[app->argpos], "--picosat"))
    {
      app->force_picosat = 1;
    }
#endif
#ifdef BTOR_USE_PRECOSAT
    else if (!strcmp (app->argv[app->argpos], "-precosat")
             || !strcmp (app->argv[app->argpos], "--precosat"))
    {
      app->force_precosat = 1;
    }
#endif
#ifdef BTOR_USE_LINGELING
    else if (!strcmp (app->argv[app->argpos], "-lingeling")
             || !strcmp (app->argv[app->argpos], "--lingeling"))
    {
      app->force_lingeling = 1;
    }
#endif
#ifdef BTOR_USE_MINISAT
    else if (!strcmp (app->argv[app->argpos], "-minisat")
             || !strcmp (app->argv[app->argpos], "--minisat"))
    {
      app->force_minisat = 1;
    }
#endif
    else if (!strcmp (app->argv[app->argpos], "-ua"))
      app->ua = 1;
    else if (strstr (app->argv[app->argpos], "-uaw=") == app->argv[app->argpos]
             && strlen (app->argv[app->argpos]) > strlen ("-uaw="))
    {
      app->ua_initial_eff_width = atoi (app->argv[app->argpos] + 5);
      app->ua                   = 1;
      if (app->ua_initial_eff_width < 1)
      {
        print_err (app, "UA start width must be greater than zero\n");
        app->err = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-ual"))
    {
      app->ua_mode = BTOR_UA_LOCAL_MODE;
      app->ua      = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-uali"))
    {
      app->ua_mode = BTOR_UA_LOCAL_INDIVIDUAL_MODE;
      app->ua      = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-uag"))
    {
      app->ua_mode = BTOR_UA_GLOBAL_MODE;
      app->ua      = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-uai"))
    {
      if (app->ua_enc == BTOR_UA_ENC_EQ_CLASSES)
      {
        print_err (app, "-uai and -uac cannot be combined\n");
        app->err = 1;
      }
      else
      {
        app->ua_ref = BTOR_UA_REF_BY_INC_ONE;
        app->ua     = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-uad"))
    {
      app->ua_ref = BTOR_UA_REF_BY_DOUBLING;
      app->ua     = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-uaz"))
    {
      app->ua_enc = BTOR_UA_ENC_ZERO_EXTEND;
      app->ua     = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-uao"))
    {
      app->ua_enc = BTOR_UA_ENC_ONE_EXTEND;
      app->ua     = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-uac"))
    {
      if (app->ua_ref == BTOR_UA_REF_BY_INC_ONE)
      {
        print_err (app, "-uai and -uac cannot be combined\n");
        app->err = 1;
      }
      else
      {
        app->ua_enc = BTOR_UA_ENC_EQ_CLASSES;
        app->ua     = 1;
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-uas"))
    {
      app->ua_enc = BTOR_UA_ENC_SIGN_EXTEND;
      app->ua     = 1;
    }
    else if (!strcmp (app->argv[app->argpos], "-tcnf")
             || !strcmp (app->argv[app->argpos], "--tseitin-cnf"))
      app->cnf_enc = BTOR_TSEITIN_CNF_ENC;
    else if (!strcmp (app->argv[app->argpos], "-pgcnf")
             || !strcmp (app->argv[app->argpos], "--plaisted-greenbaum-cnf"))
      app->cnf_enc = BTOR_PLAISTED_GREENBAUM_CNF_ENC;
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
          fclose (app->output_file);
          app->close_output_file = 0;
          app->output_file       = stdout;
          print_err_va_args (app, "multiple output files\n");
          app->err = 1;
        }
        else
        {
          app->output_file = fopen (app->argv[++app->argpos], "w");
          if (app->output_file == NULL)
          {
            app->output_file = stdout;
            print_err_va_args (
                app, "can not create '%s'\n", app->argv[app->argpos]);
            app->err = 1;
          }
          else
            app->close_output_file = 1;
        }
      }
    }
    else if (!strcmp (app->argv[app->argpos], "-bmc-replay"))
    {
      if (app->argpos < app->argc - 1)
      {
        if (app->close_replay_file)
        {
          fclose (app->replay_file);
          app->close_replay_file = 0;
          print_err_va_args (app, "multiple replay\n");
          app->err = 1;
        }
        else
        {
          app->replay_file = fopen (app->argv[++app->argpos], "w");
          if (app->replay_file == NULL)
          {
            print_err_va_args (
                app, "can not create '%s'\n", app->argv[app->argpos]);
            app->err = 1;
          }
          else
          {
            app->close_replay_file = 1;
            app->replay_mode       = BTOR_APP_REPLAY_MODE_FULL;
          }
        }
      }
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
    else if (!(temp_file = fopen (app->argv[app->argpos], "r")))
    {
      print_err_va_args (app, "can not read '%s'\n", app->argv[app->argpos]);
      app->err = 1;
    }
    else
    {
      app->input_file_name  = app->argv[app->argpos];
      app->input_file       = temp_file;
      app->close_input_file = 1;
    }
  }

  if (!app->err)
  {
    if (app->replay_mode != BTOR_APP_REPLAY_MODE_NONE
        && app->bmc_mode == BTOR_APP_BMC_MODE_BASE_INDUCT)
    {
      print_err_va_args (
          app, "Replay for 'base-and-induct' BMC mode is not supported\n");
      app->err = 1;
    }
  }
}

static void
print_sat_result (BtorMainApp *app, int sat_result)
{
  assert (app != NULL);
  if (sat_result == BTOR_UNSAT)
    print_msg (app, "unsat\n");
  else if (sat_result == BTOR_SAT)
    print_msg (app, "sat\n");
  else
  {
    assert (sat_result == BTOR_UNKNOWN);
    print_msg (app, "unknown\n");
  }
}

static BtorExp *
disjunct_constraints (Btor *btor, BtorExpPtrStack *constraints)
{
  int i;
  BtorExp *temp, *result;
  assert (btor != NULL);
  assert (constraints != NULL);
  result = btor_false_exp (btor);
  for (i = 0; i < BTOR_COUNT_STACK (*constraints); i++)
  {
    temp = btor_or_exp (btor, result, constraints->start[i]);
    btor_release_exp (btor, result);
    result = temp;
  }
  return result;
}

static BtorExp *
generate_regs_eq_zero (Btor *btor,
                       BtorPtrHashTable *inst_table,
                       const BtorExpPtrStack *bv_regs)
{
  int i;
  BtorExp *result, *temp, *zero, *eq, *cur, *inst;
  BtorPtrHashBucket *bucket;
  assert (btor != NULL);
  assert (inst_table != NULL);
  assert (bv_regs != NULL);
  result = btor_true_exp (btor);
  for (i = 0; i < BTOR_COUNT_STACK (*bv_regs); i++)
  {
    cur = bv_regs->start[i];
    assert (BTOR_IS_REGULAR_EXP (cur));
    assert (BTOR_IS_BV_VAR_EXP (cur));
    bucket = btor_find_in_ptr_hash_table (inst_table, cur);
    assert (bucket != NULL);
    assert (bucket->data.asPtr != NULL);
    inst = (BtorExp *) bucket->data.asPtr;
    zero = btor_zero_exp (btor, btor_get_exp_len (btor, inst));
    eq   = btor_eq_exp (btor, inst, zero);
    temp = btor_and_exp (btor, result, eq);
    btor_release_exp (btor, result);
    result = temp;
    btor_release_exp (btor, zero);
    btor_release_exp (btor, eq);
  }
  return result;
}

int
boolector_main (int argc, char **argv)
{
  BtorMainApp app;
#ifdef BTOR_HAVE_GETRUSAGE
  double start_time = btor_time_stamp ();
  double delta_time = 0.0;
#endif
  int return_val = 0;
  int sat_result = 0;
  int i          = 0;
  int bmc_done   = 0;
  int root_len, var_name_len;
  int need_incremental_sat_solver = 0;
  int constraints_reported, constraints_report_limit, nconstraints, bmck;
  const char *parse_error = NULL;
  char *var_name;
  Btor *btor           = NULL;
  BtorAIGMgr *amgr     = NULL;
  BtorAIGVecMgr *avmgr = NULL;
  BtorSATMgr *smgr     = NULL;
  BtorParseResult parse_res;
  BtorExpPtrStack varstack, constraints, bv_states, bv_regs, array_regs;
  BtorExpPtrStack arraystack;
  const BtorParserAPI *parser_api = NULL;
  BtorParser *parser              = NULL;
  BtorMemMgr *mem                 = NULL;
  size_t maxallocated             = 0;
  BtorExp *root, **p, *disjuncted_constraints, *bad, *bv_state;
  BtorExp **old_insts, **new_insts, *eq, *cur, *var, *temp;
  BtorExp *ne, *diff, *diff_bv, *diff_array, *not_bad;
  BtorExp *diff_arrays = NULL;
  BtorExp *regs_zero   = NULL;
  BtorPtrHashTable *reg_inst, *input_inst;
  BtorPtrHashBucket *bucket;
  BtorExpPtrStack *array_states = NULL;
  BtorCharStack prefix;

  memset (&app, 0, sizeof app);

  app.verbosity            = 0;
  app.incremental          = 0;
  app.force                = 0;
  app.output_file          = stdout;
  app.close_output_file    = 0;
  app.input_file           = stdin;
  app.input_file_name      = "<stdin>";
  app.close_input_file     = 0;
  app.close_replay_file    = 0;
  app.replay_mode          = BTOR_APP_REPLAY_MODE_NONE;
  app.argc                 = argc;
  app.argv                 = argv;
  app.argpos               = 0;
  app.done                 = 0;
  app.err                  = 0;
  app.basis                = BTOR_BINARY_BASIS;
  app.app_mode             = BTOR_APP_REGULAR_MODE;
  app.bmc_mode             = BTOR_APP_BMC_MODE_BASE_INDUCT;
  app.dump_exp             = 0;
  app.exp_file             = stdout;
  app.close_exp_file       = 0;
  app.dump_smt             = 0;
  app.smt_file             = stdout;
  app.close_smt_file       = 0;
  app.rewrite_level        = 3;
  app.ua                   = 0;
  app.ua_initial_eff_width = 1;
  app.ua_mode              = BTOR_UA_GLOBAL_MODE;
  app.ua_ref               = BTOR_UA_REF_BY_DOUBLING;
  app.ua_enc               = BTOR_UA_ENC_SIGN_EXTEND;
  app.bmcmaxk              = -1; /* -1 means it has not been set by the user */
  app.bmcadc               = 1;
#if 1
  // TODO try Tseitin as well
  app.cnf_enc = BTOR_TSEITIN_CNF_ENC;
#else
  app.cnf_enc = BTOR_PLAISTED_GREENBAUM_CNF_ENC;
#endif
  app.force_smt_input = 0;
  app.print_model     = BTOR_APP_PRINT_MODEL_NONE;
#ifdef BTOR_USE_PICOSAT
  app.force_picosat = 0;
#endif
#ifdef BTOR_USE_PRECOSAT
  app.force_precosat = 0;
#endif
#ifdef BTOR_USE_LINGELING
  app.force_lingeling = 0;
#endif
#ifdef BTOR_USE_MINISAT
  app.force_minisat = 0;
#endif

  parse_commandline_arguments (&app);

  if (app.verbosity > 0)
  {
    btor_msg_main_va_args ("Boolector Version %s %s\n", BTOR_VERSION, BTOR_ID);
    btor_msg_main_va_args ("%s\n", BTOR_CC);
    btor_msg_main_va_args ("%s\n", BTOR_CFLAGS);
    btor_msg_main_va_args ("released %s\n", BTOR_RELEASED);
    btor_msg_main_va_args ("compiled %s\n", BTOR_COMPILED);
    if (*BTOR_CC) btor_msg_main_va_args ("%s\n", BTOR_CC);

    /* Not really necessary?
     *
     * btor_msg_main_va_args ("%s\n", BTOR_OS);
     */
  }

  if (!app.done && !app.err)
  {
    BTOR_INIT_STACK (prefix);

    btor_static_btor = btor = btor_new_btor ();
    btor_static_verbosity   = app.verbosity;
    btor_set_rewrite_level_btor (btor, app.rewrite_level);

    if (app.print_model) btor_enable_model_gen (btor);

    if (app.ua)
    {
      btor_enable_under_approx (btor);
      btor_set_under_approx_initial_effective_width (btor,
                                                     app.ua_initial_eff_width);
      btor_set_under_approx_mode (btor, app.ua_mode);
      btor_set_under_approx_ref (btor, app.ua_ref);
      btor_set_under_approx_enc (btor, app.ua_enc);
    }
    btor_set_verbosity_btor (btor, app.verbosity);
    btor_set_replay_btor (btor, app.replay_mode != BTOR_APP_REPLAY_MODE_NONE);
    mem = btor->mm;

    avmgr            = btor->avmgr;
    amgr             = btor_get_aig_mgr_aigvec_mgr (avmgr);
    btor_static_smgr = smgr = btor_get_sat_mgr_aig_mgr (amgr);

    btor_set_sig_handlers ();

    if (app.force_smt_input == -1)
    {
      parser_api = btor_btor_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "forced BTOR parsing through command line option\n");
    }
    else if (app.force_smt_input == 1)
    {
      parser_api = btor_smt_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "forced SMTLIB version 1 parsing through command line option\n");
    }
    else if (app.force_smt_input == 2)
    {
      parser_api = btor_smt2_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "forced SMTLIB version 2 parsing through command line option\n");
    }
    else if (app.close_input_file && has_suffix (app.input_file_name, ".btor"))
    {
      parser_api = btor_btor_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "assuming BTOR parsing because of '.btor' suffix\n");
    }
    else if (app.close_input_file && has_suffix (app.input_file_name, ".smt2"))
    {
      parser_api = btor_smt2_parser_api ();
      if (app.verbosity > 0)
        btor_msg_main_va_args (
            "assuming SMTLIB version 2 parsing because of '.smt2' suffix\n");
    }
    else
    {
      int ch;
      parser_api = btor_btor_parser_api ();
      if ((ch = getc (app.input_file)) != EOF)
      {
        BTOR_PUSH_STACK (mem, prefix, ch);
        if (ch == '(')
        {
          if ((ch = getc (app.input_file)) != EOF)
          {
            BTOR_PUSH_STACK (mem, prefix, ch);
            if (ch == 'b')
            {
              parser_api = btor_smt_parser_api ();
              if (app.verbosity > 0)
                btor_msg_main_va_args (
                    "assuming SMTLIB version 1 parsing because of '(b' "
                    "prefix\n");
            }
            else if (ch == 's')
            {
              parser_api = btor_smt2_parser_api ();
              if (app.verbosity > 0)
                btor_msg_main_va_args (
                    "assuming SMTLIB version 2 parsing because of '(s' "
                    "prefix\n");
            }
          }
          else if (app.verbosity > 0)
            btor_msg_main_va_args (
                "assuming BTOR parsing because end of file after '('\n");
        }
        else if (app.verbosity > 0)
          btor_msg_main_va_args (
              "assuming BTOR parsing because first character different from "
              "'('\n");
      }
      else if (app.verbosity > 0)
        btor_msg_main_va_args (
            "assuming BTOR parsing because end of file found\n");
    }

    parser = parser_api->init (btor, app.verbosity, app.incremental);

    if (app.incremental)
    {
      btor_enable_inc_usage (btor);

#ifdef BTOR_USE_MINISAT
      if (app.force_picosat)
      {
        btor_enable_picosat_sat (smgr);
      }
#else
      if (1)
        ;
#endif
#ifdef BTOR_USE_MINISAT
      else if (app.force_minisat)
      {
        btor_enable_minisat_sat (smgr);
      }
#endif
#ifdef BTOR_USE_LINGELING
      else
      {
        btor_enable_lingeling_sat (smgr);
      }
#endif
      assert (btor_provides_incremental_sat (smgr));

      btor_init_sat (smgr, 1);
      btor_set_output_sat (smgr, stdout);

      if (app.verbosity >= 1) btor_enable_verbosity_sat (smgr);

      if (app.verbosity >= 1)
        btor_msg_main ("starting incremental BTOR mode\n");

      btor_set_cnf_enc_aig_mgr (amgr, app.cnf_enc);

      sat_result = BTOR_UNKNOWN;

      if ((parse_error = parser_api->parse (parser,
                                            &prefix,
                                            app.input_file,
                                            app.input_file_name,
                                            &parse_res)))
      {
        print_msg_va_args (&app, "%s\n", parse_error);
        app.err = 1;
      }
      else
      {
        if (parse_res.result == BTOR_PARSE_SAT_STATUS_SAT)
        {
          if (app.verbosity >= 1)
            btor_msg_main ("one forumla SAT in incremental mode\n");

          sat_result = BTOR_SAT;
        }
        else if (parse_res.result == BTOR_PARSE_SAT_STATUS_UNSAT)
        {
          if (app.verbosity >= 1)
            btor_msg_main ("all forumlas UNSAT in incremental mode\n");

          sat_result = BTOR_UNSAT;
        }
        else
          sat_result = BTOR_UNKNOWN;

        print_sat_result (&app, sat_result);

        if (app.print_model && sat_result == BTOR_SAT)
        {
          for (i = 0; i < parse_res.ninputs; i++)
          {
            var  = parse_res.inputs[i];
            temp = btor_pointer_chase_simplified_exp (btor, var);
            if (BTOR_IS_ARRAY_EXP (temp))
              print_array_assignment (&app, btor, var);
            else
              print_bv_assignment (&app, btor, var);
          }
        }

        if (app.verbosity > 0)
        {
          btor_print_stats_sat (smgr);
          btor_print_stats_btor (btor);
        }
      }

      btor_static_smgr = 0;
      btor_reset_sat (smgr);
    }
    else if ((parse_error = parser_api->parse (parser,
                                               &prefix,
                                               app.input_file,
                                               app.input_file_name,
                                               &parse_res)))
    {
      print_msg_va_args (&app, "%s\n", parse_error);
      app.err = 1;
    }
    else if (app.dump_exp)
    {
      if (app.verbosity) btor_msg_main_va_args ("dumping BTOR expressions\n");

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
        parser_api = NULL;
        btor_dump_exps_after_global_rewriting (btor, app.exp_file);
      }
      else
        btor_dump_exps (
            btor, app.exp_file, parse_res.outputs, parse_res.noutputs);
      app.done = 1;
    }
    else if (app.dump_smt)
    {
      if (parse_res.noutputs != 1)
      {
        print_msg_va_args (&app,
                           "%s: found %d outputs "
                           "but expected exactly one "
                           "when dumping smt\n",
                           app.input_file_name,
                           parse_res.noutputs);
        app.err = 1;
      }
      else
      {
        if (app.verbosity) btor_msg_main_va_args ("dumping in SMT format\n");

        app.done = 1;
        btor_dump_smt (btor, app.smt_file, parse_res.outputs[0]);
      }
    }
    else
    {
      assert (!app.incremental);

      if (app.ua || app.incremental || parse_res.logic != BTOR_LOGIC_QF_BV
          || parse_res.nregs)
        need_incremental_sat_solver = 1;

#ifdef BTOR_USE_PICOSAT
      if (app.force_picosat)
      {
        /* do nothing use PicoSAT */
      }
#else
      if (1)
        ;
#endif
#ifdef BTOR_USE_PRECOSAT
      else if (app.force_precosat)
      {
        if (need_incremental_sat_solver)
        {
          print_msg_va_args (&app,
                             "can not use PrecoSAT (incremental SAT required)");
          app.err = 1;
          goto DONE;
        }
        else
          btor_enable_precosat_sat (smgr);
      }
#endif
#ifdef BTOR_USE_MINISAT
      else if (app.force_minisat)
      {
        btor_enable_minisat_sat (smgr);
      }
#endif
#ifdef BTOR_USE_LINGELING
      else
      {
        btor_enable_lingeling_sat (smgr);
      }
#endif
#if !defined(BTOR_USE_LINGELING) && defined(BTOR_USE_PRECOSAT)
      else if (!need_incremental_sat_solver)
      {
        btor_enable_precosat_sat (smgr);
      }
#ifdef BTOR_USE_MINISAT
      else { btor_enable_minisat_sat (smgr); }
#endif
#endif
#if !defined(BTOR_USE_LINGELING) && !defined(BTOR_USE_PRECOSAT) \
    && defined(BTOR_USE_MINISAT)
      else { btor_enable_minisat_sat (smgr); }
#endif
      assert (need_incremental_sat_solver
              <= btor_provides_incremental_sat (smgr));

      btor_init_sat (smgr, need_incremental_sat_solver);
      btor_set_output_sat (smgr, stdout);

      if (app.verbosity > 0)
      {
        btor_msg_main_va_args ("parsed %d inputs and %d outputs\n",
                               parse_res.ninputs,
                               parse_res.noutputs);
        if (parse_res.logic == BTOR_LOGIC_QF_BV)
          btor_msg_main ("logic QF_BV\n");
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

      if (app.verbosity >= 1) btor_enable_verbosity_sat (smgr);

      if (app.verbosity >= 1) btor_msg_main ("generating SAT instance\n");

      btor_set_cnf_enc_aig_mgr (amgr, app.cnf_enc);

      BTOR_INIT_STACK (varstack);
      BTOR_INIT_STACK (arraystack);
      BTOR_INIT_STACK (constraints);

      if (app.print_model)
      {
        for (i = 0; i < parse_res.ninputs; i++)
        {
          assert (!BTOR_IS_INVERTED_EXP (parse_res.inputs[i]));
          assert (BTOR_IS_BV_VAR_EXP (parse_res.inputs[i])
                  || BTOR_IS_ARRAY_VAR_EXP (parse_res.inputs[i]));
          if (BTOR_IS_BV_VAR_EXP (parse_res.inputs[i]))
            BTOR_PUSH_STACK (
                mem, varstack, btor_copy_exp (btor, parse_res.inputs[i]));
          else
            BTOR_PUSH_STACK (
                mem, arraystack, btor_copy_exp (btor, parse_res.inputs[i]));
        }
      }

      for (i = 0; i < parse_res.noutputs; i++)
      {
        root     = parse_res.outputs[i];
        root_len = btor_get_exp_len (btor, root);
        assert (root_len >= 1);
        if (root_len > 1)
          root = btor_redor_exp (btor, root);
        else
          root = btor_copy_exp (btor, root);
        BTOR_PUSH_STACK (mem, constraints, root);
      }

      /* BMC ? */
      if (parse_res.nregs > 0)
      {
        app.app_mode = BTOR_APP_BMC_MODE;
        btor_enable_inc_usage (btor);
        if (app.verbosity > 0)
        {
          btor_msg_main ("Solving BMC problem\n");
          if (app.bmcadc)
            btor_msg_main ("Using all different constraints: yes\n");
          else
            btor_msg_main ("Using all different constraints: no\n");
          if (app.bmc_mode == BTOR_APP_BMC_MODE_BASE_ONLY)
            btor_msg_main ("Checking base case only\n");
          else if (app.bmc_mode == BTOR_APP_BMC_MODE_INDUCT_ONLY)
            btor_msg_main ("Checking inductive case only\n");
          else
          {
            assert (app.bmc_mode == BTOR_APP_BMC_MODE_BASE_INDUCT);
            btor_msg_main ("Checking base case and inductive case\n");
          }
          if (app.bmcmaxk >= 0)
            btor_msg_main_va_args ("Max bound: %d\n", app.bmcmaxk);
        }

        BTOR_INIT_STACK (bv_regs);
        BTOR_INIT_STACK (array_regs);

        for (i = 0; i < parse_res.nregs; i++)
        {
          cur = parse_res.regs[i];
          assert (BTOR_IS_REGULAR_EXP (cur));
          if (BTOR_IS_BV_VAR_EXP (cur))
            BTOR_PUSH_STACK (mem, bv_regs, cur);
          else
          {
            assert (BTOR_IS_ARRAY_VAR_EXP (cur));
            BTOR_PUSH_STACK (mem, array_regs, cur);
          }
        }

        assert (BTOR_COUNT_STACK (bv_regs) + BTOR_COUNT_STACK (array_regs)
                == parse_res.nregs);

        if (BTOR_COUNT_STACK (array_regs) > 0)
        {
          BTOR_NEWN (mem, array_states, BTOR_COUNT_STACK (array_regs));
          for (i = 0; i < BTOR_COUNT_STACK (array_regs); i++)
            BTOR_INIT_STACK (array_states[i]);
        }

        disjuncted_constraints = disjunct_constraints (btor, &constraints);
        reg_inst =
            btor_new_ptr_hash_table (mem,
                                     (BtorHashPtr) btor_hash_exp_by_id,
                                     (BtorCmpPtr) btor_compare_exp_by_id);
        BTOR_INIT_STACK (bv_states);
        BTOR_CNEWN (mem, old_insts, parse_res.nregs);
        BTOR_CNEWN (mem, new_insts, parse_res.nregs);

        for (i = 0; i < parse_res.nregs; i++)
          btor_insert_in_ptr_hash_table (reg_inst, parse_res.regs[i])
              ->data.asPtr = NULL;
        for (bmck = 0; (app.bmcmaxk == -1 || bmck <= app.bmcmaxk) && !bmc_done;
             bmck++)
        {
          if (app.verbosity > 0) btor_msg_main_va_args ("k = %d:\n", bmck);
          input_inst =
              btor_new_ptr_hash_table (mem,
                                       (BtorHashPtr) btor_hash_exp_by_id,
                                       (BtorCmpPtr) btor_compare_exp_by_id);

          /* we generate new variable instantiations for bv-vars */
          bv_state = NULL;
          for (i = 0; i < BTOR_COUNT_STACK (bv_regs); i++)
          {
            cur = bv_regs.start[i];
            assert (BTOR_IS_REGULAR_EXP (cur));
            assert (BTOR_IS_BV_VAR_EXP (cur));
            assert (cur->symbol != NULL);
            var_name_len =
                strlen (cur->symbol) + btor_num_digits_util (bmck) + 2;
            BTOR_NEWN (mem, var_name, var_name_len);
            sprintf (var_name, "%s_%d", cur->symbol, bmck);
            var = btor_var_exp (btor, cur->len, var_name);
            BTOR_DELETEN (mem, var_name, var_name_len);
            bucket = btor_find_in_ptr_hash_table (reg_inst, cur);
            assert (bucket != NULL);
            bucket->data.asPtr = var;

            if (app.print_model)
              BTOR_PUSH_STACK (mem, varstack, btor_copy_exp (btor, var));

            /* bit-vector state for all different constraint */
            if (app.bmcadc)
            {
              if (bv_state == NULL)
                bv_state = btor_copy_exp (btor, var);
              else
              {
                temp = btor_concat_exp (btor, bv_state, var);
                btor_release_exp (btor, bv_state);
                bv_state = temp;
              }
            }
          }

          /* we generate new variable instantiations for arrays */
          if (app.bmcadc) diff_arrays = btor_false_exp (btor);
          for (i = 0; i < BTOR_COUNT_STACK (array_regs); i++)
          {
            cur = array_regs.start[i];
            assert (BTOR_IS_REGULAR_EXP (cur));
            assert (BTOR_IS_ARRAY_VAR_EXP (cur));
            assert (cur->symbol != NULL);
            var_name_len =
                strlen (cur->symbol) + btor_num_digits_util (bmck) + 2;
            BTOR_NEWN (mem, var_name, var_name_len);
            sprintf (var_name, "%s_%d", cur->symbol, bmck);
            var = btor_array_exp (btor, cur->len, cur->index_len, var_name);
            BTOR_DELETEN (mem, var_name, var_name_len);
            bucket = btor_find_in_ptr_hash_table (reg_inst, cur);
            assert (bucket != NULL);
            bucket->data.asPtr = var;

            if (app.print_model)
              BTOR_PUSH_STACK (mem, arraystack, btor_copy_exp (btor, var));

            /* all different constraint */
            if (app.bmcadc)
            {
              diff_array = btor_true_exp (btor);
              for (p = array_states[i].start; p != array_states[i].top; p++)
              {
                ne   = btor_ne_exp (btor, *p, var);
                temp = btor_and_exp (btor, diff_array, ne);
                btor_release_exp (btor, diff_array);
                diff_array = temp;
                btor_release_exp (btor, ne);
              }
              temp = btor_or_exp (btor, diff_arrays, diff_array);
              btor_release_exp (btor, diff_arrays);
              diff_arrays = temp;
              BTOR_PUSH_STACK (mem, array_states[i], btor_copy_exp (btor, var));
              btor_release_exp (btor, diff_array);
            }
          }

          /* we generate expression that bv-instantiations@0 are zero */
          if (bmck == 0)
            regs_zero = generate_regs_eq_zero (btor, reg_inst, &bv_regs);

          /* incremental all different constraint */
          if (app.bmcadc)
          {
            diff_bv = btor_true_exp (btor);
            for (p = bv_states.start; p != bv_states.top; p++)
            {
              ne   = btor_ne_exp (btor, *p, bv_state);
              temp = btor_and_exp (btor, diff_bv, ne);
              btor_release_exp (btor, diff_bv);
              diff_bv = temp;
              btor_release_exp (btor, ne);
            }

            if (BTOR_COUNT_STACK (bv_regs) > 0)
              BTOR_PUSH_STACK (mem, bv_states, bv_state);

            diff = btor_or_exp (btor, diff_arrays, diff_bv);
            btor_add_constraint_exp (btor, diff);
            btor_release_exp (btor, diff_bv);
            btor_release_exp (btor, diff_arrays);
            btor_release_exp (btor, diff);
          }

          /* we set instantiations equal to last 'next' application */
          for (i = 0; i < parse_res.nregs; i++)
          {
            new_insts[i] = btor_next_exp_bmc (
                btor, reg_inst, parse_res.nexts[i], bmck, input_inst);
            if (bmck > 0)
            {
              bucket =
                  btor_find_in_ptr_hash_table (reg_inst, parse_res.regs[i]);
              assert (bucket != NULL);
              assert (bucket->data.asPtr != NULL);
              eq = btor_eq_exp (
                  btor, old_insts[i], (BtorExp *) bucket->data.asPtr);
              btor_add_constraint_exp (btor, eq);
              btor_release_exp (btor, eq);
            }
          }

          bad = btor_next_exp_bmc (
              btor, reg_inst, disjuncted_constraints, bmck, input_inst);

          if (app.print_model)
          {
            for (bucket = input_inst->first; bucket != NULL;
                 bucket = bucket->next)
            {
              var = (BtorExp *) bucket->data.asPtr;
              assert (BTOR_IS_BV_VAR_EXP (var) || BTOR_IS_ARRAY_VAR_EXP (var));
              if (BTOR_IS_BV_VAR_EXP (var))
                BTOR_PUSH_STACK (mem, varstack, btor_copy_exp (btor, var));
              else
                BTOR_PUSH_STACK (mem, arraystack, btor_copy_exp (btor, var));
            }
          }

          if (app.bmc_mode == BTOR_APP_BMC_MODE_BASE_ONLY)
          {
            if (app.verbosity > 0) btor_msg_main ("Base case:\n");
            if (bmck == 0) btor_add_constraint_exp (btor, regs_zero);
            btor_add_assumption_exp (btor, bad);
            sat_result = btor_sat_btor (btor);
            assert (sat_result != BTOR_UNKNOWN);
            if (app.verbosity > 0 || sat_result == BTOR_SAT
                || sat_result == BTOR_UNKNOWN)
              print_sat_result (&app, sat_result);
            if (sat_result == BTOR_SAT || sat_result == BTOR_UNKNOWN)
              bmc_done = 1;
            else
            {
              assert (sat_result == BTOR_UNSAT);
              /* we add NOT Bad_k, except in the last iteration */
              if (!(app.bmcmaxk != -1 && bmck == app.bmcmaxk))
              {
                not_bad = btor_not_exp (btor, bad);
                btor_add_constraint_exp (btor, not_bad);
                btor_release_exp (btor, not_bad);
              }
            }
          }
          else if (app.bmc_mode == BTOR_APP_BMC_MODE_INDUCT_ONLY)
          {
            if (app.verbosity > 0) btor_msg_main ("Inductive case:\n");
            btor_add_assumption_exp (btor, bad);
            sat_result = btor_sat_btor (btor);
            assert (sat_result != BTOR_UNKNOWN);
            if (app.verbosity > 0 || sat_result == BTOR_UNSAT
                || sat_result == BTOR_UNKNOWN)
              print_sat_result (&app, sat_result);
            if (sat_result == BTOR_UNSAT || sat_result == BTOR_UNKNOWN)
              bmc_done = 1;
            else
            {
              assert (sat_result == BTOR_SAT);
              if (!(app.bmcmaxk != -1 && bmck == app.bmcmaxk))
              /* we add NOT Bad_k, except in the last iteration */
              {
                not_bad = btor_not_exp (btor, bad);
                btor_add_constraint_exp (btor, not_bad);
                btor_release_exp (btor, not_bad);
              }
            }
          }
          else
          {
            assert (app.bmc_mode == BTOR_APP_BMC_MODE_BASE_INDUCT);
            if (app.verbosity > 0) btor_msg_main ("Inductive case:\n");
            btor_add_assumption_exp (btor, bad);
            sat_result = btor_sat_btor (btor);
            assert (sat_result != BTOR_UNKNOWN);
            if (app.verbosity > 0 || sat_result == BTOR_UNSAT
                || sat_result == BTOR_UNKNOWN)
              print_sat_result (&app, sat_result);
            if (sat_result == BTOR_UNSAT || sat_result == BTOR_UNKNOWN)
              bmc_done = 1;
            else
            {
              assert (sat_result == BTOR_SAT);
              if (app.verbosity > 0) btor_msg_main ("Base case:\n");
              btor_add_assumption_exp (btor, regs_zero);
              btor_add_assumption_exp (btor, bad);
              sat_result = btor_sat_btor (btor);
              assert (sat_result != BTOR_UNKNOWN);
              if (app.verbosity > 0 || sat_result == BTOR_SAT
                  || sat_result == BTOR_UNKNOWN)
                print_sat_result (&app, sat_result);
              if (sat_result == BTOR_SAT || sat_result == BTOR_UNKNOWN)
                bmc_done = 1;
              else
              {
                assert (sat_result == BTOR_UNSAT);
                /* we add NOT Bad_k */
                not_bad = btor_not_exp (btor, bad);
                btor_add_constraint_exp (btor, not_bad);
                btor_release_exp (btor, not_bad);
              }
            }
          }

          for (i = 0; i < parse_res.nregs; i++)
          {
            if (bmck > 0) btor_release_exp (btor, old_insts[i]);
            old_insts[i] = new_insts[i];
            new_insts[i] = NULL;
            bucket = btor_find_in_ptr_hash_table (reg_inst, parse_res.regs[i]);
            btor_release_exp (btor, (BtorExp *) bucket->data.asPtr);
            bucket->data.asPtr = NULL;
          }

          /* cleanup */
          for (bucket = input_inst->first; bucket != NULL;
               bucket = bucket->next)
            btor_release_exp (btor, (BtorExp *) bucket->data.asPtr);
          btor_delete_ptr_hash_table (input_inst);

          btor_release_exp (btor, bad);
        }

        if (app.replay_mode != BTOR_APP_REPLAY_MODE_NONE)
          btor_replay_btor (btor, app.replay_file);

        if (!bmc_done)
        {
          sat_result = BTOR_UNKNOWN;
          print_sat_result (&app, sat_result);
        }

        /* cleanup */
        btor_delete_ptr_hash_table (reg_inst);

        btor_release_exp (btor, disjuncted_constraints);
        btor_release_exp (btor, regs_zero);
        for (p = constraints.start; p < constraints.top; p++)
          btor_release_exp (btor, *p);
        BTOR_RELEASE_STACK (mem, constraints);

        for (i = 0; i < parse_res.nregs; i++)
          btor_release_exp (btor, old_insts[i]);
        BTOR_DELETEN (mem, old_insts, parse_res.nregs);

        BTOR_DELETEN (mem, new_insts, parse_res.nregs);

        for (p = bv_states.start; p < bv_states.top; p++)
          btor_release_exp (btor, *p);
        BTOR_RELEASE_STACK (mem, bv_states);

        if (BTOR_COUNT_STACK (array_regs) > 0)
        {
          for (i = 0; i < BTOR_COUNT_STACK (array_regs); i++)
          {
            for (p = array_states[i].start; p != array_states[i].top; p++)
              btor_release_exp (btor, *p);
            BTOR_RELEASE_STACK (mem, array_states[i]);
          }
          BTOR_DELETEN (mem, array_states, BTOR_COUNT_STACK (array_regs));
        }

        BTOR_RELEASE_STACK (mem, bv_regs);
        BTOR_RELEASE_STACK (mem, array_regs);
      }
      else
      {
        /* stand alone mode */
        parser_api->reset (parser);
        parser_api = NULL;

        constraints_reported     = 0;
        nconstraints             = BTOR_COUNT_STACK (constraints);
        constraints_report_limit = (19 + nconstraints) / 20;

        for (p = constraints.start; p < constraints.top; p++)
        {
          root = *p;
          btor_add_constraint_exp (btor, root);
          btor_release_exp (btor, root);

          if (app.verbosity > 1
              && p - constraints.start == constraints_report_limit)
          {
            constraints_reported = constraints_report_limit;
            constraints_report_limit += (19 + nconstraints) / 20;
            assert (nconstraints);
            btor_msg_main_va_args (
                "added %d outputs (%.0f%%)\n",
                constraints_reported,
                100.0 * constraints_reported / (double) nconstraints);
          }
        }
        BTOR_RELEASE_STACK (mem, constraints);

        if (app.verbosity > 1 && constraints_reported < nconstraints)
          btor_msg_main_va_args ("added %d outputs (100%)\n", nconstraints);

        sat_result = btor_sat_btor (btor);
        assert (sat_result != BTOR_UNKNOWN);
        print_sat_result (&app, sat_result);

        /* check if status is equal to benchmark status */
        if (sat_result == BTOR_SAT
            && parse_res.status == BTOR_PARSE_SAT_STATUS_UNSAT)
          print_msg (&app, "ERROR: status of benchmark is 'unsat'\n");
        else if (sat_result == BTOR_UNSAT
                 && parse_res.status == BTOR_PARSE_SAT_STATUS_SAT)
          print_msg (&app, "ERROR: status of benchmark is 'sat'\n");
      }
      if (sat_result == BTOR_SAT && app.print_model)
      {
        if (BTOR_COUNT_STACK (varstack) > 0)
          print_variable_assignments (
              &app, btor, varstack.start, BTOR_COUNT_STACK (varstack));
        if (BTOR_COUNT_STACK (arraystack) > 0)
          print_array_assignments (
              &app, btor, arraystack.start, BTOR_COUNT_STACK (arraystack));
      }

      if (app.verbosity > 0)
      {
        btor_print_stats_sat (smgr);
        btor_print_stats_btor (btor);
      }

      for (i = 0; i < BTOR_COUNT_STACK (varstack); i++)
        btor_release_exp (btor, varstack.start[i]);
      BTOR_RELEASE_STACK (mem, varstack);

      for (i = 0; i < BTOR_COUNT_STACK (arraystack); i++)
        btor_release_exp (btor, arraystack.start[i]);
      BTOR_RELEASE_STACK (mem, arraystack);

      btor_static_smgr = 0;
      btor_reset_sat (smgr);
    }

#if defined(BTOR_USE_PRECOSAT)
  DONE:
#endif
    if (parser_api) parser_api->reset (parser);

    maxallocated = mem->maxallocated;

    btor_static_btor      = 0;
    btor_static_verbosity = 0;
    BTOR_RELEASE_STACK (mem, prefix);
    btor_delete_btor (btor);

    btor_reset_sig_handlers ();
  }

  if (app.close_input_file) fclose (app.input_file);
  if (app.close_output_file) fclose (app.output_file);
  if (app.close_exp_file) fclose (app.exp_file);
  if (app.close_smt_file) fclose (app.smt_file);
  if (app.close_replay_file) fclose (app.replay_file);
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
  if (!app.err && !app.done && app.verbosity > 0)
  {
#ifdef BTOR_HAVE_GETRUSAGE
    delta_time = btor_time_stamp () - start_time;
    btor_msg_main_va_args ("%.1f seconds\n", delta_time);
#endif
    btor_msg_main_va_args ("%.1f MB\n", maxallocated / (double) (1 << 20));
  }
  return return_val;
}
