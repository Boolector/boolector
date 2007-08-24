#include "btormain.h"
#include "boolector.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbtor.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btormem.h"
#include "btorparse.h"
#include "btorsat.h"
#include "btorsmt.h"
#include "btorutil.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* BSD/Linux/SysV specific */
#define BTOR_HAVE_GETRUSAGE /* do we have 'getrusage' ? */

#ifdef BTOR_HAVE_GETRUSAGE
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/unistd.h>
#endif

typedef struct BtorMainApp BtorMainApp;

struct BtorMainApp
{
  FILE *output_file;
  int quiet;
  int *err;
  int *i;
  int argc;
  char **argv;
};

static const char *g_usage =
    "usage: boolector [<option>...][<input>]\n"
    "\n"
    "where <option> is one of the following:"
    "\n"
    "  -h|--help                     print usage information and exit\n"
    "  -c|--copyright                print copyright\n"
    "  -V|--version                  print version and exit\n"
    "\n"
    "  -q|--quiet                    do not print any output\n"
    "  -v|--verbose                  increase verbosity (0 default, 3 max)\n"
    "\n"
    "  -x|--hex                      hexadecimal output\n"
    "  -o|--output <file>            set output file\n"
    "  -t|--trace <file>             set trace file\n"
    "  -de|--dump-exp <file>         dump expression in BAF\n"
    "  -da|--dump-aig <file>         dump AIG in AIGER\n"
    "  -dc|--dump-cnf <file>         dump CNF in DIMACS\n"
    "  --smt                         force SMT input\n"
    "\n"
    "  -rwl<n>|--rewrite-level<n>    set rewrite level [0,2] (default 2)\n"
    "  -nrc|--no-read-consistency    no array read consistency\n";

static const char *g_copyright =
    "Copyright (c) 2007, Robert Brummayer, Armin Biere\n"
    "Institute for Formal Models and Verification\n"
    "Johannes Kepler University, Linz, Austria\n";

#ifdef BTOR_HAVE_GETRUSAGE
static double
time_stamp (void)
{
  double res = -1;
  struct rusage u;
  res = 0;
  if (!getrusage (RUSAGE_SELF, &u))
  {
    res += u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
    res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  }
  return res;
}
#endif

static void
print_verbose_msg (char *msg)
{
  assert (msg != NULL);
  fprintf (stderr, "[btormain] %s", msg);
  fflush (stderr);
}

static void
print_verbose_msg_va_args (char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  va_start (list, msg);
  fprintf (stderr, "[btormain] ");
  vfprintf (stderr, msg, list);
  va_end (list);
}

static void
print_msg (BtorMainApp *app, char *msg)
{
  assert (msg != NULL);
  if (!app->quiet) fprintf (app->output_file, msg);
}

static void
print_msg_va_args (BtorMainApp *app, char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  if (!app->quiet)
  {
    va_start (list, msg);
    vfprintf (app->output_file, msg, list);
    va_end (list);
  }
}

static void
handle_dump_file (BtorMainApp *app,
                  int *dump_file,
                  int *close_file,
                  const char *file_kind,
                  FILE **file)
{
  assert (dump_file != NULL);
  assert (close_file != NULL);
  assert (file_kind != NULL);
  assert (file != NULL);
  *dump_file = 1;
  if (*app->i < app->argc - 1)
  {
    if (*close_file)
    {
      assert (*file != NULL);
      fclose (*file);
      *close_file = 0;
      print_msg_va_args (app, "boolector: multiple %s files\n", file_kind);
      *app->err = 1;
    }
    else
    {
      (*app->i)++;
      *file = fopen (app->argv[*app->i], "w");
      if (*file == NULL)
      {
        print_msg_va_args (
            app, "boolector: can not create '%s'\n", app->argv[*app->i]);
        *app->err = 1;
      }
      else
      {
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

int
btor_main (int argc, char **argv)
{
  BtorMainApp app;
#ifdef BTOR_HAVE_GETRUSAGE
  double start_time = time_stamp ();
  double delta_time = 0.0;
#endif
  int return_val              = 0;
  int sat_result              = 0;
  int done                    = 0;
  int err                     = 0;
  int i                       = 0;
  int close_input_file        = 0;
  int close_output_file       = 0;
  int close_exp_file          = 0;
  int close_aig_file          = 0;
  int close_cnf_file          = 0;
  int close_trace_file        = 0;
  int dump_exp                = 0;
  int dump_aig                = 0;
  int dump_cnf                = 0;
  int verbosity               = 0;
  int hex                     = 0;
  int force_smt_input         = 0;
  int read_mode               = 0;
  const char *input_file_name = "<stdin>";
  const char *parse_error     = NULL;
  char *witness               = NULL;
  char *pretty_witness        = NULL;
  FILE *file                  = NULL;
  FILE *input_file            = stdin;
  FILE *exp_file              = stdout;
  FILE *aig_file              = stdout;
  FILE *cnf_file              = stdout;
  FILE *trace_file            = stdout;
  BtorExpMgr *emgr            = NULL;
  BtorExp *cur_exp            = NULL;
  BtorAIGMgr *amgr            = NULL;
  BtorAIG *aig                = NULL;
  BtorSATMgr *smgr            = NULL;
  BtorParseResult parse_res;
  const BtorParserAPI *parser_api = NULL;
  BtorParser *parser              = NULL;
  BtorMemMgr *mem                 = NULL;
  int dump_trace                  = 0;
  int rewrite_level               = 2;

  app.quiet       = 0;
  app.output_file = stdout;
  app.argc        = argc;
  app.argv        = argv;
  app.i           = &i;
  app.err         = &err;

  for (i = 1; !done && !err && i < argc; i++)
  {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help"))
    {
      print_msg_va_args (&app, "%s\n", g_usage);
      done = 1;
    }
    else if (!strcmp (argv[i], "-c") || !strcmp (argv[i], "--copyright"))
    {
      print_msg_va_args (&app, "%s", g_copyright);
      done = 1;
    }
    else if (!strcmp (argv[i], "-de") || !strcmp (argv[i], "--dump-exp"))
    {
      handle_dump_file (
          &app, &dump_exp, &close_exp_file, "expression", &exp_file);
    }
    else if (!strcmp (argv[i], "-da") || !strcmp (argv[i], "--dump-aig"))
    {
      handle_dump_file (&app, &dump_aig, &close_aig_file, "AIG", &aig_file);
    }
    else if (!strcmp (argv[i], "-dc") || !strcmp (argv[i], "--dump-cnf"))
    {
      handle_dump_file (&app, &dump_cnf, &close_cnf_file, "CNF", &cnf_file);
    }
    else if (!strcmp (argv[i], "--smt"))
    {
      force_smt_input = 1;
    }
    else if (!strcmp (argv[i], "-t") || !strcmp (argv[i], "--trace"))
    {
      handle_dump_file (
          &app, &dump_trace, &close_trace_file, "trace", &trace_file);
    }
    else if ((strstr (argv[i], "-rwl") == argv[i]
              && strlen (argv[i]) == strlen ("-rlw") + 1)
             || (strstr (argv[i], "--rewrite-level") == argv[i]
                 && strlen (argv[i]) == strlen ("--rewrite-level") + 1))
    {
      rewrite_level = (int) argv[i][strlen (argv[i]) - 1] - 48;
      assert (rewrite_level >= 0);
      if (rewrite_level > 2)
      {
        print_msg (&app, "boolector: rewrite level has to be in [0,2]\n");
        err = 1;
      }
    }
    else if (!strcmp (argv[i], "-v") || !strcmp (argv[i], "--verbose"))
    {
      verbosity++;
      app.quiet = 0;
    }
    else if (!strcmp (argv[i], "-V") || !strcmp (argv[i], "--version"))
    {
      print_msg_va_args (&app, "%s\n", BTOR_VERSION);
      done = 1;
    }
    else if (!strcmp (argv[i], "-q") || !strcmp (argv[i], "--quiet"))
    {
      app.quiet = 1;
      verbosity = 0;
    }
    else if (!strcmp (argv[i], "-x") || !strcmp (argv[i], "--hex"))
    {
      hex = 1;
    }
    else if (!strcmp (argv[i], "-nrc")
             || !strcmp (argv[i], "--no-read-consistency"))
    {
      read_mode = 0;
    }
    else if (!strcmp (argv[i], "-o") || !strcmp (argv[i], "--output"))
    {
      if (i < argc - 1)
      {
        if (close_output_file)
        {
          fclose (app.output_file);
          close_output_file = 0;
          app.output_file   = stdout;
          print_msg_va_args (&app, "boolector: multiple output files\n");
          err = 1;
        }
        else
        {
          app.output_file = fopen (argv[++i], "w");
          if (app.output_file == NULL)
          {
            app.output_file = stdout;
            print_msg_va_args (
                &app, "boolector: can not create '%s'\n", argv[i]);
            err = 1;
          }
          else
            close_output_file = 1;
        }
      }
    }
    else if (argv[i][0] == '-')
    {
      print_msg_va_args (&app, "boolector: invalid option '%s'\n", argv[i]);
      err = 1;
    }
    else if (close_input_file)
    {
      print_msg_va_args (&app, "boolector: multiple input files\n");
      err = 1;
    }
    else if (!(file = fopen (argv[i], "r")))
    {
      print_msg_va_args (&app, "boolector: can not read '%s'\n", argv[i]);
      err = 1;
    }
    else
    {
      input_file_name  = argv[i];
      input_file       = file;
      close_input_file = 1;
    }
  }

  if (!done && !err)
  {
    emgr = btor_new_exp_mgr (rewrite_level, dump_trace, verbosity, trace_file);
    mem  = btor_get_mem_mgr_exp_mgr (emgr);

    if (force_smt_input
        || (close_input_file && has_suffix (input_file_name, ".smt")))
    {
      parser_api = btor_smt_parser_api;
    }
    else
      parser_api = btor_btor_parser_api;

    parser = parser_api->init (emgr, verbosity);

    parse_error =
        parser_api->parse (parser, input_file, input_file_name, &parse_res);

    if (parse_error)
    {
      print_msg_va_args (&app, "%s\n", parse_error);
      err = 1;
    }
    else if (parse_res.nroots != 1)
    {
      print_msg_va_args (&app,
                         "%s: found %d roots but expected exactly one\n",
                         input_file_name,
                         parse_res.nroots);
      err = 1;
    }
    else if (dump_exp || dump_aig || dump_cnf)
    {
      done = 1;
      if (dump_exp)
      {
        btor_dump_exp (emgr, exp_file, parse_res.roots[0]);
      }
      if (dump_aig || dump_cnf)
      {
        amgr = btor_get_aig_mgr_aigvec_mgr (btor_get_aigvec_mgr_exp_mgr (emgr));
        aig  = btor_exp_to_aig (emgr, parse_res.roots[0]);
        if (dump_aig) btor_dump_aig (amgr, aig_file, aig);
        if (dump_cnf)
        {
          smgr = btor_get_sat_mgr_aig_mgr (amgr);
          btor_init_sat (smgr);
          btor_aig_to_sat (amgr, aig);
          btor_dump_cnf_sat (smgr, cnf_file);
          btor_reset_sat (smgr);
        }
        btor_release_aig (amgr, aig);
      }
    }
    else
    {
      amgr = btor_get_aig_mgr_aigvec_mgr (btor_get_aigvec_mgr_exp_mgr (emgr));
      smgr = btor_get_sat_mgr_aig_mgr (amgr);
      btor_init_sat (smgr);
      btor_set_output_sat (smgr, stderr);
      if (verbosity >= 3) btor_enable_verbosity_sat (smgr);
      if (verbosity == 1) print_verbose_msg ("generating SAT instance\n");
      sat_result = btor_sat_exp (emgr, parse_res.roots[0]);
      if (!app.quiet)
      {
        if (sat_result == BTOR_UNSAT)
          print_msg (&app, "UNSATISFIABLE\n");
        else if (sat_result == BTOR_SAT)
        {
          print_msg (&app, "SATISFIABLE\n");
          for (i = 0; i < parse_res.nvars; i++)
          {
            cur_exp = parse_res.vars[i];
            witness = btor_get_assignment_var_exp (emgr, cur_exp);
            if (witness != NULL)
            {
              if (hex)
                pretty_witness = btor_const_to_hex (mem, witness);
              else
                pretty_witness = witness;

              print_msg_va_args (&app,
                                 "%s %s\n",
                                 btor_get_symbol_exp (emgr, cur_exp),
                                 pretty_witness);
              if (hex) btor_freestr (mem, pretty_witness);
            }
          }
        }
        else
        {
          print_msg (&app, "UNKNOWN SAT RESULT\n");
        }
      }
      if (verbosity >= 3) btor_print_stats_sat (smgr);
      btor_reset_sat (smgr);
    }

    parser_api->reset (parser);
    btor_delete_exp_mgr (emgr);
  }

  if (close_input_file) fclose (input_file);
  if (close_output_file) fclose (app.output_file);
  if (close_exp_file) fclose (exp_file);
  if (close_aig_file) fclose (aig_file);
  if (close_cnf_file) fclose (cnf_file);
  if (close_trace_file) fclose (trace_file);
  if (err)
    return_val = BTOR_ERR_EXIT;
  else if (done)
    return_val = BTOR_SUCC_EXIT;
  else if (sat_result == BTOR_UNSAT)
    return_val = BTOR_UNSAT_EXIT;
  else if (sat_result == BTOR_SAT)
    return_val = BTOR_SAT_EXIT;
  else
  {
    assert (sat_result == BTOR_SAT);
    return_val = BTOR_UNKNOWN_EXIT;
  }
#ifdef BTOR_HAVE_GETRUSAGE
  if (!err && !done && !app.quiet)
  {
    delta_time = time_stamp () - start_time;
    print_verbose_msg_va_args ("%.1f seconds\n", delta_time);
  }
#endif
  return return_val;
}
