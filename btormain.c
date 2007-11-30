#include "btormain.h"
#include "boolector.h"
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorbtor.h"
#include "btorconfig.h"
#include "btorconst.h"
#include "btorexit.h"
#include "btorexp.h"
#include "btormem.h"
#include "btorparse.h"
#include "btorsat.h"
#include "btorsmt.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_HAVE_GETRUSAGE
#define BTOR_HAVE_STAT
#define BTOR_HAVE_ISATTY

#ifdef BTOR_HAVE_GETRUSAGE
#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>
#endif

#ifdef BTOR_HAVE_STAT
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

#ifdef BTOR_HAVE_ISATTY
#include <unistd.h>
#endif

enum BtorBasis
{
  BTOR_BINARY_BASIS = 0,
  BTOR_DECIMAL_BASIS,
  BTOR_HEXADECIMAL_BASIS
};

typedef enum BtorBasis BtorBasis;

struct BtorMainApp
{
  FILE *output_file;
  int verbosity;
  int force;
  int *err;
  int *i;
  int argc;
  char **argv;
  BtorBasis basis;
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
    "  -s|--solutions                   print assignments of variables (SAT)\n"
    "  -q|--quiet                       do not print any output\n"
    "  -v|--verbose                     increase verbosity (0 default, 3 max)\n"
    "\n"
    "  --smt                            force SMT lib format input\n"
    "\n"
    "  -x|--hex                         hexadecimal output\n"
    "  -d|--dec                         decimal output\n"
    "  -o|--output <file>               set output file\n"
    "  -de|--dump-exp <file>            dump expression in BTOR format\n"
    "  -ds|--dump-smt <file>            dump expression in SMT format\n"
    "  -f|--force                       overwrite existing output file\n"
    "\n"
    "  -rwl<n>|--rewrite-level<n>       set rewrite level [0,2] (default 2)\n"
    "  -er|--eager-read                 eager Ackermann encoding\n"
    "  -lr|--lazy-read                  iterative read consistency refinement\n"
    "  -ew|--eager-write                eager McCarthy axiom encoding\n"
    "  -lw|--lazy-write                 iterative write consistency "
    "refinement\n"
    "  -rl <n>|--refinement limit <n>   iterative refinement limit (lazy "
    "mode)\n"
    "\n"
    "  -tcnf|--tseitin-cnf              use Tseitin CNF encoding\n"
    "  -pgcnf|--plaisted-greenbaum-cnf  use Plaisted-Greenbaum CNF encoding\n";

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
  if (app->verbosity >= 0) fprintf (app->output_file, msg);
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
    fprintf (app->output_file, msg);
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

  if (*app->i < app->argc - 1)
  {
    if (*close_file)
    {
      assert (*file != NULL);
      fclose (*file);
      *close_file = 0;
      print_err_va_args (app, "multiple %s files\n", file_kind);
      *app->err = 1;
    }
    else
    {
      file_name = app->argv[++*app->i];

      if (file_already_exists (file_name) && !app->force)
      {
        print_err_va_args (
            app,
            "will not overwrite existing %s file '%s' without '-f'\n",
            file_kind,
            file_name);

        *app->err = 1;
      }
      else
      {
        *file = fopen (file_name, "w");
        if (*file == NULL)
        {
          print_err_va_args (app, "can not create '%s'\n", app->argv[*app->i]);
          *app->err = 1;
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
print_assignment (BtorMainApp *app, Btor *btor, BtorExp *exp)
{
  int not_binary   = 0;
  char *pretty     = NULL;
  char *grounded   = NULL;
  char *assignment = NULL;
  BtorMemMgr *mm   = NULL;
  BtorBasis basis  = BTOR_BINARY_BASIS;
  assert (app != NULL);
  assert (btor != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (BTOR_IS_VAR_EXP (exp));
  basis = app->basis;
  not_binary =
      (basis == BTOR_HEXADECIMAL_BASIS) || (basis == BTOR_DECIMAL_BASIS);
  mm         = btor_get_mem_mgr_btor (btor);
  assignment = btor_assignment_exp (btor, exp);

  if (assignment != NULL && !has_only_x (assignment))
  {
    if (not_binary)
    {
      grounded = btor_ground_const (mm, assignment);

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
      pretty = assignment;

    print_msg_va_args (app, "%s %s\n", btor_get_symbol_exp (btor, exp), pretty);

    if (not_binary) btor_freestr (mm, pretty);
  }
  if (assignment != NULL) btor_freestr (mm, assignment);
}

static void
print_variable_assignments (BtorMainApp *app,
                            Btor *btor,
                            BtorExp **vars,
                            int nvars)
{
  int i = 0;
  assert (app != NULL);
  assert (btor != NULL);
  assert (vars != NULL);
  assert (nvars >= 0);
  for (i = 0; i < nvars; i++) print_assignment (app, btor, vars[i]);
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
  int close_smt_file          = 0;
  int dump_exp                = 0;
  int dump_smt                = 0;
  int force_smt_input         = 0;
  int print_solutions         = 0;
  int refinement_limit        = INT_MAX;
  BtorReadEnc read_enc        = BTOR_LAZY_READ_ENC;
  BtorWriteEnc write_enc      = BTOR_LAZY_WRITE_ENC;
  BtorCNFEnc cnf_enc          = BTOR_PLAISTED_GREENBAUM_CNF_ENC;
  const char *input_file_name = "<stdin>";
  const char *parse_error     = NULL;
  FILE *file                  = NULL;
  FILE *input_file            = stdin;
  FILE *exp_file              = stdout;
  FILE *smt_file              = stdout;
  Btor *btor                  = NULL;
  BtorAIGMgr *amgr            = NULL;
  BtorAIGVecMgr *avmgr        = NULL;
  BtorSATMgr *smgr            = NULL;
  BtorParseResult parse_res;
  const BtorParserAPI *parser_api = NULL;
  BtorParser *parser              = NULL;
  BtorMemMgr *mem                 = NULL;
  int rewrite_level               = 2;
  size_t maxallocated             = 0;

  app.verbosity   = 0;
  app.force       = 0;
  app.output_file = stdout;
  app.argc        = argc;
  app.argv        = argv;
  app.i           = &i;
  app.err         = &err;
  app.basis       = BTOR_BINARY_BASIS;

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
    else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--force"))
      app.force = 1;
    else if (!strcmp (argv[i], "-de") || !strcmp (argv[i], "--dump-exp"))
      handle_dump_file (
          &app, &dump_exp, &close_exp_file, "expression", &exp_file);
    else if (!strcmp (argv[i], "-s") || !strcmp (argv[i], "--solutions"))
      print_solutions = 1;
    else if (!strcmp (argv[i], "-ds") || !strcmp (argv[i], "--dump-smt"))
      handle_dump_file (&app, &dump_smt, &close_smt_file, "SMT", &smt_file);
    else if (!strcmp (argv[i], "--smt"))
      force_smt_input = 1;
    else if ((strstr (argv[i], "-rwl") == argv[i]
              && strlen (argv[i]) == strlen ("-rlw") + 1)
             || (strstr (argv[i], "--rewrite-level") == argv[i]
                 && strlen (argv[i]) == strlen ("--rewrite-level") + 1))
    {
      rewrite_level = (int) argv[i][(int) strlen (argv[i]) - 1] - 48;
      assert (rewrite_level >= 0);
      if (rewrite_level > 2)
      {
        print_err (&app, "rewrite level has to be in [0,2]\n");
        err = 1;
      }
    }
    else if (!strcmp (argv[i], "-v") || !strcmp (argv[i], "--verbose"))
    {
      if (app.verbosity < 0)
      {
        print_err (&app, "'-q' and '-v' can not be combined\n");
        err = 1;
      }
      else if (app.verbosity == 3)
      {
        print_err (&app, "can not increase verbosity beyond '3'\n");
        err = 1;
      }
      else
        app.verbosity++;
    }
    else if (!strcmp (argv[i], "-V") || !strcmp (argv[i], "--version"))
    {
      print_msg_va_args (&app, "%s\n", BTOR_VERSION);
      done = 1;
    }
    else if (!strcmp (argv[i], "-q") || !strcmp (argv[i], "--quiet"))
    {
      if (app.verbosity > 0)
      {
        print_err (&app, "can not combine '-q' and '-v'\n");
        err = 1;
      }
      else
        app.verbosity = -1;
    }
    else if (!strcmp (argv[i], "-tcnf") || !strcmp (argv[i], "--tseitin-cnf"))
      cnf_enc = BTOR_TSEITIN_CNF_ENC;
    else if (!strcmp (argv[i], "-pgcnf")
             || !strcmp (argv[i], "--plaisted-greenbaum-cnf"))
      cnf_enc = BTOR_PLAISTED_GREENBAUM_CNF_ENC;
    else if (!strcmp (argv[i], "-x") || !strcmp (argv[i], "--hex"))
    {
      if (app.basis == BTOR_DECIMAL_BASIS)
      {
      HEXANDDECIMAL:
        print_err (&app, "can not force hexadecimal and decimal output");
        err = 1;
      }
      else
        app.basis = BTOR_HEXADECIMAL_BASIS;
    }
    else if (!strcmp (argv[i], "-d") || !strcmp (argv[i], "--decimal"))
    {
      if (app.basis == BTOR_HEXADECIMAL_BASIS) goto HEXANDDECIMAL;

      app.basis = BTOR_DECIMAL_BASIS;
    }
    else if (!strcmp (argv[i], "-er") || !strcmp (argv[i], "--eager-read"))
      read_enc = BTOR_EAGER_READ_ENC;
    else if (!strcmp (argv[i], "-lr") || !strcmp (argv[i], "--lazy-read"))
      read_enc = BTOR_LAZY_READ_ENC;
    else if (!strcmp (argv[i], "-ew") || !strcmp (argv[i], "--eager-write"))
      write_enc = BTOR_EAGER_WRITE_ENC;
    else if (!strcmp (argv[i], "-lw") || !strcmp (argv[i], "--lazy-write"))
      write_enc = BTOR_LAZY_WRITE_ENC;
    else if (!strcmp (argv[i], "-rl")
             || !strcmp (argv[i], "--refinement-limit"))
    {
      if (i < argc - 1)
      {
        refinement_limit = atoi (argv[++i]);
        if (refinement_limit < 0)
        {
          print_err_va_args (&app, "refinement limit must not be negative\n");
          err = 1;
        }
      }
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
          print_err_va_args (&app, "multiple output files\n");
          err = 1;
        }
        else
        {
          app.output_file = fopen (argv[++i], "w");
          if (app.output_file == NULL)
          {
            app.output_file = stdout;
            print_err_va_args (&app, "can not create '%s'\n", argv[i]);
            err = 1;
          }
          else
            close_output_file = 1;
        }
      }
    }
    else if (argv[i][0] == '-')
    {
      print_err_va_args (&app, "invalid option '%s'\n", argv[i]);
      err = 1;
    }
    else if (close_input_file)
    {
      print_err_va_args (&app, "multiple input files\n");
      err = 1;
    }
    else if (!(file = fopen (argv[i], "r")))
    {
      print_err_va_args (&app, "can not read '%s'\n", argv[i]);
      err = 1;
    }
    else
    {
      input_file_name  = argv[i];
      input_file       = file;
      close_input_file = 1;
    }
  }

  if (read_enc == BTOR_EAGER_READ_ENC && write_enc != BTOR_EAGER_WRITE_ENC)
  {
    print_err (&app, "can not combine eager read with uneager write\n");
    err = 1;
  }

  if (app.verbosity > 0)
    print_verbose_msg_va_args ("Boolector Version %s\n", BTOR_VERSION);

  if (!done && !err)
  {
    btor = btor_new_btor ();
    btor_set_rewrite_level_btor (btor, rewrite_level);
    btor_set_verbosity_btor (btor, app.verbosity);
    btor_set_read_enc_btor (btor, read_enc);
    btor_set_write_enc_btor (btor, write_enc);
    mem = btor_get_mem_mgr_btor (btor);

    if (force_smt_input
        || (close_input_file && has_suffix (input_file_name, ".smt")))
    {
      parser_api = btor_smt_parser_api;
    }
    else
      parser_api = btor_btor_parser_api;

    parser = parser_api->init (btor, app.verbosity);

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
    else if (btor_get_exp_len (btor, parse_res.roots[0]) != 1)
    {
      print_msg_va_args (
          &app, "%s: root has bit width different from one\n", input_file_name);
      err = 1;
    }
    else if (dump_exp)
    {
      done = 1;
      btor_dump_exp (btor, exp_file, parse_res.roots[0]);
    }
    else if (dump_smt)
    {
      done = 1;
      btor_dump_smt (btor, smt_file, parse_res.roots[0]);
    }
    else
    {
      avmgr = btor_get_aigvec_mgr_btor (btor);
      amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
      smgr  = btor_get_sat_mgr_aig_mgr (amgr);

      btor_init_sat (smgr);
      btor_set_output_sat (smgr, stderr);

      if (app.verbosity >= 3) btor_enable_verbosity_sat (smgr);

      if (app.verbosity == 1) print_verbose_msg ("generating SAT instance\n");

      btor_set_cnf_enc_aig_mgr (amgr, cnf_enc);
      btor_add_constraint_exp (btor, parse_res.roots[0]);
      sat_result = btor_sat_btor (btor, refinement_limit);

      if (app.verbosity >= 0)
      {
        if (sat_result == BTOR_UNSAT)
          print_msg (&app, "unsat\n");
        else if (sat_result == BTOR_SAT)
        {
          print_msg (&app, "sat\n");
          if (print_solutions && parse_res.nvars > 0)
            print_variable_assignments (
                &app, btor, parse_res.vars, parse_res.nvars);
        }
        else
        {
          assert (sat_result == BTOR_UNKNOWN);
          print_msg (&app, "unknown\n");
        }
      }

      if (app.verbosity > 1) btor_print_stats_sat (smgr);
      btor_reset_sat (smgr);

      if (app.verbosity > 0) btor_print_stats_btor (btor);
    }

    parser_api->reset (parser);
    maxallocated = mem->maxallocated;
    btor_delete_btor (btor);
  }

  if (close_input_file) fclose (input_file);
  if (close_output_file) fclose (app.output_file);
  if (close_exp_file) fclose (exp_file);
  if (close_smt_file) fclose (smt_file);
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
    assert (sat_result == BTOR_UNKNOWN);
    return_val = BTOR_UNKNOWN_EXIT;
  }
#ifdef BTOR_HAVE_GETRUSAGE
  if (!err && !done && app.verbosity > 0)
  {
    delta_time = time_stamp () - start_time;
    print_verbose_msg_va_args ("%.1f seconds\n", delta_time);
    print_verbose_msg_va_args ("%.1f MB\n", maxallocated / (double) (1 << 20));
  }
#endif
  return return_val;
}
