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
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
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
    "  -r|--reads                       print assignments of reads (SAT)\n"
    "  -q|--quiet                       do not print any output\n"
    "  -v|--verbose                     increase verbosity (0 default, 3 max)\n"
    "\n"
    "  --smt                            force SMT lib format input\n"
    "\n"
    "  -x|--hex                         hexadecimal output\n"
    "  -d|--dec                         decimal output\n"
    "  -o|--output <file>               set output file\n"
    "  -t|--trace <file>                set trace file\n"
    "  -da|--dump-aig <file>            dump AIG in AIGER (only for BV)\n"
    "  -dc|--dump-cnf <file>            dump CNF in DIMACS\n"
    "  -de|--dump-exp <file>            dump expression in BTOR format\n"
    "  -ds|--dump-smt <file>            dump expression in SMT format\n"
    "  -f|--force                       overwrite existing output file\n"
    "\n"
    "  -rwl<n>|--rewrite-level<n>       set rewrite level [0,2] (default 2)\n"
    "  -nr|--no-read                    no read consistency (not sound (SAT))\n"
    "  -er|--eager-read                 eager Ackermann encoding\n"
    "  -lr|--lazy-read                  iterative read consistency refinement\n"
    "  -sr|--sat-solver-read            read consistency handled by SAT "
    "solver\n"
    "  -nw|--no-write                   no write consistency (not sound "
    "(SAT))\n"
    "  -ew|--eager-write                eager McCarthy axiom encoding\n"
    "  -lw|--lazy-write                 iterative write consistency "
    "refinement\n"
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
print_assignment (BtorMainApp *app, BtorExpMgr *emgr, BtorExp *exp)
{
  int not_binary   = 0;
  char *pretty     = NULL;
  char *grounded   = NULL;
  char *assignment = NULL;
  BtorMemMgr *mm   = NULL;
  BtorBasis basis  = BTOR_BINARY_BASIS;
  assert (app != NULL);
  assert (emgr != NULL);
  assert (exp != NULL);
  assert (BTOR_IS_REGULAR_EXP (exp));
  assert (BTOR_IS_VAR_EXP (exp) || exp->kind == BTOR_READ_EXP);
  basis = app->basis;
  not_binary =
      (basis == BTOR_HEXADECIMAL_BASIS) || (basis == BTOR_DECIMAL_BASIS);
  mm         = btor_get_mem_mgr_exp_mgr (emgr);
  assignment = btor_assignment_exp (emgr, exp);

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

    if (BTOR_IS_VAR_EXP (exp))
      print_msg_va_args (
          app, "%s %s\n", btor_get_symbol_exp (emgr, exp), pretty);
    else
    {
      assert (exp->kind == BTOR_READ_EXP);
      print_msg_va_args (app, "read%d %s\n", exp->id, pretty);
    }

    if (not_binary) btor_freestr (mm, pretty);
  }
  if (assignment != NULL) btor_freestr (mm, assignment);
}

static void
print_variable_assignments (BtorMainApp *app, BtorExpMgr *emgr)
{
  BtorExp **temp             = NULL;
  BtorExp **top              = NULL;
  BtorExpPtrStack *variables = NULL;
  assert (app != NULL);
  assert (emgr != NULL);
  variables = btor_get_variables_exp_mgr (emgr);
  top       = variables->top;
  for (temp = variables->start; temp != top; temp++)
    print_assignment (app, emgr, *temp);
}

static void
print_read_assignments (BtorMainApp *app, BtorExpMgr *emgr)
{
  BtorMemMgr *mm          = NULL;
  BtorExp **temp          = NULL;
  BtorExp **top           = NULL;
  BtorExp *cur            = NULL;
  BtorExp *cur_parent     = NULL;
  BtorExpPtrStack *arrays = NULL;
  BtorExpPtrStack stack;
  assert (app != NULL);
  assert (emgr != NULL);
  mm     = btor_get_mem_mgr_exp_mgr (emgr);
  arrays = btor_get_arrays_exp_mgr (emgr);
  BTOR_INIT_STACK (stack);
  /* push arrays on stack */
  top = arrays->top;
  for (temp = arrays->start; temp != top; temp++)
    BTOR_PUSH_STACK (mm, stack, *temp);
  while (!BTOR_EMPTY_STACK (stack))
  {
    cur = BTOR_REAL_ADDR_EXP (BTOR_POP_STACK (stack));
    if (BTOR_IS_ARRAY_EXP (cur))
    {
      /* push parent writes and reads on stack */
      cur_parent = cur->last_parent;
      assert (BTOR_IS_REGULAR_EXP (cur_parent));
      while (cur_parent != NULL)
      {
        assert (BTOR_GET_TAG_EXP (cur_parent) == 0);
        BTOR_PUSH_STACK (mm, stack, cur_parent);
        cur_parent = cur_parent->prev_parent[0];
        assert (BTOR_IS_REGULAR_EXP (cur_parent));
      }
    }
    else
    {
      assert (cur->kind == BTOR_READ_EXP);
      print_assignment (app, emgr, cur);
    }
  }
  BTOR_RELEASE_STACK (mm, stack);
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
  int close_aig_file          = 0;
  int close_cnf_file          = 0;
  int close_trace_file        = 0;
  int dump_exp                = 0;
  int dump_aig                = 0;
  int dump_cnf                = 0;
  int dump_smt                = 0;
  int dump_binary_aig         = 0;
  int force_smt_input         = 0;
  int print_solutions         = 0;
  int print_reads             = 0;
  BtorReadEnc read_enc        = BTOR_LAZY_READ_ENC;
  BtorWriteEnc write_enc      = BTOR_LAZY_WRITE_ENC;
  BtorCNFEnc cnf_enc          = BTOR_PLAISTED_GREENBAUM_CNF_ENC;
  const char *input_file_name = "<stdin>";
  const char *parse_error     = NULL;
  FILE *file                  = NULL;
  FILE *input_file            = stdin;
  FILE *exp_file              = stdout;
  FILE *aig_file              = stdout;
  FILE *cnf_file              = stdout;
  FILE *smt_file              = stdout;
  FILE *trace_file            = stdout;
  BtorExpMgr *emgr            = NULL;
  BtorAIGMgr *amgr            = NULL;
  BtorAIGVecMgr *avmgr        = NULL;
  BtorAIG *aig                = NULL;
  BtorSATMgr *smgr            = NULL;
  BtorParseResult parse_res;
  const BtorParserAPI *parser_api = NULL;
  BtorParser *parser              = NULL;
  BtorMemMgr *mem                 = NULL;
  int dump_trace                  = 0;
  int rewrite_level               = 2;

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
    else if (!strcmp (argv[i], "-r") || !strcmp (argv[i], "--reads"))
      print_reads = 1;
    else if (!strcmp (argv[i], "-ds") || !strcmp (argv[i], "--dump-smt"))
      handle_dump_file (&app, &dump_smt, &close_smt_file, "SMT", &smt_file);
    else if (!strcmp (argv[i], "-da") || !strcmp (argv[i], "--dump-aig"))
      handle_dump_file (&app, &dump_aig, &close_aig_file, "AIG", &aig_file);
    else if (!strcmp (argv[i], "-dc") || !strcmp (argv[i], "--dump-cnf"))
      handle_dump_file (&app, &dump_cnf, &close_cnf_file, "CNF", &cnf_file);
    else if (!strcmp (argv[i], "--smt"))
      force_smt_input = 1;
    else if (!strcmp (argv[i], "-t") || !strcmp (argv[i], "--trace"))
      handle_dump_file (
          &app, &dump_trace, &close_trace_file, "trace", &trace_file);
    else if ((strstr (argv[i], "-rwl") == argv[i]
              && strlen (argv[i]) == strlen ("-rlw") + 1)
             || (strstr (argv[i], "--rewrite-level") == argv[i]
                 && strlen (argv[i]) == strlen ("--rewrite-level") + 1))
    {
      rewrite_level = (int) argv[i][strlen (argv[i]) - 1] - 48;
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
    else if (!strcmp (argv[i], "-nr") || !strcmp (argv[i], "--no-read"))
      read_enc = BTOR_NO_READ_ENC;
    else if (!strcmp (argv[i], "-er") || !strcmp (argv[i], "--eager-read"))
      read_enc = BTOR_EAGER_READ_ENC;
    else if (!strcmp (argv[i], "-lr") || !strcmp (argv[i], "--lazy-read"))
      read_enc = BTOR_LAZY_READ_ENC;
    else if (!strcmp (argv[i], "-sr") || !strcmp (argv[i], "--sat-solver-read"))
      read_enc = BTOR_SAT_SOLVER_READ_ENC;
    else if (!strcmp (argv[i], "-nw") || !strcmp (argv[i], "--no-write"))
      write_enc = BTOR_NO_WRITE_ENC;
    else if (!strcmp (argv[i], "-ew") || !strcmp (argv[i], "--eager-write"))
      write_enc = BTOR_EAGER_WRITE_ENC;
    else if (!strcmp (argv[i], "-lw") || !strcmp (argv[i], "--lazy-write"))
      write_enc = BTOR_LAZY_WRITE_ENC;
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

  if (!done && !err)
  {
    emgr =
        btor_new_exp_mgr (rewrite_level, dump_trace, app.verbosity, trace_file);
    btor_set_read_enc_exp_mgr (emgr, read_enc);
    btor_set_write_enc_exp_mgr (emgr, write_enc);
    mem = btor_get_mem_mgr_exp_mgr (emgr);

    if (force_smt_input
        || (close_input_file && has_suffix (input_file_name, ".smt")))
    {
      parser_api = btor_smt_parser_api;
    }
    else
      parser_api = btor_btor_parser_api;

    parser = parser_api->init (emgr, app.verbosity);

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
    else if (btor_get_exp_len (emgr, parse_res.roots[0]) != 1)
    {
      print_msg_va_args (
          &app, "%s: root has bit width different from one\n", input_file_name);
      err = 1;
    }
    else if (dump_exp || dump_aig || dump_cnf || dump_smt)
    {
      done = 1;
      if (dump_exp)
      {
        btor_dump_exp (emgr, exp_file, parse_res.roots[0]);
      }
      else if (dump_smt)
      {
        btor_dump_smt (emgr, smt_file, parse_res.roots[0]);
      }
      else
      {
        avmgr = btor_get_aigvec_mgr_exp_mgr (emgr);
        amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
        smgr  = btor_get_sat_mgr_aig_mgr (amgr);

        if (dump_aig)
        {
          aig = btor_exp_to_aig (emgr, parse_res.roots[0]);
#ifdef BTOR_HAVE_ISATTY
          if (close_aig_file || !isatty (1)) dump_binary_aig = 1;
#endif
          btor_dump_aig (amgr, dump_binary_aig, aig_file, aig);
          btor_release_aig (amgr, aig);
        }
        else if (dump_cnf)
        {
          btor_set_cnf_enc_aig_mgr (amgr, cnf_enc);
          btor_init_sat (smgr);
          btor_exp_to_sat (emgr, parse_res.roots[0]);
          btor_dump_cnf_sat (smgr, cnf_file);
          btor_reset_sat (smgr);
        }
      }
    }
    else
    {
      avmgr = btor_get_aigvec_mgr_exp_mgr (emgr);
      amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);
      smgr  = btor_get_sat_mgr_aig_mgr (amgr);

      btor_init_sat (smgr);
      btor_set_output_sat (smgr, stderr);

      if (app.verbosity >= 3) btor_enable_verbosity_sat (smgr);

      if (app.verbosity == 1) print_verbose_msg ("generating SAT instance\n");

      btor_set_cnf_enc_aig_mgr (amgr, cnf_enc);
      sat_result = btor_sat_exp (emgr, parse_res.roots[0]);

      if (app.verbosity >= 0)
      {
        if (sat_result == BTOR_UNSAT)
          print_msg (&app, "UNSATISFIABLE\n");
        else if (sat_result == BTOR_SAT)
        {
          print_msg (&app, "SATISFIABLE\n");
          if (print_solutions) print_variable_assignments (&app, emgr);
          if (print_reads) print_read_assignments (&app, emgr);
        }
        else
        {
          assert (sat_result == BTOR_UNKNOWN);
          print_msg (&app, "UNKNOWN SAT RESULT\n");
        }
      }

      if (app.verbosity >= 3) btor_print_stats_sat (smgr);
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
  }
#endif
  return return_val;
}
