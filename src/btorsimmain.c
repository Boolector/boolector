/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "btorfmt/btorfmt.h"
#include "utils/btorrng.h"
#include "utils/btorstack.h"

static void
die (char *m, ...)
{
  fflush (stdout);
  fputs ("btorsim: ", stderr);
  va_list ap;
  va_start (ap, m);
  vfprintf (stderr, m, ap);
  va_end (ap);
  fprintf (stderr, "\n");
  exit (1);
}

static int verbosity;

static void
msg (int level, char *m, ...)
{
  if (level < verbosity) return;
  assert (m);
  printf ("[btorsim] ");
  va_list ap;
  va_start (ap, m);
  vprintf (m, ap);
  va_end (ap);
  printf ("\n");
}

static const char *usage =
    "usage: btorsim [ <option> ... ] [ <btor> [ <witness> ] ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -h       print this command line option summary\n"
    "  -c       check only <witness> and do not print trace\n"
    "  -v       increase verbosity level (multiple times if necessary)\n"
    "  -r <n>   generate <n> random transitions (default 20)\n"
    "  -s <s>   random seed (default '0')\n"
    "\n"
    "and '<btor>' is sequential model in 'BTOR' format\n"
    "and '<witness>' a trace in 'BTOR' witness format.\n"
    "\n"
    "The simulator either checks a given witness (checking mode) or\n"
    "randomly generates inputs (random mode). If no BTOR model path is\n"
    "specified then it is read from '<stdin>' and the simulator switches\n"
    "to random mode.  If a model but no witness is specified then by\n"
    "default the simulator reads the witness from '<stdin>' and switches\n"
    "to checking mode unless a '-r ...' option is given in which case\n"
    "it uses random mode and does not read a witness.\n";

static const char *model_path;
static const char *witness_path;
static FILE *model_file;
static FILE *witness_file;
static int close_model_file;
static int close_witness_file;

static int
parse_positive_number (const char *str, int *res_ptr)
{
  const char *p = str;
  if (!*p) return 0;
  if (*p == '0' && p[1]) return 0;
  int res = 0;
  while (*p)
  {
    const int ch = *p++;
    if (!isdigit (ch)) return 0;
    if (INT_MAX / 10 < res) return 0;
    res *= 10;
    const int digit = ch - '0';
    if (INT_MAX - digit < res) return 0;
    res += digit;
  }
  *res_ptr = res;
  return 1;
}

static int checking_mode = 0;
static int random_mode   = 0;
static BtorFormatReader *model;

static BtorMemMgr *mem;

BTOR_DECLARE_STACK (BtorFormatLinePtr, BtorFormatLine *);

static BtorFormatLinePtrStack inputs;
static BtorFormatLinePtrStack states;
static BtorFormatLinePtrStack bads;
static BtorFormatLinePtrStack constraints;

static long num_format_lines;
static BtorFormatLine **inits;
static BtorFormatLine **nexts;

static void
parse_model_line (BtorFormatLine *l)
{
  switch (l->tag)
  {
    case BTOR_FORMAT_TAG_bad:
    {
      long i = (long) BTOR_COUNT_STACK (bads);
      msg (1, "bads %s at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (bads, l);
    }
    break;

    case BTOR_FORMAT_TAG_constraint:
    {
      long i = (long) BTOR_COUNT_STACK (constraints);
      msg (1, "constraint %s at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (constraints, l);
    }
    break;

    case BTOR_FORMAT_TAG_init: inits[l->args[0]] = l; break;

    case BTOR_FORMAT_TAG_input:
    {
      long i = (long) BTOR_COUNT_STACK (inputs);
      if (l->symbol)
        msg (1, "input %ld %s at line %ld", i, l->symbol, l->lineno);
      else
        msg (1, "input %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (inputs, l);
    }
    break;

    case BTOR_FORMAT_TAG_next: nexts[l->args[0]] = l; break;

    case BTOR_FORMAT_TAG_sort:
    {
      switch (l->sort.tag)
      {
        case BTOR_FORMAT_TAG_SORT_bitvec:
          msg (
              1, "sort bitvec %u at line %ld", l->sort.bitvec.width, l->lineno);
          break;
        case BTOR_FORMAT_TAG_SORT_array:
        default:
          die ("parse error in '%s' at line %ld: unsupported sort '%s'",
               model_path,
               l->lineno,
               l->sort.name);
          break;
      }
    }
    break;

    case BTOR_FORMAT_TAG_state:
    {
      long i = (long) BTOR_COUNT_STACK (states);
      if (l->symbol)
        msg (1, "state %ld %s at line %ld", i, l->symbol, l->lineno);
      else
        msg (1, "state %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (states, l);
    }
    break;

    case BTOR_FORMAT_TAG_zero: break;

    case BTOR_FORMAT_TAG_add:
    case BTOR_FORMAT_TAG_and:
    case BTOR_FORMAT_TAG_concat:
    case BTOR_FORMAT_TAG_const:
    case BTOR_FORMAT_TAG_constd:
    case BTOR_FORMAT_TAG_consth:
    case BTOR_FORMAT_TAG_dec:
    case BTOR_FORMAT_TAG_eq:
    case BTOR_FORMAT_TAG_fair:
    case BTOR_FORMAT_TAG_iff:
    case BTOR_FORMAT_TAG_implies:
    case BTOR_FORMAT_TAG_inc:
    case BTOR_FORMAT_TAG_ite:
    case BTOR_FORMAT_TAG_justice:
    case BTOR_FORMAT_TAG_mul:
    case BTOR_FORMAT_TAG_nand:
    case BTOR_FORMAT_TAG_ne:
    case BTOR_FORMAT_TAG_neg:
    case BTOR_FORMAT_TAG_nor:
    case BTOR_FORMAT_TAG_not:
    case BTOR_FORMAT_TAG_one:
    case BTOR_FORMAT_TAG_ones:
    case BTOR_FORMAT_TAG_or:
    case BTOR_FORMAT_TAG_output:
    case BTOR_FORMAT_TAG_read:
    case BTOR_FORMAT_TAG_redand:
    case BTOR_FORMAT_TAG_redor:
    case BTOR_FORMAT_TAG_redxor:
    case BTOR_FORMAT_TAG_rol:
    case BTOR_FORMAT_TAG_ror:
    case BTOR_FORMAT_TAG_saddo:
    case BTOR_FORMAT_TAG_sdiv:
    case BTOR_FORMAT_TAG_sdivo:
    case BTOR_FORMAT_TAG_sext:
    case BTOR_FORMAT_TAG_sgt:
    case BTOR_FORMAT_TAG_sgte:
    case BTOR_FORMAT_TAG_slice:
    case BTOR_FORMAT_TAG_sll:
    case BTOR_FORMAT_TAG_slt:
    case BTOR_FORMAT_TAG_slte:
    case BTOR_FORMAT_TAG_smod:
    case BTOR_FORMAT_TAG_smulo:
    case BTOR_FORMAT_TAG_sra:
    case BTOR_FORMAT_TAG_srem:
    case BTOR_FORMAT_TAG_srl:
    case BTOR_FORMAT_TAG_ssubo:
    case BTOR_FORMAT_TAG_sub:
    case BTOR_FORMAT_TAG_uaddo:
    case BTOR_FORMAT_TAG_udiv:
    case BTOR_FORMAT_TAG_uext:
    case BTOR_FORMAT_TAG_ugt:
    case BTOR_FORMAT_TAG_ugte:
    case BTOR_FORMAT_TAG_ult:
    case BTOR_FORMAT_TAG_ulte:
    case BTOR_FORMAT_TAG_umulo:
    case BTOR_FORMAT_TAG_urem:
    case BTOR_FORMAT_TAG_usubo:
    case BTOR_FORMAT_TAG_write:
    case BTOR_FORMAT_TAG_xnor:
    case BTOR_FORMAT_TAG_xor:
    default:
      die ("parse error in '%s' at line %ld: unsupported '%ld %s%s'",
           model_path,
           l->lineno,
           l->id,
           l->name,
           l->nargs ? " ..." : "");
      break;
  }
}

static void
parse_model ()
{
  mem = btor_mem_mgr_new ();
  BTOR_INIT_STACK (mem, inputs);
  BTOR_INIT_STACK (mem, states);
  BTOR_INIT_STACK (mem, bads);
  BTOR_INIT_STACK (mem, constraints);
  assert (model_file);
  BtorFormatReader *model = btorfmt_new ();
  if (!btorfmt_read_lines (model, model_file))
    die ("parse error in '%s' at %s", model_path, btorfmt_error (model));
  num_format_lines = btorfmt_max_id (model);
  BTOR_CNEWN (mem, inits, num_format_lines);
  BTOR_CNEWN (mem, nexts, num_format_lines);
  BtorFormatLineIterator it = btorfmt_iter_init (model);
  BtorFormatLine *line;
  while ((line = btorfmt_iter_next (&it))) parse_model_line (line);
}

static int print_trace = 1;

static BtorRNG rng;

int
main (int argc, char **argv)
{
  int res = 0, r = -1, s = -1;
  for (int i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
      fputs (usage, stdout), exit (0);
    else if (!strcmp (argv[i], "-c"))
      print_trace = 0;
    else if (!strcmp (argv[i], "-v"))
      verbosity++;
    else if (!strcmp (argv[i], "-r"))
    {
      if (++i == argc) die ("argument to '-r' missing");
      if (!parse_positive_number (argv[i], &r))
        die ("invalid number in '-r %s'", argv[i]);
    }
    else if (!strcmp (argv[i], "-s"))
    {
      if (++i == argc) die ("argument to '-s' missing");
      if (!parse_positive_number (argv[i], &s))
        die ("invalid number in '-s %s'", argv[i]);
    }
    else if (argv[i][0] == '-')
      die ("invalid command line option '%s' (try '-h')", argv[i]);
    else if (witness_path)
      die ("too many file arguments '%s', '%s', and '%s'",
           model_path,
           witness_path,
           argv[i]);
    else if (model_path)
      witness_path = argv[i];
    else
      model_path = argv[i];
  }
  if (model_path)
  {
    if (!(model_file = fopen (model_path, "r")))
      die ("failed to open BTOR model file '%s' for reading", model_path);
    close_model_file = 1;
  }
  else
  {
    model_path       = "<stdin>";
    model_file       = stdin;
    close_model_file = 0;
  }
  if (witness_path)
  {
    if (!(witness_file = fopen (witness_path, "r")))
      die ("failed to open witness file '%s' for reading", witness_path);
    close_witness_file = 1;
    if (r >= 0)
      die ("unexpected '-r %d' since witness '%s' specified", r, witness_path);
    msg (0, "checking mode: model and witness specified");
    random_mode   = 0;
    checking_mode = 1;
  }
  else if (close_model_file)
  {
    close_witness_file = 0;
    if (r >= 0)
    {
      random_mode   = 1;
      checking_mode = 0;
      msg (0,
           "random mode: "
           "model and '-r %d' specified, but no witness",
           r);
    }
    else
    {
      msg (0,
           "checking mode: "
           "model, but no witness nor '-r ...' option specified");
      witness_path  = "<stdin>";
      witness_file  = stdin;
      checking_mode = 1;
      random_mode   = 0;
    }
  }
  else
  {
    close_witness_file = 0;
    msg (0, "random mode: no model nor witness specified");
    random_mode   = 1;
    checking_mode = 0;
  }
  if (model_path) msg (0, "reading BTOR model from '%s'", model_path);
  parse_model ();
  if (s < 0)
    s = 0;
  else if (!random_mode)
    die ("specifying a random seed in checking mode does not make sense");
  if (random_mode)
  {
    msg (0, "using random seed %d", s);
    btor_rng_init (&rng, (uint32_t) s);
  }
  if (witness_path) msg (0, "reading BTOR witness from '%s'", witness_path);
  if (close_model_file && fclose (model_file))
    die ("can not close model file '%s'", model_path);
  if (close_witness_file && fclose (witness_file))
    die ("can not close witness file '%s'", witness_path);

  BTOR_RELEASE_STACK (inputs);
  BTOR_RELEASE_STACK (states);
  BTOR_RELEASE_STACK (bads);
  BTOR_RELEASE_STACK (constraints);
  btorfmt_delete (model);
  BTOR_DELETEN (mem, inits, num_format_lines);
  BTOR_DELETEN (mem, nexts, num_format_lines);
  btor_mem_mgr_delete (mem);

  return res;
}
