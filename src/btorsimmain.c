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

#include "btorbv.h"
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
  if (level > verbosity) return;
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
    "specified then it is read from '<stdin>'.  The simulator only uses\n"
    "checking mode if both the BTOR model and a witness file are specified.\n";

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

static BtorBitVector **current_state;
static BtorBitVector **next_state;

static void
parse_model_line (BtorFormatLine *l)
{
  switch (l->tag)
  {
    case BTOR_FORMAT_TAG_bad:
    {
      long i = (long) BTOR_COUNT_STACK (bads);
      msg (1, "bad %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (bads, l);
    }
    break;

    case BTOR_FORMAT_TAG_constraint:
    {
      long i = (long) BTOR_COUNT_STACK (constraints);
      msg (1, "constraint %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (constraints, l);
    }
    break;

    case BTOR_FORMAT_TAG_init: inits[l->args[0]] = l; break;

    case BTOR_FORMAT_TAG_input:
    {
      long i = (long) BTOR_COUNT_STACK (inputs);
      if (l->symbol)
        msg (1, "input %ld '%s' at line %ld", i, l->symbol, l->lineno);
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
        msg (1, "state %ld '%s' at line %ld", i, l->symbol, l->lineno);
      else
        msg (1, "state %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (states, l);
    }
    break;

    case BTOR_FORMAT_TAG_add:
    case BTOR_FORMAT_TAG_eq:
    case BTOR_FORMAT_TAG_ite:
    case BTOR_FORMAT_TAG_one:
    case BTOR_FORMAT_TAG_ones:
    case BTOR_FORMAT_TAG_zero: break;

    case BTOR_FORMAT_TAG_and:
    case BTOR_FORMAT_TAG_concat:
    case BTOR_FORMAT_TAG_const:
    case BTOR_FORMAT_TAG_constd:
    case BTOR_FORMAT_TAG_consth:
    case BTOR_FORMAT_TAG_dec:
    case BTOR_FORMAT_TAG_fair:
    case BTOR_FORMAT_TAG_iff:
    case BTOR_FORMAT_TAG_implies:
    case BTOR_FORMAT_TAG_inc:
    case BTOR_FORMAT_TAG_justice:
    case BTOR_FORMAT_TAG_mul:
    case BTOR_FORMAT_TAG_nand:
    case BTOR_FORMAT_TAG_ne:
    case BTOR_FORMAT_TAG_neg:
    case BTOR_FORMAT_TAG_nor:
    case BTOR_FORMAT_TAG_not:
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
  model = btorfmt_new ();
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

static void
update_current_state (long id, BtorBitVector *bv)
{
  assert (0 <= id), assert (id < num_format_lines);
  if (current_state[id]) btor_bv_free (mem, current_state[id]);
  current_state[id] = bv;
}

static BtorBitVector *
randomly_simulate (long id)
{
  int sign = id < 0 ? -1 : 1;
  if (sign < 0) id = -id;
  assert (0 <= id), assert (id < num_format_lines);
  BtorFormatLine *l = btorfmt_get_line_by_id (model, id);
  if (!l) die ("internal error: unexpected empty ID %ld", id);
  BtorBitVector *res = 0;
  switch (l->tag)
  {
    case BTOR_FORMAT_TAG_zero:
      res = btor_bv_new (mem, l->sort.bitvec.width);
      break;
    default:
      die ("can not randomly simulate operator '%s' at line %ld",
           l->name,
           l->lineno);
      break;
  }
  if (sign < 0)
  {
    BtorBitVector *tmp = btor_bv_neg (mem, res);
    btor_bv_free (mem, res);
    res = tmp;
  }
  return res;
}

static void
random_initialization ()
{
  msg (0, "random initialization");
  for (long i = 0; i < BTOR_COUNT_STACK (states); i++)
  {
    BtorFormatLine *state = BTOR_PEEK_STACK (states, i);
    BtorFormatLine *init  = inits[state->id];
    if (init)
    {
      assert (init->nargs == 2);
      assert (init->args[0] == state->id);
      BtorBitVector *update = randomly_simulate (init->args[1]);
      update_current_state (state->id, update);
    }
    else
    {
      // TODO random initialization
    }
  }
}

static void
random_step (long k)
{
  msg (0, "random step %ld", k);
}

static void
random_simulations (long k)
{
  random_initialization ();
  for (long i = 0; i <= k; i++) random_step (i);
}

int
main (int argc, char **argv)
{
  int r = -1, s = -1;
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
    model_path = "<stdin>";
    model_file = stdin;
  }
  if (witness_path)
  {
    if (!(witness_file = fopen (witness_path, "r")))
      die ("failed to open witness file '%s' for reading", witness_path);
    close_witness_file = 1;
  }
  if (model_path && witness_path)
  {
    msg (0, "checking mode: both model and witness specified");
    checking_mode = 1;
    random_mode   = 0;
  }
  else
  {
    msg (0, "random mode: witness not specified");
    checking_mode = 0;
    random_mode   = 1;
  }
  if (checking_mode)
  {
    if (r >= 0)
      die ("number of random test vectors specified in checking mode");
    if (s >= 0) die ("random seed specified in checking mode");
  }
  assert (model_path);
  msg (0, "reading BTOR model from '%s'", model_path);
  parse_model ();
  if (close_model_file && fclose (model_file))
    die ("can not close model file '%s'", model_path);
  BTOR_CNEWN (mem, current_state, num_format_lines);
  BTOR_CNEWN (mem, next_state, num_format_lines);
  if (random_mode)
  {
    if (r < 0) r = 20;
    if (s < 0) s = 0;
    msg (0, "using random seed %d", s);
    btor_rng_init (&rng, (uint32_t) s);
    random_simulations (r);
  }
  else
  {
    assert (witness_path);
    msg (0, "reading BTOR witness from '%s'", witness_path);
    // TODO
    if (close_witness_file && fclose (witness_file))
      die ("can not close witness file '%s'", witness_path);
  }
  BTOR_RELEASE_STACK (inputs);
  BTOR_RELEASE_STACK (states);
  BTOR_RELEASE_STACK (bads);
  BTOR_RELEASE_STACK (constraints);
  btorfmt_delete (model);
  BTOR_DELETEN (mem, inits, num_format_lines);
  BTOR_DELETEN (mem, nexts, num_format_lines);
  for (long i = 0; i < num_format_lines; i++)
    if (current_state[i]) btor_bv_free (mem, current_state[i]);
  for (long i = 0; i < num_format_lines; i++)
    if (next_state[i]) btor_bv_free (mem, next_state[i]);
  BTOR_DELETEN (mem, current_state, num_format_lines);
  BTOR_DELETEN (mem, next_state, num_format_lines);
  btor_mem_mgr_delete (mem);
  return 0;
}
