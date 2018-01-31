/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Armin Biere.
 *  Copyright (C) 2018 Aina Niemetz.
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
static int print_states;

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
    "  -h        print this command line option summary\n"
    "  -c        check only <witness> and do not print trace\n"
    "  -v        increase verbosity level (multiple times if necessary)\n"
    "  -r <n>    generate <n> random transitions (default 20)\n"
    "  -s <s>    random seed (default '0')\n"
    "\n"
    "  --states  print all states\n"
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

static long
parse_positive_number (const char *str, int *res_ptr)
{
  const char *p = str;
  if (!*p) return 0;
  if (*p == '0' && p[1]) return 0;
  long res = 0;
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

BTOR_DECLARE_STACK (BtorLong, long);

static BtorLongStack reached;

static long constraints_violated = -1;
static long unreached_bads;

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
      msg (2, "bad %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (bads, l);
      BTOR_PUSH_STACK (reached, -1);
    }
    break;

    case BTOR_FORMAT_TAG_constraint:
    {
      long i = (long) BTOR_COUNT_STACK (constraints);
      msg (2, "constraint %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (constraints, l);
    }
    break;

    case BTOR_FORMAT_TAG_init: inits[l->args[0]] = l; break;

    case BTOR_FORMAT_TAG_input:
    {
      long i = (long) BTOR_COUNT_STACK (inputs);
      if (l->symbol)
        msg (2, "input %ld '%s' at line %ld", i, l->symbol, l->lineno);
      else
        msg (2, "input %ld at line %ld", i, l->lineno);
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
              2, "sort bitvec %u at line %ld", l->sort.bitvec.width, l->lineno);
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
        msg (2, "state %ld '%s' at line %ld", i, l->symbol, l->lineno);
      else
        msg (2, "state %ld at line %ld", i, l->lineno);
      BTOR_PUSH_STACK (states, l);
    }
    break;

    case BTOR_FORMAT_TAG_add:
    case BTOR_FORMAT_TAG_and:
    case BTOR_FORMAT_TAG_concat:
    case BTOR_FORMAT_TAG_const:
    case BTOR_FORMAT_TAG_constd:
    case BTOR_FORMAT_TAG_consth:
    case BTOR_FORMAT_TAG_eq:
    case BTOR_FORMAT_TAG_implies:
    case BTOR_FORMAT_TAG_ite:
    case BTOR_FORMAT_TAG_ne:
    case BTOR_FORMAT_TAG_not:
    case BTOR_FORMAT_TAG_one:
    case BTOR_FORMAT_TAG_ones:
    case BTOR_FORMAT_TAG_or:
    case BTOR_FORMAT_TAG_redand:
    case BTOR_FORMAT_TAG_redor:
    case BTOR_FORMAT_TAG_slice:
    case BTOR_FORMAT_TAG_sub:
    case BTOR_FORMAT_TAG_uext:
    case BTOR_FORMAT_TAG_ult:
    case BTOR_FORMAT_TAG_ulte:
    case BTOR_FORMAT_TAG_xnor:
    case BTOR_FORMAT_TAG_xor:
    case BTOR_FORMAT_TAG_zero: break;

    case BTOR_FORMAT_TAG_dec:
    case BTOR_FORMAT_TAG_fair:
    case BTOR_FORMAT_TAG_iff:
    case BTOR_FORMAT_TAG_inc:
    case BTOR_FORMAT_TAG_justice:
    case BTOR_FORMAT_TAG_mul:
    case BTOR_FORMAT_TAG_nand:
    case BTOR_FORMAT_TAG_neg:
    case BTOR_FORMAT_TAG_nor:
    case BTOR_FORMAT_TAG_output:
    case BTOR_FORMAT_TAG_read:
    case BTOR_FORMAT_TAG_redxor:
    case BTOR_FORMAT_TAG_rol:
    case BTOR_FORMAT_TAG_ror:
    case BTOR_FORMAT_TAG_saddo:
    case BTOR_FORMAT_TAG_sdiv:
    case BTOR_FORMAT_TAG_sdivo:
    case BTOR_FORMAT_TAG_sext:
    case BTOR_FORMAT_TAG_sgt:
    case BTOR_FORMAT_TAG_sgte:
    case BTOR_FORMAT_TAG_sll:
    case BTOR_FORMAT_TAG_slt:
    case BTOR_FORMAT_TAG_slte:
    case BTOR_FORMAT_TAG_smod:
    case BTOR_FORMAT_TAG_smulo:
    case BTOR_FORMAT_TAG_sra:
    case BTOR_FORMAT_TAG_srem:
    case BTOR_FORMAT_TAG_srl:
    case BTOR_FORMAT_TAG_ssubo:
    case BTOR_FORMAT_TAG_uaddo:
    case BTOR_FORMAT_TAG_udiv:
    case BTOR_FORMAT_TAG_ugt:
    case BTOR_FORMAT_TAG_ugte:
    case BTOR_FORMAT_TAG_umulo:
    case BTOR_FORMAT_TAG_urem:
    case BTOR_FORMAT_TAG_usubo:
    case BTOR_FORMAT_TAG_write:
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
  BTOR_INIT_STACK (mem, reached);
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

static void
delete_current_state (long id)
{
  assert (0 <= id), assert (id < num_format_lines);
  if (current_state[id]) btor_bv_free (mem, current_state[id]);
  current_state[id] = 0;
}

static BtorBitVector *
randomly_simulate (long id)
{
  int sign = id < 0 ? -1 : 1;
  if (sign < 0) id = -id;
  assert (0 <= id), assert (id < num_format_lines);
  BtorBitVector *res = current_state[id];
  if (!res)
  {
    BtorFormatLine *l = btorfmt_get_line_by_id (model, id);
    if (!l) die ("internal error: unexpected empty ID %ld", id);
    BtorBitVector *args[3] = {0, 0, 0};
    for (uint32_t i = 0; i < l->nargs; i++)
      args[i] = randomly_simulate (l->args[i]);
    switch (l->tag)
    {
      case BTOR_FORMAT_TAG_add:
        assert (l->nargs == 2);
        res = btor_bv_add (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_and:
        assert (l->nargs == 2);
        res = btor_bv_and (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_concat:
        assert (l->nargs == 2);
        res = btor_bv_concat (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_const:
        assert (l->nargs == 0);
        res = btor_bv_char_to_bv (mem, l->constant);
        break;
      case BTOR_FORMAT_TAG_constd:
        assert (l->nargs == 0);
        res = btor_bv_constd (mem, l->constant, l->sort.bitvec.width);
        break;
      case BTOR_FORMAT_TAG_consth:
        assert (l->nargs == 0);
        res = btor_bv_consth (mem, l->constant, l->sort.bitvec.width);
        break;
      case BTOR_FORMAT_TAG_eq:
        assert (l->nargs == 2);
        res = btor_bv_eq (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_implies:
        assert (l->nargs == 2);
        res = btor_bv_implies (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_ite:
        assert (l->nargs == 3);
        res = btor_bv_ite (mem, args[0], args[1], args[2]);
        break;
      case BTOR_FORMAT_TAG_ne:
        assert (l->nargs == 2);
        res = btor_bv_ne (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_not:
        assert (l->nargs == 1);
        res = btor_bv_not (mem, args[0]);
        break;
      case BTOR_FORMAT_TAG_one:
        res = btor_bv_one (mem, l->sort.bitvec.width);
        break;
      case BTOR_FORMAT_TAG_ones:
        res = btor_bv_ones (mem, l->sort.bitvec.width);
        break;
      case BTOR_FORMAT_TAG_or:
        assert (l->nargs == 2);
        res = btor_bv_or (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_redand:
        assert (l->nargs == 1);
        res = btor_bv_redand (mem, args[0]);
        break;
      case BTOR_FORMAT_TAG_redor:
        assert (l->nargs == 1);
        res = btor_bv_redor (mem, args[0]);
        break;
      case BTOR_FORMAT_TAG_slice:
        assert (l->nargs == 1);
        res = btor_bv_slice (mem, args[0], l->args[1], l->args[2]);
        break;
      case BTOR_FORMAT_TAG_sub:
        assert (l->nargs == 2);
        res = btor_bv_sub (mem, args[0], args[1]);
        break;
        break;
      case BTOR_FORMAT_TAG_uext:
        assert (l->nargs == 1);
        res = btor_bv_uext (mem, args[0], l->sort.bitvec.width);
        break;
      case BTOR_FORMAT_TAG_ult:
        assert (l->nargs == 2);
        res = btor_bv_ult (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_ulte:
        assert (l->nargs == 2);
        res = btor_bv_ulte (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_xnor:
        assert (l->nargs == 2);
        res = btor_bv_xnor (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_xor:
        assert (l->nargs == 2);
        res = btor_bv_xor (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_zero:
        res = btor_bv_zero (mem, l->sort.bitvec.width);
        break;
      default:
        die ("can not randomly simulate operator '%s' at line %ld",
             l->name,
             l->lineno);
        break;
    }
    for (uint32_t i = 0; i < l->nargs; i++) btor_bv_free (mem, args[i]);
    update_current_state (id, res);
  }
  res = btor_bv_copy (mem, res);
  if (sign < 0)
  {
    BtorBitVector *tmp = btor_bv_not (mem, res);
    btor_bv_free (mem, res);
    res = tmp;
  }
  return res;
}

static void
random_inputs (long k)
{
  msg (1, "random inputs %ld", k);
  if (print_trace) printf ("@%ld\n", k);
  for (long i = 0; i < BTOR_COUNT_STACK (inputs); i++)
  {
    BtorFormatLine *input = BTOR_PEEK_STACK (inputs, i);
    uint32_t width        = input->sort.bitvec.width;
    BtorBitVector *update = btor_bv_new_random (mem, &rng, width);
    update_current_state (input->id, update);
    if (print_trace)
    {
      printf ("%ld ", i);
      btor_bv_print_without_new_line (update);
      if (input->symbol) printf (" %s@%ld", input->symbol, k);
      fputc ('\n', stdout);
    }
  }
}

static void
random_initialization ()
{
  msg (1, "random initialization");
  if (print_trace) printf ("#0\n");
  for (long i = 0; i < BTOR_COUNT_STACK (states); i++)
  {
    BtorFormatLine *state = BTOR_PEEK_STACK (states, i);
    assert (0 <= state->id), assert (state->id < num_format_lines);
    assert (!current_state[state->id]);
    BtorFormatLine *init = inits[state->id];
    BtorBitVector *update;
    if (init)
    {
      assert (init->nargs == 2);
      assert (init->args[0] == state->id);
      update = randomly_simulate (init->args[1]);
    }
    else
    {
      assert (state->sort.tag == BTOR_FORMAT_TAG_SORT_bitvec);
      uint32_t width = state->sort.bitvec.width;
      update         = btor_bv_new_random (mem, &rng, width);
    }
    update_current_state (state->id, update);
    if (print_trace)
    {
      printf ("%ld ", i);
      btor_bv_print_without_new_line (update);
      if (state->symbol) printf (" %s#0", state->symbol);
      fputc ('\n', stdout);
    }
  }
}

static void
random_step (long k)
{
  msg (1, "random step %ld", k);
  for (long i = 0; i < num_format_lines; i++)
  {
    BtorFormatLine *l = btorfmt_get_line_by_id (model, i);
    if (!l) continue;
    if (l->tag == BTOR_FORMAT_TAG_sort || l->tag == BTOR_FORMAT_TAG_init
        || l->tag == BTOR_FORMAT_TAG_next || l->tag == BTOR_FORMAT_TAG_bad
        || l->tag == BTOR_FORMAT_TAG_constraint
        || l->tag == BTOR_FORMAT_TAG_fair || l->tag == BTOR_FORMAT_TAG_justice)
      continue;

    BtorBitVector *bv = randomly_simulate (i);
#if 0
    printf ("[btorim] %ld %s ", l->id, l->name);
    btor_bv_print (bv);
    fflush (stdout);
#endif
    btor_bv_free (mem, bv);
  }
  for (long i = 0; i < BTOR_COUNT_STACK (states); i++)
  {
    BtorFormatLine *state = BTOR_PEEK_STACK (states, i);
    assert (0 <= state->id), assert (state->id < num_format_lines);
    BtorFormatLine *next = nexts[state->id];
    BtorBitVector *update;
    if (next)
    {
      assert (next->nargs == 2);
      assert (next->args[0] == state->id);
      update = randomly_simulate (next->args[1]);
    }
    else
    {
      assert (state->sort.tag == BTOR_FORMAT_TAG_SORT_bitvec);
      uint32_t width = state->sort.bitvec.width;
      update         = btor_bv_new_random (mem, &rng, width);
    }
    assert (!next_state[state->id]);
    next_state[state->id] = update;
  }

  if (constraints_violated < 0)
  {
    for (long i = 0; i < BTOR_COUNT_STACK (constraints); i++)
    {
      BtorFormatLine *constraint = BTOR_PEEK_STACK (constraints, i);
      BtorBitVector *bv          = current_state[constraint->args[0]];
      if (!btor_bv_is_zero (bv)) continue;
      msg (1,
           "constraint(%ld) '%ld constraint %ld' violdated at time %ld",
           i,
           constraint->id,
           constraint->args[0],
           k);
      constraints_violated = k;
    }
  }

  if (constraints_violated < 0)
  {
    for (long i = 0; i < BTOR_COUNT_STACK (bads); i++)
    {
      long r = BTOR_PEEK_STACK (reached, i);
      if (r >= 0) continue;
      BtorFormatLine *bad = BTOR_PEEK_STACK (bads, i);
      BtorBitVector *bv   = current_state[bad->args[0]];
      if (btor_bv_is_zero (bv)) continue;
      BTOR_POKE_STACK (reached, i, k);
      assert (unreached_bads > 0);
      if (!--unreached_bads)
        msg (1,
             "all %ld bad state properties reached",
             (long) BTOR_COUNT_STACK (bads));
    }
  }
}

static void
random_transition (long k)
{
  msg (1, "random step %ld", k);
  for (long i = 0; i < num_format_lines; i++) delete_current_state (i);
  if (print_trace && print_states) printf ("#%ld\n", k);
  for (long i = 0; i < BTOR_COUNT_STACK (states); i++)
  {
    BtorFormatLine *state = BTOR_PEEK_STACK (states, i);
    assert (0 <= state->id), assert (state->id < num_format_lines);
    BtorBitVector *update = next_state[state->id];
    assert (update);
    update_current_state (state->id, update);
    next_state[state->id] = 0;
    if (print_trace && print_states)
    {
      printf ("%ld ", i);
      btor_bv_print_without_new_line (update);
      if (state->symbol) printf (" %s#%ld", state->symbol, k);
      fputc ('\n', stdout);
    }
  }
}

static void
random_simulations (long k)
{
  assert (k >= 0);

  unreached_bads = BTOR_COUNT_STACK (bads);
  random_initialization ();
  random_inputs (0);
  random_step (0);

  for (long i = 1; i <= k; i++)
  {
    if (constraints_violated >= 0) break;
    if (!unreached_bads) break;
    random_transition (i);
    random_inputs (i);
    random_step (i);
  }

  if (unreached_bads < BTOR_COUNT_STACK (bads))
  {
    printf ("[btorsim] reached bad state properties {");
    for (long i = 0; i < BTOR_COUNT_STACK (bads); i++)
    {
      long r = BTOR_PEEK_STACK (reached, i);
      if (r >= 0) printf (" b%ld@%ld", i, r);
    }
    printf (" }\n");
  }
  else if (!BTOR_EMPTY_STACK (bads))
    msg (0, "no bad state property reached");

  if (constraints_violated >= 0)
    msg (0, "constraints violated at time %ld", constraints_violated);
  else if (!BTOR_EMPTY_STACK (constraints))
    msg (0, "constraints always satisfied");
}

static long charno;
static long columnno;
static long lineno = 1;
static BtorCharStack buffer;

static int
next_char ()
{
  assert (witness_file);
  int ch = getc_unlocked (witness_file);
  if (ch == '\n') lineno++, columnno = 0;
  if (ch != EOF) columnno++, charno++;
  return ch;
}

static void
parse_error (const char *msg, ...)
{
  fflush (stdout);
  assert (witness_path);
  fprintf (stderr,
           "btorsim: parse error in '%s' at line %ld column %ld: ",
           witness_path,
           lineno,
           columnno);
  va_list ap;
  va_start (ap, msg);
  vfprintf (stderr, msg, ap);
  va_end (ap);
  fprintf (stderr, "\n");
  exit (1);
}

static long count_sat_witnesses = 0, count_unsat_witnesses = 0;

static BtorLongStack bad_witnesses;

static long
parse_unsigned_number (char *ch_ptr)
{
  int ch = next_char ();
  long res;
  if (ch == '0')
  {
    ch = next_char ();
    if (isdigit (ch)) parse_error ("unexpected digit '%c' after '0'", ch);
    res = 0;
  }
  else if (!isdigit (ch))
    parse_error ("expected digit");
  else
  {
    res = ch - '0';
    while (isdigit (ch = next_char ()))
    {
      if (LONG_MAX / 10 < res)
        parse_error ("number too large (too many digits)");
      res *= 10;
      const int digit = ch - '0';
      if (LONG_MAX - digit < res) parse_error ("number too large");
      res += digit;
    }
  }
  *ch_ptr = ch;
  return res;
}

static void
parse_sat_witness ()
{
  msg (1, "parsing 'sat' witness %ld", count_sat_witnesses);
  BTOR_INIT_STACK (mem, bad_witnesses);
  for (;;)
  {
    int type = next_char ();
    if (type != 'b' && type != 'j') parse_error ("expected 'b' or 'j'");
    char ch;
    long bad = parse_unsigned_number (&ch);
    if (ch != ' ' && ch != '\n')
    {
      if (isprint (ch))
        parse_error (
            "unexpected '%c' after number (expected space or new-line)", ch);
      else
        parse_error (
            "unexpected character 0x%02x after number"
            " (expected space or new-line)",
            ch);
    }
  }
  BTOR_RELEASE_STACK (bad_witnesses);
}

static void
parse_unsat_witness ()
{
  msg (1, "parsing 'unsat' witness %ld", count_unsat_witnesses);
  die ("'unsat' witnesses not supported yet");
}

static void
parse_witnesses ()
{
  BTOR_INIT_STACK (mem, buffer);
  assert (witness_file);
  for (;;)
  {
    int ch = next_char ();
    if (ch == EOF) break;
    if (ch == 's')
    {
      if ((ch = next_char ()) == 'a' && (ch = next_char ()) == 't'
          && (ch = next_char ()) == '\n')
      {  // TODO '\r'
        count_sat_witnesses++;
        msg (0,
             "found witness %ld header 'sat' in '%s' at line %ld",
             witness_path,
             count_sat_witnesses,
             lineno - 1);
        if (count_sat_witnesses > 1)
          die ("more than one 'sat' witness not supported yet");
        parse_sat_witness ();
        continue;
      }
    }
    else if (ch == 'u')
    {
      if ((ch = next_char ()) == 'n' && (ch = next_char ()) == 's'
          && (ch = next_char ()) == 'a' && (ch = next_char ()) == 't'
          && (ch = next_char ()) == '\n')
      {  // TODO '\r'
        count_unsat_witnesses++;
        msg (0,
             "found witness %ld header 'unsat' in '%s' at line %ld",
             witness_path,
             count_unsat_witnesses,
             lineno - 1);
        parse_unsat_witness ();
        continue;
      }
    }
    while (ch != '\n')
    {
      ch = next_char ();
      if (ch == EOF) parse_error ("unexpected end-of-file before new-line");
    }
  }
  BTOR_RELEASE_STACK (buffer);
  msg (1,
       "finished parsing witness after reading %ld (%.1f MB)",
       charno,
       charno / (double) (1l << 20));
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
    else if (!strcmp (argv[i], "--states"))
      print_states = 1;
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
    msg (1, "checking mode: both model and witness specified");
    checking_mode = 1;
    random_mode   = 0;
  }
  else
  {
    msg (1, "random mode: witness not specified");
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
  msg (1, "reading BTOR model from '%s'", model_path);
  parse_model ();
  if (close_model_file && fclose (model_file))
    die ("can not close model file '%s'", model_path);
  BTOR_CNEWN (mem, current_state, num_format_lines);
  BTOR_CNEWN (mem, next_state, num_format_lines);
  if (random_mode)
  {
    if (r < 0) r = 20;
    if (s < 0) s = 0;
    msg (1, "using random seed %d", s);
    btor_rng_init (&rng, (uint32_t) s);
    random_simulations (r);
  }
  else
  {
    assert (witness_path);
    msg (1, "reading BTOR witness from '%s'", witness_path);
    parse_witnesses ();
    if (close_witness_file && fclose (witness_file))
      die ("can not close witness file '%s'", witness_path);
  }
  BTOR_RELEASE_STACK (inputs);
  BTOR_RELEASE_STACK (states);
  BTOR_RELEASE_STACK (bads);
  BTOR_RELEASE_STACK (reached);
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
