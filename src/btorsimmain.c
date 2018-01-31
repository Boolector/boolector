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
  fputs ("*** 'btorsim' error: ", stderr);
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
    "  -b <n>    fake simulation to satisfy bad state property 'b<n>'\n"
    "  -j <n>    fake simulation to satisfy justice property 'j<n>'\n"
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

static int
parse_int (const char *str, int *res_ptr)
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

static int
parse_long (const char *str, long *res_ptr)
{
  const char *p = str;
  if (!*p) return 0;
  if (*p == '0' && p[1]) return 0;
  long res = 0;
  while (*p)
  {
    const int ch = *p++;
    if (!isdigit (ch)) return 0;
    if (LONG_MAX / 10 < res) return 0;
    res *= 10;
    const int digit = ch - '0';
    if (LONG_MAX - digit < res) return 0;
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
static BtorFormatLinePtrStack justices;

BTOR_DECLARE_STACK (BtorLong, long);

static BtorLongStack reached_bads;

static long constraints_violated = -1;
static long num_unreached_bads;

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
      BTOR_PUSH_STACK (reached_bads, -1);
      num_unreached_bads++;
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
    case BTOR_FORMAT_TAG_mul:
    case BTOR_FORMAT_TAG_nand:
    case BTOR_FORMAT_TAG_ne:
    case BTOR_FORMAT_TAG_nor:
    case BTOR_FORMAT_TAG_not:
    case BTOR_FORMAT_TAG_one:
    case BTOR_FORMAT_TAG_ones:
    case BTOR_FORMAT_TAG_or:
    case BTOR_FORMAT_TAG_redand:
    case BTOR_FORMAT_TAG_redor:
    case BTOR_FORMAT_TAG_slice:
    case BTOR_FORMAT_TAG_sub:
    case BTOR_FORMAT_TAG_uext:
    case BTOR_FORMAT_TAG_ugt:
    case BTOR_FORMAT_TAG_ugte:
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
    case BTOR_FORMAT_TAG_neg:
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
  BTOR_INIT_STACK (mem, justices);
  BTOR_INIT_STACK (mem, reached_bads);
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
simulate (long id)
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
    for (uint32_t i = 0; i < l->nargs; i++) args[i] = simulate (l->args[i]);
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
      case BTOR_FORMAT_TAG_mul:
        assert (l->nargs == 2);
        res = btor_bv_mul (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_nand:
        assert (l->nargs == 2);
        res = btor_bv_nand (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_ne:
        assert (l->nargs == 2);
        res = btor_bv_ne (mem, args[0], args[1]);
        break;
      case BTOR_FORMAT_TAG_nor:
        assert (l->nargs == 2);
        res = btor_bv_nor (mem, args[0], args[1]);
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
        {
          uint32_t width = args[0]->width;
          assert (width <= l->sort.bitvec.width);
          uint32_t padding = l->sort.bitvec.width - width;
          if (padding)
            res = btor_bv_uext (mem, args[0], padding);
          else
            res = btor_bv_copy (mem, args[0]);
        }
        break;
      case BTOR_FORMAT_TAG_ugt:
        assert (l->nargs == 2);
        res = btor_bv_ult (mem, args[1], args[0]);
        break;
      case BTOR_FORMAT_TAG_ugte:
        assert (l->nargs == 2);
        res = btor_bv_ulte (mem, args[1], args[0]);
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

static int print_trace = 1;
static BtorRNG rng;

static void
initialize_inputs (long k, int randomize)
{
  msg (1, "initializing inputs @%ld", k);
  if (print_trace) printf ("@%ld\n", k);
  for (long i = 0; i < BTOR_COUNT_STACK (inputs); i++)
  {
    BtorFormatLine *input = BTOR_PEEK_STACK (inputs, i);
    uint32_t width        = input->sort.bitvec.width;
    if (current_state[input->id]) continue;
    BtorBitVector *update;
    if (randomize)
      update = btor_bv_new_random (mem, &rng, width);
    else
      update = btor_bv_new (mem, width);
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
initialize_states (int randomly)
{
  msg (1, "initializing states at #0");
  if (print_trace) printf ("#0\n");
  for (long i = 0; i < BTOR_COUNT_STACK (states); i++)
  {
    BtorFormatLine *state = BTOR_PEEK_STACK (states, i);
    assert (0 <= state->id), assert (state->id < num_format_lines);
    if (current_state[state->id]) continue;
    BtorFormatLine *init = inits[state->id];
    BtorBitVector *update;
    if (init)
    {
      assert (init->nargs == 2);
      assert (init->args[0] == state->id);
      update = simulate (init->args[1]);
    }
    else
    {
      assert (state->sort.tag == BTOR_FORMAT_TAG_SORT_bitvec);
      uint32_t width = state->sort.bitvec.width;
      if (randomly)
        update = btor_bv_new_random (mem, &rng, width);
      else
        update = btor_bv_new (mem, width);
    }
    update_current_state (state->id, update);
    if (print_trace && !init)
    {
      printf ("%ld ", i);
      btor_bv_print_without_new_line (update);
      if (state->symbol) printf (" %s#0", state->symbol);
      fputc ('\n', stdout);
    }
  }
}

static void
simulate_step (long k, int randomize_states_that_are_inputs)
{
  msg (1, "simulate step %ld", k);
  for (long i = 0; i < num_format_lines; i++)
  {
    BtorFormatLine *l = btorfmt_get_line_by_id (model, i);
    if (!l) continue;
    if (l->tag == BTOR_FORMAT_TAG_sort || l->tag == BTOR_FORMAT_TAG_init
        || l->tag == BTOR_FORMAT_TAG_next || l->tag == BTOR_FORMAT_TAG_bad
        || l->tag == BTOR_FORMAT_TAG_constraint
        || l->tag == BTOR_FORMAT_TAG_fair || l->tag == BTOR_FORMAT_TAG_justice)
      continue;

    BtorBitVector *bv = simulate (i);
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
      update = simulate (next->args[1]);
    }
    else
    {
      assert (state->sort.tag == BTOR_FORMAT_TAG_SORT_bitvec);
      uint32_t width = state->sort.bitvec.width;
      if (randomize_states_that_are_inputs)
        update = btor_bv_new_random (mem, &rng, width);
      else
        update = btor_bv_new (mem, width);
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
      long r = BTOR_PEEK_STACK (reached_bads, i);
      if (r >= 0) continue;
      BtorFormatLine *bad = BTOR_PEEK_STACK (bads, i);
      BtorBitVector *bv   = current_state[bad->args[0]];
      if (btor_bv_is_zero (bv)) continue;
      long bound = BTOR_PEEK_STACK (reached_bads, i);
      if (bound >= 0) continue;
      BTOR_POKE_STACK (reached_bads, i, k);
      assert (num_unreached_bads > 0);
      if (!--num_unreached_bads)
        msg (1,
             "all %ld bad state properties reached",
             (long) BTOR_COUNT_STACK (bads));
    }
  }
}

static void
transition (long k)
{
  msg (1, "transition %ld", k);
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
report ()
{
  if (num_unreached_bads < BTOR_COUNT_STACK (bads))
  {
    printf ("[btorsim] reached bad state properties {");
    for (long i = 0; i < BTOR_COUNT_STACK (bads); i++)
    {
      long r = BTOR_PEEK_STACK (reached_bads, i);
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

static void
random_simulation (long k)
{
  msg (1, "starting random simulation up to bound %ld", k);
  assert (k >= 0);

  const int randomize = 1;

  initialize_states (randomize);
  initialize_inputs (0, randomize);
  simulate_step (0, randomize);

  for (long i = 1; i <= k; i++)
  {
    if (constraints_violated >= 0) break;
    if (!num_unreached_bads) break;
    transition (i);
    initialize_inputs (i, randomize);
    simulate_step (i, randomize);
  }

  if (print_trace) printf (".\n"), fflush (stdout);
  report ();
}

static long charno;
static long columno;
static long lineno = 1;
static int saved_char;
static int char_saved;
static uint64_t last_line_length;

static BtorCharStack constant;
static BtorCharStack symbol;

static int
next_char ()
{
  int res;
  if (char_saved)
  {
    res        = saved_char;
    char_saved = 0;
  }
  else
  {
    res = getc_unlocked (witness_file);
  }
  if (res == '\n')
  {
    last_line_length = columno;
    columno          = 0;
    lineno++;
  }
  else if (res != EOF)
  {
    columno++;
  }
  if (res != EOF) charno++;
  return res;
}

static void
prev_char (int ch)
{
  assert (!char_saved);
  if (ch == '\n')
  {
    columno = last_line_length;
    assert (lineno > 0);
    lineno--;
  }
  else if (ch != EOF)
  {
    assert (charno > 0);
    charno--;
    assert (columno > 0);
    columno--;
  }
  saved_char = ch;
  char_saved = 1;
}

static void
parse_error (const char *msg, ...)
{
  fflush (stdout);
  assert (witness_path);
  fprintf (stderr,
           "*** 'btorsim' parse error in '%s' at line %ld column %ld: ",
           witness_path,
           lineno,
           columno);
  va_list ap;
  va_start (ap, msg);
  vfprintf (stderr, msg, ap);
  va_end (ap);
  fprintf (stderr, "\n");
  exit (1);
}

static long count_sat_witnesses;
static long count_unsat_witnesses;
static long count_unknown_witnesses;
static long count_witnesses;

static BtorLongStack claimed_bad_witnesses;
static BtorLongStack claimed_justice_witnesses;

static long
parse_unsigned_number (int *ch_ptr)
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

static long constant_columno;
static int found_end_of_witness;

static long
parse_assignment ()
{
  int ch = next_char ();
  if (ch == EOF) parse_error ("unexpected end-of-file (without '.')");
  if (ch == '.')
  {
    while ((ch = next_char ()) == ' ')
      ;
    if (ch == EOF) parse_error ("end-of-file after '.' instead of new-line");
    if (ch != '\n')
    {
      if (isprint (ch))
        parse_error ("unexpected character '%c' after '.'", ch);
      else
        parse_error ("unexpected character code 0x%02x after '.'", ch);
    }
    msg (4, "read terminating '.'");
    found_end_of_witness = 1;
    return -1;
  }
  if (ch == '@')
  {
    prev_char (ch);
    return -1;
  }
  prev_char (ch);
  long res = parse_unsigned_number (&ch);
  if (ch != ' ') parse_error ("space missing after '%ld'", res);
  BTOR_RESET_STACK (constant);
  constant_columno = columno + 1;
  while ((ch = next_char ()) == '0' || ch == '1')
    BTOR_PUSH_STACK (constant, ch);
  if (ch == '[') parse_error ("can not handle array assignments yet");
  if (BTOR_EMPTY_STACK (constant)) parse_error ("empty constant");
  if (BTOR_EMPTY_STACK (constant))
    if (ch != ' ' && ch != '\n')
      parse_error ("expected space or new-line after assignment");
  BTOR_PUSH_STACK (constant, 0);
  BTOR_RESET_STACK (symbol);
  while (ch != '\n')
    if ((ch = next_char ()) == EOF)
      parse_error ("unexpected end-of-file in assignment");
    else if (ch != '\n')
      BTOR_PUSH_STACK (symbol, ch);
  if (!BTOR_EMPTY_STACK (symbol)) BTOR_PUSH_STACK (symbol, 0);
  return res;
}

static void
parse_state_part (long k)
{
  int ch = next_char ();
  if (k > 0)
  {
    if (ch == '#')
      parse_error (
          "state assignments only supported in first frame at this point");
    prev_char (ch);
    return;
  }
  if (ch != '#' || (ch = next_char ()) != '0' || (ch = next_char ()) != '\n')
    parse_error ("missing '#0' state part header of frame 0");
  long state_pos;
  while ((state_pos = parse_assignment ()) >= 0)
  {
    long saved_charno = charno;
    charno            = 1;
    assert (lineno > 1);
    lineno--;
    if (state_pos >= BTOR_COUNT_STACK (states))
      parse_error ("less than %ld states defined", state_pos);
    if (BTOR_EMPTY_STACK (symbol))
      msg (4,
           "state assignment '%ld %s' at time frame %ld",
           state_pos,
           constant.start,
           k);
    else
      msg (4,
           "state assignment '%ld %s %s' at time frame %ld",
           state_pos,
           constant.start,
           symbol.start,
           k);
    BtorFormatLine *state = BTOR_PEEK_STACK (states, state_pos);
    assert (state);
    if (strlen (constant.start) != state->sort.bitvec.width)
      charno = constant_columno,
      parse_error ("expected constant of width '%u'", state->sort.bitvec.width);
    assert (0 <= state->id), assert (state->id < num_format_lines);
    if (current_state[state->id])
      parse_error ("state %ld id %ld assigned twice in frame %ld",
                   state_pos,
                   state->id,
                   k);
    BtorBitVector *val   = btor_bv_char_to_bv (mem, constant.start);
    BtorFormatLine *init = inits[state->id];
    if (init)
    {
      assert (init->nargs == 2);
      assert (init->args[0] == state->id);
      BtorBitVector *tmp = simulate (init->args[1]);
      if (btor_bv_compare (val, tmp))
        parse_error (
            "incompatible initialized state %ld id %ld", state_pos, state->id);
      btor_bv_free (mem, tmp);
    }
    lineno++;
    charno = saved_charno;
    update_current_state (state->id, val);
  }
}

static void
parse_input_part (long k)
{
  int ch = next_char ();
  if (ch != '@' || parse_unsigned_number (&ch) != k || ch != '\n')
    parse_assignment ("missing '@%ld' input part in frame %ld", k, k);
  long input_pos;
  while ((input_pos = parse_assignment ()) >= 0)
  {
    if (input_pos >= BTOR_COUNT_STACK (inputs))
      parse_error ("less than %ld defined", input_pos);
    if (BTOR_EMPTY_STACK (symbol))
      msg (4,
           "input assignment '%ld %s' at time frame %ld",
           input_pos,
           constant.start,
           k);
    else
      msg (4,
           "input assignment '%ld %s %s' at time frame %ld",
           input_pos,
           constant.start,
           symbol.start,
           k);
    BtorFormatLine *l = BTOR_PEEK_STACK (inputs, input_pos);
    assert (l);
    if (strlen (constant.start) != l->sort.bitvec.width)
      parse_error ("expected constant of width '%u'", l->sort.bitvec.width);
  }
}

static int
parse_frame (long k)
{
  if (k > 0) transition (k);
  msg (2, "parsing frame %ld", k);
  parse_state_part (k);
  parse_input_part (k);
  const int randomize = 0;
  if (!k) initialize_states (randomize);
  initialize_inputs (k, randomize);
  simulate_step (k, randomize);
  return !found_end_of_witness;
}

static void
parse_sat_witness ()
{
  assert (count_witnesses == 1);

  msg (1, "parsing 'sat' witness %ld", count_sat_witnesses);

  BTOR_INIT_STACK (mem, claimed_bad_witnesses);
  BTOR_INIT_STACK (mem, claimed_justice_witnesses);

  for (;;)
  {
    int type = next_char ();
    if (type == ' ') continue;
    if (type == '\n') break;
    ;
    if (type != 'b' && type != 'j') parse_error ("expected 'b' or 'j'");
    int ch;
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
    if (type == 'b')
    {
      if (bad >= BTOR_COUNT_STACK (bads))
        parse_error ("invalid bad state property number %ld", bad);
      msg (3, "... claims to be witness of bad state property number %ld", bad);
      BTOR_PUSH_STACK (claimed_bad_witnesses, bad);
    }
    else
      parse_error ("can not handle justice properties yet");
    if (ch == '\n') break;
  }

  long k = 0;
  while (parse_frame (k)) k++;

  if (!k) parse_error ("initial frame 0 missing");
  msg (1, "finished parsing k = %ld frames", k);

  report ();
  if (print_trace) printf (".\n"), fflush (stdout);

  for (long i = 0; i < BTOR_COUNT_STACK (claimed_bad_witnesses); i++)
  {
    long bad_pos      = BTOR_PEEK_STACK (claimed_bad_witnesses, i);
    long bound        = BTOR_PEEK_STACK (reached_bads, bad_pos);
    BtorFormatLine *l = BTOR_PEEK_STACK (bads, bad_pos);
    if (bound < 0)
      die ("claimed bad state property 'b%ld' id %ld not reached",
           bad_pos,
           l->id);
  }

  BTOR_RELEASE_STACK (claimed_bad_witnesses);
  BTOR_RELEASE_STACK (claimed_justice_witnesses);
}

static void
parse_unknown_witness ()
{
  msg (1, "parsing unknown witness %ld", count_unknown_witnesses);
  long k = 0;

  while (parse_frame (k)) k++;

  if (!k) parse_error ("initial frame 0 missing");

  report ();
  if (print_trace) printf (".\n"), fflush (stdout);

  msg (1, "finished parsing k = %ld frames", k);
}

static void
parse_unsat_witness ()
{
  msg (1, "parsing 'unsat' witness %ld", count_unsat_witnesses);
  die ("'unsat' witnesses not supported yet");
}

static int
parse_and_check_witness ()
{
  int ch = next_char ();
  if (ch == EOF) return 0;

  found_end_of_witness = 0;

  if (ch == '#')
  {
    count_witnesses++;
    count_unknown_witnesses++;
    if (count_sat_witnesses + count_unknown_witnesses > 1)
      die ("more than one actual witness not supported yet");
    prev_char (ch);
    parse_unknown_witness ();
    return 1;
  }

  if (ch == 's')
  {
    if ((ch = next_char ()) == 'a' && (ch = next_char ()) == 't'
        && (ch = next_char ()) == '\n')
    {
      count_witnesses++;
      count_sat_witnesses++;
      msg (0,
           "found witness %ld header 'sat' in '%s' at line %ld",
           count_sat_witnesses,
           witness_path,
           lineno - 1);
      if (count_witnesses > 1)
        die ("more than one actual witness not supported yet");
      parse_sat_witness ();
      return 1;
    }
  }

  if (ch == 'u')
  {
    if ((ch = next_char ()) == 'n' && (ch = next_char ()) == 's'
        && (ch = next_char ()) == 'a' && (ch = next_char ()) == 't'
        && (ch = next_char ()) == '\n')
    {
      count_witnesses++;
      count_unsat_witnesses++;
      msg (0,
           "found witness %ld header 'unsat' in '%s' at line %ld",
           witness_path,
           count_unsat_witnesses,
           lineno - 1);
      parse_unsat_witness ();
      return 1;
    }
  }

  while (ch != '\n')
  {
    ch = next_char ();
    if (ch == EOF) parse_error ("unexpected end-of-file before new-line");
  }

  return 1;
}

static void
parse_and_check_all_witnesses ()
{
  BTOR_INIT_STACK (mem, constant);
  BTOR_INIT_STACK (mem, symbol);
  assert (witness_file);
  while (parse_and_check_witness ())
    ;
  BTOR_RELEASE_STACK (constant);
  BTOR_RELEASE_STACK (symbol);
  msg (1,
       "finished parsing %ld witnesses after reading %ld bytes (%.1f MB)",
       count_witnesses,
       charno,
       charno / (double) (1l << 20));
}

int
main (int argc, char **argv)
{
  long fake_bad = -1, fake_justice = -1;
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
      if (!parse_int (argv[i], &r)) die ("invalid number in '-r %s'", argv[i]);
    }
    else if (!strcmp (argv[i], "-s"))
    {
      if (++i == argc) die ("argument to '-s' missing");
      if (!parse_int (argv[i], &s)) die ("invalid number in '-s %s'", argv[i]);
    }
    else if (!strcmp (argv[i], "-b"))
    {
      if (++i == argc) die ("argument to '-b' missing");
      if (!parse_long (argv[i], &fake_bad))
        die ("invalid number in '-b %s'", argv[i]);
    }
    else if (!strcmp (argv[i], "-j"))
    {
      if (++i == argc) die ("argument to '-j' missing");
      if (!parse_long (argv[i], &fake_justice))
        die ("invalid number in '-j %s'", argv[i]);
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
    if (fake_bad >= 0) die ("can not fake bad state property in checking mode");
    if (fake_justice >= 0)
      die ("can not fake justice property in checking mode");
  }
  assert (model_path);
  msg (1, "reading BTOR model from '%s'", model_path);
  parse_model ();
  if (fake_bad >= BTOR_COUNT_STACK (bads))
    die ("invalid faked bad state property number %ld", fake_bad);
  if (fake_justice >= BTOR_COUNT_STACK (justices))
    die ("invalid faked justice property number %ld", fake_justice);
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
    if (print_trace)
    {
      if (fake_bad >= 0 && fake_justice >= 0)
        printf ("sat\nb%ld j%ld\n", fake_bad, fake_justice);
      else if (fake_bad >= 0)
        printf ("sat\nb%ld\n", fake_bad);
      else if (fake_justice >= 0)
        printf ("sat\nj%ld\n", fake_justice);
    }
    random_simulation (r);
  }
  else
  {
    assert (witness_path);
    msg (1, "reading BTOR witness from '%s'", witness_path);
    parse_and_check_all_witnesses ();
    if (close_witness_file && fclose (witness_file))
      die ("can not close witness file '%s'", witness_path);
  }
  BTOR_RELEASE_STACK (inputs);
  BTOR_RELEASE_STACK (states);
  BTOR_RELEASE_STACK (bads);
  BTOR_RELEASE_STACK (justices);
  BTOR_RELEASE_STACK (reached_bads);
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
