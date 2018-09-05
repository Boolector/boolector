/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017-2018 Aina Niemetz.
 *  Copyright (C) 2017 Mathias Preiner.
 *  Copyright (C) 2018 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolectormc.h"
#include "btormc.h"

#include "btor2parser/btor2parser.h"
#include "utils/btorhashint.h"
#include "utils/btormem.h"
#include "utils/btoroptparse.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>

#define LEN_OPTSTR 38
#define LEN_PARAMSTR 16
#define LEN_HELPSTR 80

#define BTOR_MC_SUCC_EXIT 0
#define BTOR_MC_ERR_EXIT 1

/*------------------------------------------------------------------------*/

static void
print_opt (FILE *out,
           BtorMemMgr *mm,
           const char *lng,
           const char *shrt,
           bool isflag,
           uint32_t dflt,
           const char *desc,
           bool print_dflt)
{
  assert (lng);
  assert (desc);

  char paramstr[LEN_PARAMSTR];
  char *descstr, descstrline[LEN_HELPSTR], *word;
  size_t i, len, len_paramstr;
  int32_t j;
  BtorCharStack optstr;
  BtorCharPtrStack words;

  if (!isflag)
    sprintf (paramstr, "<n>");
  else
    paramstr[0] = '\0';

  /* option string ------------------------------------------ */
  BTOR_INIT_STACK (mm, optstr);
  BTOR_PUSH_STACK (optstr, ' ');
  BTOR_PUSH_STACK (optstr, ' ');
  len_paramstr = strlen (paramstr);
  if (shrt)
  {
    BTOR_PUSH_STACK (optstr, '-');
    for (i = 0, len = strlen (shrt); i < len; i++)
      BTOR_PUSH_STACK (optstr, shrt[i]);
    if (len_paramstr > 0) BTOR_PUSH_STACK (optstr, ' ');
    for (i = 0; i < len_paramstr; i++)
      BTOR_PUSH_STACK (optstr, paramstr[i]);
    BTOR_PUSH_STACK (optstr, ',');
    BTOR_PUSH_STACK (optstr, ' ');
  }
  BTOR_PUSH_STACK (optstr, '-');
  BTOR_PUSH_STACK (optstr, '-');
  for (i = 0, len = strlen (lng); i < len; i++)
    BTOR_PUSH_STACK (optstr, lng[i]);
  if (len_paramstr > 0) BTOR_PUSH_STACK (optstr, '=');
  for (i = 0; i < len_paramstr; i++)
    BTOR_PUSH_STACK (optstr, paramstr[i]);

  len = BTOR_COUNT_STACK (optstr);
  for (i = len; i < LEN_OPTSTR - 1; i++) BTOR_PUSH_STACK (optstr, ' ');
  BTOR_PUSH_STACK (optstr, '\0');
  assert (strlen (optstr.start) <= LEN_OPTSTR);

  /* formatted description ---------------------------------- */
  /* append default value to description */
  if (print_dflt)
  {
    len = strlen (desc) + 3 + btor_util_num_digits (dflt);
    BTOR_CNEWN (mm, descstr, len + 1);
    sprintf (descstr, "%s [%u]", desc, dflt);
  }
  else
  {
    len = strlen (desc);
    BTOR_CNEWN (mm, descstr, len + 1);
    sprintf (descstr, "%s", desc);
  }
  BTOR_INIT_STACK (mm, words);
  word = strtok (descstr, " ");
  while (word)
  {
    BTOR_PUSH_STACK (words, btor_mem_strdup (mm, word));
    word = strtok (0, " ");
  }
  BTOR_DELETEN (mm, descstr, len + 1);

  BTOR_CLRN (descstrline, LEN_HELPSTR);
  sprintf (descstrline, "%s ", optstr.start);
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
    fprintf (out, "%s\n", descstrline);
    BTOR_CLRN (descstrline, LEN_HELPSTR);
    memset (descstrline, ' ', LEN_OPTSTR * sizeof (char));
  } while (i < BTOR_COUNT_STACK (words));

  /* cleanup */
  BTOR_RELEASE_STACK (optstr);
  while (!BTOR_EMPTY_STACK (words))
    btor_mem_freestr (mm, BTOR_POP_STACK (words));
  BTOR_RELEASE_STACK (words);
}

static void
print_help (FILE *out, BtorMC *mc)
{
  assert (mc);

  int32_t i;
  BtorMCOpt *o;

  fprintf (out, "usage: btormc [<option>...][<input>]\n");
  fprintf (out, "\n");
  fprintf (out, "where <option> is one of the following:\n");
  fprintf (out, "\n");

  print_opt (
      out, mc->mm, "help", "h", true, 0, "print this message and exit", false);
  print_opt (out, mc->mm, "copyright", 0, true, 0, "print copyright", false);
  print_opt (out, mc->mm, "version", 0, true, 0, "print version", false);

  fprintf (out, "\n");

  print_opt (out, mc->mm, "dump", "d", true, 0, "dump formula", false);
  print_opt (
      out,
      mc->mm,
      "checkall",
      "ca",
      true,
      0,
      "check the disjunction of given properties rather than checking each "
      "property individually",
      false);

  for (i = 0; i < BTOR_MC_OPT_NUM_OPTS; i++)
  {
    o = &mc->options[i];
    print_opt (out, mc->mm, o->lng, o->shrt, o->isflag, o->dflt, o->desc, true);
  }
}

static int32_t
error (char *m, ...)
{
  va_list list;
  va_start (list, m);
  fputs ("btormc: ", stderr);
  vfprintf (stderr, m, list);
  fprintf (stderr, "\n");
  va_end (list);
  return BTOR_MC_ERR_EXIT;
}

static void
msg (char *m, ...)
{
  assert (m);

  va_list list;
  va_start (list, m);
  fprintf (stdout, "[btormc] ");
  vfprintf (stdout, m, list);
  fprintf (stdout, "\n");
  va_end (list);
}

#define BTOR_MC_BOOLECTOR_FUN(name) (n =)

static int32_t
parse (BtorMC *mc, FILE *infile, const char *infile_name, bool checkall)
{
  assert (mc);
  assert (infile);
  assert (infile_name);

  uint32_t i, verb, bw;
  long j;
  int32_t res;
  const char *err;
  BtorIntHashTable *sortmap;
  BtorIntHashTable *nodemap;
  BtorIntHashTableIterator it;
  Btor2Parser *bfr;
  Btor2LineIterator lit;
  Btor2Line *l;
  BoolectorNode *e[3], *n;
  BoolectorSort s, si, se;
  Btor *btor;
  BoolectorNodePtrStack bad;

  verb    = btor_mc_get_opt (mc, BTOR_MC_OPT_VERBOSITY);
  res     = BTOR_MC_SUCC_EXIT;
  bfr     = btor2parser_new ();
  nodemap = 0;
  sortmap = 0;

  BTOR_INIT_STACK (mc->mm, bad);

  if (verb) msg ("parsing input file...");

  if (!btor2parser_read_lines (bfr, infile))
  {
    err = btor2parser_error (bfr);
    assert (err);
    res = error ("parse error in '%s' %s", infile_name, err);
    goto DONE;
  }

  if (verb) msg ("finished parsing");

  sortmap = btor_hashint_map_new (mc->mm);
  nodemap = btor_hashint_map_new (mc->mm);
  btor    = mc->btor;

  lit = btor2parser_iter_init (bfr);
  while ((l = btor2parser_iter_next (&lit)))
  {
    n = 0;
    s = 0;

    if (l->id > INT32_MAX)
    {
      res = error ("given id '%" PRId64 "' exceeds INT32_MAX", l->id);
      goto DONE;
    }

    /* sort */
    if (l->tag != BTOR2_TAG_sort && l->sort.id)
    {
      if (l->sort.id > INT32_MAX)
      {
        res = error ("given id '%" PRId64 "' exceeds INT32_MAX", l->sort.id);
        goto DONE;
      }
      assert (btor_hashint_map_contains (sortmap, l->sort.id));
      s = btor_hashint_map_get (sortmap, l->sort.id)->as_ptr;
      assert (s);
    }

    /* args */
    for (i = 0; i < l->nargs; i++)
    {
      long signed_arg   = l->args[i];
      long unsigned_arg = signed_arg < 0 ? -signed_arg : signed_arg;
      assert (btor_hashint_map_contains (nodemap, unsigned_arg));
      BoolectorNode *tmp = btor_hashint_map_get (nodemap, unsigned_arg)->as_ptr;
      if (signed_arg < 0)
      {
        e[i] = boolector_not (btor, tmp);
        boolector_release (btor, tmp);
      }
      else
      {
        e[i] = tmp;
      }
      assert (e[i]);
    }

    switch (l->tag)
    {
      case BTOR2_TAG_add:
        assert (l->nargs == 2);
        n = boolector_add (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_and:
        assert (l->nargs == 2);
        n = boolector_and (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_bad:
        assert (l->nargs == 1);
        if (checkall)
          BTOR_PUSH_STACK (bad, boolector_copy (btor, e[0]));
        else
          boolector_mc_bad (mc, e[0]);
        if (l->symbol) boolector_set_symbol (btor, e[0], l->symbol);
        break;

      case BTOR2_TAG_concat:
        assert (l->nargs == 2);
        n = boolector_concat (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_const:
        assert (l->nargs == 0);
        assert (l->constant);
        bw = l->sort.bitvec.width;
        if (!btor_util_check_bin_to_bv (mc->mm, l->constant, bw))
        {
          res = error (
              "parse error: invalid 'const' %s of bw %u", l->constant, bw);
          goto DONE;
        }
        n = boolector_const (btor, l->constant);
        break;

      case BTOR2_TAG_constd:
        assert (l->nargs == 0);
        assert (l->constant);
        bw = l->sort.bitvec.width;
        if (!btor_util_check_dec_to_bv (mc->mm, l->constant, bw))
        {
          res = error (
              "parse error: invalid 'constd' %s of bw %u", l->constant, bw);
          goto DONE;
        }
        n = boolector_constd (btor, s, l->constant);
        break;

      case BTOR2_TAG_consth:
        assert (l->nargs == 0);
        assert (l->constant);
        bw = l->sort.bitvec.width;
        if (!btor_util_check_hex_to_bv (mc->mm, l->constant, bw))
        {
          res = error (
              "parse error: invalid 'consth' %s of bw %u", l->constant, bw);
          goto DONE;
        }
        n = boolector_consth (btor, s, l->constant);
        break;

      case BTOR2_TAG_constraint:
        assert (l->nargs == 1);
        boolector_mc_constraint (mc, e[0]);
        break;

      case BTOR2_TAG_dec:
        assert (l->nargs == 1);
        n = boolector_dec (btor, e[0]);
        break;

      case BTOR2_TAG_eq:
        assert (l->nargs == 2);
        n = boolector_eq (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_fair:
        fprintf (stderr, "warning: unsupported tag '%s'\n", l->name);
        // TODO
        // assert (l->nargs == 1);
        // boolector_mc_fair (mc, e[0]);
        break;

      case BTOR2_TAG_iff:
        assert (l->nargs == 2);
        n = boolector_iff (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_implies:
        assert (l->nargs == 2);
        n = boolector_implies (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_inc:
        assert (l->nargs == 1);
        n = boolector_inc (btor, e[0]);
        break;

      case BTOR2_TAG_init:
        assert (l->nargs == 2);
        assert (boolector_get_sort (btor, e[0]) == s);
        assert (!boolector_is_bitvec_sort (btor, s)
                || boolector_get_sort (btor, e[1]) == s);
        assert (!boolector_is_array_sort (btor, s)
                || boolector_get_width (btor, e[0])
                       == boolector_get_width (btor, e[1]));
        boolector_mc_init (mc, e[0], e[1]);
        break;

      case BTOR2_TAG_input:
        assert (l->nargs == 0);
        n = boolector_mc_input (mc, s, l->symbol);
        break;

      case BTOR2_TAG_ite:
        assert (l->nargs == 3);
        n = boolector_cond (btor, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_justice:
        fprintf (stderr, "warning: unsupported tag '%s'\n", l->name);
        // TODO
        // assert (l->nargs == 1);
        // boolector_mc_justice (mc, e[0]);
        break;

      case BTOR2_TAG_mul:
        assert (l->nargs == 2);
        n = boolector_mul (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_nand:
        assert (l->nargs == 2);
        n = boolector_nand (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ne:
        assert (l->nargs == 2);
        n = boolector_ne (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_neg:
        assert (l->nargs == 1);
        n = boolector_neg (btor, e[0]);
        break;

      case BTOR2_TAG_next:
        assert (l->nargs == 2);
        assert (boolector_get_sort (btor, e[0]) == s);
        assert (boolector_get_sort (btor, e[1]) == s);
        boolector_mc_next (mc, e[0], e[1]);
        break;

      case BTOR2_TAG_nor:
        assert (l->nargs == 2);
        n = boolector_nor (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_not:
        assert (l->nargs == 1);
        n = boolector_not (btor, e[0]);
        break;

      case BTOR2_TAG_one:
        assert (l->nargs == 0);
        n = boolector_one (btor, s);
        break;

      case BTOR2_TAG_ones:
        assert (l->nargs == 0);
        n = boolector_ones (btor, s);
        break;

      case BTOR2_TAG_or:
        assert (l->nargs == 2);
        n = boolector_or (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_output:
        fprintf (stderr, "warning: unsupported tag '%s'\n", l->name);
        // TODO
        break;

      case BTOR2_TAG_read:
        assert (l->nargs == 2);
        n = boolector_read (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_redand:
        assert (l->nargs == 1);
        n = boolector_redand (btor, e[0]);
        break;

      case BTOR2_TAG_redor:
        assert (l->nargs == 1);
        n = boolector_redor (btor, e[0]);
        break;

      case BTOR2_TAG_redxor:
        assert (l->nargs == 1);
        n = boolector_redxor (btor, e[0]);
        break;

      case BTOR2_TAG_rol:
        assert (l->nargs == 2);
        n = boolector_rol (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ror:
        assert (l->nargs == 2);
        n = boolector_ror (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_saddo:
        assert (l->nargs == 2);
        n = boolector_saddo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sdiv:
        assert (l->nargs == 2);
        n = boolector_sdiv (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sdivo:
        assert (l->nargs == 2);
        n = boolector_sdivo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sext:
        assert (l->nargs == 1);
        n = boolector_sext (btor, e[0], l->args[1]);
        break;

      case BTOR2_TAG_sgt:
        assert (l->nargs == 2);
        n = boolector_sgt (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sgte:
        assert (l->nargs == 2);
        n = boolector_sgte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_slice:
        assert (l->nargs == 1);
        n = boolector_slice (btor, e[0], l->args[1], l->args[2]);
        break;

      case BTOR2_TAG_sll:
        assert (l->nargs == 2);
        n = boolector_sll (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_slt:
        assert (l->nargs == 2);
        n = boolector_slt (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_slte:
        assert (l->nargs == 2);
        n = boolector_slte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sort:
        if (l->sort.tag == BTOR2_TAG_SORT_bitvec)
        {
          assert (l->sort.bitvec.width);
          s = boolector_bitvec_sort (btor, l->sort.bitvec.width);
        }
        else
        {
          assert (l->sort.tag == BTOR2_TAG_SORT_array);
          j = l->sort.array.index;
          assert (j);
          if (j > INT32_MAX)
          {
            res = error ("given id '%" PRId64 "' exceeds INT32_MAX", j);
            goto DONE;
          }
          assert (btor_hashint_map_contains (sortmap, j));
          si = (BoolectorSort) btor_hashint_map_get (sortmap, j)->as_ptr;
          assert (si);
          j = l->sort.array.element;
          assert (j);
          if (j > INT32_MAX)
          {
            res = error ("given id '%" PRId64 "' exceeds INT32_MAX", j);
            goto DONE;
          }
          assert (btor_hashint_map_contains (sortmap, j));
          se = (BoolectorSort) btor_hashint_map_get (sortmap, j)->as_ptr;
          assert (se);
          s = boolector_array_sort (btor, si, se);
        }
        assert (!btor_hashint_map_contains (sortmap, l->id));
        btor_hashint_map_add (sortmap, l->id)->as_ptr = s;
        break;

      case BTOR2_TAG_smod:
        assert (l->nargs == 2);
        n = boolector_smod (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_smulo:
        assert (l->nargs == 2);
        n = boolector_smulo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sra:
        assert (l->nargs == 2);
        n = boolector_sra (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_srem:
        assert (l->nargs == 2);
        n = boolector_srem (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_srl:
        assert (l->nargs == 2);
        n = boolector_srl (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ssubo:
        assert (l->nargs == 2);
        n = boolector_ssubo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_state:
        assert (l->nargs == 0);
        n = boolector_mc_state (mc, s, l->symbol);
        break;

      case BTOR2_TAG_sub:
        assert (l->nargs == 2);
        n = boolector_sub (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_uaddo:
        assert (l->nargs == 2);
        n = boolector_uaddo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_udiv:
        assert (l->nargs == 2);
        n = boolector_udiv (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_uext:
        assert (l->nargs == 1);
        n = boolector_uext (btor, e[0], l->args[1]);
        break;

      case BTOR2_TAG_ugt:
        assert (l->nargs == 2);
        n = boolector_ugt (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ugte:
        assert (l->nargs == 2);
        n = boolector_ugte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ult:
        assert (l->nargs == 2);
        n = boolector_ult (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ulte:
        assert (l->nargs == 2);
        n = boolector_ulte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_umulo:
        assert (l->nargs == 2);
        n = boolector_umulo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_urem:
        assert (l->nargs == 2);
        n = boolector_urem (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_usubo:
        assert (l->nargs == 2);
        n = boolector_usubo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_write:
        assert (l->nargs == 3);
        n = boolector_write (btor, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_xnor:
        assert (l->nargs == 2);
        n = boolector_xnor (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_xor:
        assert (l->nargs == 2);
        n = boolector_xor (btor, e[0], e[1]);
        break;

      default:
        assert (l->tag == BTOR2_TAG_zero);
        assert (l->nargs == 0);
        n = boolector_zero (btor, s);
    }
    assert (!s || !n || boolector_get_sort (btor, n) == s);
    if (n)
    {
      assert (!btor_hashint_map_contains (nodemap, l->id));
      btor_hashint_map_add (nodemap, l->id)->as_ptr = n;
    }
  }
  if (checkall && BTOR_COUNT_STACK (bad))
  {
    BoolectorNode *tmp;
    BoolectorNode *b = boolector_copy (btor, BTOR_PEEK_STACK (bad, 0));
    for (i = 1; i < BTOR_COUNT_STACK (bad); i++)
    {
      tmp = boolector_or (btor, b, BTOR_PEEK_STACK (bad, i));
      boolector_release (btor, b);
      b = tmp;
    }
    boolector_mc_bad (mc, b);
    boolector_release (btor, b);
  }
DONE:
  while (!BTOR_EMPTY_STACK (bad))
    boolector_release (btor, BTOR_POP_STACK (bad));
  BTOR_RELEASE_STACK (bad);
  if (nodemap)
  {
    btor_iter_hashint_init (&it, nodemap);
    while (btor_iter_hashint_has_next (&it))
    {
      j = it.cur_pos;
      n = btor_iter_hashint_next_data (&it)->as_ptr;
      boolector_release (btor, n);
    }
    btor_hashint_map_delete (nodemap);
  }
  if (sortmap)
  {
    btor_iter_hashint_init (&it, sortmap);
    while (btor_iter_hashint_has_next (&it))
      boolector_release_sort (btor, btor_iter_hashint_next_data (&it)->as_ptr);
    btor_hashint_map_delete (sortmap);
  }
  btor2parser_delete (bfr);
  return res;
}

int32_t
main (int32_t argc, char **argv)
{
  size_t i, len;
  int32_t close_infile;
  int32_t res;
  bool dump, checkall;
  uint32_t kmin, kmax;
  char *infile_name, *cmd;
  FILE *infile, *out;
  BtorParsedOpt *po;
  BtorParsedOptPtrStack opts;
  BtorParsedInput *pin;
  BtorParsedInputPtrStack infiles;
  BtorMemMgr *mm;
  BtorMCOption opt;
  BtorMCOpt *o;
  BtorMC *mc;

  close_infile = 0;
  infile       = stdin;
  infile_name  = "<stdin>";
  out          = stdout;

  res = BTOR_MC_SUCC_EXIT;

  dump     = false;
  checkall = false;

  mm = btor_mem_mgr_new ();
  mc = boolector_mc_new ();

  BTOR_INIT_STACK (mm, opts);
  BTOR_INIT_STACK (mm, infiles);

  btor_optparse_parse (mm, argc, argv, &opts, &infiles, 0, 0);

  /* input file ======================================================= */

  if (BTOR_COUNT_STACK (infiles) > 1)
  {
    res = error ("multiple input files");
    goto DONE;
  }
  else if (BTOR_COUNT_STACK (infiles) == 1)
  {
    infile_name = BTOR_PEEK_STACK (infiles, 0)->name;
    if (!btor_util_file_exists (infile_name))
    {
      infile = 0;
    }
    else if (btor_util_file_has_suffix (infile_name, ".gz")
             || btor_util_file_has_suffix (infile_name, ".bz2")
             || btor_util_file_has_suffix (infile_name, ".7z")
             || btor_util_file_has_suffix (infile_name, ".zip"))
    {
      len = strlen (infile_name);
      BTOR_NEWN (mm, cmd, len + 40);
      if (btor_util_file_has_suffix (infile_name, ".gz"))
        sprintf (cmd, "gunzip -c %s", infile_name);
      else if (btor_util_file_has_suffix (infile_name, ".bz2"))
        sprintf (cmd, "bzcat %s", infile_name);
      else if (btor_util_file_has_suffix (infile_name, ".7z"))
        sprintf (cmd, "7z x -so %s 2> /dev/null", infile_name);
      else if (btor_util_file_has_suffix (infile_name, ".zip"))
        sprintf (cmd, "unzip -p %s", infile_name);

      if ((infile = popen (cmd, "r"))) close_infile = 2;

      BTOR_DELETEN (mm, cmd, len + 40);
    }
    else if ((infile = fopen (infile_name, "r")))
    {
      close_infile = 1;
    }

    if (!infile)
    {
      res = error ("can not read '%s'", infile_name);
      goto DONE;
    }
  }

  /* options ========================================================== */

  for (i = 0; i < BTOR_COUNT_STACK (opts); i++)
  {
    po = BTOR_PEEK_STACK (opts, i);

    /* main-only options */

    if (strcmp (po->name.start, "h") == 0
        || strcmp (po->name.start, "help") == 0)
    {
      print_help (out, mc);
      return 0;
    }
    else if (strcmp (po->name.start, "copyright") == 0)
    {
      fprintf (out, "%s", boolector_copyright (mc->btor));
      return 0;
    }
    else if (strcmp (po->name.start, "version") == 0)
    {
      fprintf (out, "%s\n", boolector_version (mc->btor));
    }
    else if (strcmp (po->name.start, "d") == 0
             || strcmp (po->name.start, "dump") == 0)
    {
      dump = true;
    }
    else if (strcmp (po->name.start, "ca") == 0
             || strcmp (po->name.start, "checkall") == 0)
    {
      checkall = true;
    }
    /* mc options */
    else
    {
      for (opt = 0; opt < BTOR_MC_OPT_NUM_OPTS; opt++)
      {
        o = &mc->options[opt];
        if ((o->shrt && strcmp (po->name.start, o->shrt) == 0)
            || strcmp (po->name.start, o->lng) == 0)
        {
          break;
        }
        o = 0;
      }
      if (!o)
      {
        res = error ("invalid option '%s'", po->orig.start);
        goto DONE;
      }
      if (BTOR_ARG_IS_MISSING (BTOR_ARG_EXPECT_INT, o->isflag, po->readval))
      {
        res = error ("missing argument for '%s'", po->orig.start);
        goto DONE;
      }
      if (BTOR_ARG_IS_INVALID (BTOR_ARG_EXPECT_INT, o->isflag, po->readval))
      {
        res = error ("invalid argument for '%s', expected int", po->orig.start);
        goto DONE;
      }
      if (o->isflag)
      {
        if (po->isdisable)
        {
          btor_mc_set_opt (mc, opt, 0);
        }
        else
        {
          switch (opt)
          {
            case BTOR_MC_OPT_VERBOSITY:
              if (BTOR_ARG_READ_IS_INT (po->readval))
                btor_mc_set_opt (mc, opt, po->val);
              else
                btor_mc_set_opt (mc, opt, btor_mc_get_opt (mc, opt) + 1);
              break;
            default:
              assert (opt != BTOR_MC_OPT_NUM_OPTS);
              if (BTOR_ARG_READ_IS_INT (po->readval))
                btor_mc_set_opt (mc, opt, po->val);
              else
                btor_mc_set_opt (mc, opt, 1);
          }
        }
      }
      else
      {
        assert (BTOR_ARG_READ_IS_INT (po->readval));
        btor_mc_set_opt (mc, opt, po->val);
      }
    }
  }

  /* parse and execute ================================================ */

  res = parse (mc, infile, infile_name, checkall);

  if (res == BTOR_MC_SUCC_EXIT)
  {
    if (dump)
    {
      boolector_mc_dump (mc, out);
    }
    else
    {
      kmin = boolector_mc_get_opt (mc, BTOR_MC_OPT_MIN_K);
      kmax = boolector_mc_get_opt (mc, BTOR_MC_OPT_MAX_K);
      (void) boolector_mc_bmc (mc, kmin, kmax);
    }
  }

DONE:
  if (close_infile == 1)
    fclose (infile);
  else if (close_infile == 2)
    pclose (infile);
  boolector_mc_delete (mc);
  while (!BTOR_EMPTY_STACK (opts))
  {
    po = BTOR_POP_STACK (opts);
    assert (po->mm == mm);
    BTOR_RELEASE_STACK (po->orig);
    BTOR_RELEASE_STACK (po->name);
    BTOR_DELETE (mm, po);
  }
  BTOR_RELEASE_STACK (opts);
  while (!BTOR_EMPTY_STACK (infiles))
  {
    pin = BTOR_POP_STACK (infiles);
    assert (pin->mm == mm);
    BTOR_DELETE (mm, pin);
  }
  BTOR_RELEASE_STACK (infiles);
  btor_mem_mgr_delete (mm);
  return res;
}
