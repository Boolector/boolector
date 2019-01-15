/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btor2parser/btor2parser.h"
#include "btormsg.h"
#include "btorparse.h"
#include "btortypes.h"
#include "utils/btorhashint.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>

/*------------------------------------------------------------------------*/

void boolector_set_btor_id (Btor *, BoolectorNode *, int32_t);

void boolector_add_output (Btor *, BoolectorNode *);

/*------------------------------------------------------------------------*/

struct BtorBTOR2Parser
{
  BtorMemMgr *mm;
  Btor *btor;
  char *error;
  const char *infile_name;
  Btor2Parser *bfr;
};

typedef struct BtorBTOR2Parser BtorBTOR2Parser;

/*------------------------------------------------------------------------*/

static void
perr_btor2 (BtorBTOR2Parser *parser, uint64_t lineno, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start (ap, fmt);
    bytes = btor_mem_parse_error_msg_length (parser->infile_name, fmt, ap);
    va_end (ap);

    va_start (ap, fmt);
    parser->error = btor_mem_parse_error_msg (
        parser->mm, parser->infile_name, lineno, 0, fmt, ap, bytes);
    va_end (ap);
  }
}

/*------------------------------------------------------------------------*/

static BtorBTOR2Parser *
new_btor2_parser (Btor *btor)
{
  BtorMemMgr *mm = btor_mem_mgr_new ();
  BtorBTOR2Parser *res;

  BTOR_NEW (mm, res);
  BTOR_CLR (res);

  res->mm   = mm;
  res->btor = btor;
  res->bfr  = btor2parser_new ();

  return res;
}

static void
delete_btor2_parser (BtorBTOR2Parser *parser)
{
  BtorMemMgr *mm;

  mm = parser->mm;
  btor2parser_delete (parser->bfr);
  btor_mem_freestr (mm, parser->error);
  BTOR_DELETE (mm, parser);
  btor_mem_mgr_delete (mm);
}

static const char *
parse_btor2_parser (BtorBTOR2Parser *parser,
                    BtorCharStack *prefix,
                    FILE *infile,
                    const char *infile_name,
                    FILE *outfile,
                    BtorParseResult *res)
{
  assert (parser);
  assert (infile);
  assert (infile_name);
  (void) prefix;
  (void) outfile;

  uint32_t i, bw;
  int64_t j, signed_arg, unsigned_arg;
  Btor2LineIterator lit;
  Btor2Line *line;
  BtorIntHashTable *sortmap;
  BtorIntHashTable *nodemap;
  BtorIntHashTableIterator it;
  BoolectorNode *e[3], *node, *tmp;
  BoolectorSort sort, sort_index, sort_elem;
  BtorMemMgr *mm;
  BtorMsg *msg;
  Btor *btor;
  bool found_arrays, found_lambdas;

  btor = parser->btor;
  msg  = boolector_get_btor_msg (btor);

  BTOR_MSG (msg, 1, "parsing %s", infile_name);

  BTOR_CLR (res);

  mm = parser->mm;

  found_arrays = false;
  found_lambdas = false;

  nodemap = 0;
  sortmap = 0;

  parser->infile_name = infile_name;

  /* btor2parser doesn't allow to pass the prefix, we have to rewind to the
   * beginning of the input file instead. */
  if (fseek (infile, 0L, SEEK_SET))
  {
    perr_btor2 (parser, 0, "error when rewinding input file");
    goto DONE;
  }

  if (!btor2parser_read_lines (parser->bfr, infile))
  {
    parser->error = btor_mem_strdup (mm, btor2parser_error (parser->bfr));
    assert (parser->error);
    goto DONE;
  }

  sortmap = btor_hashint_map_new (mm);
  nodemap = btor_hashint_map_new (mm);

  lit = btor2parser_iter_init (parser->bfr);
  while ((line = btor2parser_iter_next (&lit)))
  {
    node = 0;
    sort = 0;

    if (line->id > INT32_MAX)
    {
      perr_btor2 (
          parser, line->id, "given id '%" PRId64 "' exceeds INT32_MAX", line->id);
      goto DONE;
    }

    /* sort ----------------------------------------------------------------  */

    if (line->tag != BTOR2_TAG_sort && line->sort.id)
    {
      if (line->sort.id > INT32_MAX)
      {
        perr_btor2 (parser,
                    line->id,
                    "given id '%" PRId64 "' exceeds INT32_MAX",
                    line->sort.id);
        goto DONE;
      }
      assert (btor_hashint_map_contains (sortmap, line->sort.id));
      sort = btor_hashint_map_get (sortmap, line->sort.id)->as_ptr;
      assert (sort);
    }

    /* arguments -----------------------------------------------------------  */

    for (i = 0; i < line->nargs; i++)
    {
      signed_arg   = line->args[i];
      unsigned_arg = signed_arg < 0 ? -signed_arg : signed_arg;
      assert (btor_hashint_map_contains (nodemap, unsigned_arg));
      tmp = btor_hashint_map_get (nodemap, unsigned_arg)->as_ptr;
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

    switch (line->tag)
    {
      case BTOR2_TAG_add:
        assert (line->nargs == 2);
        node = boolector_add (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_and:
        assert (line->nargs == 2);
        node = boolector_and (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_concat:
        assert (line->nargs == 2);
        node = boolector_concat (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_const:
        assert (line->nargs == 0);
        assert (line->constant);
        bw = line->sort.bitvec.width;
        if (!btor_util_check_bin_to_bv (mm, line->constant, bw))
        {
          perr_btor2 (parser,
                      line->id,
                      "invalid 'const' %sort of bw %u",
                      line->constant,
                      bw);
          goto DONE;
        }
        node = boolector_const (btor, line->constant);
        break;

      case BTOR2_TAG_constd:
        assert (line->nargs == 0);
        assert (line->constant);
        bw = line->sort.bitvec.width;
        if (!btor_util_check_dec_to_bv (mm, line->constant, bw))
        {
          perr_btor2 (parser,
                      line->id,
                      "invalid 'constd' %sort of bw %u",
                      line->constant,
                      bw);
          goto DONE;
        }
        node = boolector_constd (btor, sort, line->constant);
        break;

      case BTOR2_TAG_consth:
        assert (line->nargs == 0);
        assert (line->constant);
        bw = line->sort.bitvec.width;
        if (!btor_util_check_hex_to_bv (mm, line->constant, bw))
        {
          perr_btor2 (parser,
                      line->id,
                      "invalid 'consth' %sort of bw %u",
                      line->constant,
                      bw);
          goto DONE;
        }
        node = boolector_consth (btor, sort, line->constant);
        break;

      case BTOR2_TAG_constraint:
        assert (line->nargs == 1);
        boolector_assert (btor, e[0]);
        break;

      case BTOR2_TAG_dec:
        assert (line->nargs == 1);
        node = boolector_dec (btor, e[0]);
        break;

      case BTOR2_TAG_eq:
        assert (line->nargs == 2);
        node = boolector_eq (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_iff:
        assert (line->nargs == 2);
        node = boolector_iff (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_implies:
        assert (line->nargs == 2);
        node = boolector_implies (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_inc:
        assert (line->nargs == 1);
        node = boolector_inc (btor, e[0]);
        break;

      case BTOR2_TAG_input:
        assert (line->nargs == 0);
        if (boolector_is_bitvec_sort (btor, sort))
          node = boolector_var (btor, sort, line->symbol);
        else
        {
          node = boolector_array (btor, sort, line->symbol);
          found_arrays = true;
        }
        boolector_set_btor_id (btor, node, line->id);
        break;

      case BTOR2_TAG_ite:
        assert (line->nargs == 3);
        node = boolector_cond (btor, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_mul:
        assert (line->nargs == 2);
        node = boolector_mul (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_nand:
        assert (line->nargs == 2);
        node = boolector_nand (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ne:
        assert (line->nargs == 2);
        node = boolector_ne (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_neg:
        assert (line->nargs == 1);
        node = boolector_neg (btor, e[0]);
        break;

      case BTOR2_TAG_nor:
        assert (line->nargs == 2);
        node = boolector_nor (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_not:
        assert (line->nargs == 1);
        node = boolector_not (btor, e[0]);
        break;

      case BTOR2_TAG_one:
        assert (line->nargs == 0);
        node = boolector_one (btor, sort);
        break;

      case BTOR2_TAG_ones:
        assert (line->nargs == 0);
        node = boolector_ones (btor, sort);
        break;

      case BTOR2_TAG_or:
        assert (line->nargs == 2);
        node = boolector_or (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_output: boolector_add_output (btor, e[0]); break;

      case BTOR2_TAG_read:
        assert (line->nargs == 2);
        node = boolector_read (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_redand:
        assert (line->nargs == 1);
        node = boolector_redand (btor, e[0]);
        break;

      case BTOR2_TAG_redor:
        assert (line->nargs == 1);
        node = boolector_redor (btor, e[0]);
        break;

      case BTOR2_TAG_redxor:
        assert (line->nargs == 1);
        node = boolector_redxor (btor, e[0]);
        break;

      case BTOR2_TAG_rol:
        assert (line->nargs == 2);
        node = boolector_rol (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ror:
        assert (line->nargs == 2);
        node = boolector_ror (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_saddo:
        assert (line->nargs == 2);
        node = boolector_saddo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sdiv:
        assert (line->nargs == 2);
        node = boolector_sdiv (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sdivo:
        assert (line->nargs == 2);
        node = boolector_sdivo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sext:
        assert (line->nargs == 1);
        node = boolector_sext (btor, e[0], line->args[1]);
        break;

      case BTOR2_TAG_sgt:
        assert (line->nargs == 2);
        node = boolector_sgt (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sgte:
        assert (line->nargs == 2);
        node = boolector_sgte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_slice:
        assert (line->nargs == 1);
        node = boolector_slice (btor, e[0], line->args[1], line->args[2]);
        break;

      case BTOR2_TAG_sll:
        assert (line->nargs == 2);
        node = boolector_sll (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_slt:
        assert (line->nargs == 2);
        node = boolector_slt (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_slte:
        assert (line->nargs == 2);
        node = boolector_slte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sort:
        if (line->sort.tag == BTOR2_TAG_SORT_bitvec)
        {
          assert (line->sort.bitvec.width);
          sort = boolector_bitvec_sort (btor, line->sort.bitvec.width);
        }
        else
        {
          assert (line->sort.tag == BTOR2_TAG_SORT_array);
          j = line->sort.array.index;
          assert (j);
          if (j > INT32_MAX)
          {
            perr_btor2 (
                parser, line->id, "given id '%" PRId64 "' exceeds INT32_MAX", j);
            goto DONE;
          }
          assert (btor_hashint_map_contains (sortmap, j));
          sort_index =
              (BoolectorSort) btor_hashint_map_get (sortmap, j)->as_ptr;
          assert (sort_index);
          j = line->sort.array.element;
          assert (j);
          if (j > INT32_MAX)
          {
            perr_btor2 (
                parser, line->id, "given id '%" PRId64 "' exceeds INT32_MAX", j);
            goto DONE;
          }
          assert (btor_hashint_map_contains (sortmap, j));
          sort_elem = (BoolectorSort) btor_hashint_map_get (sortmap, j)->as_ptr;
          assert (sort_elem);
          sort = boolector_array_sort (btor, sort_index, sort_elem);
        }
        assert (!btor_hashint_map_contains (sortmap, line->id));
        btor_hashint_map_add (sortmap, line->id)->as_ptr = sort;
        break;

      case BTOR2_TAG_smod:
        assert (line->nargs == 2);
        node = boolector_smod (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_smulo:
        assert (line->nargs == 2);
        node = boolector_smulo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sra:
        assert (line->nargs == 2);
        node = boolector_sra (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_srem:
        assert (line->nargs == 2);
        node = boolector_srem (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_srl:
        assert (line->nargs == 2);
        node = boolector_srl (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ssubo:
        assert (line->nargs == 2);
        node = boolector_ssubo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_sub:
        assert (line->nargs == 2);
        node = boolector_sub (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_uaddo:
        assert (line->nargs == 2);
        node = boolector_uaddo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_udiv:
        assert (line->nargs == 2);
        node = boolector_udiv (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_uext:
        assert (line->nargs == 1);
        node = boolector_uext (btor, e[0], line->args[1]);
        break;

      case BTOR2_TAG_ugt:
        assert (line->nargs == 2);
        node = boolector_ugt (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ugte:
        assert (line->nargs == 2);
        node = boolector_ugte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ult:
        assert (line->nargs == 2);
        node = boolector_ult (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_ulte:
        assert (line->nargs == 2);
        node = boolector_ulte (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_umulo:
        assert (line->nargs == 2);
        node = boolector_umulo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_urem:
        assert (line->nargs == 2);
        node = boolector_urem (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_usubo:
        assert (line->nargs == 2);
        node = boolector_usubo (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_write:
        assert (line->nargs == 3);
        node = boolector_write (btor, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_xnor:
        assert (line->nargs == 2);
        node = boolector_xnor (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_xor:
        assert (line->nargs == 2);
        node = boolector_xor (btor, e[0], e[1]);
        break;

      case BTOR2_TAG_zero:
        assert (line->nargs == 0);
        node = boolector_zero (btor, sort);
        break;

      default:
        assert (line->tag == BTOR2_TAG_bad
             || line->tag == BTOR2_TAG_fair
             || line->tag == BTOR2_TAG_init
             || line->tag == BTOR2_TAG_justice
             || line->tag == BTOR2_TAG_next
             || line->tag == BTOR2_TAG_state);
        perr_btor2 (parser,
                    line->id,
                    "model checking extensions not supported by boolector, try "
                    "btormc instead");
        goto DONE;
    }
    assert (!sort || !node || boolector_get_sort (btor, node) == sort);
    if (node)
    {
      assert (!btor_hashint_map_contains (nodemap, line->id));
      btor_hashint_map_add (nodemap, line->id)->as_ptr = node;
    }
  }
DONE:
  if (nodemap)
  {
    btor_iter_hashint_init (&it, nodemap);
    while (btor_iter_hashint_has_next (&it))
    {
      j    = it.cur_pos;
      node = btor_iter_hashint_next_data (&it)->as_ptr;
      boolector_release (btor, node);
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
  if (res)
  {
    if (found_arrays || found_lambdas)
      res->logic = BTOR_LOGIC_QF_AUFBV;
    else
      res->logic = BTOR_LOGIC_QF_BV;
    res->status = BOOLECTOR_UNKNOWN;
  }
  if (parser->error) return parser->error;
  return 0;
}

static BtorParserAPI parsebtor2_parser_api = {
    (BtorInitParser) new_btor2_parser,
    (BtorResetParser) delete_btor2_parser,
    (BtorParse) parse_btor2_parser,
};

const BtorParserAPI *
btor_parsebtor2_parser_api ()
{
  return &parsebtor2_parser_api;
}
