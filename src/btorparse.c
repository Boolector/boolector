/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2016 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorparse.h"
#include "boolector.h"
#include "btorcore.h"
#include "btoropt.h"
#include "parser/btorbtor.h"
#include "parser/btorsmt.h"
#include "parser/btorsmt2.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

static int
has_compressed_suffix (const char *str, const char *suffix)
{
  int l = strlen (str), k = strlen (suffix), d = l - k;
  if (d < 0) return 0;
  if (!strcmp (str + d, suffix)) return 1;
  if (d - 3 >= 0 && !strcmp (str + l - 3, ".gz") && !strcmp (str + l - 3, ".7z")
      && !strncmp (str + d - 3, suffix, k))
    return 1;
  return 0;
}

/* return BOOLECTOR_(SAT|UNSAT|UNKNOWN|PARSE_ERROR) */
static int
parse_aux (Btor *btor,
           FILE *infile,
           BtorCharStack *prefix,
           const char *infile_name,
           FILE *outfile,
           const BtorParserAPI *parser_api,
           char **error_msg,
           int *status,
           char *msg)
{
  assert (btor);
  assert (infile);
  assert (infile_name);
  assert (outfile);
  assert (parser_api);
  assert (error_msg);
  assert (status);

  BtorParser *parser;
  BtorParseOpt parse_opt;
  BtorParseResult parse_res;
  BoolectorNode *root;
  int i, root_len, res;
  char *emsg;

  res                        = BOOLECTOR_UNKNOWN;
  *error_msg                 = 0;
  parse_opt.verbosity        = btor_opt_get (btor, BTOR_OPT_VERBOSITY);
  parse_opt.incremental      = btor_opt_get (btor, BTOR_OPT_INCREMENTAL);
  parse_opt.incremental_smt1 = btor_opt_get (btor, BTOR_OPT_INCREMENTAL_SMT1);
  parse_opt.interactive      = btor_opt_get (btor, BTOR_OPT_PARSE_INTERACTIVE);
  parse_opt.need_model       = btor_opt_get (btor, BTOR_OPT_MODEL_GEN);

  BTOR_MSG (btor->msg, 1, "%s", msg);
  parser = parser_api->init (btor, &parse_opt);

  if ((emsg = parser_api->parse (
           parser, prefix, infile, infile_name, outfile, &parse_res)))
  {
    res                   = BOOLECTOR_PARSE_ERROR;
    btor->parse_error_msg = btor_mem_strdup (btor->mm, emsg);
    *error_msg            = btor->parse_error_msg;
  }
  else
  {
    res = parse_res.nsatcalls ? parse_res.result : BOOLECTOR_PARSE_UNKNOWN;

    if (!parse_opt.incremental)
    {
      // FIXME this is only used for non-incremental smt1 and btor
      // maybe move root handling into respective parsers??
      /* assert root(s) if not incremental
       * Note: we have to do this via API calls for API tracing!!! */
      for (i = 0; i < parse_res.noutputs; i++)
      {
        root     = parse_res.outputs[i];
        root_len = boolector_get_width (btor, root);
        assert (root_len >= 1);
        if (root_len > 1)
          root = boolector_redor (btor, root);
        else
          root = boolector_copy (btor, root);
        boolector_assert (btor, root);
        boolector_release (btor, root);
      }
    }

    BTOR_MSG (btor->msg,
              1,
              "parsed %d inputs and %d outputs",
              parse_res.ninputs,
              parse_res.noutputs);
    if (parse_res.logic == BTOR_LOGIC_QF_BV)
      BTOR_MSG (btor->msg, 1, "logic QF_BV");
    else
    {
      assert (parse_res.logic == BTOR_LOGIC_QF_AUFBV);
      BTOR_MSG (btor->msg, 1, "logic QF_AUFBV");
    }

    if (parse_res.status == BOOLECTOR_SAT)
      BTOR_MSG (btor->msg, 1, "status sat");
    else if (parse_res.status == BOOLECTOR_UNSAT)
      BTOR_MSG (btor->msg, 1, "status unsat");
    else
    {
      assert (parse_res.status == BOOLECTOR_UNKNOWN);
      BTOR_MSG (btor->msg, 1, "status unknown");
    }

    BTOR_MSG (btor->msg, 2, "added %d outputs (100%)", parse_res.noutputs);
  }

  if (status) *status = parse_res.status;

  /* cleanup */
  parser_api->reset (parser);

  return res;
}

int
btor_parse (Btor *btor,
            FILE *infile,
            const char *infile_name,
            FILE *outfile,
            char **error_msg,
            int *status)
{
  assert (btor);
  assert (infile);
  assert (infile_name);
  assert (outfile);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  int first, second, res, len;
  char ch, *msg;
  BtorCharStack prefix;
  BtorMemMgr *mem;

  len = 40 + strlen (infile_name);
  BTOR_NEWN (btor->mm, msg, len);
  mem = btor_mem_mgr_new ();
  BTOR_INIT_STACK (mem, prefix);

  if (has_compressed_suffix (infile_name, ".btor"))
  {
    parser_api = btor_btor_parser_api ();
    sprintf (msg, "parsing '%s'", infile_name);
  }
  else if (has_compressed_suffix (infile_name, ".smt2"))
  {
    parser_api = btor_smt2_parser_api ();
    sprintf (msg, "parsing '%s'", infile_name);
  }
  else
  {
    first = second = 0;
    parser_api     = btor_btor_parser_api ();
    sprintf (msg, "assuming BTOR input, parsing '%s'", infile_name);
    for (;;)
    {
      ch = getc (infile);
      BTOR_PUSH_STACK (prefix, ch);
      if (!ch || ch == EOF) break;
      if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')
      {
        BTOR_PUSH_STACK (prefix, ch);
      }
      else if (ch == ';')
      {
        BTOR_PUSH_STACK (prefix, ';');
        do
        {
          ch = getc (infile);
          if (ch == EOF) break;
          BTOR_PUSH_STACK (prefix, ch);
        } while (ch != '\n');
        if (ch == EOF) break;
      }
      else if (!first)
        first = ch;
      else
      {
        second = ch;
        break;
      }
    }

    if (ch != EOF && ch)
    {
      assert (first && second);
      if (first == '(')
      {
        if (second == 'b')
        {
          parser_api = btor_smt_parser_api ();
          sprintf (
              msg, "assuming SMT-LIB v1 input,  parsing '%s'", infile_name);
        }
        else
        {
          parser_api = btor_smt2_parser_api ();
          sprintf (
              msg, "assuming SMT-LIB v2 input,  parsing '%s'", infile_name);
        }
      }
    }
  }

  res = parse_aux (btor,
                   infile,
                   &prefix,
                   infile_name,
                   outfile,
                   parser_api,
                   error_msg,
                   status,
                   msg);

  /* cleanup */
  BTOR_RELEASE_STACK (prefix);
  btor_mem_mgr_delete (mem);
  BTOR_DELETEN (btor->mm, msg, len);

  return res;
}

int
btor_parse_btor (Btor *btor,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 char **error_msg,
                 int *status)
{
  assert (btor);
  assert (infile);
  assert (infile_name);
  assert (outfile);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  parser_api = btor_btor_parser_api ();
  return parse_aux (
      btor, infile, 0, infile_name, outfile, parser_api, error_msg, status, 0);
}

int
btor_parse_smt1 (Btor *btor,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 char **error_msg,
                 int *status)
{
  assert (btor);
  assert (infile);
  assert (infile_name);
  assert (outfile);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  parser_api = btor_smt_parser_api ();
  return parse_aux (
      btor, infile, 0, infile_name, outfile, parser_api, error_msg, status, 0);
}

int
btor_parse_smt2 (Btor *btor,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 char **error_msg,
                 int *status)
{
  assert (btor);
  assert (infile);
  assert (infile_name);
  assert (outfile);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  parser_api = btor_smt2_parser_api ();
  return parse_aux (
      btor, infile, 0, infile_name, outfile, parser_api, error_msg, status, 0);
}
