/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorparse.h"
#include "boolector.h"
#include "btorcore.h"
#include "btormem.h"
#include "btoropt.h"
#include "btorstack.h"
#include "parser/btorbtor.h"
#include "parser/btorsmt.h"
#include "parser/btorsmt2.h"

static void
btor_msg_parse (char *fmt, ...)
{
  va_list ap;
  fprintf (stdout, "[btorparse] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

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
btor_parse_aux (Btor *btor,
                FILE *file,
                const char *file_name,
                const BtorParserAPI *parser_api,
                char **error_msg,
                int *status,
                char *msg)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (parser_api);
  assert (error_msg);
  assert (status);

  BtorParser *parser;
  BtorParseOpt parse_opt;
  BtorParseResult parse_res;
  BoolectorNode *root;
  int i, root_len, res;
  char *emsg;

  res                   = BOOLECTOR_UNKNOWN;
  parse_opt.verbosity   = btor_get_opt (btor, "verbosity")->val;
  parse_opt.incremental = btor_get_opt (btor, "incremental")->val;
  if (btor_get_opt (btor, "incremental_in_depth")->val)
  {
    parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_IN_DEPTH;
    parse_opt.window = btor_get_opt (btor, "incremental_in_depth")->val;
  }
  else if (btor_get_opt (btor, "incremental_look_ahead")->val)
  {
    parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_LOOK_AHEAD;
    parse_opt.window = btor_get_opt (btor, "incremental_look_ahead")->val;
  }
  else if (btor_get_opt (btor, "incremental_look_ahead")->val)
  {
    parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_INTERVAL;
    parse_opt.window = btor_get_opt (btor, "incremental_interval")->val;
  }
  parse_opt.need_model = btor_get_opt (btor, "model_gen")->val;

  if (parse_opt.verbosity) btor_msg_parse ("%s", msg);
  parser = parser_api->init (btor, &parse_opt);

  if ((emsg = parser_api->parse (parser, 0, file, file_name, &parse_res)))
  {
    res                   = BOOLECTOR_PARSE_ERROR;
    btor->parse_error_msg = btor_strdup (btor->mm, emsg);
    *error_msg            = btor->parse_error_msg;
  }
  else
  {
    res = parse_res.result;

    /* assert root(s)
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

    if (parse_opt.verbosity)
    {
      btor_msg_parse ("parsed %d inputs and %d outputs",
                      parse_res.ninputs,
                      parse_res.noutputs);

      if (parse_res.logic == BTOR_LOGIC_QF_BV)
        btor_msg_parse ("logic QF_BV");
      else
      {
        assert (parse_res.logic == BTOR_LOGIC_QF_AUFBV);
        btor_msg_parse ("logic QF_AUFBV");
      }

      if (parse_res.status == BOOLECTOR_SAT)
        btor_msg_parse ("status sat");
      else if (parse_res.status == BOOLECTOR_UNSAT)
        btor_msg_parse ("status unsat");
      else
      {
        assert (parse_res.status == BOOLECTOR_UNKNOWN);
        btor_msg_parse ("status unknown");
      }
    }

    if (parse_opt.verbosity > 1)
      btor_msg_parse ("added %d outputs (100%)", parse_res.noutputs);
  }

  if (status) *status = parse_res.status;

  /* cleanup */
  parser_api->reset (parser);

  return res;
}

int
btor_parse (Btor *btor,
            FILE *file,
            const char *file_name,
            char **error_msg,
            int *status)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  int first, second;
  char ch, *msg;
  BtorCharStack prefix;
  BtorMemMgr *mem;

  msg = "";
  mem = btor_new_mem_mgr ();

  if (has_compressed_suffix (file_name, ".btor"))
    parser_api = btor_btor_parser_api ();
  else if (has_compressed_suffix (file_name, ".smt2"))
    parser_api = btor_smt2_parser_api ();
  else
  {
    first = second = 0;
    BTOR_INIT_STACK (prefix);
    parser_api = btor_btor_parser_api ();
    msg        = "assuming BTOR input";
    for (;;)
    {
      ch = getc (file);
      BTOR_PUSH_STACK (mem, prefix, ch);
      if (!ch || ch == EOF) break;
      if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')
      {
        BTOR_PUSH_STACK (mem, prefix, ch);
      }
      else if (ch == ';')
      {
        BTOR_PUSH_STACK (mem, prefix, ';');
        do
        {
          ch = getc (file);
          if (ch == EOF) break;
          BTOR_PUSH_STACK (mem, prefix, ch);
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
          msg        = "assuming SMT-LIB v1 input";
        }
        else
        {
          parser_api = btor_smt2_parser_api ();
          msg        = "assuming SMT-LIB v2 input";
        }
      }
    }
    BTOR_RELEASE_STACK (mem, prefix);
    rewind (file);
  }

  return btor_parse_aux (
      btor, file, file_name, parser_api, error_msg, status, msg);
}

int
btor_parse_btor (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 char **error_msg,
                 int *status)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  parser_api = btor_btor_parser_api ();
  return btor_parse_aux (
      btor, file, file_name, parser_api, error_msg, status, 0);
}

int
btor_parse_smt1 (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 char **error_msg,
                 int *status)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  parser_api = btor_smt_parser_api ();
  return btor_parse_aux (
      btor, file, file_name, parser_api, error_msg, status, 0);
}

int
btor_parse_smt2 (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 char **error_msg,
                 int *status)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (error_msg);
  assert (status);

  const BtorParserAPI *parser_api;
  parser_api = btor_smt2_parser_api ();
  return btor_parse_aux (
      btor, file, file_name, parser_api, error_msg, status, 0);
}
