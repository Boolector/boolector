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

static const char *
btor_parse_aux (Btor *btor,
                FILE *file,
                const char *file_name,
                BtorParserAPI *parser_api,
                BtorParseResult *parse_res,
                char *msg)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (parser_api);
  assert (parse_res);

  BtorParser *parser;
  BtorParseOpt parse_opt;

  parse_opt.verbosity   = boolector_get_opt (btor, "verbosity")->val;
  parse_opt.incremental = boolector_get_opt (btor, "incremental")->val;
  if (boolector_get_opt (btor, "incremental_in_depth")->val)
  {
    parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_IN_DEPTH;
    parse_opt.window = boolector_get_opt (btor, "incremental_in_depth")->val;
  }
  else if (boolector_get_opt (btor, "incremental_look_ahead")->val)
  {
    parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_LOOK_AHEAD;
    parse_opt.window = boolector_get_opt (btor, "incremental_look_ahead")->val;
  }
  else if (boolector_get_opt (btor, "incremental_look_ahead")->val)
  {
    parse_opt.incremental |= BTOR_PARSE_MODE_INCREMENTAL_INTERVAL;
    parse_opt.window = boolector_get_opt (btor, "incremental_interval")->val;
  }
  parse_opt.need_model = boolector_get_opt (btor, "model_gen")->val;

  btor_msg_parse ("%s", msg);
  parser = parser_api->init (btor, &parse_opt);
  return parser_api->parse (parser, 0, file, file_name, parse_res);
}

const char *
btor_parse (Btor *btor,
            FILE *file,
            const char *file_name,
            BtorParseResult *parse_res)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (parse_res);

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
    for (;;)
    {
      msg = "assuming BTOR input";
      ch  = getc (file);
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
  }
  return btor_parse_aux (btor, file, file_name, parser_api, parse_res, msg);
}

const char *
btor_parse_btor (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 BtorParseResult *parse_res)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (parse_res);

  const BtorParserAPI *parser_api;
  parser_api = btor_btor_parser_api ();
  return btor_parse_aux (btor, file, file_name, parser_api, parse_res, 0);
}

const char *
btor_parse_smt1 (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 BtorParseResult *parse_res)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (parse_res);

  const BtorParserAPI *parser_api;
  parser_api = btor_smt_parser_api ();
  return btor_parse_aux (btor, file, file_name, parser_api, parse_res, 0);
}

const char *
btor_parse_smt2 (Btor *btor,
                 FILE *file,
                 const char *file_name,
                 BtorParseResult *parse_res)
{
  assert (btor);
  assert (file);
  assert (file_name);
  assert (parse_res);

  const BtorParserAPI *parser_api;
  parser_api = btor_smt2_parser_api ();
  return btor_parse_aux (btor, file, file_name, parser_api, parse_res, 0);
}
