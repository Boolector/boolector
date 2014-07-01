/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#include "btoraig.h"
#include "btoraigvec.h"
#include "btorhash.h"
#include "parser/btorbtor.h"
#include "stdio.h"

#include <stdio.h>
#include <string.h>

#define BTOR_HAVE_ISATTY

#ifdef BTOR_HAVE_ISATTY
#include <unistd.h>
#endif

static void
die (int prefix, const char *fmt, ...)
{
  va_list ap;
  if (prefix) fputs ("*** synthebtor: ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  exit (1);
}

int
main (int argc, char **argv)
{
  int i, j, verbosity, close_input, close_output, binary, merge, rwl;
  FILE *input_file, *output_file, *file;
  BtorAIG *aig, *tmp, *merged, **p;
  BtorPtrHashTable *back_annotation;
  const char *input_name;
  const char *parse_error;
  BtorPtrHashBucket *b;
  BtorParseResult model;
  BtorAIGVecMgr *avmgr;
  BtorAIGPtrStack regs;
  BtorAIGPtrStack nexts;
  BtorAIGPtrStack aigs;
  BtorParseOpt parse_opt;
  BtorParser *parser;
  BtorAIGMgr *amgr;
  BtorMemMgr *mem;
  BtorAIGVec *av;
  Btor *btor;
  BtorNode **outputs;

  verbosity    = 0;
  close_input  = 0;
  close_output = 0;
  binary       = 0;
  merge        = 0;
  input_name   = "<stdin>";
  input_file   = stdin;
  output_file  = stdout;
  rwl          = 3;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("usage: synthebor [-h][-v][-m][-rwl[0123]][<input>[<output>]]\n");
      exit (0);
    }
    else if (!strcmp (argv[i], "-v"))
      verbosity++;
    else if (!strcmp (argv[i], "-m"))
      merge = 1;
    else if (!strcmp (argv[i], "-rwl0"))
      rwl = 0;
    else if (!strcmp (argv[i], "-rwl1"))
      rwl = 1;
    else if (!strcmp (argv[i], "-rwl2"))
      rwl = 2;
    else if (!strcmp (argv[i], "-rwl3"))
      rwl = 3;
    else if (argv[i][0] == '-')
      die (1, "invalid command line option '%s'", argv[i]);
    else if (close_output)
      die (1, "too many files");
    else if (close_input)
    {
      if (!strcmp (argv[i], input_name))
        die (1, "input and output are the same");

      if (!(file = fopen (argv[i], "w")))
        die (1, "can not write '%s'", argv[i]);

      output_file  = file;
      close_output = 1;
    }
    else if (!(file = fopen (argv[i], "r")))
      die (1, "can not read '%s'", argv[i]);
    else
    {
      input_file  = file;
      input_name  = argv[i];
      close_input = 1;
    }
  }

  btor = btor_new_btor ();

  btor_set_opt_verbosity (btor, verbosity);
  btor_set_opt_rewrite_level (btor, rwl);

  BTOR_CLR (&parse_opt);

  parser = btor_btor_parser_api ()->init (btor, &parse_opt);

  parse_error = btor_btor_parser_api ()->parse (
      parser, 0, input_file, input_name, &model);
  if (parse_error) die (0, parse_error);

  if (!model.noutputs) die (1, "no roots in '%s'", input_name);

  mem   = btor->mm;
  avmgr = btor->avmgr;
  amgr  = btor_get_aig_mgr_aigvec_mgr (avmgr);

  back_annotation = btor_new_ptr_hash_table (mem, 0, 0);

  BTOR_INIT_STACK (regs);
  BTOR_INIT_STACK (nexts);

  BTOR_INIT_STACK (aigs);
  merged = BTOR_AIG_TRUE;

  // FIXME synthebtor should use api calls and BoolectorNodes only!!!
  outputs = (BtorNode **) model.outputs;
  //

  for (i = 0; i < model.noutputs; i++)
  {
    av = btor_exp_to_aigvec (btor, outputs[i], back_annotation);
    for (j = 0; j < av->len; j++)
    {
      aig = av->aigs[j];

      if (merge)
      {
        tmp = btor_and_aig (amgr, merged, aig);
        btor_release_aig (amgr, merged);
        merged = tmp;
      }
      else
      {
        aig = btor_copy_aig (amgr, aig);
        BTOR_PUSH_STACK (mem, aigs, aig);
      }
    }
    btor_release_delete_aigvec (avmgr, av);
  }

  if (merge) BTOR_PUSH_STACK (mem, aigs, merged);

#ifdef BTOR_HAVE_ISATTY
  if (close_output || !isatty (1)) binary = 1;
#endif
  assert (BTOR_COUNT_STACK (regs) == BTOR_COUNT_STACK (nexts));
  btor_dump_aiger (amgr,
                   binary,
                   output_file,
                   BTOR_COUNT_STACK (aigs),
                   aigs.start,
                   BTOR_COUNT_STACK (regs),
                   regs.start,
                   nexts.start,
                   back_annotation);

  for (p = aigs.start; p < aigs.top; p++) btor_release_aig (amgr, *p);
  BTOR_RELEASE_STACK (mem, aigs);

  for (p = regs.start; p < regs.top; p++) btor_release_aig (amgr, *p);
  BTOR_RELEASE_STACK (mem, regs);

  for (p = nexts.start; p < nexts.top; p++) btor_release_aig (amgr, *p);
  BTOR_RELEASE_STACK (mem, nexts);

  for (b = back_annotation->first; b; b = b->next)
    btor_freestr (mem, b->data.asStr);

  btor_delete_ptr_hash_table (back_annotation);

  btor_btor_parser_api ()->reset (parser);
  btor_delete_btor (btor);

  if (close_input) fclose (input_file);

  if (close_output) fclose (output_file);

  return 0;
}
