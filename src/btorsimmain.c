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

static void
msg (char *m, ...)
{
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
  int res  = 0;
  *res_ptr = res;
  return 1;
}

static int checking_mode = 0;
static int random_mode   = 0;

int
main (int argc, char **argv)
{
  int res = 0, r = -1, s = -1, print_trace = 1;
  for (int i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
      fputs (usage, stdout), exit (0);
    else if (!strcmp (argv[i], "-c"))
      print_trace = 0;
    else if (!strcmp (argv[i], "-r"))
    {
      if (++i == argc) die ("argument to '-r' missing");
      if ((r = atoi (argv[i])) < 1)
        die ("invalid argument '%s' to '-r'", argv[i]);
    }
    else if (!strcmp (argv[i], "-s"))
    {
      if (++i == argc) die ("argument to '-s' missing");
      if ((s = atoi (argv[i])) < 1)
        die ("invalid argument '%s' to '-s'", argv[i]);
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
      die ("failed to open btor model file '%s' for reading", model_path);
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
    msg ("checking mode: model and witness specified");
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
      msg (
          "random mode: "
          "model and '-r %s' specified, but no witness",
          r);
    }
    else
    {
      msg (
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
    msg ("random mode: no model nor witness specified");
    random_mode   = 1;
    checking_mode = 0;
  }
  if (s < 0) s = 0;
  msg ("random seed %d", s);
  if (model_path) msg ("reading BTOR model from '%s'", model_path);
  if (witness_path) msg ("reading BTOR witness from '%s'", witness_path);
  if (close_model_file && !fclose (model_file))
    die ("can not close model file '%s'", model_path);
  if (close_witness_file && !fclose (witness_file))
    die ("can not close witness file '%s'", witness_path);
  return res;
}
