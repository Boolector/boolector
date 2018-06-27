/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include "testsmtaxioms.h"
#include "boolector.h"
#include "testrunner.h"
#include "utils/btorstack.h"

#include <assert.h>
#include <stdio.h>

#define BTOR_TEST_SMTAXIOM_TEMP_OUTFILE_NAME "smtaxiomout.tmp"

static Btor *g_btor;
static BtorMemMgr *g_mm;
static FILE *g_fout = NULL;

static char *axioms[] = {
    "bvashr",
    "bvnand",
    "bvnor",
    "bvsge",
    "bvsgt",
    "bvsle",
    "bvslt",
    "bvuge",
    "bvugt",
    "bvule",
    "bvxnor",
    "bvxor",
    "bvsub",
    0, /* below are the 'hard' test cases (no 16, 32, 64 bits) */
    "bvsmod",
    "bvsdiv",
    "bvsrem",
    0};

static void
test_g_args_unsat (void)
{
  assert (boolector_sat (g_btor) == BOOLECTOR_UNSAT);
}

static void
test_smtaxiom (int32_t argc, char **argv, char *p, int32_t i)
{
  FILE *fin;
  char *buffer, *name, *prefix = "smtaxiom";
  int32_t parse_res, parse_status;
  char *parse_err;
  size_t len_name, len_buffer;

  g_btor = boolector_new ();
  if (g_rwreads) boolector_set_opt (g_btor, BTOR_OPT_BETA_REDUCE_ALL, 1);

  len_name = strlen (prefix) + strlen (p) + 10 + 1;
  BTOR_NEWN (g_mm, name, len_name);
  sprintf (name, "smtaxiom%s%d", p, i);

  len_buffer = strlen (btor_log_dir) + strlen (name) + 4 + 1;
  BTOR_NEWN (g_mm, buffer, len_buffer);
  sprintf (buffer, "%s%s.smt", btor_log_dir, name);

  fin = fopen (buffer, "r");
  assert (fin != NULL);
  g_fout = fopen (BTOR_TEST_SMTAXIOM_TEMP_OUTFILE_NAME, "w");
  assert (g_fout != NULL);
  parse_res =
      boolector_parse (g_btor, fin, buffer, g_fout, &parse_err, &parse_status);
  assert (parse_res != BOOLECTOR_PARSE_ERROR);

  run_test_case (argc, argv, test_g_args_unsat, name, 0);

  fclose (fin);
  fclose (g_fout);
  BTOR_DELETEN (g_mm, name, len_name);
  BTOR_DELETEN (g_mm, buffer, len_buffer);
  boolector_delete (g_btor);
}

void
init_smtaxioms_tests (void)
{
  g_mm = btor_mem_mgr_new ();
}

void
run_smtaxioms_tests (int32_t argc, char **argv)
{
  BtorMemMgr *mem;
  int32_t i, first;
  char **p;

  mem = btor_mem_mgr_new ();

  for (first = 1, p = axioms; first || *p; p++)
  {
    if (!*p)
    {
      first = 0;
      p++;
    }

    for (i = 1; i <= 8; i++) test_smtaxiom (argc, argv, *p, i);

    if (first)
    {
      test_smtaxiom (argc, argv, *p, 16);
      test_smtaxiom (argc, argv, *p, 32);
      test_smtaxiom (argc, argv, *p, 64);
    }
  }

  btor_mem_mgr_delete (mem);
}

void
finish_smtaxioms_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}
