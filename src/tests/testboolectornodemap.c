/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <assert.h>
#include "boolector.h"
#include "testrunner.h"
#include "utils/boolectornodemap.h"

static Btor *g_btor;

void
init_boolectornodemap_tests (void)
{
  assert (!g_btor);
}

void
finish_boolectornodemap_tests (void)
{
  assert (!g_btor);
}

/*------------------------------------------------------------------------*/

static void
init_boolectornodemap_test (void)
{
  assert (!g_btor);
  g_btor = boolector_new ();
  assert (g_btor);
}

static void
finish_boolectornodemap_test (void)
{
  assert (g_btor);
  boolector_delete (g_btor);
  g_btor = 0;
}

/*------------------------------------------------------------------------*/

void
test_boolectornodemap0 ()
{
  init_boolectornodemap_test ();

  BoolectorSort sort = boolector_bitvec_sort (g_btor, 32);
  BoolectorNode *a   = boolector_var (g_btor, sort, "a");
  BoolectorNode *b   = boolector_var (g_btor, sort, "b");
  BoolectorNode *s   = boolector_sub (g_btor, a, b);
  BoolectorNode *o   = boolector_one (g_btor, sort);
  BoolectorNode *t   = boolector_unsigned_int (g_btor, 2, sort);

  BoolectorNodeMap *map = boolector_nodemap_new (g_btor);
  BoolectorNode *d;
  boolector_nodemap_map (map, a, t);
  boolector_nodemap_map (map, b, o);
  d = boolector_nodemap_substitute_node (g_btor, map, s);
  (void) d;
  assert (d == o);
  boolector_nodemap_delete (map);

  boolector_release (g_btor, a);
  boolector_release (g_btor, b);
  boolector_release (g_btor, o);
  boolector_release (g_btor, s);
  boolector_release (g_btor, t);
  boolector_release_sort (g_btor, sort);

  finish_boolectornodemap_test ();
}

/*------------------------------------------------------------------------*/

static BoolectorNode *
test_boolectornodemap1_mapper (Btor *btor, void *state, BoolectorNode *node)
{
  const char *symbol;
  (void) state;
  assert (btor == g_btor);
  if (!boolector_is_var (btor, node)) return 0;
  symbol = boolector_get_symbol (btor, node);
  assert (symbol);
  return boolector_int (btor, atoi (symbol), boolector_get_sort (btor, node));
}

void
test_boolectornodemap1 ()
{
  init_boolectornodemap_test ();

  BoolectorSort sort = boolector_bitvec_sort (g_btor, 8);
  BoolectorNode *a   = boolector_var (g_btor, sort, "11");
  BoolectorNode *b   = boolector_var (g_btor, sort, "22");
  BoolectorNode *c   = boolector_var (g_btor, sort, "33");
  BoolectorNode *s;

  BoolectorNode *sum = boolector_add (g_btor, a, b);
  s                  = boolector_add (g_btor, sum, c);
  boolector_release (g_btor, sum);

  BoolectorNodeMap *map = boolector_nodemap_new (g_btor);
  BoolectorNode *d, *g;
  d = boolector_nodemap_extended_substitute_node (
      g_btor, map, 0, test_boolectornodemap1_mapper, boolector_release, s);
  (void) d;
  g = boolector_int (g_btor, 66, sort);
  assert (d == g);
  boolector_release (g_btor, g);
  boolector_nodemap_delete (map);

  boolector_release (g_btor, a);
  boolector_release (g_btor, b);
  boolector_release (g_btor, c);
  boolector_release (g_btor, s);
  boolector_release_sort (g_btor, sort);

  finish_boolectornodemap_test ();
}

/*------------------------------------------------------------------------*/

void
run_boolectornodemap_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (boolectornodemap0);
  BTOR_RUN_TEST (boolectornodemap1);
}
