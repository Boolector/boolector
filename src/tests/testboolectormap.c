/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <assert.h>
#include "boolector.h"
#include "testrunner.h"
#include "utils/boolectormap.h"

static Btor *g_btor;

void
init_boolectormap_tests (void)
{
  assert (!g_btor);
}

void
finish_boolectormap_tests (void)
{
  assert (!g_btor);
}

/*------------------------------------------------------------------------*/

static void
init_boolectormap_test (void)
{
  assert (!g_btor);
  g_btor = boolector_new ();
  assert (g_btor);
}

static void
finish_boolectormap_test (void)
{
  assert (g_btor);
  boolector_delete (g_btor);
  g_btor = 0;
}

/*------------------------------------------------------------------------*/

void
test_boolectormap0 ()
{
  init_boolectormap_test ();

  BoolectorSort sort = boolector_bitvec_sort (g_btor, 32);
  BoolectorNode *a   = boolector_var (g_btor, sort, "a");
  BoolectorNode *b   = boolector_var (g_btor, sort, "b");
  BoolectorNode *s   = boolector_sub (g_btor, a, b);
  BoolectorNode *o   = boolector_one (g_btor, sort);
  BoolectorNode *t   = boolector_unsigned_int (g_btor, 2, sort);

  BoolectorNodeMap *map = boolector_new_node_map (g_btor);
  BoolectorNode *d;
  boolector_map_node (map, a, t);
  boolector_map_node (map, b, o);
  d = boolector_non_recursive_substitute_node (g_btor, map, s);
  (void) d;
  assert (d == o);
  boolector_delete_node_map (map);

  boolector_release (g_btor, a);
  boolector_release (g_btor, b);
  boolector_release (g_btor, o);
  boolector_release (g_btor, s);
  boolector_release (g_btor, t);
  boolector_release_sort (g_btor, sort);

  finish_boolectormap_test ();
}

/*------------------------------------------------------------------------*/

static BoolectorNode *
test_boolectormap1_mapper (Btor *btor, void *state, BoolectorNode *node)
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
test_boolectormap1 ()
{
  init_boolectormap_test ();

  BoolectorSort sort = boolector_bitvec_sort (g_btor, 8);
  BoolectorNode *a   = boolector_var (g_btor, sort, "11");
  BoolectorNode *b   = boolector_var (g_btor, sort, "22");
  BoolectorNode *c   = boolector_var (g_btor, sort, "33");
  BoolectorNode *s;

  BoolectorNode *sum = boolector_add (g_btor, a, b);
  s                  = boolector_add (g_btor, sum, c);
  boolector_release (g_btor, sum);

  BoolectorNodeMap *map = boolector_new_node_map (g_btor);
  BoolectorNode *d, *g;
  d = boolector_non_recursive_extended_substitute_node (
      g_btor, map, 0, test_boolectormap1_mapper, boolector_release, s);
  g = boolector_int (g_btor, 66, sort);
  assert (d == g);
  boolector_release (g_btor, g);
  boolector_delete_node_map (map);

  boolector_release (g_btor, a);
  boolector_release (g_btor, b);
  boolector_release (g_btor, c);
  boolector_release (g_btor, s);
  boolector_release_sort (g_btor, sort);

  finish_boolectormap_test ();
}

/*------------------------------------------------------------------------*/

void
run_boolectormap_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (boolectormap0);
  BTOR_RUN_TEST (boolectormap1);
}
