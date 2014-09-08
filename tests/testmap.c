
/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmap.h"
#include "btorexp.h"
#include "btormap.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static Btor *g_btor;

void
init_map_tests (void)
{
  assert (!g_btor);
}

void
finish_map_tests (void)
{
  assert (!g_btor);
}

/*------------------------------------------------------------------------*/

static void
init_map_test (void)
{
  assert (!g_btor);
  g_btor = btor_new_btor ();
  assert (g_btor);
}

static void
finish_map_test (void)
{
  assert (g_btor);
  btor_delete_btor (g_btor);
  g_btor = 0;
}

/*------------------------------------------------------------------------*/

void
test_mapnewdel ()
{
  BtorNodeMap *map;
  init_map_test ();
  map = btor_new_node_map (g_btor);
  btor_delete_node_map (map);
  finish_map_test ();
}

/*------------------------------------------------------------------------*/

void
test_map0 ()
{
  init_map_test ();

  BtorNode *a = btor_var_exp (g_btor, 32, "a");
  BtorNode *b = btor_var_exp (g_btor, 32, "b");
  BtorNode *s = btor_sub_exp (g_btor, a, b);
  BtorNode *o = btor_one_exp (g_btor, 32);
  BtorNode *t = btor_unsigned_exp (g_btor, 2, 32);

  BtorNodeMap *map = btor_new_node_map (g_btor);
  BtorNode *d;
  btor_map_node (map, a, t);
  btor_map_node (map, b, o);
  d = btor_non_recursive_substitute_node (g_btor, map, s);
  assert (d == o);
  btor_delete_node_map (map);
  // btor_release_exp (g_btor, d); // No, map owns reference!!!!!!

  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, b);
  btor_release_exp (g_btor, o);
  btor_release_exp (g_btor, s);
  btor_release_exp (g_btor, t);

  finish_map_test ();
}

/*------------------------------------------------------------------------*/

static BtorNode *
test_map1_mapper (Btor *btor, void *state, BtorNode *node)
{
  char *symbol;
  (void) state;
  assert (btor == g_btor);
  assert (BTOR_IS_REGULAR_NODE (node));
  if (!BTOR_IS_BV_VAR_NODE (node)) return 0;
  symbol = btor_get_symbol_exp (btor, node);
  assert (symbol);
  return btor_int_exp (btor, atoi (symbol), 8);
}

void
test_map1 ()
{
  init_map_test ();

  BtorNode *a = btor_var_exp (g_btor, 8, "11");
  BtorNode *b = btor_var_exp (g_btor, 8, "22");
  BtorNode *c = btor_var_exp (g_btor, 8, "33");
  BtorNode *s;

  BtorNode *sum = btor_add_exp (g_btor, a, b);
  s             = btor_add_exp (g_btor, sum, c);
  btor_release_exp (g_btor, sum);

  BtorNodeMap *map = btor_new_node_map (g_btor);
  BtorNode *d, *g;
  d = btor_non_recursive_extended_substitute_node (
      g_btor, map, 0, test_map1_mapper, btor_release_exp, s);
  g = btor_int_exp (g_btor, 66, 8);
  assert (d == g);
  btor_release_exp (g_btor, g);
  btor_delete_node_map (map);

  btor_release_exp (g_btor, a);
  btor_release_exp (g_btor, b);
  btor_release_exp (g_btor, c);
  btor_release_exp (g_btor, s);

  finish_map_test ();
}

void
test_map2 ()
{
  Btor *stor       = btor_new_btor ();
  Btor *dtor       = btor_new_btor ();
  Btor *mtor       = btor_new_btor ();
  BtorNode *s      = btor_var_exp (stor, 32, "s");
  BtorNode *d      = btor_var_exp (dtor, 32, "d");
  BtorNodeMap *map = btor_new_node_map (mtor);
  BtorNode *m;
  btor_map_node (map, s, d);
  m = btor_mapped_node (map, s);
  assert (m == d);
  btor_release_exp (stor, s);
  btor_release_exp (dtor, d);
  btor_delete_node_map (map);
  btor_delete_btor (stor);
  btor_delete_btor (dtor);
  btor_delete_btor (mtor);
}

void
test_map3 ()
{
  Btor *stor       = btor_new_btor ();
  Btor *dtor       = btor_new_btor ();
  Btor *mtor       = btor_new_btor ();
  BtorNode *s      = btor_var_exp (stor, 32, "0");
  BtorNode *t      = btor_var_exp (stor, 32, "1");
  BtorNode *a      = btor_and_exp (stor, s, t);
  BtorNodeMap *map = btor_new_node_map (mtor);
  // BtorNode * m;
  // m = btor_mapped_node (map, s);
  btor_release_exp (stor, t);
  btor_release_exp (stor, s);
  btor_release_exp (stor, a);
  btor_delete_node_map (map);
  btor_delete_btor (stor);
  btor_delete_btor (dtor);
  btor_delete_btor (mtor);
}

/*------------------------------------------------------------------------*/

void
run_map_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (mapnewdel);
  BTOR_RUN_TEST (map0);
  BTOR_RUN_TEST (map1);
  BTOR_RUN_TEST (map2);
  BTOR_RUN_TEST (map3);
}
