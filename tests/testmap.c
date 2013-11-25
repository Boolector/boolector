
/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013 Aina Niemetz.
 *
 *  All rights reserved.
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testmap.h"
#include "boolector.h"
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
  g_btor = boolector_new ();
  assert (g_btor);
}

static void
finish_map_test (void)
{
  assert (g_btor);
  boolector_delete (g_btor);
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
  {
    BtorNode *a = boolector_var (g_btor, 32, "a");
    BtorNode *b = boolector_var (g_btor, 32, "b");
    BtorNode *s = boolector_sub (g_btor, a, b);
    BtorNode *o = boolector_one (g_btor, 32);
    BtorNode *t = boolector_unsigned_int (g_btor, 2, 32);
    {
      BtorNodeMap *map = btor_new_node_map (g_btor);
      BtorNode *d;
      btor_map_node (map, a, t);
      btor_map_node (map, b, o);
      d = btor_non_recursive_substitute_node (g_btor, map, s);
      assert (d == o);
      btor_delete_node_map (map);
      // boolector_release (g_btor, d); // No, map owns reference!!!!!!
    }
    boolector_release (g_btor, a);
    boolector_release (g_btor, b);
    boolector_release (g_btor, o);
    boolector_release (g_btor, s);
    boolector_release (g_btor, t);
  }
  finish_map_test ();
}

/*------------------------------------------------------------------------*/

static BtorNode *
test_map1_mapper (Btor *btor, void *state, BtorNode *node)
{
  (void) state;
  assert (btor == g_btor);
  assert (BTOR_IS_REGULAR_NODE (node));
  if (!BTOR_IS_BV_VAR_NODE (node)) return 0;
  assert (node->symbol);
  return boolector_int (btor, atoi (node->symbol), 8);
}

void
test_map1 ()
{
  init_map_test ();
  {
    BtorNode *a = boolector_var (g_btor, 8, "11");
    BtorNode *b = boolector_var (g_btor, 8, "22");
    BtorNode *c = boolector_var (g_btor, 8, "33");
    BtorNode *s;
    {
      BtorNode *sum = boolector_add (g_btor, a, b);
      s             = boolector_add (g_btor, sum, c);
      boolector_release (g_btor, sum);
    }
    {
      BtorNodeMap *map = btor_new_node_map (g_btor);
      BtorNode *d, *g;
      d = btor_non_recursive_extended_substitute_node (
          g_btor, map, 0, test_map1_mapper, boolector_release, s);
      g = boolector_int (g_btor, 66, 8);
      assert (d == g);
      boolector_release (g_btor, g);
      btor_delete_node_map (map);
    }
    boolector_release (g_btor, a);
    boolector_release (g_btor, b);
    boolector_release (g_btor, c);
    boolector_release (g_btor, s);
  }
  finish_map_test ();
}

/*------------------------------------------------------------------------*/

void
run_map_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (mapnewdel);
  BTOR_RUN_TEST (map0);
  BTOR_RUN_TEST (map1);
}
