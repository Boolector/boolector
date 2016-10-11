
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

#include "testmap.h"
#include "btorcore.h"
#include "btorexp.h"
#include "testrunner.h"
#include "utils/btornodemap.h"

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
test_map1 ()
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
}
