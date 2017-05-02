
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
#include "btornode.h"
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
  g_btor = btor_new ();
  assert (g_btor);
}

static void
finish_map_test (void)
{
  assert (g_btor);
  btor_delete (g_btor);
  g_btor = 0;
}

/*------------------------------------------------------------------------*/

void
test_mapnewdel ()
{
  BtorNodeMap *map;
  init_map_test ();
  map = btor_nodemap_new (g_btor);
  btor_nodemap_delete (map);
  finish_map_test ();
}

/*------------------------------------------------------------------------*/
void
test_map0 ()
{
  Btor *stor, *dtor, *mtor;
  BtorNode *s, *d, *m;
  BtorNodeMap *map;
  BtorSortId sort;

  stor = btor_new ();
  dtor = btor_new ();
  mtor = btor_new ();
  sort = btor_sort_bitvec (stor, 32);
  s    = btor_var_exp (stor, sort, "s");
  btor_sort_release (stor, sort);
  sort = btor_sort_bitvec (dtor, 32);
  d    = btor_var_exp (dtor, sort, "d");
  btor_sort_release (dtor, sort);
  map = btor_nodemap_new (mtor);
  btor_nodemap_map (map, s, d);
  m = btor_nodemap_mapped (map, s);
  assert (m == d);
  btor_release_exp (stor, s);
  btor_release_exp (dtor, d);
  btor_nodemap_delete (map);
  btor_delete (stor);
  btor_delete (dtor);
  btor_delete (mtor);
}

void
test_map1 ()
{
  Btor *stor, *mtor;
  BtorNode *s, *t, *a;
  BtorSortId sort;
  BtorNodeMap *map;

  stor = btor_new ();
  mtor = btor_new ();
  sort = btor_sort_bitvec (stor, 32);
  s    = btor_var_exp (stor, sort, "0");
  t    = btor_var_exp (stor, sort, "1");
  a    = btor_and_exp (stor, s, t);
  map  = btor_nodemap_new (mtor);
  // BtorNode * m;
  // m = btor_nodemap_mapped (map, s);
  btor_sort_release (stor, sort);
  btor_release_exp (stor, t);
  btor_release_exp (stor, s);
  btor_release_exp (stor, a);
  btor_nodemap_delete (map);
  btor_delete (stor);
  btor_delete (mtor);
}

/*------------------------------------------------------------------------*/

void
run_map_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (mapnewdel);
  BTOR_RUN_TEST (map0);
  BTOR_RUN_TEST (map1);
}
