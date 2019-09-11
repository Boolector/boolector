/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorunionfind.h"

#include "btornode.h"
#include "utils/btorhashint.h"

struct BtorUnionFind
{
  BtorMemMgr *mm;
  BtorIntHashTable *cache; /* Maps node ids to UnionFindNode */
};

struct UnionFindNode
{
  int32_t id;
  struct UnionFindNode *parent;
  BtorNode *node;
};

typedef struct UnionFindNode UnionFindNode;

static UnionFindNode *
get_node (BtorUnionFind *ufind, BtorNode *n)
{
  assert (ufind);
  assert (n);

  int32_t id = btor_node_get_id (n);
  assert (btor_hashint_map_contains (ufind->cache, id));
  return btor_hashint_map_get (ufind->cache, id)->as_ptr;
}

static UnionFindNode *
new_node (BtorUnionFind *ufind, BtorNode *n)
{
  assert (ufind);
  assert (n);

  int32_t id;
  UnionFindNode *ufind_node;

  id = btor_node_get_id (n);

  if (btor_hashint_map_contains (ufind->cache, id))
  {
    ufind_node = btor_hashint_map_get (ufind->cache, id)->as_ptr;
  }
  else
  {
    BTOR_CNEW (ufind->mm, ufind_node);
    btor_hashint_map_add (ufind->cache, id)->as_ptr = ufind_node;
    ufind_node->node                                = n;
    ufind_node->id                                  = id;
  }
  return ufind_node;
}

static UnionFindNode *
find_node (UnionFindNode *node)
{
  assert (node);

  UnionFindNode *parent, *repr;

  /* Find representative. */
  repr = node;
  while (repr->parent)
  {
    repr = repr->parent;
  }

  /* Shorten path for all nodes. */
  while (node->parent)
  {
    parent       = node->parent;
    node->parent = repr;
    node         = parent;
  }

  return repr;
}

BtorUnionFind *
btor_ufind_new (BtorMemMgr *mm)
{
  assert (mm);

  BtorUnionFind *ufind;

  BTOR_CNEW (mm, ufind);
  ufind->mm    = mm;
  ufind->cache = btor_hashint_map_new (mm);

  return ufind;
}

void
btor_ufind_delete (BtorUnionFind *ufind)
{
  assert (ufind);

  for (size_t i = 0; i < ufind->cache->size; i++)
  {
    if (!ufind->cache->data[i].as_ptr) continue;
    BTOR_DELETE (ufind->mm, (UnionFindNode *) ufind->cache->data[i].as_ptr);
  }
  btor_hashint_map_delete (ufind->cache);
  BTOR_DELETE (ufind->mm, ufind);
}

void
btor_ufind_add (BtorUnionFind *ufind, BtorNode *x)
{
  assert (ufind);
  assert (x);

  (void) new_node (ufind, x);
}

void
btor_ufind_merge (BtorUnionFind *ufind, BtorNode *x, BtorNode *y)
{
  assert (ufind);
  assert (x);
  assert (y);

  UnionFindNode *n1, *n2;

  n1 = find_node (new_node (ufind, x));
  n2 = find_node (new_node (ufind, y));

  assert (!n1->parent);
  assert (!n2->parent);

  if (n1->id != n2->id)
  {
    /* Choose node with lower id to be representative. */
    if (abs (n1->id) < abs (n2->id))
    {
      n2->parent = n1;
    }
    else
    {
      n1->parent = n2;
    }
  }
}

BtorNode *
btor_ufind_get_repr (BtorUnionFind *ufind, BtorNode *x)
{
  assert (ufind);
  assert (x);

  int32_t id = btor_node_get_id (x);
  if (btor_hashint_map_contains (ufind->cache, id))
  {
    UnionFindNode *n = find_node (get_node (ufind, x));
    return n->node;
  }
  return x;
}

bool
btor_ufind_is_equal (BtorUnionFind *ufind, BtorNode *x, BtorNode *y)
{
  assert (ufind);
  assert (x);
  assert (y);

  return btor_ufind_get_repr (ufind, x) == btor_ufind_get_repr (ufind, y);
}
