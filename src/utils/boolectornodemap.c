/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/boolectornodemap.h"
#include "btorcore.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

/*------------------------------------------------------------------------*/

#include <limits.h>

/*------------------------------------------------------------------------*/

BoolectorNodeMap *
boolector_nodemap_new (Btor *btor)
{
  BoolectorNodeMap *res;

  assert (btor);

  BTOR_NEW (btor->mm, res);
  res->btor  = btor;
  res->table = btor_new_ptr_hash_table (btor->mm,
                                        (BtorHashPtr) btor_hash_exp_by_id,
                                        (BtorCmpPtr) btor_compare_exp_by_id);

  return res;
}

void
boolector_nodemap_delete (BoolectorNodeMap *map)
{
  assert (map);

  BtorPtrHashTableIterator it;
  BtorNode *e;
  Btor *btor;

  btor_init_ptr_hash_table_iterator (&it, map->table);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    e    = it.bucket->data.as_ptr;
    btor = BTOR_REAL_ADDR_NODE (e)->btor;
    btor_dec_exp_ext_ref_counter (btor, e);
    btor_release_exp (btor, e);

    e    = btor_next_ptr_hash_table_iterator (&it);
    btor = BTOR_REAL_ADDR_NODE (e)->btor;
    btor_dec_exp_ext_ref_counter (btor, e);
    btor_release_exp (btor, e);
  }
  btor_delete_ptr_hash_table (map->table);
  BTOR_DELETE (map->btor->mm, map);
}

BoolectorNode *
boolector_nodemap_mapped (BoolectorNodeMap *map, const BoolectorNode *n)
{
  BtorPtrHashBucket *bucket;
  BtorNode *real_node;
  BoolectorNode *nres;
  BtorNode *eres;
  BtorNode *e;

  e = BTOR_IMPORT_BOOLECTOR_NODE (n);
  e = btor_simplify_exp (BTOR_REAL_ADDR_NODE (e)->btor, e);

  real_node = BTOR_REAL_ADDR_NODE (e);
  bucket    = btor_get_ptr_hash_table (map->table, real_node);
  if (!bucket) return 0;
  assert (bucket->key == real_node);
  eres = bucket->data.as_ptr;
  if (BTOR_IS_INVERTED_NODE (n)) eres = BTOR_INVERT_NODE (eres);
  nres = BTOR_EXPORT_BOOLECTOR_NODE (eres);
  return nres;
}

int
boolector_nodemap_count (const BoolectorNodeMap *map)
{
  assert (map);
  return map->table->count;
}

void
boolector_nodemap_map (BoolectorNodeMap *map,
                       BoolectorNode *nsrc,
                       BoolectorNode *ndst)
{
  BtorPtrHashBucket *bucket;
  BtorNode *esrc, *edst;
  Btor *sbtor, *dbtor;

  assert (map);
  assert (nsrc);
  assert (ndst);

  esrc = BTOR_IMPORT_BOOLECTOR_NODE (nsrc);
  edst = BTOR_IMPORT_BOOLECTOR_NODE (ndst);

  esrc = btor_simplify_exp (BTOR_REAL_ADDR_NODE (esrc)->btor, esrc);
  edst = btor_simplify_exp (BTOR_REAL_ADDR_NODE (edst)->btor, edst);

  if (BTOR_IS_INVERTED_NODE (esrc))
  {
    esrc = BTOR_INVERT_NODE (esrc);
    edst = BTOR_INVERT_NODE (edst);
  }
  assert (!btor_get_ptr_hash_table (map->table, esrc));
  bucket = btor_add_ptr_hash_table (map->table, esrc);
  assert (bucket);

  sbtor = BTOR_REAL_ADDR_NODE (esrc)->btor;
  esrc  = btor_copy_exp (sbtor, esrc);
  assert (bucket->key == esrc);
  btor_inc_exp_ext_ref_counter (sbtor, esrc);
  bucket->key = esrc;

  dbtor = BTOR_REAL_ADDR_NODE (edst)->btor;
  assert (!bucket->data.as_ptr);
  edst = btor_copy_exp (dbtor, edst);
  btor_inc_exp_ext_ref_counter (dbtor, edst);
  bucket->data.as_ptr = edst;
}

/*------------------------------------------------------------------------*/

static BoolectorNode *
boolector_map_node_internal (Btor *btor,
                             BoolectorNodeMap *map,
                             BoolectorNode *n)
{
  assert (btor);
  assert (n);

  BtorNode *src, *dst, *e, *tmp;
  BoolectorNode *m[3];
  int i;

  e = BTOR_IMPORT_BOOLECTOR_NODE (n);
  assert (BTOR_IS_REGULAR_NODE (e));

  m[0] = m[1] = m[2] = 0;

  for (i = 0; i < e->arity; i++)
  {
    src = e->e[i];
    dst = BTOR_IMPORT_BOOLECTOR_NODE (
        boolector_nodemap_mapped (map, BTOR_EXPORT_BOOLECTOR_NODE (src)));
    tmp  = dst ? dst : src;
    m[i] = BTOR_EXPORT_BOOLECTOR_NODE (tmp);
    assert (BTOR_REAL_ADDR_NODE (m[i])->btor == btor);
  }

  assert (!btor_is_proxy_node (e));

  switch (e->kind)
  {
    case BTOR_BV_CONST_NODE:

      assert (BTOR_REAL_ADDR_NODE (e) == e);
      if (e->btor != btor)
      {
        tmp = btor_const_exp (btor, btor_const_get_bits (e));
        btor_inc_exp_ext_ref_counter (btor, tmp);
        return BTOR_EXPORT_BOOLECTOR_NODE (tmp);
      }

      // ELSE FALL THROUGH!!!

    case BTOR_BV_VAR_NODE:
    case BTOR_UF_NODE:      // FIXME
    case BTOR_LAMBDA_NODE:  // FIXME
      return boolector_copy (btor, n);

    case BTOR_SLICE_NODE:
      return boolector_slice (
          btor, m[0], btor_slice_get_upper (e), btor_slice_get_lower (e));
    case BTOR_AND_NODE: return boolector_and (btor, m[0], m[1]);
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE: return boolector_eq (btor, m[0], m[1]);
    case BTOR_ADD_NODE: return boolector_add (btor, m[0], m[1]);
    case BTOR_MUL_NODE: return boolector_mul (btor, m[0], m[1]);
    case BTOR_ULT_NODE: return boolector_ult (btor, m[0], m[1]);
    case BTOR_SLL_NODE: return boolector_sll (btor, m[0], m[1]);
    case BTOR_SRL_NODE: return boolector_srl (btor, m[0], m[1]);
    case BTOR_UDIV_NODE: return boolector_udiv (btor, m[0], m[1]);
    case BTOR_UREM_NODE: return boolector_urem (btor, m[0], m[1]);
    case BTOR_CONCAT_NODE: return boolector_concat (btor, m[0], m[1]);
    default:
      assert (btor_is_bv_cond_node (e));
      return boolector_cond (btor, m[0], m[1], m[2]);
  }
}

BoolectorNode *
boolector_nodemap_non_recursive_extended_substitute_node (
    Btor *btor,
    BoolectorNodeMap *map,
    void *state,
    BoolectorNodeMapper mapper,
    BoolectorNodeReleaser release,
    BoolectorNode *nroot)
{
  BtorNodePtrStack working_stack;
  BtorNode *node, *mapped;
  BoolectorNode *res;
  BtorNode *eroot;
  BtorMemMgr *mm;
  BtorIntHashTable *mark;
  BtorHashTableData *d;
  int i;

  eroot = BTOR_IMPORT_BOOLECTOR_NODE (nroot);
  eroot = btor_simplify_exp (BTOR_REAL_ADDR_NODE (eroot)->btor, eroot);

  mm   = btor->mm;
  mark = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, working_stack);
  BTOR_PUSH_STACK (working_stack, eroot);

  while (!BTOR_EMPTY_STACK (working_stack))
  {
    node = BTOR_POP_STACK (working_stack);
    node = BTOR_REAL_ADDR_NODE (node);
    btor_inc_exp_ext_ref_counter (node->btor, node);
    assert (!btor_is_proxy_node (node));
    if (boolector_nodemap_mapped (map, BTOR_EXPORT_BOOLECTOR_NODE (node)))
      goto DEC_EXT_REFS_AND_CONTINUE;
    d = btor_hashint_map_get (mark, node->id);
    if (d && d->as_int == 1) goto DEC_EXT_REFS_AND_CONTINUE;
    mapped = BTOR_IMPORT_BOOLECTOR_NODE (
        mapper (btor, state, BTOR_EXPORT_BOOLECTOR_NODE (node)));
    if (mapped)
    {
      boolector_nodemap_map (map,
                             BTOR_EXPORT_BOOLECTOR_NODE (node),
                             BTOR_EXPORT_BOOLECTOR_NODE (mapped));
      release (btor, BTOR_EXPORT_BOOLECTOR_NODE (mapped));
    }
    else if (!d)
    {
      btor_hashint_map_add (mark, node->id);
      BTOR_PUSH_STACK (working_stack, node);
      for (i = node->arity - 1; i >= 0; i--)
        BTOR_PUSH_STACK (working_stack, node->e[i]);
    }
    else
    {
      mapped = BTOR_IMPORT_BOOLECTOR_NODE (boolector_map_node_internal (
          btor, map, BTOR_EXPORT_BOOLECTOR_NODE (node)));
      boolector_nodemap_map (map,
                             BTOR_EXPORT_BOOLECTOR_NODE (node),
                             BTOR_EXPORT_BOOLECTOR_NODE (mapped));
      boolector_release (btor, BTOR_EXPORT_BOOLECTOR_NODE (mapped));
      assert (d->as_int == 0);
      d->as_int = 1;
    }
  DEC_EXT_REFS_AND_CONTINUE:
    assert (!BTOR_IS_INVERTED_NODE (node));
    btor_dec_exp_ext_ref_counter (node->btor, node);
  }
  BTOR_RELEASE_STACK (working_stack);
  btor_hashint_map_delete (mark);
  res = boolector_nodemap_mapped (map, nroot);
  assert (res);
  return res;
}

static BoolectorNode *
boolector_never_map_mapper (Btor *btor, void *state, BoolectorNode *node)
{
  (void) btor;
  (void) state;
  (void) node;
  return 0;
}

BoolectorNode *
boolector_nodemap_non_recursive_substitute_node (Btor *btor,
                                                 BoolectorNodeMap *map,
                                                 BoolectorNode *root)
{
  return boolector_nodemap_non_recursive_extended_substitute_node (
      btor, map, 0, boolector_never_map_mapper, 0, root);
}
