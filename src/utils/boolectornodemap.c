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

#include "boolector.h"
#include "btorcore.h"
#include "btorexp.h"
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
  res->table = btor_hashptr_table_new (btor->mm,
                                       (BtorHashPtr) btor_node_hash_by_id,
                                       (BtorCmpPtr) btor_node_compare_by_id);

  return res;
}

void
boolector_nodemap_delete (BoolectorNodeMap *map)
{
  assert (map);

  BtorPtrHashTableIterator it;
  BtorNode *e;
  Btor *btor;

  btor_iter_hashptr_init (&it, map->table);
  while (btor_iter_hashptr_has_next (&it))
  {
    e    = it.bucket->data.as_ptr;
    btor = btor_node_real_addr (e)->btor;
    btor_node_dec_ext_ref_counter (btor, e);
    btor_node_release (btor, e);

    e    = btor_iter_hashptr_next (&it);
    btor = btor_node_real_addr (e)->btor;
    btor_node_dec_ext_ref_counter (btor, e);
    btor_node_release (btor, e);
  }
  btor_hashptr_table_delete (map->table);
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
  e = btor_simplify_exp (btor_node_real_addr (e)->btor, e);

  real_node = btor_node_real_addr (e);
  bucket    = btor_hashptr_table_get (map->table, real_node);
  if (!bucket) return 0;
  assert (bucket->key == real_node);
  eres = bucket->data.as_ptr;
  if (btor_node_is_inverted (e)) eres = btor_node_invert (eres);
  nres = BTOR_EXPORT_BOOLECTOR_NODE (eres);
  return nres;
}

uint32_t
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

  esrc = btor_simplify_exp (btor_node_real_addr (esrc)->btor, esrc);
  edst = btor_simplify_exp (btor_node_real_addr (edst)->btor, edst);

  if (btor_node_is_inverted (esrc))
  {
    esrc = btor_node_invert (esrc);
    edst = btor_node_invert (edst);
  }
  assert (!btor_hashptr_table_get (map->table, esrc));
  bucket = btor_hashptr_table_add (map->table, esrc);
  assert (bucket);

  sbtor = btor_node_real_addr (esrc)->btor;
  esrc  = btor_node_copy (sbtor, esrc);
  assert (bucket->key == esrc);
  btor_node_inc_ext_ref_counter (sbtor, esrc);
  bucket->key = esrc;

  dbtor = btor_node_real_addr (edst)->btor;
  assert (!bucket->data.as_ptr);
  edst = btor_node_copy (dbtor, edst);
  btor_node_inc_ext_ref_counter (dbtor, edst);
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
  uint32_t i;

  e = BTOR_IMPORT_BOOLECTOR_NODE (n);
  assert (btor_node_is_regular (e));

  m[0] = m[1] = m[2] = 0;

  for (i = 0; i < e->arity; i++)
  {
    src = e->e[i];
    dst = BTOR_IMPORT_BOOLECTOR_NODE (
        boolector_nodemap_mapped (map, BTOR_EXPORT_BOOLECTOR_NODE (src)));
    tmp  = dst ? dst : src;
    m[i] = BTOR_EXPORT_BOOLECTOR_NODE (tmp);
    assert (btor_node_real_addr (tmp)->btor == btor);
  }

  assert (!btor_node_is_proxy (e));

  switch (e->kind)
  {
    case BTOR_BV_CONST_NODE:

      assert (btor_node_real_addr (e) == e);
      if (e->btor != btor)
      {
        tmp = btor_exp_const (btor, btor_node_const_get_bits (e));
        btor_node_inc_ext_ref_counter (btor, tmp);
        return BTOR_EXPORT_BOOLECTOR_NODE (tmp);
      }

      // ELSE FALL THROUGH!!!

    case BTOR_BV_VAR_NODE:
    case BTOR_UF_NODE:      // FIXME
    case BTOR_LAMBDA_NODE:  // FIXME
      return boolector_copy (btor, n);

    case BTOR_SLICE_NODE:
      return boolector_slice (btor,
                              m[0],
                              btor_node_slice_get_upper (e),
                              btor_node_slice_get_lower (e));
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
      assert (btor_node_is_bv_cond (e));
      return boolector_cond (btor, m[0], m[1], m[2]);
  }
}

BoolectorNode *
boolector_nodemap_extended_substitute_node (Btor *btor,
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
  uint32_t i;

  eroot = BTOR_IMPORT_BOOLECTOR_NODE (nroot);
  eroot = btor_simplify_exp (btor_node_real_addr (eroot)->btor, eroot);

  mm   = btor->mm;
  mark = btor_hashint_map_new (mm);

  BTOR_INIT_STACK (mm, working_stack);
  BTOR_PUSH_STACK (working_stack, eroot);

  while (!BTOR_EMPTY_STACK (working_stack))
  {
    node = BTOR_POP_STACK (working_stack);
    node = btor_node_real_addr (node);
    btor_node_inc_ext_ref_counter (node->btor, node);
    assert (!btor_node_is_proxy (node));
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
      for (i = 1; i <= node->arity; i++)
        BTOR_PUSH_STACK (working_stack, node->e[node->arity - i]);
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
    assert (!btor_node_is_inverted (node));
    btor_node_dec_ext_ref_counter (node->btor, node);
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
boolector_nodemap_substitute_node (Btor *btor,
                                   BoolectorNodeMap *map,
                                   BoolectorNode *root)
{
  return boolector_nodemap_extended_substitute_node (
      btor, map, 0, boolector_never_map_mapper, 0, root);
}
