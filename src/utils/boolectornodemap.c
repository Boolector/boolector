/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2015 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
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
map_node_internal (Btor *btor, BoolectorNodeMap *map, BoolectorNode *n)
{
  assert (btor);
  assert (n);

  BtorNode *src, *dst, *e[3], *node, *res = 0;
  uint32_t i;

  node = BTOR_IMPORT_BOOLECTOR_NODE (n);
  assert (btor_node_is_regular (node));
  assert (!btor_node_is_proxy (node));

  for (i = 0; i < node->arity; i++)
  {
    src = node->e[i];
    dst = BTOR_IMPORT_BOOLECTOR_NODE (
        boolector_nodemap_mapped (map, BTOR_EXPORT_BOOLECTOR_NODE (src)));
    e[i] = dst ? dst : src;
    assert (btor_node_real_addr (e[i])->btor == btor);
  }

  switch (node->kind)
  {
    case BTOR_VAR_NODE: res = btor_node_copy (btor, node); break;
    case BTOR_CONST_NODE:
      res = btor_exp_bv_const (btor, btor_node_bv_const_get_bits (node));
      break;
    case BTOR_BV_SLICE_NODE:
      res = btor_exp_bv_slice (btor,
                               e[0],
                               btor_node_bv_slice_get_upper (node),
                               btor_node_bv_slice_get_lower (node));
      break;
    case BTOR_BV_AND_NODE: res = btor_exp_bv_and (btor, e[0], e[1]); break;
    case BTOR_BV_EQ_NODE:
    case BTOR_FUN_EQ_NODE: res = btor_exp_eq (btor, e[0], e[1]); break;
    case BTOR_BV_ADD_NODE: res = btor_exp_bv_add (btor, e[0], e[1]); break;
    case BTOR_BV_MUL_NODE: res = btor_exp_bv_mul (btor, e[0], e[1]); break;
    case BTOR_BV_ULT_NODE: res = btor_exp_bv_ult (btor, e[0], e[1]); break;
    case BTOR_BV_SLL_NODE: res = btor_exp_bv_sll (btor, e[0], e[1]); break;
    case BTOR_BV_SRL_NODE: res = btor_exp_bv_srl (btor, e[0], e[1]); break;
    case BTOR_BV_UDIV_NODE: res = btor_exp_bv_udiv (btor, e[0], e[1]); break;
    case BTOR_BV_UREM_NODE: res = btor_exp_bv_urem (btor, e[0], e[1]); break;
    case BTOR_BV_CONCAT_NODE: res = btor_exp_bv_concat (btor, e[0], e[1]); break;
    case BTOR_ARGS_NODE: res = btor_exp_args (btor, e, node->arity); break;
    case BTOR_UPDATE_NODE:
      res = btor_exp_update (btor, e[0], e[1], e[2]);
      break;
    case BTOR_APPLY_NODE:
      assert (btor_node_is_array (e[0]));
      assert (btor_node_is_args (e[1]));
      assert (e[1]->arity == 1);
      res = btor_exp_read (btor, e[0], e[1]->e[0]);
      break;
    case BTOR_PARAM_NODE:
    case BTOR_LAMBDA_NODE:  // FIXME
    case BTOR_UF_NODE:      // FIXME
      abort ();
      break;
    default:
      assert (btor_node_is_cond (node));
      res = btor_exp_cond (btor, e[0], e[1], e[2]);
  }
  assert (res);

  btor_node_inc_ext_ref_counter (btor, res);
  return BTOR_EXPORT_BOOLECTOR_NODE (res);
}

static BoolectorNode *
extended_substitute_node (Btor *btor,
                          BoolectorNodeMap *map,
                          void *state,
                          BoolectorNodeMapper mapper,
                          BoolectorNodeReleaser release,
                          BoolectorNode *nroot)
{
  assert (!mapper || release);
  assert (!release || mapper);

  BtorNodePtrStack working_stack;
  BtorNode *node;
  BoolectorNode *res, *nnode, *mapped;
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
  do
  {
    node = btor_node_real_addr (BTOR_POP_STACK (working_stack));
    assert (!btor_node_is_proxy (node));
    nnode = BTOR_EXPORT_BOOLECTOR_NODE (node);

    if (boolector_nodemap_mapped (map, nnode)) continue;

    d = btor_hashint_map_get (mark, node->id);
    if (d && d->as_int == 1) continue;

    /* we are iterating over internal nodes, but 'mapper' can call
     * boolector_* function on 'nnode'.thus, we have to make sure that nnode
     * has at least one external reference. */
    btor_node_inc_ext_ref_counter (btor, node);
    if (mapper && (mapped = mapper (btor, state, nnode)))
    {
      assert (release);
      boolector_nodemap_map (map, nnode, mapped);
      release (btor, mapped);
    }
    else if (!d)
    {
      btor_hashint_map_add (mark, node->id);
      BTOR_PUSH_STACK (working_stack, node);
      for (i = 1; i <= node->arity; i++)
        BTOR_PUSH_STACK (working_stack, node->e[node->arity - i]);
    }
    else if (!d->as_int)
    {
      mapped = map_node_internal (btor, map, nnode);
      boolector_nodemap_map (map, nnode, mapped);
      boolector_release (btor, mapped);
      assert (d->as_int == 0);
      d->as_int = 1;
    }
    btor_node_dec_ext_ref_counter (btor, node);
  } while (!BTOR_EMPTY_STACK (working_stack));
  BTOR_RELEASE_STACK (working_stack);
  btor_hashint_map_delete (mark);
  res = boolector_nodemap_mapped (map, nroot);
  assert (res);
  return res;
}

BoolectorNode *
boolector_nodemap_extended_substitute_node (Btor *btor,
                                            BoolectorNodeMap *map,
                                            void *state,
                                            BoolectorNodeMapper mapper,
                                            BoolectorNodeReleaser release,
                                            BoolectorNode *nroot)
{
  return extended_substitute_node (btor, map, state, mapper, release, nroot);
}

BoolectorNode *
boolector_nodemap_substitute_node (Btor *btor,
                                   BoolectorNodeMap *map,
                                   BoolectorNode *root)
{
  return extended_substitute_node (btor, map, 0, 0, 0, root);
}
