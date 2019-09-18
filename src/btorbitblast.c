/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbitblast.h"

#include "btorabort.h"
#include "btorcore.h"
#include "btornode.h"
#include "utils/btorhashint.h"
#include "utils/btorutil.h"

BtorAIGVec *
btor_bitblast_exp (Btor *btor,
                   BtorAIGVecMgr *avmgr,
                   BtorNode *exp,
                   BtorPtrHashTable *node_to_aigvec,
                   BtorIntHashTable *symbols)
{
  assert (btor);
  assert (exp);

  size_t len;
  uint32_t i, bw;
  BtorMemMgr *mm;
  BtorNode *cur;
  BtorNodePtrStack visit;
  BtorIntHashTable *cache;
  BtorHashTableData *d, *dd;
  BtorPtrHashBucket *b;
  BtorAIGVec *res, *av[3] = {0, 0, 0};
  const char *name;
  char *buf;

  mm    = btor->mm;
  cache = btor_hashint_map_new (btor->mm);

  BTOR_INIT_STACK (btor->mm, visit);
  BTOR_PUSH_STACK (visit, exp);

  while (!BTOR_EMPTY_STACK (visit))
  {
    cur = btor_node_real_addr (BTOR_POP_STACK (visit));

    if (!(d = btor_hashint_map_get (cache, cur->id)))
    {
      d = btor_hashint_map_add (cache, cur->id);

      if (node_to_aigvec && (b = btor_hashptr_table_get (node_to_aigvec, cur)))
      {
        d->as_ptr = btor_aigvec_copy (avmgr, b->data.as_ptr);
        continue;
      }

      BTOR_PUSH_STACK (visit, cur);
      for (i = 0; i < cur->arity; i++)
      {
        BTOR_PUSH_STACK (visit, cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      for (i = 0; i < cur->arity; i++)
      {
        dd = btor_hashint_map_get (cache, btor_node_real_addr (cur->e[i])->id);
        assert (dd->as_ptr);
        if (btor_node_is_inverted (cur->e[i]))
        {
          av[i] = btor_aigvec_not (avmgr, dd->as_ptr);
        }
        else
        {
          av[i] = btor_aigvec_copy (avmgr, dd->as_ptr);
        }
      }

      res = 0;
      switch (cur->kind)
      {
        case BTOR_BV_CONST_NODE:
          res = btor_aigvec_const (avmgr, btor_node_bv_const_get_bits (cur));
          break;
        case BTOR_VAR_NODE:
          bw  = btor_node_bv_get_width (btor, cur);
          res = btor_aigvec_var (avmgr, bw);

          if (btor_node_is_bv_var (cur) && symbols
              && (name = btor_node_get_symbol (btor, cur)))
          {
            len = strlen (name) + 3 + btor_util_num_digits (bw);
            if (btor_node_bv_get_width (btor, cur) > 1)
            {
              buf = btor_mem_malloc (btor->mm, len);
              for (i = 0; i < res->width; i++)
              {
                snprintf (buf, len, "%s[%u]", name, res->width - i - 1);
                btor_hashint_map_add (symbols, res->aigs[i]->id << 1)->as_str =
                    btor_mem_strdup (mm, buf);
              }
              btor_mem_free (mm, buf, len);
            }
            else
            {
              assert (btor_node_bv_get_width (btor, cur) == 1);
              btor_hashint_map_add (symbols, res->aigs[0]->id << 1)->as_str =
                  btor_mem_strdup (btor->mm, name);
            }
          }
          break;
        case BTOR_BV_SLICE_NODE:
          res = btor_aigvec_slice (avmgr,
                                   av[0],
                                   btor_node_bv_slice_get_upper (cur),
                                   btor_node_bv_slice_get_lower (cur));
          break;
        case BTOR_BV_AND_NODE:
          res = btor_aigvec_and (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_EQ_NODE: res = btor_aigvec_eq (avmgr, av[0], av[1]); break;
        case BTOR_BV_ADD_NODE:
          res = btor_aigvec_add (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_MUL_NODE:
          res = btor_aigvec_mul (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_ULT_NODE:
          res = btor_aigvec_ult (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_SLL_NODE:
          res = btor_aigvec_sll (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_SRL_NODE:
          res = btor_aigvec_srl (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_UDIV_NODE:
          res = btor_aigvec_udiv (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_UREM_NODE:
          res = btor_aigvec_urem (avmgr, av[0], av[1]);
          break;
        case BTOR_BV_CONCAT_NODE:
          res = btor_aigvec_concat (avmgr, av[0], av[1]);
          break;
        case BTOR_COND_NODE:
          res = btor_aigvec_cond (avmgr, av[0], av[1], av[2]);
          break;
        default:
          BTOR_ABORT (true,
                      "Unsupported kind for bit-blasting: %s",
                      g_btor_op2str[cur->kind]);
      }
      assert (res);
      d->as_ptr = res;

      if (node_to_aigvec)
      {
        btor_hashptr_table_add (node_to_aigvec, btor_node_copy (btor, cur))
            ->data.as_ptr = btor_aigvec_copy (avmgr, res);
      }

      for (i = 0; i < cur->arity; i++)
      {
        btor_aigvec_release_delete (avmgr, av[i]);
      }
    }
  }
  BTOR_RELEASE_STACK (visit);

  if (btor_node_is_inverted (exp))
  {
    d = btor_hashint_map_get (cache, cur->id);
    assert (d->as_ptr);
    res = btor_aigvec_not (avmgr, d->as_ptr);
  }
  else
  {
    res = btor_aigvec_copy (avmgr, d->as_ptr);
  }

  for (i = 0; i < cache->size; i++)
  {
    if (!cache->data[i].as_ptr) continue;
    btor_aigvec_release_delete (avmgr, cache->data[i].as_ptr);
  }
  btor_hashint_map_delete (cache);

  return res;
}
