/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslv.h"
#include "btorcore.h"

void
btor_delete_slv_mgr (Btor *btor)
{
  assert (btor);
  if (!btor->slvmgr) return;
  btor->slvmgr->api.delete_slv (btor);
  BTOR_DELETE (btor->mm, btor->slvmgr);
  btor->slvmgr = 0;
}

BtorSlvMgr *
btor_clone_slv_mgr (Btor *clone, Btor *btor, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (btor);
  assert (exp_map);

  BtorSlvMgr *res;

  if (!btor->slvmgr) return 0;

  BTOR_NEW (clone->mm, res);
  memcpy (res, btor->slvmgr, sizeof (BtorSlvMgr));
  if (btor->slvmgr->slv)
    res->slv = btor->slvmgr->api.clone_slv (clone, btor, exp_map);
  return res;
}
