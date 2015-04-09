/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvmgr.h"
#include "btorexit.h"

//#define BTOR_ABORT_SLV(cond,msg) \
//do { \
//  if (cond) \
//    { \
//      printf ("[btorslv] %s: %s\n", __func__, msg); \
//      fflush (stdout); \
//      exit (BTOR_ERR_EXIT); \
//    } \
//} while (0)

BtorSlvMgr *
btor_new_slv_mgr (BtorMemMgr *mm, BtorMsg *msg)
{
  assert (mm);

  BtorSlvMgr *res;

  BTOR_CNEW (mm, res);
  res->mm  = mm;
  res->msg = msg;
  // TODO enable default
  BTOR_MSG (msg, 1, "enabled %s engine", res->name);
  return res;
}

BtorSlvMgr *
btor_clone_slv_mgr (BtorMemMgr *mm, BtorMsg *msg, BtorSlvMgr *slvmgr)
{
  assert (mm);
  assert (msg);
  assert (slvmgr);

  BtorSlvmgr *res;

  BTOR_NEW (mm, res);
  res->mm   = mm;
  res->msg  = msg;
  res->name = slvmgr->name;
  return res;
}

void
btor_delete_slv_mgr (BtorSlvMgr *slvmgr)
{
  assert (slvmgr);
  BTOR_DELETE (svlmgr->mm, slvmgr);
}
