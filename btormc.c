#include "btormc.h"
#include "btorexp.h"

#include <stdarg.h>

typedef enum BtorMcKind
{
  BTOR_INPUT_MC_NODE = 1,
  BTOR_LATCH_MC_NODE = 2,
} BtorMcKind;

typedef struct BtorMcNode BtorMcNode;

struct BtorMcNode
{
  int id;
  BtorMcKind kind;
  BtorNode *node, *next, *init;
  BtorNodePtrStack copies;
};

struct BtorMC
{
  Btor *btor;
  int verbosity, ninputs, nlatches;
  BtorPtrHashTable *mcnodes;
};

static unsigned
btor_hash_mc_node (BtorMcNode *n)
{
  return btor_hash_exp_by_id (n->node);
}

static int
btor_cmp_mc_node (BtorMcNode *m, BtorMcNode *n)
{
  return btor_compare_exp_by_id (m->node, n->node);
}

BtorMC *
boolector_new_mc (void)
{
  BtorMemMgr *mm;
  BtorMC *res;
  Btor *btor = boolector_new ();
  mm         = btor->mm;
  BTOR_CNEW (mm, res);
  res->btor    = btor;
  res->mcnodes = btor_new_ptr_hash_table (
      mm, (BtorHashPtr) btor_hash_mc_node, (BtorCmpPtr) btor_cmp_mc_node);
  return res;
}

void
boolector_set_verbosity_mc (BtorMC *mc, int verbosity)
{
  mc->verbosity = verbosity;
}

static void
btor_delete_mc_node (BtorMC *mc, BtorMcNode *mcn)
{
  BtorMemMgr *mm;
  BtorNode *node;
  Btor *btor;
  assert (mc);
  if (mcn->kind == BTOR_INPUT_MC_NODE)
  {
    assert (mc->ninputs > 0);
    mc->ninputs--;
  }
  else
  {
    assert (mcn->kind == BTOR_LATCH_MC_NODE);
    assert (mc->nlatches > 0);
    mc->nlatches--;
  }
  btor = mc->btor;
  mm   = btor->mm;
  while (!BTOR_EMPTY_STACK (mcn->copies))
    if ((node = BTOR_POP_STACK (mcn->copies))) btor_release_exp (btor, node);
  btor_release_exp (btor, mcn->node);
  if (mcn->next) btor_release_exp (btor, mcn->next);
  if (mcn->init) btor_release_exp (btor, mcn->init);
  BTOR_RELEASE_STACK (mm, mcn->copies);
  BTOR_DELETE (mm, mcn);
}

static void
btor_msg_mc (BtorMC *mc, int level, const char *fmt, ...)
{
  va_list ap;
  assert (mc);
  if (mc->verbosity < level) return;
  assert (fmt != NULL);
  fprintf (stdout, "[btormc] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  putc ('\n', stdout);
  fflush (stdout);
}

void
boolector_delete_mc (BtorMC *mc)
{
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  Btor *btor;
  assert (mc);
  btor_msg_mc (mc,
               1,
               "deleting model with %d inputs and %d latches",
               mc->ninputs,
               mc->nlatches);
  btor = mc->btor;
  mm   = btor->mm;
  for (bucket = mc->mcnodes->first; bucket; bucket = bucket->next)
    btor_delete_mc_node (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->mcnodes);
  BTOR_DELETE (mm, mc);
  boolector_delete (btor);
}

Btor *
boolector_mc_btor (BtorMC *mc)
{
  assert (mc);
  return mc->btor;
}

static BtorMcNode *
btor_new_mc_node (BtorMC *mc, BtorMcKind kind, int width, const char *name)
{
  BtorMemMgr *mm;
  BtorMcNode *res;
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  BTOR_CNEW (mm, res);
  if (kind == BTOR_INPUT_MC_NODE)
    res->id = mc->ninputs++;
  else
  {
    assert (kind == BTOR_LATCH_MC_NODE);
    res->id = mc->nlatches++;
  }
  res->kind = kind;
  res->node = boolector_var (btor, width, name);
  assert (BTOR_EMPTY_STACK (res->copies));
  btor_insert_in_ptr_hash_table (mc->mcnodes, res);
  return res;
}

BtorNode *
boolector_input (BtorMC *mc, int width, const char *name)
{
  BtorMcNode *mcnode;
  BtorNode *res;
  assert (mc);
  assert (1 <= width);
  mcnode = btor_new_mc_node (mc, BTOR_INPUT_MC_NODE, width, name);
  res    = mcnode->node;
  if (name)
    btor_msg_mc (mc, 2, "%d. input[%d] named \"%s\"", mcnode->id, width, name);
  else
    btor_msg_mc (mc, 2, "%d. input[%d] (anonymous)", mcnode->id, width);
  return res;
}

BtorNode *
boolector_latch (BtorMC *mc, int width, const char *name)
{
  BtorMcNode *mcnode;
  BtorNode *res;
  assert (mc);
  assert (1 <= width);
  mcnode = btor_new_mc_node (mc, BTOR_LATCH_MC_NODE, width, name);
  res    = mcnode->node;
  if (name)
    btor_msg_mc (mc, 2, "%d. latch[%d] named \"%s\"", mcnode->id, width, name);
  else
    btor_msg_mc (mc, 2, "%d. latch[%d] (anonymous)", mcnode->id, width);
  return res;
}
