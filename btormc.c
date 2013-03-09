#include "btormc.h"
#include "btorexp.h"

#include <stdarg.h>

typedef struct BtorMcInput
{
  int id;
  BtorNode *node;
} BtorMcInput;

typedef struct BtorMcLatch
{
  int id;
  BtorNode *node, *next, *init;
} BtorMcLatch;

typedef struct BtorMcFrame
{
  int time;
  BtorNodePtrStack inputs, init, latches, next, bad;
} BtorMcFrame;

BTOR_DECLARE_STACK (McFrame, BtorMcFrame);

struct BtorMC
{
  Btor *btor;
  int verbosity;
  BtorMcFrameStack frames;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *latches;
  BtorNodePtrStack bad;
};

BtorMC *
boolector_new_mc (void)
{
  BtorMemMgr *mm;
  BtorMC *res;
  Btor *btor = boolector_new ();
  mm         = btor->mm;
  BTOR_CNEW (mm, res);
  res->btor    = btor;
  res->inputs  = btor_new_ptr_hash_table (mm,
                                         (BtorHashPtr) btor_hash_exp_by_id,
                                         (BtorCmpPtr) btor_compare_exp_by_id);
  res->latches = btor_new_ptr_hash_table (mm,
                                          (BtorHashPtr) btor_hash_exp_by_id,
                                          (BtorCmpPtr) btor_compare_exp_by_id);
  return res;
}

void
boolector_set_verbosity_mc (BtorMC *mc, int verbosity)
{
  mc->verbosity = verbosity;
}

Btor *
boolector_btor_mc (BtorMC *mc)
{
  assert (mc);
  return mc->btor;
}

static void
btor_delete_mc_input (BtorMC *mc, BtorMcInput *input)
{
  BtorMemMgr *mm;
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  btor_release_exp (btor, input->node);
  BTOR_DELETE (mm, input);
}

static void
btor_delete_mc_latch (BtorMC *mc, BtorMcLatch *latch)
{
  BtorMemMgr *mm;
  Btor *btor;
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  btor_release_exp (btor, latch->node);
  if (latch->init) btor_release_exp (btor, latch->init);
  if (latch->next) btor_release_exp (btor, latch->next);
  BTOR_DELETE (mm, latch);
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

static void
btor_release_mc_frame (BtorMC *mc, BtorMcFrame *frame)
{
  Btor *btor = mc->btor;
  while (!BTOR_EMPTY_STACK (frame->inputs))
    btor_release_exp (btor, BTOR_POP_STACK (frame->inputs));
  while (!BTOR_EMPTY_STACK (frame->latches))
    btor_release_exp (btor, BTOR_POP_STACK (frame->init));
  while (!BTOR_EMPTY_STACK (frame->init))
    btor_release_exp (btor, BTOR_POP_STACK (frame->latches));
  while (!BTOR_EMPTY_STACK (frame->next))
    btor_release_exp (btor, BTOR_POP_STACK (frame->next));
  while (!BTOR_EMPTY_STACK (frame->bad))
    btor_release_exp (btor, BTOR_POP_STACK (frame->bad));
  BTOR_RELEASE_STACK (btor->mm, frame->inputs);
  BTOR_RELEASE_STACK (btor->mm, frame->init);
  BTOR_RELEASE_STACK (btor->mm, frame->latches);
  BTOR_RELEASE_STACK (btor->mm, frame->next);
  BTOR_RELEASE_STACK (btor->mm, frame->bad);
}

void
boolector_delete_mc (BtorMC *mc)
{
  BtorPtrHashBucket *bucket;
  BtorMemMgr *mm;
  BtorMcFrame *f;
  Btor *btor;
  assert (mc);
  btor_msg_mc (mc,
               1,
               "deleting model checker: %u inputs, %u latches, %u bad",
               mc->inputs->count,
               mc->latches->count,
               BTOR_COUNT_STACK (mc->bad));
  btor = mc->btor;
  mm   = btor->mm;
  for (f = mc->frames.start; f < mc->frames.top; f++)
    btor_release_mc_frame (mc, f);
  BTOR_RELEASE_STACK (mm, mc->frames);
  for (bucket = mc->inputs->first; bucket; bucket = bucket->next)
    btor_delete_mc_input (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->inputs);
  for (bucket = mc->latches->first; bucket; bucket = bucket->next)
    btor_delete_mc_latch (mc, bucket->data.asPtr);
  btor_delete_ptr_hash_table (mc->latches);
  while (!BTOR_EMPTY_STACK (mc->bad))
    btor_release_exp (btor, BTOR_POP_STACK (mc->bad));
  BTOR_RELEASE_STACK (mm, mc->bad);
  BTOR_DELETE (mm, mc);
  boolector_delete (btor);
}

Btor *
boolector_mc_btor (BtorMC *mc)
{
  assert (mc);
  return mc->btor;
}

BtorNode *
boolector_input (BtorMC *mc, int width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMcInput *input;
  BtorMemMgr *mm;
  BtorNode *res;
  Btor *btor;
  assert (1 <= width);
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  res  = boolector_var (btor, width, name);
  BTOR_NEW (mm, input);
  assert (input);
  input->id   = (int) mc->inputs->count;
  input->node = res;
  bucket      = btor_insert_in_ptr_hash_table (mc->inputs, res);
  assert (bucket);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = input;
  if (name)
    btor_msg_mc (
        mc, 2, "declared input%d[%d] named \"%s\"", input->id, width, name);
  else
    btor_msg_mc (mc, 2, "declared input%d[%d]", input->id, width);
  return res;
}

BtorNode *
boolector_latch (BtorMC *mc, int width, const char *name)
{
  BtorPtrHashBucket *bucket;
  BtorMcLatch *latch;
  BtorMemMgr *mm;
  BtorNode *res;
  Btor *btor;
  assert (1 <= width);
  assert (mc);
  btor = mc->btor;
  mm   = btor->mm;
  res  = boolector_var (btor, width, name);
  BTOR_NEW (mm, latch);
  assert (latch);
  latch->id   = (int) mc->latches->count;
  latch->node = res;
  latch->init = latch->next = 0;
  bucket                    = btor_insert_in_ptr_hash_table (mc->latches, res);
  assert (bucket);
  assert (!bucket->data.asPtr);
  bucket->data.asPtr = latch;
  if (name)
    btor_msg_mc (
        mc, 2, "declared latch%d[%d] named \"%s\"", latch->id, width, name);
  else
    btor_msg_mc (mc, 2, "declared latch%d[%d]", latch->id, width);
  return res;
}

static BtorMcLatch *
btor_find_mc_latch (BtorMC *mc, BtorNode *node)
{
  BtorPtrHashBucket *bucket;
  BtorMcLatch *res;
  assert (mc);
  assert (node);
  bucket = btor_find_in_ptr_hash_table (mc->latches, node);
  if (!bucket) return 0;
  res = bucket->data.asPtr;
  assert (res->node == bucket->key);
  return res;
}

void
boolector_next (BtorMC *mc, BtorNode *node, BtorNode *next)
{
  BtorMcLatch *latch;
  Btor *btor;
  assert (mc);
  assert (node);
  assert (next);
  btor = mc->btor;
  assert (btor_get_exp_len (btor, node) == btor_get_exp_len (btor, next));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->next);
  latch->next = btor_copy_exp (mc->btor, next);
  btor_msg_mc (mc, 2, "adding NEXT latch%d", latch->id);
}

void
boolector_init (BtorMC *mc, BtorNode *node, BtorNode *init)
{
  BtorMcLatch *latch;
  Btor *btor;
  assert (mc);
  assert (node);
  assert (init);
  btor = mc->btor;
  assert (btor_get_exp_len (btor, node) == btor_get_exp_len (btor, init));
  latch = btor_find_mc_latch (mc, node);
  assert (latch);
  assert (latch->node == node);
  assert (!latch->init);
  latch->init = btor_copy_exp (mc->btor, init);
  btor_msg_mc (mc, 2, "adding INIT latch%d", latch->id);
}

int
boolector_bad (BtorMC *mc, BtorNode *bad)
{
  int res;
  assert (mc);
  res = BTOR_COUNT_STACK (mc->bad);
  (void) btor_copy_exp (mc->btor, bad);
  BTOR_PUSH_STACK (mc->btor->mm, mc->bad, bad);
  btor_msg_mc (mc, 2, "adding BAD property%d", res);
  return res;
}

int
boolector_bmc (BtorMC *mc, int maxk)
{
  return -1;
}

char *
boolector_mc_assignment (BtorMC *mc, BtorNode *node, int time)
{
  assert (mc);
  assert (node);
  assert (0 <= time);
  return 0;
}

void
boolector_free_mc_assignment (BtorMC *mc, char *assignment)
{
  assert (mc);
  assert (assignment);
  btor_freestr (mc->btor->mm, assignment);
}
