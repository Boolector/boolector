#include "btoribv.h"

#include <string.h>

BtorIBV::BtorIBV (Btor *b) : btor (b) {}

void
BtorIBV::delete_ibv_variable (BtorIBVNode *node)
{
  assert (node);
  assert (!node->is_constant);
  assert (node->name);
  btor_freestr (btor->mm, node->name);
  BTOR_RELEASE_STACK (btor->mm, node->assignments);
  for (BtorIBVRangeName *rn = node->ranges.start; rn < node->ranges.top; rn++)
    btor_freestr (btor->mm, rn->name);
  BTOR_RELEASE_STACK (btor->mm, node->ranges);
  btor_free (btor->mm, node, sizeof *node);
}

static size_t
btor_ibv_constant_bytes ()
{
  return (size_t) & (((BtorIBVNode *) 0)->name);
}

void
BtorIBV::delete_ibv_constant (BtorIBVNode *node)
{
  assert (node);
  assert (node->is_constant);
  assert (node->cached);
  btor_release_exp (btor, node->cached);
  btor_free (btor->mm, node, btor_ibv_constant_bytes ());
}

void
BtorIBV::delete_ibv_node (BtorIBVNode *node)
{
  assert (node);
  if (node->cached) btor_release_exp (btor, node->cached);
  if (node->is_constant)
    delete_ibv_constant (node);
  else
    delete_ibv_variable (node);
}

BtorIBV::~BtorIBV ()
{
  while (!BTOR_EMPTY_STACK (idtab))
  {
    BtorIBVNode *node = BTOR_POP_STACK (idtab);
    if (node) delete_ibv_node (node);
  }
  BTOR_RELEASE_STACK (btor->mm, idtab);
}

BtorIBVNode *
BtorIBV::new_node (unsigned id, bool is_constant, unsigned width)
{
  assert (id > 0);
  BTOR_FIT_STACK (btor->mm, idtab, id);
  assert (!BTOR_PEEK_STACK (idtab, id));
  size_t bytes =
      is_constant ? btor_ibv_constant_bytes () : sizeof (BtorIBVNode);
  BtorIBVNode *node = (BtorIBVNode *) btor_malloc (btor->mm, bytes);
  memset (node, 0, bytes);
  node->id          = id;
  node->is_constant = is_constant;
  node->width       = width;
  node->cached      = 0;
  BTOR_POKE_STACK (idtab, id, node);
  return node;
}

void
BtorIBV::addConstant (unsigned id, const string &str, unsigned width)
{
  BtorIBVNode *node;
  assert (str.size () == width);
  node         = new_node (id, true, width);
  node->cached = btor_const_exp (btor, str.c_str ());
}

void
BtorIBV::addVariable (unsigned id,
                      const string &str,
                      unsigned width,
                      bool isNextState,
                      bool isLoopBreaking,
                      bool isStateRetain,
                      IBitVector::DirectionKind direction)
{
  assert (id > 0);
  BTOR_FIT_STACK (btor->mm, idtab, id);
  assert (!BTOR_PEEK_STACK (idtab, id));
  BtorIBVNode *node      = new_node (id, false, width);
  node->name             = btor_strdup (btor->mm, str.c_str ());
  node->is_next_state    = isNextState;
  node->is_loop_breaking = isLoopBreaking;
  node->is_state_retain  = isStateRetain;
  node->direction        = direction;
  BTOR_INIT_STACK (node->ranges);
  BTOR_INIT_STACK (node->assignments);
}

void
BtorIBV::addRangeName (IBitVector::BitRange br,
                       const string &name,
                       unsigned fmsb,
                       unsigned flsb)
{
  assert (br.m_nLsb <= br.m_nMsb);
  assert (flsb <= fmsb);
  assert (fmsb - flsb == (br.m_nMsb - br.m_nLsb));
  BtorIBVNode *node = id2node (br.m_nId);
  assert (!node->is_constant);
  BtorIBVRangeName rn;
  rn.from.msb = fmsb, rn.from.lsb = flsb;
  rn.to.msb = br.m_nMsb, rn.to.lsb = br.m_nLsb;
  rn.name = btor_strdup (btor->mm, name.c_str ());
  BTOR_PUSH_STACK (btor->mm, node->ranges, rn);
}

void
BtorIBV::addBinOp (IBitVector::BitRange o,
                   IBitVector::BitRange a,
                   IBitVector::BitRange b,
                   BtorIBVBinOp op)
{
  assert (o.getWidth () == a.getWidth ());
  assert (o.getWidth () == b.getWidth ());
  BtorIBVNode *on = bitrange2node (o);
  BtorIBVNode *an = bitrange2node (a);
  BtorIBVNode *bn = bitrange2node (b);
}
