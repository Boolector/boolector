#include "btoribv.h"

#include <string.h>

BtorIBV::BtorIBV (Btor *b) : btor (b) {}

void
BtorIBV::delete_ibv_var (BtorIBVariable *var)
{
  assert (var);
  assert (var->name);
  btor_freestr (btor->mm, var->name);
  BTOR_RELEASE_STACK (btor->mm, var->assignments);
  for (BtorIBVRangeName *rn = var->ranges.start; rn < var->ranges.top; rn++)
    btor_freestr (btor->mm, rn->name);
  BTOR_RELEASE_STACK (btor->mm, var->ranges);
  btor_free (btor->mm, var, sizeof *var);
}

void
BtorIBV::delete_ibv_node (BtorIBVNode *node)
{
  assert (node);
  assert (node->exp);
  btor_release_exp (btor, node->exp);
  if (node->tag == BTOR_IBV_VARIABLE) delete_ibv_var (node->var);
  btor_free (btor->mm, node, sizeof *node);
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
BtorIBV::new_node (unsigned id, BtorIBVTag tag, unsigned width, BtorNode *exp)
{
  assert (id > 0);
  BTOR_FIT_STACK (btor->mm, idtab, id);
  assert (!BTOR_PEEK_STACK (idtab, id));
  BtorIBVNode *node = (BtorIBVNode *) btor_malloc (btor->mm, sizeof *node);
  node->id          = id;
  node->tag         = tag;
  node->width       = width;
  node->exp         = exp;
  node->var         = 0;
  BTOR_POKE_STACK (idtab, id, node);
  return node;
}

void
BtorIBV::addConstant (unsigned id, const string &str, unsigned width)
{
  assert (str.size () == width);
  (void) new_node (
      id, BTOR_IBV_CONSTANT, width, btor_const_exp (btor, str.c_str ()));
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
  BtorIBVNode *node = new_node (
      id, BTOR_IBV_VARIABLE, width, btor_var_exp (btor, width, str.c_str ()));
  BtorIBVariable *var = (BtorIBVariable *) btor_malloc (btor->mm, sizeof *var);
  var->name           = btor_strdup (btor->mm, str.c_str ());
  var->is_next_state  = isNextState;
  var->is_loop_breaking = isLoopBreaking;
  var->is_state_retain  = isStateRetain;
  var->direction        = direction;
  BTOR_INIT_STACK (var->ranges);
  BTOR_INIT_STACK (var->assignments);
  node->var = var;
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
  assert (node->tag == BTOR_IBV_VARIABLE);
  BtorIBVRangeName rn;
  rn.from.msb = fmsb, rn.from.lsb = flsb;
  rn.to.msb = br.m_nMsb, rn.to.lsb = br.m_nLsb;
  rn.name = btor_strdup (btor->mm, name.c_str ());
  assert (node->var);
  BTOR_PUSH_STACK (btor->mm, node->var->ranges, rn);
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
