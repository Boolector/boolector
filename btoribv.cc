#include "btoribv.h"

BtorIBV::BtorIBV (Btor* b) : btor (b) {}

BtorIBV::~BtorIBV ()
{
  while (!BTOR_EMPTY_STACK (id2node))
  {
    BtorNode* node = BTOR_POP_STACK (id2node);
    if (node) btor_release_exp (btor, node);
  }
  BTOR_RELEASE_STACK (btor->mm, id2node);
}

void
BtorIBV::addBtorNode (unsigned id, BtorNode* node)
{
  BTOR_FIT_STACK (btor->mm, id2node, id);
  assert (!BTOR_PEEK_STACK (id2node, id));
  BTOR_POKE_STACK (id2node, id, node);
}
