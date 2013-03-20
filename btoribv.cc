#include "btoribv.h"

struct BtorIBVNode
{
  unsigned id;
  unsigned width;
  BtorNode* exp;
  char* name;   // for variables
  char* value;  // for constants
};

BtorIBV::BtorIBV (Btor* b) : btor (b)
{
  BTOR_PUSH_STACK (btor->mm, id2node, 0);  // Assume '0' invalid id.
}

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
  assert (id > 0);
  BTOR_FIT_STACK (btor->mm, id2node, id);
  assert (!BTOR_PEEK_STACK (id2node, id));
  BTOR_POKE_STACK (id2node, id, node);
}
