#include "btoribv.h"

#include <string.h>

BtorIBV::BtorIBV (Btor* b) : btor (b)
{
  BTOR_PUSH_STACK (btor->mm, id2node, 0);  // Assume '0' invalid id.
}

void
BtorIBV::delete_ibv_node (BtorIBVNode* node)
{
  assert (node);
  assert (node->exp);
  btor_release_exp (btor, node->exp);
}

BtorIBV::~BtorIBV ()
{
  while (!BTOR_EMPTY_STACK (id2node))
  {
    BtorIBVNode* node = BTOR_POP_STACK (id2node);
    if (node) delete_ibv_node (node);
  }
  BTOR_RELEASE_STACK (btor->mm, id2node);
}

void
BtorIBV::addConstant (unsigned id, const string& str, unsigned width)
{
  BtorIBVNode* node;
  assert (str.size () == width);
  assert (strlen (str.c_str ()) == width);
  BTOR_FIT_STACK (btor->mm, id2node, id);
  assert (!BTOR_PEEK_STACK (id2node, id));
  node        = (BtorIBVNode*) btor_malloc (btor->mm, sizeof *node);
  node->tag   = BTOR_IBV_CONSTANT;
  node->width = width;
  node->exp   = btor_const_exp (btor, str.c_str ());
  BTOR_PUSH_STACK (btor->mm, id2node, node);
}
