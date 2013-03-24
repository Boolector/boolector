#include "btoribv.h"

#include <string.h>

BtorIBV::BtorIBV (Btor *b) : btor (b)
{
  BTOR_PUSH_STACK (btor->mm, id2node, 0);  // Assume '0' invalid id.
}

void
BtorIBV::delete_ibv_var (BtorIBVariable *var)
{
  assert (var);
  assert (var->name);
  btor_freestr (btor->mm, var->name);
  // TODO delete assignments
  // TODO delete ranges
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
  while (!BTOR_EMPTY_STACK (id2node))
  {
    BtorIBVNode *node = BTOR_POP_STACK (id2node);
    if (node) delete_ibv_node (node);
  }
  BTOR_RELEASE_STACK (btor->mm, id2node);
}

BtorIBVNode *
BtorIBV::new_node (unsigned id, BtorIBVTag tag, unsigned width, BtorNode *exp)
{
  assert (id > 0);
  BTOR_FIT_STACK (btor->mm, id2node, id);
  assert (!BTOR_PEEK_STACK (id2node, id));
  BtorIBVNode *node = (BtorIBVNode *) btor_malloc (btor->mm, sizeof *node);
  node->id          = id;
  node->tag         = tag;
  node->width       = width;
  node->exp         = exp;
  node->var         = 0;
  BTOR_POKE_STACK (id2node, id, node);
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
  BTOR_FIT_STACK (btor->mm, id2node, id);
  assert (!BTOR_PEEK_STACK (id2node, id));
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

unsigned
BtorIBV::id2width (unsigned id)
{
  assert (0 < id);
  BtorIBVNode *node = BTOR_PEEK_STACK (id2node, id);
  assert (node);
  return node->width;  // could as well just return 'node->exp->width'
}
