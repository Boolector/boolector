#include "btoribv.h"

#include <cstdarg>
#include <cstdio>
#include <cstring>

void
BtorIBV::msg (int level, const char *fmt, ...)
{
  va_list ap;
  if (level > verbosity) return;
  fputs ("[btoribv] ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

void
BtorIBV::wrn (const char *fmt, ...)
{
  va_list ap;
  fputs ("[btoribv] *** WARNING *** ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

BtorIBV::BtorIBV (Btor *b) : btor (b) {}

void
BtorIBV::delete_ibv_variable (BtorIBVNode *node)
{
  assert (node);
  assert (!node->is_constant);
  assert (node->name);
  btor_freestr (btor->mm, node->name);
  for (BtorIBVAssignment *a = node->assignments.start;
       a < node->assignments.top;
       a++)
  {
    size_t bytes = a->nranges * sizeof *a->ranges;
    btor_free (btor->mm, a->ranges, bytes);
  }
  BTOR_RELEASE_STACK (btor->mm, node->assignments);
  for (BtorIBVRangeName *r = node->ranges.start; r < node->ranges.top; r++)
    btor_freestr (btor->mm, r->name);
  BTOR_RELEASE_STACK (btor->mm, node->ranges);
  btor_free (btor->mm, node->assigned, node->width);
  btor_free (btor->mm, node->marked, node->width);
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
  node->assigned         = (signed char *) btor_malloc (btor->mm, node->width);
  node->marked           = (signed char *) btor_malloc (btor->mm, node->width);
  memset (node->assigned, 0, node->width);
  memset (node->marked, 0, node->width);
  BTOR_INIT_STACK (node->ranges);
  BTOR_INIT_STACK (node->assignments);
  msg (1, "added variable %s of width %u", node->name, width);
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
  BtorIBVRangeName rn;
  rn.from.msb = fmsb, rn.from.lsb = flsb;
  rn.to.msb = br.m_nMsb, rn.to.lsb = br.m_nLsb;
  rn.name = btor_strdup (btor->mm, name.c_str ());
  BTOR_PUSH_STACK (btor->mm, node->ranges, rn);
  assert (node->name);
  msg (1,
       "added external range %s[%u..%u] mapped to %s[%u..%u]",
       rn.name,
       rn.from.msb,
       rn.from.lsb,
       node->name,
       rn.to.msb,
       rn.to.lsb);
}

void
BtorIBV::addUnary (BtorIBVTag tag, BitRange o, BitRange a)
{
  assert (tag & BTOR_IBV_IS_UNARY);
  assert ((tag & ~BTOR_IBV_IS_PREDICATE) <= BTOR_IBV_MAX_UNARY);
  assert (o.getWidth () == a.getWidth ());
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  check_bit_range (a);
  BtorIBVRange *r =
      (BtorIBVRange *) btor_malloc (btor->mm, 1 * sizeof (BtorIBVRange));
  r[0] = a;
  BtorIBVAssignment assignment (tag, o.m_nMsb, o.m_nLsb, 0, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
}

void
BtorIBV::addBinary (BtorIBVTag tag, BitRange o, BitRange a, BitRange b)
{
  assert (tag & BTOR_IBV_IS_BINARY);
  assert ((tag & ~BTOR_IBV_IS_PREDICATE) <= BTOR_IBV_MAX_BINARY);
  assert (a.getWidth () == b.getWidth ());
  if (tag & BTOR_IBV_IS_PREDICATE)
    assert (o.getWidth () == 1);
  else
    assert (o.getWidth () == a.getWidth ());
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  check_bit_range (a), check_bit_range (b);
  BtorIBVRange *r =
      (BtorIBVRange *) btor_malloc (btor->mm, 2 * sizeof (BtorIBVRange));
  r[0] = a, r[1] = b;
  BtorIBVAssignment assignment (tag, o.m_nMsb, o.m_nLsb, 0, 2, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
}

void
BtorIBV::addCondition (BitRange o, BitRange c, BitRange t, BitRange e)
{
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  check_bit_range (c), check_bit_range (t), check_bit_range (e);
  assert (t.getWidth () == e.getWidth ());
  assert (o.getWidth () == t.getWidth ());
  unsigned cw  = c.getWidth ();
  bool bitwise = (cw != 1);
  if (bitwise) assert (t.getWidth () == cw);
  BtorIBVTag tag = BTOR_IBV_COND;
  if (!bitwise) tag = (BtorIBVTag) (tag | BTOR_IBV_IS_PREDICATE);
  BtorIBVRange *r =
      (BtorIBVRange *) btor_malloc (btor->mm, 3 * sizeof (BtorIBVRange));
  r[0] = c, r[1] = t, r[2] = e;
  BtorIBVAssignment assignment (tag, o.m_nMsb, o.m_nLsb, 0, 3, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
}

void
BtorIBV::mark_assigned (BtorIBVNode *n, BitRange r)
{
  assert (n);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (2, "assigning %s[%u]", n->name, i);
    assert (!n->assigned[i]);
    n->assigned[i] = 1;
  }
}
