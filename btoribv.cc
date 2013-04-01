#include "btoribv.h"

#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstring>

extern "C" {
#include "btorabort.h"
};

static void
btoribv_msghead ()
{
  fputs ("[btoribv] ", stdout);
}

static void
btoribv_msgtail ()
{
  fputc ('\n', stdout);
  fflush (stdout);
}

void
BtorIBV::msg (int level, const char *fmt, ...)
{
  va_list ap;
  if (level > verbosity) return;
  btoribv_msghead ();
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  btoribv_msgtail ();
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

void
BtorIBV::print (const BtorIBVAssignment &a)
{
  BtorIBVNode *on = id2node (a.range.id);
  printf ("%s[%u:%u] = ", on->name, a.range.msb, a.range.lsb);
  const char *opname;
  switch (a.tag & BTOR_IBV_OPS)
  {
    case BTOR_IBV_AND: opname = "AND"; break;
    case BTOR_IBV_BUF: opname = "BUF"; break;
    case BTOR_IBV_CASE: opname = "CASE"; break;
    case BTOR_IBV_CONCAT: opname = "CONCAT"; break;
    case BTOR_IBV_COND: opname = "COND"; break;
    case BTOR_IBV_CONDBW: opname = "CONDBW"; break;
    case BTOR_IBV_DIV: opname = "DIV"; break;
    case BTOR_IBV_EQUAL: opname = "EQUAL"; break;
    case BTOR_IBV_LE: opname = "LE"; break;
    case BTOR_IBV_LEFT_SHIFT: opname = "LEFT_SHIFT"; break;
    case BTOR_IBV_LT: opname = "LT"; break;
    case BTOR_IBV_MOD: opname = "MOD"; break;
    case BTOR_IBV_MUL: opname = "MUL"; break;
    case BTOR_IBV_NON_STATE: opname = "NON_STATE"; break;
    case BTOR_IBV_NOT: opname = "NOT"; break;
    case BTOR_IBV_OR: opname = "OR"; break;
    case BTOR_IBV_PARCASE: opname = "PARCASE"; break;
    case BTOR_IBV_REPLICATE: opname = "REPLICATE"; break;
    case BTOR_IBV_RIGHT_SHIFT: opname = "RIGHT_SHIFT"; break;
    case BTOR_IBV_SIGN_EXTEND: opname = "SIGN_EXTEND"; break;
    case BTOR_IBV_STATE: opname = "STATE"; break;
    case BTOR_IBV_SUB: opname = "SUB"; break;
    case BTOR_IBV_SUM: opname = "SUM"; break;
    case BTOR_IBV_XOR: opname = "XOR"; break;
    case BTOR_IBV_ZERO_EXTEND: opname = "ZERO_EXTEND"; break;
    default:
      assert (!"UNKNOWN");
      opname = "UNKNOWN";
      break;
  }
  fputs (opname, stdout);
  if (a.tag & BTOR_IBV_IS_PREDICATE) fputs ("_PRED", stdout);
  for (unsigned i = 0; i < a.nranges; i++)
  {
    BtorIBVRange *r = a.ranges + i;
    if (r->id)
    {
      BtorIBVNode *in = id2node (r->id);
      printf (" %s[%u:%u]", in->name, r->msb, r->lsb);
    }
    else
      printf (" X");
  }
  if (a.tag & BTOR_IBV_HAS_ARG) printf (" %u", a.arg);
}

void
BtorIBV::println (const BtorIBVAssignment &a)
{
  print (a), fputc ('\n', stdout), fflush (stdout);
}

void
BtorIBV::printf3 (const char *fmt, ...)
{
  if (verbosity < 3) return;
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
}

void
BtorIBV::msg (int level, const BtorIBVAssignment &a, const char *fmt, ...)
{
  va_list ap;
  if (level > verbosity) return;
  btoribv_msghead ();
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputs (" '", stdout);
  print (a);
  fputc ('\'', stdout);
  btoribv_msgtail ();
}

BtorIBV::BtorIBV () : gentrace (false), verbosity (0)
{
  BTOR_INIT_STACK (idtab);
  BTOR_INIT_STACK (assertions);
  BTOR_INIT_STACK (assumptions);
  btormc = boolector_new_mc ();
  btor   = boolector_btor_mc (btormc);
  BTOR_CLR (&stats);
}

void
BtorIBV::delete_ibv_release_variable (BtorIBVNode *node)
{
  assert (node);
  assert (!node->is_constant);
  for (BtorIBVAssignment *a = node->assignments.start;
       a < node->assignments.top;
       a++)
  {
    BTOR_DELETEN (btor->mm, a->ranges, a->nranges);
  }
  BTOR_RELEASE_STACK (btor->mm, node->assignments);
  for (BtorIBVRangeName *r = node->ranges.start; r < node->ranges.top; r++)
    btor_freestr (btor->mm, r->name);
  BTOR_RELEASE_STACK (btor->mm, node->ranges);
  if (node->assigned) BTOR_DELETEN (btor->mm, node->assigned, node->width);
  if (node->next) BTOR_DELETEN (btor->mm, node->next, node->width);
}

void
BtorIBV::delete_ibv_node (BtorIBVNode *node)
{
  assert (node);
  assert (node->name);
  btor_freestr (btor->mm, node->name);
  if (node->cached) btor_release_exp (btor, node->cached);
  if (node->forwarded) btor_release_exp (btor, node->forwarded);
  if (!node->is_constant) delete_ibv_release_variable (node);
  BTOR_DELETEN (btor->mm, node->flags, node->width);
  BTOR_DELETE (btor->mm, node);
}

BtorIBV::~BtorIBV ()
{
  while (!BTOR_EMPTY_STACK (idtab))
  {
    BtorIBVNode *node = BTOR_POP_STACK (idtab);
    if (node) delete_ibv_node (node);
  }
  BTOR_RELEASE_STACK (btor->mm, idtab);
  BTOR_RELEASE_STACK (btor->mm, assertions);
  BTOR_RELEASE_STACK (btor->mm, assumptions);
  boolector_delete_mc (btormc);
}

void
BtorIBV::setVerbosity (int v)
{
  assert (v >= 0);
  verbosity = v;
  boolector_set_verbosity_mc (btormc, v);
}

void
BtorIBV::enableTraceGeneration ()
{
  gentrace = true;
  boolector_enable_trace_gen (btormc);
}

BtorIBVNode *
BtorIBV::new_node (unsigned id, unsigned width)
{
  assert (0 < id);
  assert (0 < width);
  while (BTOR_COUNT_STACK (idtab) <= id) BTOR_PUSH_STACK (btor->mm, idtab, 0);
  assert (!BTOR_PEEK_STACK (idtab, id));
  BtorIBVNode *node;
  BTOR_CNEW (btor->mm, node);
  node->id        = id;
  node->width     = width;
  node->cached    = 0;
  node->forwarded = 0;
  node->name      = 0;
  BTOR_CNEWN (btor->mm, node->flags, width);
  BTOR_POKE_STACK (idtab, id, node);
  return node;
}

void
BtorIBV::addConstant (unsigned id, const string &str, unsigned width)
{
  BtorIBVNode *node;
  assert (0 < id);
  assert (0 < width);  // TODO really?
  assert (str.size () == width);
  node              = new_node (id, width);
  node->cached      = btor_const_exp (btor, str.c_str ());
  node->forwarded   = boolector_copy (btor, node->cached);
  node->name        = btor_strdup (btor->mm, str.c_str ());
  node->is_constant = true;
  msg (3, "added id %u constant %s of width %u", id, str.c_str (), width);
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
  assert (0 < id);
  assert (0 < width);
  BtorIBVNode *n      = new_node (id, width);
  n->name             = btor_strdup (btor->mm, str.c_str ());
  n->is_next_state    = isNextState;
  n->is_loop_breaking = isLoopBreaking;
  n->is_state_retain  = isStateRetain;
  n->direction        = direction;
  n->marked           = 0;
  BTOR_INIT_STACK (n->ranges);
  BTOR_INIT_STACK (n->assignments);
  const char *extra;
  switch ((isNextState << 2) | (isLoopBreaking << 1) | isStateRetain)
  {
    case 4 | 2 | 1: extra = " next loopbrk retain"; break;
    case 4 | 2 | 0: extra = " next loopbrk"; break;
    case 4 | 0 | 1: extra = " next retain"; break;
    case 4 | 0 | 0: extra = " next"; break;
    case 0 | 2 | 1: extra = " loopbrk retain"; break;
    case 0 | 2 | 0: extra = " loopbrk"; break;
    case 0 | 0 | 1: extra = " retain"; break;
    default: extra = ""; break;
  }
  msg (3, "id %u variable '%s[%u:0]'%s", n->id, n->name, width - 1, extra);
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
  BtorIBVNode *n = id2node (br.m_nId);
  BtorIBVRangeName rn;
  rn.from.msb = fmsb, rn.from.lsb = flsb;
  rn.to.msb = br.m_nMsb, rn.to.lsb = br.m_nLsb;
  rn.name = btor_strdup (btor->mm, name.c_str ());
  BTOR_PUSH_STACK (btor->mm, n->ranges, rn);
  assert (n->name);
  msg (3,
       "id %u range '%s[%u:%u]' mapped to '%s[%u:%u]'",
       n->id,
       rn.name,
       rn.from.msb,
       rn.from.lsb,
       n->name,
       rn.to.msb,
       rn.to.lsb);
}

bool
BtorIBV::mark_used (BtorIBVNode *n, unsigned i)
{
  assert (n);
  assert (i < n->width);
  if (n->flags[i].used) return 0;
  msg (3, "id %u using '%s[%u]'", n->id, n->name, i);
  n->flags[i].used = 1;
  return 1;
}

void
BtorIBV::mark_assigned (BtorIBVNode *n, BitRange r)
{
  assert (n);
  assert (!n->is_constant);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (3, "id %u assigning '%s[%u]'", n->id, n->name, i);
    if (n->flags[i].state.current)
      wrn ("id %u bit '%s[%u]' marked current of state and is now assigned",
           n->id,
           n->name,
           i);
    assert (!n->flags[i].assigned);
    n->flags[i].assigned = 1;
  }
}

void
BtorIBV::mark_current_state (BtorIBVNode *n, BitRange r)
{
  assert (n);
  assert (!n->is_constant);
  assert (!n->is_next_state);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (3, "id %u current state '%s[%u]'", n->id, n->name, i);
    if (n->flags[i].assigned)
      wrn ("id %u bit '%s[%u]' assigned and now marked current state",
           n->id,
           n->name,
           i);
    assert (!n->flags[i].state.current);
    n->flags[i].state.current = 1;
  }
}

void
BtorIBV::mark_current_nonstate (BtorIBVNode *n, BitRange r)
{
  assert (n);
  assert (!n->is_constant);
  assert (!n->is_next_state);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (3, "id %u current non-state '%s[%u]'", n->id, n->name, i);
    assert (!n->flags[i].nonstate.current);
    n->flags[i].nonstate.current = 1;
  }
}

void
BtorIBV::mark_next_state (BtorIBVNode *n, BitRange r)
{
  assert (n);
  // TODO failed for 'toy_multibit_clock'
  // assert (n->is_constant || n->is_next_state);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (3, "id %u next state '%s[%u]'", n->id, n->name, i);
    assert (!n->flags[i].state.next);
    n->flags[i].state.next = 1;
  }
}

void
BtorIBV::mark_next_nonstate (BtorIBVNode *n, BitRange r)
{
  assert (n);
  // TODO failed for 'toy_multibit_clock'
  // assert (n->is_constant || n->is_next_state);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (3, "id %u next non-state '%s[%u]'", n->id, n->name, i);
    assert (!n->flags[i].nonstate.next);
    n->flags[i].nonstate.next = 1;
  }
}

void
BtorIBV::addUnary (BtorIBVTag tag, BitRange o, BitRange a)
{
  assert (tag & BTOR_IBV_IS_UNARY);
  assert ((tag & ~BTOR_IBV_IS_PREDICATE) <= BTOR_IBV_MAX_UNARY);
  if (tag == BTOR_IBV_SIGN_EXTEND || tag == BTOR_IBV_ZERO_EXTEND)
    assert (a.getWidth () <= o.getWidth ());
  else
    assert (a.getWidth () == o.getWidth ());
  BtorIBVNode *on = bitrange2node (o);
  assert (!on->is_constant);
  mark_assigned (on, o);
  BtorIBVNode *an = bitrange2node (a);
  assert (an->is_constant || an->is_constant == on->is_constant);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 1);
  r[0] = a;
  BtorIBVAssignment assignment (tag, o, 0, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (3, assignment, "id %u unary assignment", on->id);
}

void
BtorIBV::addUnaryArg (BtorIBVTag tag, BitRange o, BitRange a, unsigned arg)
{
  assert (tag & BTOR_IBV_IS_UNARY);
  switch (tag)
  {
    case BTOR_IBV_LEFT_SHIFT:
    case BTOR_IBV_RIGHT_SHIFT: assert (o.getWidth () == a.getWidth ()); break;
    default:
      assert (tag == BTOR_IBV_REPLICATE);
      assert (arg > 0);
      assert (UINT_MAX / arg >= a.getWidth ());
      assert (a.getWidth () * arg == o.getWidth ());
      break;
  }
  tag             = (BtorIBVTag) (tag | BTOR_IBV_HAS_ARG);
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  BtorIBVNode *an = bitrange2node (a);
  assert (an->is_constant || an->is_constant == on->is_constant);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 1);
  r[0] = a;
  BtorIBVAssignment assignment (tag, o, arg, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (3, assignment, "id %u unary assignment (with argument)", on->id);
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
  BtorIBVNode *an = bitrange2node (a);
  assert (an->is_constant || an->is_constant == on->is_constant);
  BtorIBVNode *bn = bitrange2node (b);
  assert (bn->is_constant || bn->is_constant == on->is_constant);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 2);
  r[0] = a, r[1] = b;
  BtorIBVAssignment assignment (tag, o, 0, 2, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (3, assignment, "id %u binary assignment", on->id);
}

void
BtorIBV::addCondition (BitRange o, BitRange c, BitRange t, BitRange e)
{
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  assert (t.getWidth () == e.getWidth ());
  assert (o.getWidth () == t.getWidth ());
  BtorIBVNode *cn = bitrange2node (c);
  assert (cn->is_constant || cn->is_constant == on->is_constant);
  BtorIBVNode *tn = bitrange2node (c);
  assert (tn->is_constant || tn->is_constant == on->is_constant);
  BtorIBVNode *en = bitrange2node (c);
  assert (en->is_constant || en->is_constant == on->is_constant);
  unsigned cw  = c.getWidth ();
  bool bitwise = (cw != 1);
  if (bitwise) assert (t.getWidth () == cw);
  BtorIBVTag tag = bitwise ? BTOR_IBV_CONDBW : BTOR_IBV_COND;
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 3);
  r[0] = c, r[1] = t, r[2] = e;
  BtorIBVAssignment assignment (tag, o, 0, 3, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (3, assignment, "id %u %scondition", on->id, bitwise ? "bitwise " : "");
}

void
BtorIBV::addConcat (BitRange o, const vector<BitRange> &ops)
{
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  unsigned n = 0, sum = 0;
  vector<BitRange>::const_iterator it;
  for (it = ops.begin (); it != ops.end (); it++)
  {
    BitRange r      = *it;
    BtorIBVNode *rn = bitrange2node (r);
    assert (rn->is_constant || rn->is_constant == on->is_constant);
    assert (on->width >= r.getWidth ());
    assert (on->width - r.getWidth () >= sum);
    sum += r.getWidth ();
    n++;
  }
  assert (on->width == sum);
  assert (n > 0);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, n);
  unsigned i = 0;
  for (it = ops.begin (); it != ops.end (); it++) r[i++] = *it;
  assert (i == n);
  BtorIBVAssignment a (BTOR_IBV_CONCAT, o, 0, n, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (3, a, "id %u %u-ary concatination", on->id, n);
}

void
BtorIBV::addCaseOp (BtorIBVTag tag, BitRange o, const vector<BitRange> &ops)
{
  assert (tag == BTOR_IBV_CASE || tag == BTOR_IBV_PARCASE);
  assert (tag & BTOR_IBV_IS_VARIADIC);
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  unsigned n = 0;
  assert (ops.begin () != ops.end ());
  vector<BitRange>::const_iterator it;
  for (it = ops.begin (); it != ops.end (); it++)
  {
    BitRange c = *it++;
    if (c.m_nId)
    {
      BtorIBVNode *cn = bitrange2node (c);
      assert (cn->is_constant || cn->is_constant == on->is_constant);
      assert (c.getWidth () == 1 || c.getWidth () == o.getWidth ());
    }
    else
      assert (it + 1 == ops.end ());
    assert (it != ops.end ());
    BitRange d = *it;
    check_bit_range (d);
    assert (d.getWidth () == o.getWidth ());
    assert (n < UINT_MAX / 2);
    n++;
  }
  assert (n > 0);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 2 * n);
  unsigned i = 0;
  for (it = ops.begin (); it != ops.end (); it++) r[i++] = *it++, r[i++] = *it;
  assert (i == 2 * n);
  BtorIBVAssignment a (tag, o, 0, 2 * n, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (3, a, "id %u %u-ary case", on->id, n);
}

void
BtorIBV::addState (BitRange o, BitRange init, BitRange next)
{
  BtorIBVNode *on = bitrange2node (o);
  assert (!on->is_constant);
  assert (!on->is_next_state);
  bool initialized = (init.m_nId != 0);
  if (initialized)
  {
    check_bit_range (init);
    assert (init.getWidth () == o.getWidth ());
  }
  BtorIBVNode *nextn = bitrange2node (next);
  // TODO: failed for 'toy_multibit_clock'
  // assert (nextn->is_constant || nextn->is_next_state);
  assert (next.getWidth () == o.getWidth ());
  mark_current_state (on, o);
  mark_next_state (nextn, next);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 2);
  r[0] = init, r[1] = next;
  BtorIBVAssignment a (BTOR_IBV_STATE, o, 0, 2, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (3, a, "id %u state", on->id);
}

void
BtorIBV::addNonState (BitRange o, BitRange next)
{
  BtorIBVNode *on = bitrange2node (o);
  assert (!on->is_constant);
  assert (!on->is_next_state);
  BtorIBVNode *nextn = bitrange2node (next);
  assert (nextn->is_constant || nextn->is_next_state);
  mark_current_nonstate (on, o);
  mark_next_nonstate (nextn, next);
  assert (next.getWidth () == o.getWidth ());
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 1);
  r[0] = next;
  BtorIBVAssignment a (BTOR_IBV_NON_STATE, o, 0, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (3, a, "id %u non-state", on->id);
}

void
BtorIBV::addAssertion (Bit r)
{
  BtorIBVBit s   = r;
  BtorIBVNode *n = id2node (s.id);
  assert (s.bit < n->width);
  BTOR_PUSH_STACK (btor->mm, assertions, s);
  msg (3, "assertion '%s[%u]'", n->name, s.bit);
}

void
BtorIBV::addAssumption (BitRange r, bool initial)
{
  assert (r.getWidth () == 1);
  BtorIBVRange s = r;
  BtorIBVAssumption a (s, initial);
  BtorIBVNode *n = id2node (s.id);
  assert (s.msb < n->width);
  BTOR_PUSH_STACK (btor->mm, assumptions, a);
  msg (3,
       "%sinitial assumption '%s[%u]'",
       (initial ? "" : "non-"),
       n->name,
       s.msb);
}

static double
percent (double a, double b)
{
  return b ? 100 * a / b : 0;
}

/*------------------------------------------------------------------------*/

struct BtorIBVBitNext
{
  BtorIBVBit bit;
  bool next;
  BtorIBVBitNext (BtorIBVBit b, bool n) : bit (b), next (n) {}
  BtorIBVBitNext (unsigned id, unsigned b, bool n) : bit (id, b), next (n) {}
};

extern "C" {
BTOR_DECLARE_STACK (IBVBitNext, BtorIBVBitNext);
};

/*------------------------------------------------------------------------*/

void
BtorIBV::analyze ()
{
  // general statistics first

  struct
  {
    unsigned consts, nonconsts;
    struct
    {
      unsigned state, nonstate;
    } assoc;
    struct
    {
      unsigned nologic, current, next, both;
    } nonstate;
  } bits, vars;
  BTOR_CLR (&bits);
  BTOR_CLR (&vars);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant)
      vars.consts++, bits.consts += n->width;
    else
    {
      vars.nonconsts++, bits.nonconsts += n->width;
      unsigned nonstate = 0, state = 0, nologic = 0, current = 0, next = 0,
               both = 0;
      for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
           a++)
      {
        if (a->tag == BTOR_IBV_STATE) state += a->range.getWidth ();
        if (a->tag == BTOR_IBV_NON_STATE)
        {
          nonstate += a->range.getWidth ();
          assert (a->nranges == 1);
          BtorIBVNode *o = id2node (a->ranges[0].id);
          for (unsigned i = a->range.lsb; i <= a->range.msb; i++)
          {
            int cass = n->flags[i].assigned;
            int nass =
                o->is_constant
                || o->flags[i - a->range.lsb + a->ranges[0].lsb].assigned;
            if (cass && nass)
              both++;
            else if (cass)
              current++;
            else if (nass)
              next++;
            else
              nologic++;
          }
        }
      }
      if (state) vars.assoc.state++, bits.assoc.state += state;
      if (nonstate) vars.assoc.nonstate++, bits.assoc.nonstate += nonstate;
      if (nologic) vars.nonstate.nologic++, bits.nonstate.nologic += nologic;
      if (current) vars.nonstate.current++, bits.nonstate.current += current;
      if (next) vars.nonstate.next++, bits.nonstate.next += next;
      if (both) vars.nonstate.both++, bits.nonstate.both += both;
    }
  }
  if (vars.consts) msg (2, "%u constants, %u bits", vars.consts, bits.consts);
  if (vars.nonconsts)
    msg (2, "%u variables, %u bits", vars.nonconsts, bits.nonconsts);
  if (vars.assoc.state)
    msg (2,
         "%u state associations, %u bits",
         vars.assoc.state,
         bits.assoc.state);
  if (vars.assoc.nonstate)
    msg (2,
         "%u non-state associations, %u bits",
         vars.assoc.nonstate,
         bits.assoc.nonstate);
  if (vars.nonstate.nologic)
    msg (2,
         "%u non-state variables with neither current nor next assignment, %u "
         "bits",
         vars.nonstate.nologic,
         bits.nonstate.nologic);
  if (vars.nonstate.current)
    msg (2,
         "%u non-state variables with only current assignment, %u bits",
         vars.nonstate.current,
         bits.nonstate.current);
  if (vars.nonstate.next)
    msg (2,
         "%u non-state variables with only next assignment, %u bits",
         vars.nonstate.next,
         bits.nonstate.next);
  if (vars.nonstate.both)
    msg (
        2,
        "%u non-state variables with both current and next assignment, %u bits",
        vars.nonstate.both,
        bits.nonstate.both);

  /*----------------------------------------------------------------------*/

  unsigned nextstatebits = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    if (!n->is_next_state) continue;
    for (unsigned i = 0; i < n->width; i++)
      BTOR_ABORT_BOOLECTOR (!n->flags[i].assigned && n->flags[i].state.next,
                            "next state '%s[%u]' unassigned",
                            n->name,
                            i);
    nextstatebits += n->width;
  }
  if (nextstatebits)
    msg (1, "all %u next state function bits are assigned", nextstatebits);

  /*----------------------------------------------------------------------*/

  unsigned sumassignedbits = 0, sumstatebits = 0, sumnonstatebits = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      for (unsigned i = a->range.lsb; i <= a->range.msb; i++)
      {
        if (a->tag == BTOR_IBV_STATE)
        {
          if (!n->next) BTOR_CNEWN (btor->mm, n->next, n->width);
          n->next[i] = a;
          sumstatebits++;
        }
        else if (a->tag == BTOR_IBV_NON_STATE)
        {
          if (!n->next) BTOR_CNEWN (btor->mm, n->next, n->width);
          n->next[i] = a;
          sumnonstatebits++;
        }
        else
        {
          if (!n->assigned) BTOR_CNEWN (btor->mm, n->assigned, n->width);
          n->assigned[i] = a;
          sumassignedbits++;
        }
      }
    }
  }
  msg (1,
       "added short-cuts to all %u assigned, %u state and %u non-state bits",
       sumassignedbits,
       sumstatebits,
       sumnonstatebits);

  /*----------------------------------------------------------------------*/

  msg (1, "determining dependencies and used bits ...");
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (unsigned i = 0; i < n->width; i++)
    {
      // constants are implicitly all reachable (and used)
      if (n->is_constant)
        n->flags[i].depends.mark = 2;
      else
        assert (!n->flags[i].depends.mark);
    }
  }
  unsigned used = 0;
  BtorIBVBitStack work;
  BTOR_INIT_STACK (work);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (unsigned i = 0; i < n->width; i++)
    {
      int mark = n->flags[i].depends.mark;
      if (mark)
      {
        assert (mark == 2);
        continue;
      }
      BTOR_PUSH_STACK (btor->mm, work, BtorIBVBit (n->id, i));
      while (!BTOR_EMPTY_STACK (work))
      {
        BtorIBVBit b   = BTOR_TOP_STACK (work);
        BtorIBVNode *o = id2node (b.id);
        mark           = o->flags[b.bit].depends.mark;
        if (mark == 2)
        {
          (void) BTOR_POP_STACK (work);
        }
        else
        {
          o->flags[b.bit].depends.mark++;
          assert (o->flags[b.bit].depends.mark <= 2);
          if (o->flags[b.bit].assigned)
          {
            assert (o->assigned);
            BtorIBVAssignment *a = o->assigned[b.bit];
            assert (a);
            assert (a->tag != BTOR_IBV_STATE);
            assert (a->tag != BTOR_IBV_NON_STATE);
            assert (b.bit >= a->range.lsb);
            bool bitwise = a->tag == BTOR_IBV_BUF || a->tag == BTOR_IBV_NOT
                           || a->tag == BTOR_IBV_OR || a->tag == BTOR_IBV_AND
                           || a->tag == BTOR_IBV_XOR
                           || a->tag == BTOR_IBV_CONDBW;
            // TODO for BTOR_IBV_CONCAT we can determine the defining bit
            // exactly and for BTOR_IBV_{ADD,SUB,MUL} more precise
            // reasoning is possible too (restrict the 'k' below to bits
            // at smaller or equal position).
            for (unsigned j = 0; j < a->nranges; j++)
            {
              BtorIBVRange r = a->ranges[j];
              if (!r.id) continue;
              assert (b.bit >= a->range.lsb);
              BtorIBVNode *m = id2node (r.id);
              for (unsigned k = 0; k < m->width; k++)
              {
                if (bitwise && k != b.bit - a->range.lsb + r.lsb) continue;
                if (mark == 1)
                {
                  assert (m->flags[k].depends.mark == 2);
                  if (mark_used (m, k)) used++;
                  if (m->flags[k].depends.next && !o->flags[b.bit].depends.next)
                  {
                    msg (3,
                         "id %u transitively next dependend '%s[%u]'",
                         m->id,
                         m->name,
                         k);
                    o->flags[b.bit].depends.next = 1;
                  }
                  if (m->flags[k].depends.current
                      && !o->flags[b.bit].depends.current)
                  {
                    msg (3,
                         "id %u transitively current dependend '%s[%u]'",
                         m->id,
                         m->name,
                         k);
                    o->flags[b.bit].depends.current = 1;
                  }
                }
                else
                {
                  assert (!mark);
                  if (!m->flags[k].depends.mark)
                  {
                    BtorIBVBit c (m->id, k);
                    BTOR_PUSH_STACK (btor->mm, work, c);
                  }
                  else if (!m->flags[k].depends.mark == 1)
                  {
                    BTOR_ABORT_BOOLECTOR (
                        m->flags[k].depends.mark != 2,
                        "can not set next/current flag for cyclic '%s[%u]'",
                        m->name,
                        k);
                  }
                  else
                    assert (m->flags[k].depends.mark == 2);
                }
              }
            }
            if (mark == 1) (void) BTOR_POP_STACK (work);
          }
          else
          {
            assert (mark == 0);
            if (o->is_next_state)
              o->flags[b.bit].depends.next = 1;
            else
              (o->flags[b.bit].depends.current) = 1;
            o->flags[b.bit].depends.mark = 2;
            (void) BTOR_POP_STACK (work);
          }
        }
      }
    }
  }
  BTOR_RELEASE_STACK (btor->mm, work);
  //
  // TODO: This is a 'quick' fix to handle 'forwarding' of assignments to
  // current non-state variables, if the corresponding next-state variable
  // is not assigned but used.  Then this assignment to the current
  // non-state variable has to 'forwarded', which means to mark all the
  // current state variables in its cone to be 'forwarded' and used.
  // The proper solution would be to implement a cone-of-influence reduction
  // which has an additional 'bit' to denote the context in which a
  // variable is used.  Then forwarding means using a current non-state
  // variable in a next context.  Even though it did not happen in the
  // examples we tried, the reverse might also be necessary, i.e.
  // 'backwarding'.
  //
  BtorIBVBitStack forward;
  BTOR_INIT_STACK (forward);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      if (a->tag != BTOR_IBV_NON_STATE) continue;
      BtorIBVRange r  = a->ranges[0];
      BtorIBVNode *rn = id2node (r.id);
      for (unsigned i = a->range.lsb; i <= a->range.msb; i++)
      {
        if (!n->flags[i].assigned) continue;
        assert (i >= a->range.lsb);
        unsigned k = i - a->range.lsb + r.lsb;
        // TODO coverage hole: have not seen the following condition.
        if (rn->flags[k].assigned) continue;
        BTOR_PUSH_STACK (btor->mm, forward, BtorIBVBit (n->id, i));
      }
    }
  }
  unsigned forwarding = 0, forwarded = 0;
  while (!BTOR_EMPTY_STACK (forward))
  {
    // TODO: conjecture: checking for cycles not necessary here.
    BtorIBVBit b    = BTOR_POP_STACK (forward);
    BtorIBVNode *bn = id2node (b.id);
    if (bn->flags[b.bit].forwarded) continue;
    if (mark_used (bn, b.bit)) used++;
    if (bn->flags[b.bit].state.current) continue;
    bn->flags[b.bit].forwarded = 1;
    if (bn->is_next_state)
    {
      assert (bn->flags[b.bit].nonstate.next);
      assert (!bn->flags[b.bit].assigned);
      msg (3, "fowarded id %u '%s[%u]'", bn->id, bn->name, b.bit);
      forwarded++;
      continue;
    }
    BtorIBVAssignment *a = 0;
    if (bn->assigned && bn->assigned[b.bit])
      a = bn->assigned[b.bit];
    else if (bn->next && bn->next[b.bit])
      a = bn->next[b.bit];
    if (!a) continue;
    assert (a->tag != BTOR_IBV_STATE);
    if (a->tag == BTOR_IBV_NON_STATE)
    {
      BtorIBVRange r = a->ranges[0];
      BtorIBVNode *m = id2node (r.id);
      unsigned k     = b.bit - a->range.lsb + r.lsb;
      assert (m->flags[k].nonstate.next);
      assert (!m->flags[k].assigned);
      msg (3, "fowarding id %u '%s[%u]'", bn->id, bn->name, b.bit);
      forwarding++;
    }
    assert (b.bit >= a->range.lsb);
    bool bitwise = a->tag == BTOR_IBV_BUF || a->tag == BTOR_IBV_NOT
                   || a->tag == BTOR_IBV_OR || a->tag == BTOR_IBV_AND
                   || a->tag == BTOR_IBV_XOR || a->tag == BTOR_IBV_CONDBW;
    // TODO ditto as above ... (search for 'bitwise')
    for (unsigned j = 0; j < a->nranges; j++)
    {
      BtorIBVRange r = a->ranges[j];
      if (!r.id) continue;
      assert (b.bit >= a->range.lsb);
      BtorIBVNode *m = id2node (r.id);
      for (unsigned k = 0; k < m->width; k++)
      {
        if (bitwise && k != b.bit - a->range.lsb + r.lsb) continue;
        if (m->flags[k].forwarded) continue;
        BtorIBVBit c (m->id, k);
        BTOR_PUSH_STACK (btor->mm, forward, c);
      }
    }
  }
  BTOR_RELEASE_STACK (btor->mm, forward);
  if (forwarded)
    msg (2, "forwarded %u non-assigned current non-state bits", forwarded);
  // assert (forwarded == forwarding);
  //
  // After determining current and next dependencies print statistics.
  //
  unsigned next = 0, current = 0, both = 0, none = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (unsigned i = 0; i < n->width; i++)
    {
      assert (n->flags[i].depends.mark == 2);
      bool fc = n->flags[i].depends.current;
      bool fn = n->flags[i].depends.next;
      if (fc && fn)
        both++;
      else if (fc)
        current++;
      else if (fn)
        next++;
      else
        none++;
    }
  }
  //
  unsigned onlyinassertions = 0;
  for (BtorIBVBit *a = assertions.start; a < assertions.top; a++)
  {
    BtorIBVNode *n = id2node (a->id);
    if (mark_used (n, a->bit)) onlyinassertions++, used++;
  }
  if (onlyinassertions)
    msg (2, "%u bits only used in assertions", onlyinassertions);
  //
  unsigned onlyinassumptions = 0;
  for (BtorIBVAssumption *a = assumptions.start; a < assumptions.top; a++)
  {
    BtorIBVNode *n = id2node (a->range.id);
    assert (a->range.msb == a->range.lsb);
    if (mark_used (n, a->range.lsb)) onlyinassumptions++, used++;
  }
  if (onlyinassumptions)
    msg (2, "%u bits only used in assumptions", onlyinassumptions);
  //
  // TODO to precisely figure out the used logic we actually would need to
  // implement a recursive cone-of-influence reduction, recursive over the
  // next state functions. For now we simply assume anything which has a
  // next state function is used, which might lead to some bits assumed to
  // be used without being actually used.
  //
  unsigned onlyinnext = 0, onlyininit = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      if (a->tag != BTOR_IBV_STATE) continue;
      for (unsigned i = a->ranges[1].lsb; i <= a->ranges[1].msb; i++)
        if (mark_used (id2node (a->ranges[1].id), i)) onlyinnext++, used++;
      if (a->ranges[0].id)
        for (unsigned i = a->ranges[0].lsb; i <= a->ranges[0].msb; i++)
          if (mark_used (id2node (a->ranges[0].id), i)) onlyininit++, used++;
    }
  }
  unsigned sum = next + current + both + none;
  if (next)
    msg (2,
         "%u bits depend transitively only on next %.0f%%",
         next,
         percent (next, sum));
  if (current)
    msg (2,
         "%u bits depend transitively only on current %.0f%%",
         current,
         percent (current, sum));
  if (both)
    msg (2,
         "%u bits depend transitively both on current and next %.0f%%",
         both,
         percent (both, sum));
  if (none)
    msg (2,
         "%u bits depend transitively neither on current nor next %.0f%%",
         none,
         percent (none, sum));
  //
  msg (2, "used %u bits", used);
  if (onlyinnext)
    msg (2, "%u bits only used in next state assignment", onlyinnext);
  if (onlyininit)
    msg (2, "%u bits only used in init state assignment", onlyininit);

  /*----------------------------------------------------------------------*/

  msg (1, "determining actual current and next inputs ...");
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (unsigned i = 0; i < n->width; i++)
      if (!n->flags[i].assigned && !n->flags[i].state.current)
        n->flags[i].input = 1;
  }
  unsigned resetcurrent = 0, resetnext = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      if (a->tag != BTOR_IBV_NON_STATE) continue;
      BtorIBVRange r = a->ranges[0];
      BtorIBVNode *o = id2node (r.id);
      for (unsigned i = a->range.lsb; i <= a->range.msb; i++)
      {
        unsigned k = i - a->range.lsb + r.lsb;
        if (n->flags[i].input)
        {
          if (o->is_constant || o->flags[k].assigned)
          {
            msg (3,
                 "next of unassigned non-state '%s[%u]' actually assigned (so "
                 "no input)",
                 n->name,
                 i);
            n->flags[i].input            = 0;
            n->flags[i].implicit.current = 1;
            resetcurrent++;
          }
        }
        if (o->flags[k].input)
        {
          if (n->flags[i].assigned)
          {
            msg (3,
                 "non-state '%s[%u]' with next '%s[%u]' actually assigned (so "
                 "no input)",
                 n->name,
                 i,
                 o->name,
                 k);
            o->flags[k].input         = 0;
            o->flags[i].implicit.next = 1;
            resetnext++;
          }
        }
      }
    }
  }
  if (resetcurrent)
    msg (2,
         "%u unassigned current non-state bits assigned in next state",
         resetcurrent);
  if (resetnext)
    msg (2,
         "%u unassigned next non-state bits assigned in current state",
         resetnext);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      if (a->tag != BTOR_IBV_NON_STATE) continue;
      BtorIBVRange r = a->ranges[0];
      BtorIBVNode *o = id2node (r.id);
      for (unsigned i = a->range.lsb; i <= a->range.msb; i++)
      {
        unsigned k = i - a->range.lsb + r.lsb;

        // ----------------------------------------------//
        // One of the main invariants of our translation //
        // ----------------------------------------------//
        //
        assert (n->flags[i].input == o->flags[k].input);

        if (n->flags[i].used && o->flags[k].used)
        {
          // used in both phases ...
        }
        else if (n->flags[i].used)
        {
          assert (!n->flags[i].onephase);
          n->flags[i].onephase = 1;
          msg (3,
               "id %u input '%s[%u]' used in one-phase (current) only",
               n->id,
               n->name,
               i);
        }
        else if (o->flags[k].used)
        {
          assert (!o->flags[k].onephase);
          o->flags[k].onephase = 1;
          msg (3,
               "id %u input '%s[%u]' used in one-phase (next) only",
               o->id,
               o->name,
               k);
        }
      }
    }
  }
  struct
  {
    struct
    {
      unsigned current, next;
    } vars, bits;
  } inputs, onephase;
  BTOR_CLR (&inputs);
  BTOR_CLR (&onephase);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    unsigned bits = 0, onephasebits = 0;
    for (unsigned i = 0; i < n->width; i++)
    {
      if (n->flags[i].input)
      {
        bits++;
        if (n->flags[i].onephase) onephasebits++;
      }
    }
    if (bits)
    {
      if (n->is_next_state)
      {
        inputs.vars.next++;
        inputs.bits.next += bits;
      }
      else
      {
        inputs.vars.current++;
        inputs.bits.current += bits;
      }
    }
    if (onephasebits)
    {
      if (n->is_next_state)
      {
        onephase.vars.next++;
        onephase.bits.next += onephasebits;
      }
      else
      {
        onephase.vars.current++;
        onephase.bits.current += onephasebits;
      }
    }
  }
  if (inputs.vars.current)
    msg (2,
         "found %u actual current inputs, %u bits",
         inputs.vars.current,
         inputs.bits.current);
  if (inputs.vars.next)
    msg (2,
         "found %u actual next inputs, %u bits",
         inputs.vars.next,
         inputs.bits.next);
  if (onephase.vars.current)
    msg (2,
         "found %u one-phase current inputs %.0f%%, %u bits %.0f%%",
         onephase.vars.current,
         percent (onephase.vars.current, inputs.vars.current),
         onephase.bits.current,
         percent (onephase.bits.current, inputs.bits.current));
  if (onephase.vars.next)
    msg (2,
         "found %u one-phase next inputs %.0f%%, %u bits %.0f%%",
         onephase.vars.next,
         percent (onephase.vars.next, inputs.vars.next),
         onephase.bits.next,
         percent (onephase.bits.next, inputs.bits.next));

  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (unsigned i = 0; i < n->width; i++)
    {
      if (verbosity > 2) btoribv_msghead ();
      printf3 ("classified id %u ", n->id);

      if (n->is_constant)
        printf3 ("constant");
      else if (n->is_next_state)
        printf3 ("next");
      else
        printf3 ("current");
      printf3 (" '%s[%u]' as", n->name, i);

      BtorIBVFlags flags = n->flags[i];

#define CLASSIFY(NAME)                \
  do                                  \
  {                                   \
    assert (!n->flags[i].classified); \
    n->flags[i].classified = NAME;    \
    printf3 (" " #NAME);              \
  } while (0)

      if (flags.used)
      {
        if (n->is_constant)
          CLASSIFY (CONSTANT);
        else if (flags.assigned)
        {
          CLASSIFY (ASSIGNED);
          assert (!flags.state.current);
          if (flags.state.next) printf3 (" next_state");
        }
        else if (flags.implicit.current)
          CLASSIFY (ASSIGNED_IMPLICIT_CURRENT);
        else if (flags.implicit.next)
          CLASSIFY (ASSIGNED_IMPLICIT_NEXT);
        else if (!flags.input)
        {
          assert (!flags.state.next);
          if (flags.state.current) CLASSIFY (CURRENT_STATE);
        }
        else
        {
          if (!flags.onephase)
            CLASSIFY (TWO_PHASE_INPUT);
          else if (n->is_next_state)
            CLASSIFY (ONE_PHASE_ONLY_NEXT_INPUT);
          else
            CLASSIFY (ONE_PHASE_ONLY_CURRENT_INPUT);
          assert (!flags.state.current);
          assert (flags.input);
        }
      }
      else
        CLASSIFY (NOT_USED);

      if (!n->flags[i].classified) printf3 (" UNCLASSIFIED");
      if (flags.nonstate.current) printf3 (" current_non_state");
      if (flags.nonstate.next) printf3 (" next_non_state");
      if (flags.forwarded) printf3 (" forwarded");
      if (verbosity > 2) btoribv_msgtail ();

      BTOR_ABORT_BOOLECTOR (
          !n->flags[i].classified, "unclassified bit %s[%u]", n->name, i);
    }
  }
}

BtorNode *
BtorIBV::translate_range (BtorIBVRange r, bool forward)
{
  if (!r.id) return 0;
  BtorIBVNode *n = id2node (r.id);
  BtorNode *exp  = forward ? n->cached : n->forwarded;
  assert (exp);
  return boolector_slice (btor, exp, (int) r.msb, (int) r.lsb);
}

BtorNode *
BtorIBV::translate_assignment (BtorIBVAssignment *a, bool forward)
{
  BtorNodePtrStack stack;
  BTOR_INIT_STACK (stack);
  for (unsigned i = 0; i < a->nranges; i++)
  {
    BtorIBVRange r = a->ranges[i];
    BtorNode *exp  = translate_range (r, forward);
    BTOR_PUSH_STACK (btor->mm, stack, exp);
  }
  BtorNode *res;
  if (a->tag & BTOR_IBV_IS_PREDICATE)
  {
    switch (a->tag)
    {
      default:
        BTOR_ABORT_BOOLECTOR (true, "predicate tag %d not handled", a->tag);
        res = 0;
        break;
    }
  }
  else
  {
    switch (a->tag)
    {
      case BTOR_IBV_BUF:
        res = boolector_copy (btor, BTOR_PEEK_STACK (stack, 0));
        break;
      case BTOR_IBV_NOT:
        res = boolector_not (btor, BTOR_PEEK_STACK (stack, 0));
        break;
      default:
        BTOR_ABORT_BOOLECTOR (true, "non-predicate tag %d not handled", a->tag);
        res = 0;
        break;
    }
  }
  while (!BTOR_EMPTY_STACK (stack))
  {
    BtorNode *exp = BTOR_POP_STACK (stack);
    if (exp) boolector_release (btor, exp);
  }
  BTOR_RELEASE_STACK (btor->mm, stack);
  return res;
}

BtorNode *
BtorIBV::translate_new_input (BtorIBVRange r, bool next)
{
  BtorIBVNode *n = id2node (r.id);
  BtorNode *res;
  char suffix[30];
  if (n->width == r.getWidth ())
  {
    assert (!r.lsb);
    assert (r.msb + 1 == n->width);
    suffix[0] = 0;
  }
  else
    sprintf (suffix, "[%u:%u]", r.msb, r.msb);
  char prefix[10];
  if (next)
    strcpy (prefix, "next(");
  else
    prefix[0] = 0;
  if (next) strcat (suffix, ")");
  int len    = strlen (prefix) + strlen (n->name) + strlen (suffix) + 1;
  char *name = (char *) btor_malloc (btor->mm, len);
  sprintf (name, "%s%s%s", suffix, n->name, suffix);
  res = boolector_latch (btormc, (int) n->width, name);
  btor_free (btor->mm, name, len);
  stats.inputs++;
  return res;
}

BtorNode *
BtorIBV::translate_new_latch (BtorIBVRange r)
{
  BtorIBVNode *n = id2node (r.id);
  BtorNode *res;
  if (n->width == r.getWidth ())
  {
    assert (!r.lsb);
    assert (r.msb + 1 == n->width);
    res = boolector_latch (btormc, (int) n->width, n->name);
  }
  else
  {
    char suffix[20];
    sprintf (suffix, "[%u:%u]", r.msb, r.msb);
    int len    = strlen (n->name) + strlen (suffix) + 1;
    char *name = (char *) btor_malloc (btor->mm, len);
    sprintf (name, "%s%s", n->name, suffix);
    res = boolector_latch (btormc, (int) n->width, name);
    btor_free (btor->mm, name, len);
  }
  stats.latches++;
  return res;
}

void
BtorIBV::translate_node (BtorIBVNode *n)
{
  assert (!n->is_constant);
  assert (!n->cached);
  assert (!n->forwarded);
  bool atleastoneforwarded = false, atleastonenotinput = false;
  for (unsigned i = 0; i <= n->width; i++)
  {
    if (n->flags[i].forwarded) atleastoneforwarded = 1;
    if (n->flags[i].classified != TWO_PHASE_INPUT
        && n->flags[i].classified != ONE_PHASE_ONLY_CURRENT_INPUT
        && n->flags[i].classified != ONE_PHASE_ONLY_NEXT_INPUT)
      atleastonenotinput = 1;
  }
  BtorNode *forwarded = 0, *cached = 0;
  unsigned msb;
  for (unsigned lsb = 0; lsb < n->width; lsb = msb + 1)
  {
    BtorIBVAssignment *a = n->assigned ? n->assigned[lsb] : 0;
    if (!a) a = n->next ? n->next[lsb] : 0;
    BtorNode *f = 0, *c = 0;
    if (a)
    {
      msb = a->range.msb;
      if (a->tag == BTOR_IBV_STATE)
      {
        assert (!atleastoneforwarded);
        c = translate_new_latch (a->range);
      }
      else if (a->tag == BTOR_IBV_NON_STATE)
      {
        BTOR_ABORT_BOOLECTOR (
            atleastonenotinput,
            "can not handle non-state bits not classified as inputs yet");
      }
      else
      {
        c = translate_assignment (a, false);
        if (atleastoneforwarded) f = translate_assignment (a, true);
      }
    }
    else
    {
      msb = n->width;
      if (n->is_next_state)
      {
        assert (!atleastoneforwarded);
        BtorIBVRange r (n->id, msb, lsb);
        c = translate_new_input (r, true);
      }
      else
      {
        BtorIBVRange r (n->id, msb, lsb);
        c = translate_new_input (r, false);
        if (atleastoneforwarded) f = translate_new_input (r, true);
      }
    }
    if (c)
    {
      BtorNode *tmp = cached;
      cached        = boolector_concat (btor, c, cached);
      boolector_release (btor, tmp);
    }
    if (f)
    {
      BtorNode *tmp = forwarded;
      forwarded     = boolector_concat (btor, f, forwarded);
      boolector_release (btor, tmp);
    }
  }
  assert (!cached || !forwarded
          || boolector_get_width (btor, cached)
                 == boolector_get_width (btor, forwarded));
  n->cached    = cached;
  n->forwarded = forwarded;
}

void
BtorIBV::translate ()
{
  BtorIBVNodePtrStack work;
  BTOR_INIT_STACK (work);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) assert (n->cached);
    unsigned i;
    for (i = 0; i < n->width; i++)
      if (n->flags[i].used) break;
    if (i == n->width) continue;
    BTOR_PUSH_STACK (btor->mm, work, n);
    n->marked = 0;
  }
  msg (1, "translating %u nodes", (unsigned) BTOR_COUNT_STACK (work));
  while (!BTOR_EMPTY_STACK (work))
  {
    BtorIBVNode *n = BTOR_TOP_STACK (work);
    if (n->cached)
    {
      assert (n->is_constant || n->marked == 2);
      BTOR_POP_STACK (work);
    }
    else if (n->marked == 1)
    {
      translate_node (n);
      assert (n->cached);
      n->marked = 2;
      BTOR_POP_STACK (work);
    }
    else
    {
      assert (!n->marked);
      n->marked = 1;
      for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
           a++)
      {
        BtorIBVNode *o = id2node (a->range.id);
        if (!o->marked) BTOR_PUSH_STACK (btor->mm, work, o);
      }
    }
  }
  BTOR_RELEASE_STACK (btor->mm, work);
  msg (2,
       "translated %u inputs, %u latches, %u nexts, %u inits",
       stats.inputs,
       stats.latches,
       stats.nexts,
       stats.inits);
}
