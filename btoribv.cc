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
  BtorIBVNode *on = id2node (a.id);
  printf ("%s[%u..%u] = ", on->name, a.msb, a.lsb);
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
      printf (" %s[%u..%u]", in->name, r->msb, r->lsb);
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
}

void
BtorIBV::delete_ibv_variable (BtorIBVNode *node)
{
  assert (node);
  assert (!node->is_constant);
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
  btor_free (btor->mm, node->state, node->width);
  btor_free (btor->mm, node, sizeof *node);
}

static size_t
btor_ibv_constant_bytes ()
{
  return (size_t) & (((BtorIBVNode *) 0)->is_next_state);
}

void
BtorIBV::delete_ibv_constant (BtorIBVNode *node)
{
  assert (node);
  assert (node->is_constant);
  btor_free (btor->mm, node, btor_ibv_constant_bytes ());
}

void
BtorIBV::delete_ibv_node (BtorIBVNode *node)
{
  assert (node);
  assert (node->name);
  btor_freestr (btor->mm, node->name);
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
BtorIBV::new_node (unsigned id, bool is_constant, unsigned width)
{
  assert (0 < id);
  assert (0 < width);
  while (BTOR_COUNT_STACK (idtab) <= id) BTOR_PUSH_STACK (btor->mm, idtab, 0);
  assert (!BTOR_PEEK_STACK (idtab, id));
  size_t bytes =
      is_constant ? btor_ibv_constant_bytes () : sizeof (BtorIBVNode);
  BtorIBVNode *node = (BtorIBVNode *) btor_malloc (btor->mm, bytes);
  memset (node, 0, bytes);
  node->id          = id;
  node->is_constant = is_constant;
  node->width       = width;
  node->cached      = 0;
  node->name        = 0;
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
  node         = new_node (id, true, width);
  node->cached = btor_const_exp (btor, str.c_str ());
  node->name   = btor_strdup (btor->mm, str.c_str ());
  msg (1, "added constant %s of width %u", str.c_str (), width);
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
  BtorIBVNode *n      = new_node (id, false, width);
  n->name             = btor_strdup (btor->mm, str.c_str ());
  n->is_next_state    = isNextState;
  n->is_loop_breaking = isLoopBreaking;
  n->is_state_retain  = isStateRetain;
  n->direction        = direction;
  n->marked           = 0;
  n->assigned         = (signed char *) btor_malloc (btor->mm, n->width);
  n->state            = (signed char *) btor_malloc (btor->mm, n->width);
  memset (n->assigned, 0, n->width);
  memset (n->state, 0, n->width);
  BTOR_INIT_STACK (n->ranges);
  BTOR_INIT_STACK (n->assignments);
  const char *extra;
  switch ((isNextState << 2) | (isLoopBreaking << 1) | isStateRetain)
  {
    case 4 | 2 | 1: extra = " (flags: next,loopbrk,retain)"; break;
    case 4 | 2 | 0: extra = " (flags: next,loopbrk)"; break;
    case 4 | 0 | 1: extra = " (flags: next,retain)"; break;
    case 4 | 0 | 0: extra = " (flags: next)"; break;
    case 0 | 2 | 1: extra = " (flags: loopbrk,retain)"; break;
    case 0 | 2 | 0: extra = " (flags: loopbrk)"; break;
    case 0 | 0 | 1: extra = " (flags: retain)"; break;
    default: extra = "(no flags)"; break;
  }
  msg (1, "id %u variable '%s[%u..0]' %s", n->id, n->name, width - 1, extra);
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
  msg (1,
       "id %u range '%s[%u..%u]' mapped to '%s[%u..%u]'",
       n->id,
       rn.name,
       rn.from.msb,
       rn.from.lsb,
       n->name,
       rn.to.msb,
       rn.to.lsb);
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
    msg (2, "id %u assigning '%s[%u]'", n->id, n->name, i);
    assert (!n->assigned[i]);
    n->assigned[i] = 1;
  }
}

void
BtorIBV::mark_state (BtorIBVNode *n, BitRange r, int mark)
{
  assert (mark == -1 || mark == 1);
  assert (n);
  assert (!n->is_constant);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (unsigned i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    msg (2, "id %u 'next %s[%u]'", n->id, n->name, i);
    assert (!n->state[i]);
    n->state[i] = mark;
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
  mark_assigned (on, o);
  check_bit_range (a);
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, sizeof *r);
  r[0]            = a;
  BtorIBVAssignment assignment (tag, on->id, o.m_nMsb, o.m_nLsb, 0, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (1, assignment, "id %u unary assignment", on->id);
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
  check_bit_range (a);
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, sizeof *r);
  r[0]            = a;
  BtorIBVAssignment assignment (tag, on->id, o.m_nMsb, o.m_nLsb, arg, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (1, assignment, "id %u unary assignment (with argument)", on->id);
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
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, 2 * sizeof *r);
  r[0] = a, r[1] = b;
  BtorIBVAssignment assignment (tag, on->id, o.m_nMsb, o.m_nLsb, 0, 2, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (1, assignment, "id %u binary assignment", on->id);
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
  BtorIBVTag tag  = bitwise ? BTOR_IBV_CONDBW : BTOR_IBV_COND;
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, 3 * sizeof *r);
  r[0] = c, r[1] = t, r[2] = e;
  BtorIBVAssignment assignment (tag, on->id, o.m_nMsb, o.m_nLsb, 0, 3, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, assignment);
  msg (1, assignment, "id %u %scondition", on->id, bitwise ? "bitwise " : "");
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
    BitRange r = *it;
    check_bit_range (r);
    assert (on->width >= r.getWidth ());
    assert (on->width - r.getWidth () >= sum);
    sum += r.getWidth ();
    n++;
  }
  assert (on->width == sum);
  assert (n > 0);
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, n * sizeof *r);
  unsigned i      = 0;
  for (it = ops.begin (); it != ops.end (); it++) r[i++] = *it;
  assert (i == n);
  BtorIBVAssignment a (BTOR_IBV_CONCAT, on->id, o.m_nMsb, o.m_nLsb, 0, n, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (1, a, "id %u %u-ary concatination", on->id, n);
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
      check_bit_range (c);
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
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, 2 * n * sizeof *r);
  unsigned i      = 0;
  for (it = ops.begin (); it != ops.end (); it++) r[i++] = *it++, r[i++] = *it;
  assert (i == 2 * n);
  BtorIBVAssignment a (tag, on->id, o.m_nMsb, o.m_nLsb, 0, 2 * n, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (1, a, "id %u %u-ary case", on->id, n);
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
  // TODO: failed in 'toy_multibit_clock' and 'toy_clock'
  // assert (nextn->is_constant || nextn->is_next_state);
  assert (next.getWidth () == o.getWidth ());
  if (!nextn->is_constant && nextn->is_next_state) mark_state (nextn, o, 1);
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, 2 * sizeof *r);
  r[0] = init, r[1] = next;
  BtorIBVAssignment a (BTOR_IBV_STATE, on->id, o.m_nMsb, o.m_nLsb, 0, 2, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (1, a, "id %u state", on->id);
}

void
BtorIBV::addNonState (BitRange o, BitRange next)
{
  BtorIBVNode *on = bitrange2node (o);
  assert (!on->is_constant);
  assert (!on->is_next_state);
  BtorIBVNode *nextn = bitrange2node (next);
  assert (nextn->is_constant || nextn->is_next_state);
  if (!nextn->is_constant && nextn->is_next_state) mark_state (nextn, o, -1);
  assert (next.getWidth () == o.getWidth ());
  BtorIBVRange *r = (BtorIBVRange *) btor_malloc (btor->mm, sizeof *r);
  r[0]            = next;
  BtorIBVAssignment a (BTOR_IBV_NON_STATE, on->id, o.m_nMsb, o.m_nLsb, 0, 1, r);
  BTOR_PUSH_STACK (btor->mm, on->assignments, a);
  msg (1, a, "id %u non-state", on->id);
}

void
BtorIBV::addAssertion (Bit r)
{
  BtorIBVBit s   = r;
  BtorIBVNode *n = id2node (s.id);
  assert (s.bit < n->width);
  BTOR_PUSH_STACK (btor->mm, assertions, s);
  msg (1, "assertion '%s[%u]'", n->name, s.bit);
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
  msg (1,
       "%sinitial assumption '%s[%u]'",
       (initial ? "" : "non-"),
       n->name,
       s.msb);
}

void
BtorIBV::check_all_next_states_assigned ()
{
  msg (1, "checking that all next states are assigned");
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    if (!n->is_next_state) continue;
    unsigned unassigned = 0;
    for (unsigned i = 0; i < n->width; i++)
      if (!n->state[i]) unassigned++;
    if (unassigned == n->width)
      wrn ("next state '%s[%u:0]' unassigned", n->name, n->width - 1);
    else if (unassigned)
      for (unsigned i = 0; i < n->width; i++)
        if (!n->state[i])
          wrn ("next state bit '%s[%u]' unassigned", n->name, i);
  }
}

void
BtorIBV::check_non_cyclic_assignments ()
{
  msg (1, "checking that assignments are non-cyclic");
  BtorIntStack work;
  BTOR_INIT_STACK (work);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      assert (a->id == n->id);
      BTOR_PUSH_STACK (btor->mm, work, a->id);
    }
    while (!BTOR_EMPTY_STACK (work))
    {
      unsigned id    = BTOR_TOP_STACK (work);
      BtorIBVNode *n = id2node (id);
      assert (!n->is_constant);
      if (n->marked == 1)
      {
        (void) BTOR_POP_STACK (work);
        n->marked = 2;
      }
      else if (n->marked == 2)
      {
        (void) BTOR_POP_STACK (work);
      }
      else
      {
        assert (!n->marked);
        n->marked = 1;
        // if (n->is_next_state) continue;
        for (BtorIBVAssignment *a = n->assignments.start;
             a < n->assignments.top;
             a++)
        {
          if (a->tag == BTOR_IBV_STATE) continue;
          if (a->tag == BTOR_IBV_NON_STATE) continue;
          for (BtorIBVRange *r = a->ranges; r < a->ranges + a->nranges; r++)
          {
            if (!r->id) continue;
            BtorIBVNode *m = id2node (r->id);
            if (m->is_constant) continue;
            if (m->marked == 1)
            {
              wrn ("variable %s might depend recursively on itself", m->name);
            }
            else if (m->marked != 2)
            {
              assert (!m->marked);
              BTOR_PUSH_STACK (btor->mm, work, m->id);
            }
          }
        }
      }
    }
  }
  BTOR_RELEASE_STACK (btor->mm, work);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    if (!n->marked) continue;
    assert (n->marked == 2);
    n->marked = 0;
  }
}

void
BtorIBV::translate ()
{
  struct
  {
    unsigned consts;
    struct
    {
      unsigned inputs, states;
    } current, next;
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
      unsigned assigned = 0;
      for (signed char *p = n->assigned; p < n->assigned + n->width; p++)
        if (*p) assigned++;
      assert (assigned <= n->width);
      unsigned unassigned = n->width - assigned;
      if (n->is_next_state)
      {
        if (unassigned)
          vars.next.inputs++;
        else
          vars.next.states++;
        bits.next.inputs += unassigned;
        bits.next.states += assigned;
      }
      else
      {
        if (unassigned)
          vars.current.inputs++;
        else
          vars.current.states++;
        bits.current.inputs += unassigned;
        bits.current.states += assigned;
      }
    }
  }
  msg (1, "%u constants, %u bits", vars.consts, bits.consts);
  msg (1,
       "%u current state variables, %u bits",
       vars.current.states,
       bits.current.states);
  msg (1,
       "%u next state variables, %u bits",
       vars.next.states,
       bits.next.states);
  msg (1,
       "%u current state inputs, %u bits",
       vars.current.inputs,
       bits.current.inputs);
  msg (1, "%u next state inputs, %u bits", vars.next.inputs, bits.next.inputs);
}
