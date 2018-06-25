/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2016 Armin Biere.
 *  Copyright (C) 2014-2018 Aina Niemetz.
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoribv.hh"
#include "btortypes.h"

#include <cinttypes>
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstring>

extern "C" {
#include "btorabort.h"
#include "btorcore.h"
#include "utils/btorutil.h"
};

#define BTORIBV_COVER(COND)                                     \
  do                                                            \
  {                                                             \
    if (!(COND)) break;                                         \
    fprintf (stderr,                                            \
             "%s:%d: in %s: Coverage target '" #COND "' hit\n", \
             __FILE__,                                          \
             __LINE__,                                          \
             __FUNCTION__);                                     \
    fflush (stderr);                                            \
    abort ();                                                   \
  } while (0)

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
BtorIBV::warn (const char *fmt, ...)
{
  va_list ap;
  if (!verbosity) return;
  btoribv_msghead ();
  fputs ("warning: ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  btoribv_msgtail ();
}

void
BtorIBV::msg (uint32_t level, const char *fmt, ...)
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

static const char *
btor_ibv_tag_to_str (BtorIBVTag tag)
{
  switch (tag & BTOR_IBV_OPS)
  {
    case BTOR_IBV_AND: return "AND";
    case BTOR_IBV_BUF: return "BUF";
    case BTOR_IBV_CASE: return "CASE";
    case BTOR_IBV_CONCAT: return "CONCAT";
    case BTOR_IBV_COND: return "COND";
    case BTOR_IBV_CONDBW: return "CONDBW";
    case BTOR_IBV_DIV: return "DIV";
    case BTOR_IBV_EQUAL: return "EQUAL";
    case BTOR_IBV_LE: return "LE";
    case BTOR_IBV_LEFT_SHIFT: return "LEFT_SHIFT";
    case BTOR_IBV_LT: return "LT";
    case BTOR_IBV_MOD: return "MOD";
    case BTOR_IBV_MUL: return "MUL";
    case BTOR_IBV_NON_STATE: return "NON_STATE";
    case BTOR_IBV_NOT: return "NOT";
    case BTOR_IBV_OR: return "OR";
    case BTOR_IBV_PARCASE: return "PARCASE";
    case BTOR_IBV_REPLICATE: return "REPLICATE";
    case BTOR_IBV_RIGHT_SHIFT: return "RIGHT_SHIFT";
    case BTOR_IBV_SIGN_EXTEND: return "SIGN_EXTEND";
    case BTOR_IBV_STATE: return "STATE";
    case BTOR_IBV_SUB: return "SUB";
    case BTOR_IBV_SUM: return "SUM";
    case BTOR_IBV_XOR: return "XOR";
    case BTOR_IBV_ZERO_EXTEND: return "ZERO_EXTEND";
    default: assert (!"UNKNOWN"); return "UNKNOWN";
  }
}

void
BtorIBV::print (const BtorIBVAssignment &a)
{
  BtorIBVNode *on = id2node (a.range.id);
  printf ("%s[%u:%u] = ", on->name, a.range.msb, a.range.lsb);
  const char *opname = btor_ibv_tag_to_str (a.tag);
  fputs (opname, stdout);
  if (a.tag & BTOR_IBV_IS_PREDICATE) fputs ("_PRED", stdout);
  for (uint32_t i = 0; i < a.nranges; i++)
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
BtorIBV::msg (uint32_t level, const BtorIBVAssignment &a, const char *fmt, ...)
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

BtorIBV::BtorIBV () : state (BTOR_IBV_START), gentrace (false), verbosity (0)
{
  btormc = boolector_mc_new ();
  btor   = boolector_mc_get_btor (btormc);
  BTOR_CLR (&stats);
  BTOR_INIT_STACK (btor->mm, idtab);
  BTOR_INIT_STACK (btor->mm, assertions);
  BTOR_INIT_STACK (btor->mm, assumptions);
}

void
BtorIBV::delete_ibv_release_variable (BtorIBVNode *node)
{
  assert (node);

  for (BtorIBVAssignment *a = node->assignments.start;
       a < node->assignments.top;
       a++)
    BTOR_DELETEN (btor->mm, a->ranges, a->nranges);
  BTOR_RELEASE_STACK (node->assignments);

  for (BtorIBVAtom *a = node->atoms.start; a < node->atoms.top; a++)
  {
    if (a->current.exp) boolector_release (btor, a->current.exp);
    if (a->next.exp) boolector_release (btor, a->next.exp);
  }
  BTOR_RELEASE_STACK (node->atoms);

  for (BtorIBVRangeName *r = node->ranges.start; r < node->ranges.top; r++)
    btor_mem_freestr (btor->mm, r->name);
  BTOR_RELEASE_STACK (node->ranges);

  if (node->assigned) BTOR_DELETEN (btor->mm, node->assigned, node->width);

  if (node->next) BTOR_DELETEN (btor->mm, node->next, node->width);

  if (node->prev) BTOR_DELETEN (btor->mm, node->prev, node->width);
}

void
BtorIBV::delete_ibv_node (BtorIBVNode *node)
{
  assert (node);
  assert (node->name);
  btor_mem_freestr (btor->mm, node->name);
  if (node->cached) boolector_release (btor, node->cached);
  delete_ibv_release_variable (node);
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
  BTOR_RELEASE_STACK (idtab);
  BTOR_RELEASE_STACK (assertions);
  BTOR_RELEASE_STACK (assumptions);
  boolector_mc_delete (btormc);
}

void
BtorIBV::setVerbosity (uint32_t v)
{
  verbosity = v;
  boolector_mc_set_opt (btormc, BTOR_MC_OPT_VERBOSITY, v);
}

void
BtorIBV::setStop (bool stop)
{
  boolector_mc_set_opt (btormc, BTOR_MC_OPT_STOP_FIRST, stop);
}

void
BtorIBV::setReachedAtBoundCallBack (
    void *state, void (*fun) (void *state, int32_t i, int32_t k))
{
  boolector_mc_set_reached_at_bound_call_back (btormc, state, fun);
}

void
BtorIBV::setStartingBoundCallBack (void *state,
                                   void (*fun) (void *state, int32_t k))
{
  boolector_mc_set_starting_bound_call_back (btormc, state, fun);
}

int32_t
BtorIBV::hasAssertionBeenViolatedAtBound (int32_t assertion_number)
{
  BTOR_ABORT (assertion_number < 0, "negative assertion number");
  BTOR_ABORT ((int32_t) BTOR_COUNT_STACK (assertions) <= assertion_number,
              "assertion number %d out of range (only added %u assertions)",
              assertion_number,
              BTOR_COUNT_STACK (assertions));
  return boolector_mc_reached_bad_at_bound (btormc, assertion_number);
}

static void
btoribv_delegate_reached_at_bound (void *ptr, int32_t i, int32_t k)
{
  assert (ptr);
  BtorIBV::ReachedAtBoundListener *listener =
      (BtorIBV::ReachedAtBoundListener *) ptr;
  listener->reachedAtBound (i, k);
}

void
BtorIBV::setReachedAtBoundListener (BtorIBV::ReachedAtBoundListener *listener)
{
  boolector_mc_set_reached_at_bound_call_back (
      btormc, listener, btoribv_delegate_reached_at_bound);
}

static void
btoribv_delegate_starting_bound (void *ptr, int32_t k)
{
  assert (ptr);
  BtorIBV::StartingBoundListener *listener =
      (BtorIBV::StartingBoundListener *) ptr;
  listener->startingBound (k);
}

void
BtorIBV::setStartingBoundListener (BtorIBV::StartingBoundListener *listener)
{
  boolector_mc_set_starting_bound_call_back (
      btormc, listener, btoribv_delegate_starting_bound);
}

void
BtorIBV::setRewriteLevel (uint32_t rwl)
{
  BTOR_ABORT (rwl < 1, "rewrite level has to be at least 1");
  BTOR_ABORT (rwl > 3, "rewrite level has to be at most 3");
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, rwl);
}

void
BtorIBV::enableTraceGeneration ()
{
  gentrace = true;
  boolector_mc_set_opt (btormc, BTOR_MC_OPT_TRACE_GEN, 1);
}

BtorIBVNode *
BtorIBV::new_node (uint32_t id, uint32_t width)
{
  assert (0 < id);
  assert (0 < width);
  while (BTOR_COUNT_STACK (idtab) <= id) BTOR_PUSH_STACK (idtab, 0);
  assert (!BTOR_PEEK_STACK (idtab, id));
  BtorIBVNode *node;
  BTOR_CNEW (btor->mm, node);
  node->id     = id;
  node->width  = width;
  node->cached = 0;
  node->name   = 0;
  BTOR_CNEWN (btor->mm, node->flags, width);
  BTOR_POKE_STACK (idtab, id, node);
  return node;
}

void
BtorIBV::addConstant (uint32_t id, const string &str, uint32_t width)
{
  BTOR_IBV_REQUIRE_START ();

  BtorIBVNode *node;
  assert (0 < id);
  assert (0 < width);  // TODO really?
  BTOR_ABORT (str.size () != width,
              "constant '%s' width %" PRId64
              " does not match width argument %u",
              str.c_str (),
              (long) str.size (),
              width);
  node = new_node (id, width);
  for (size_t i = 0; i < str.size (); i++)
    assert (str[i] == '0' || str[i] == '1' || str[i] == 'x');
  node->name        = btor_mem_strdup (btor->mm, str.c_str ());
  node->is_constant = true;
  BTOR_INIT_STACK (btor->mm, node->ranges);
  BTOR_INIT_STACK (btor->mm, node->assignments);
  BTOR_INIT_STACK (btor->mm, node->atoms);
  msg (3, "added id %u constant %s of width %u", id, str.c_str (), width);
}

void
BtorIBV::addVariable (uint32_t id,
                      const string &str,
                      uint32_t width,
                      bool isNextState,
                      BitVector::BvVariableSource src,
                      BitVector::DirectionKind direction)
{
  BTOR_IBV_REQUIRE_START ();

  assert (0 < id);
  assert (0 < width);
  BtorIBVNode *n   = new_node (id, width);
  n->name          = btor_mem_strdup (btor->mm, str.c_str ());
  n->is_next_state = isNextState;
  n->direction     = direction;
  n->source        = src;
  n->marked        = 0;
  BTOR_INIT_STACK (btor->mm, n->ranges);
  BTOR_INIT_STACK (btor->mm, n->assignments);
  BTOR_INIT_STACK (btor->mm, n->atoms);
  const char *srcstr;
  switch (src)
  {
    case NONE: srcstr = "NONE"; break;
    case STATE_RETAIN: srcstr = "STATE_RETAIN"; break;
    case INTERMEDIATE_RESULT: srcstr = "INTERMEDIATE_RESULT"; break;
    case LOOP_BREAKER: srcstr = "LOOP_BREAKER"; break;
    case PAST: srcstr = "PAST"; break;
    case CLOCK: srcstr = "CLOCK"; break;
    case CLOCK_PAST: srcstr = "CLOCK_PAST"; break;
    case CLOCK_TMP: srcstr = "CLOCK_TMP"; break;
    case CLOCK_TMP_PAST: srcstr = "CLOCK_TMP_PAST"; break;
    case DUMMY_ASSUMPTION: srcstr = "DUMMY_ASSUMPTION"; break;
    default: srcstr = "INVALID_SOURCE"; break;
  }
  const char *dirstr;
  switch (direction)
  {
    case INTERNAL: dirstr = " "; break;
    case INPUT: dirstr = "INPUT"; break;
    case OUTPUT: dirstr = "OUTPUT"; break;
    case INOUT: dirstr = "INOUT"; break;
    default: dirstr = "INVALID_DIRECTION"; break;
  }
  msg (3,
       "id %u variable '%s[%u:0]' %s %s",
       n->id,
       n->name,
       width - 1,
       srcstr,
       dirstr);
}

void
BtorIBV::addRangeName (BitVector::BitRange br,
                       const string &name,
                       uint32_t fmsb,
                       uint32_t flsb)
{
  assert (br.m_nLsb <= br.m_nMsb);
  assert (flsb <= fmsb);
  assert (fmsb - flsb == (br.m_nMsb - br.m_nLsb));
  BtorIBVNode *n = id2node (br.m_nId);
  BtorIBVRangeName rn;
  rn.from.msb = fmsb, rn.from.lsb = flsb;
  rn.to.msb = br.m_nMsb, rn.to.lsb = br.m_nLsb;
  rn.name = btor_mem_strdup (btor->mm, name.c_str ());
  BTOR_PUSH_STACK (n->ranges, rn);
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
BtorIBV::mark_used (BtorIBVNode *n, uint32_t i)
{
  assert (n);
  assert (i < n->width);
  if (n->flags[i].used) return 0;
  if (!n->used)
  {
    msg (3, "id %u using '%s' (at least one bit)", n->id, n->name);
    n->used = 1;
  }
  msg (3, "id %u using '%s[%u]'", n->id, n->name, i);
  n->flags[i].used = 1;
  return 1;
}

bool
BtorIBV::mark_coi (BtorIBVNode *n, uint32_t i)
{
  assert (n);
  assert (i < n->width);
  if (n->flags[i].coi) return 0;
  if (!n->coi)
  {
    msg (3, "id %u in COI '%s' (at least one bit)", n->id, n->name);
    n->coi = 1;
  }
  msg (3, "id %u in COI '%s[%u]'", n->id, n->name, i);
  n->flags[i].coi = 1;
  return 1;
}

void
BtorIBV::mark_assigned (BtorIBVNode *n, BitRange r)
{
  assert (n);
  assert (!n->is_constant);
  assert (r.m_nLsb <= r.m_nMsb);
  assert (r.m_nMsb < n->width);
  for (uint32_t i = r.m_nLsb; i <= r.m_nMsb; i++)
  {
    BTOR_ABORT (n->flags[i].assigned,
                "id %u node '%s[%u]' assigned twice",
                n->id,
                n->name,
                i);
    msg (3, "id %u assigning '%s[%u]'", n->id, n->name, i);
    if (n->flags[i].state.current)
      wrn ("id %u bit '%s[%u]' marked current of state and is now assigned",
           n->id,
           n->name,
           i);
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
  for (uint32_t i = r.m_nLsb; i <= r.m_nMsb; i++)
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
  for (uint32_t i = r.m_nLsb; i <= r.m_nMsb; i++)
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
  for (uint32_t i = r.m_nLsb; i <= r.m_nMsb; i++)
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
  for (uint32_t i = r.m_nLsb; i <= r.m_nMsb; i++)
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
  BTOR_PUSH_STACK (on->assignments, assignment);
  msg (3, assignment, "id %u unary assignment", on->id);
  (void) an;
}

void
BtorIBV::addUnaryArg (BtorIBVTag tag, BitRange o, BitRange a, uint32_t arg)
{
  assert (tag & (BTOR_IBV_IS_BINARY | BTOR_IBV_IS_UNARY));
  switch (tag)
  {
    case BTOR_IBV_LEFT_SHIFT:
    case BTOR_IBV_RIGHT_SHIFT: assert (o.getWidth () == a.getWidth ()); break;
    default:
      assert (tag == BTOR_IBV_REPLICATE);
      assert (arg > 0);
      assert (UINT32_MAX / arg >= a.getWidth ());
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
  BTOR_PUSH_STACK (on->assignments, assignment);
  msg (3, assignment, "id %u unary assignment (with argument)", on->id);
  (void) an;
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
#ifndef NDEBUG
  BtorIBVNode *an = bitrange2node (a);
  assert (an->is_constant || an->is_constant == on->is_constant);
  BtorIBVNode *bn = bitrange2node (b);
  assert (bn->is_constant || bn->is_constant == on->is_constant);
#endif
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 2);
  r[0] = a, r[1] = b;
  BtorIBVAssignment assignment (tag, o, 0, 2, r);
  BTOR_PUSH_STACK (on->assignments, assignment);
  msg (3, assignment, "id %u binary assignment", on->id);
}

void
BtorIBV::addCondition (BitRange o, BitRange c, BitRange t, BitRange e)
{
  BTOR_IBV_REQUIRE_START ();

  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  assert (t.getWidth () == e.getWidth ());
  assert (o.getWidth () == t.getWidth ());
  check_bit_range (c);
  check_bit_range (t);
  check_bit_range (e);
  uint32_t cw  = c.getWidth ();
  bool bitwise = (cw != 1);
  if (bitwise) assert (t.getWidth () == cw);
  BtorIBVTag tag = bitwise ? BTOR_IBV_CONDBW : BTOR_IBV_COND;
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 3);
  r[0] = c, r[1] = t, r[2] = e;
  BtorIBVAssignment assignment (tag, o, 0, 3, r);
  BTOR_PUSH_STACK (on->assignments, assignment);
  msg (3, assignment, "id %u %scondition", on->id, bitwise ? "bitwise " : "");
}

void
BtorIBV::addConcat (BitRange o, const vector<BitRange> &ops)
{
  BTOR_IBV_REQUIRE_START ();

  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  uint32_t n = 0, sum = 0;
  vector<BitRange>::const_iterator it;
  for (it = ops.begin (); it != ops.end (); it++)
  {
    BitRange r = *it;
#ifndef NDEBUG
    BtorIBVNode *rn = bitrange2node (r);
    assert (rn->is_constant || rn->is_constant == on->is_constant);
#endif
    assert (on->width >= r.getWidth ());
    assert (on->width - r.getWidth () >= sum);
    sum += r.getWidth ();
    n++;
  }
  assert (on->width == sum);
  assert (n > 0);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, n);
  uint32_t i = 0;
  for (it = ops.begin (); it != ops.end (); it++) r[i++] = *it;
  assert (i == n);
  BtorIBVAssignment a (BTOR_IBV_CONCAT, o, 0, n, r);
  BTOR_PUSH_STACK (on->assignments, a);
  msg (3, a, "id %u %u-ary concatination", on->id, n);
}

void
BtorIBV::addCaseOp (BtorIBVTag tag, BitRange o, const vector<BitRange> &ops)
{
  assert (tag == BTOR_IBV_CASE || tag == BTOR_IBV_PARCASE);
  assert (tag & BTOR_IBV_IS_VARIADIC);
  BtorIBVNode *on = bitrange2node (o);
  mark_assigned (on, o);
  uint32_t n = 0;
  assert (ops.begin () != ops.end ());
  vector<BitRange>::const_iterator it;
  for (it = ops.begin (); it != ops.end (); it++)
  {
    BitRange c = *it++;
    if (c.m_nId)
    {
#ifndef NDEBUG
      BtorIBVNode *cn = bitrange2node (c);
      assert (cn->is_constant || cn->is_constant == on->is_constant);
      assert (c.getWidth () == 1 || c.getWidth () == o.getWidth ());
#endif
    }
    else
      assert (it + 1 == ops.end ());
    assert (it != ops.end ());
    BitRange d = *it;
    check_bit_range (d);
    assert (d.getWidth () == o.getWidth ());
    assert (n < UINT32_MAX / 2);
    n++;
  }
  assert (n > 0);
  BtorIBVRange *r;
  BTOR_NEWN (btor->mm, r, 2 * n);
  uint32_t i = 0;
  for (it = ops.begin (); it != ops.end (); it++) r[i++] = *it++, r[i++] = *it;
  assert (i == 2 * n);
  BtorIBVAssignment a (tag, o, 0, 2 * n, r);
  BTOR_PUSH_STACK (on->assignments, a);
  msg (3, a, "id %u %u-ary case", on->id, n);
}

static char
bit (const char *bits, uint32_t pos, uint32_t width)
{
  assert (pos < width);
  return bits[width - pos - 1];
}

void
BtorIBV::addState (BitRange o, BitRange init, BitRange next)
{
  BTOR_IBV_REQUIRE_START ();

  BtorIBVNode *on = bitrange2node (o);
  assert (!on->is_constant);
  assert (!on->is_next_state);
  bool initialized = (init.m_nId != 0);
  if (initialized)
  {
    assert (init.getWidth () == o.getWidth ());
    BtorIBVNode *in = bitrange2node (init);
    assert (in->is_constant);
    const char *n = in->name;
    uint32_t w    = in->width;
    assert (strlen (n) == w);
    uint32_t imsb = init.m_nMsb, ilsb = imsb;
    bool isx = (bit (n, imsb, w) != '0' && bit (n, imsb, w) != '1');
    while (ilsb > init.m_nLsb
           && (isx
               == (bit (n, ilsb - 1, w) != '0' && bit (n, ilsb - 1, w) != '1')))
      ilsb--;
    if (ilsb > init.m_nLsb)
    {
      uint32_t diff = imsb - ilsb;
      {
        BitRange lo (o.m_nId, o.m_nMsb, o.m_nMsb - diff);
        BitRange li (isx ? 0 : init.m_nId,
                     isx ? 0 : init.m_nMsb,
                     isx ? 0 : init.m_nMsb - diff);
        BitRange ln (next.m_nId, next.m_nMsb, next.m_nMsb - diff);
        addState (lo, li, ln);
      }
      {
        BitRange ro (o.m_nId, o.m_nMsb - diff - 1, o.m_nLsb);
        BitRange ri (init.m_nId, init.m_nMsb - diff - 1, init.m_nLsb);
        BitRange rn (next.m_nId, next.m_nMsb - diff - 1, next.m_nLsb);
        addState (ro, ri, rn);
      }
      return;
    }
    if (isx) init = BitRange (0, 0, 0);
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
  BTOR_PUSH_STACK (on->assignments, a);
  msg (3, a, "id %u state", on->id);
}

void
BtorIBV::addNonState (BitRange o, BitRange next)
{
  BTOR_IBV_REQUIRE_START ();

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
  BTOR_PUSH_STACK (on->assignments, a);
  msg (3, a, "id %u non-state", on->id);
}

void
BtorIBV::addAssertion (BitRange r)
{
  BTOR_IBV_REQUIRE_START ();
  assert (r.getWidth () == 1);

  BtorIBVBit s (r.m_nId, r.m_nMsb);
  BtorIBVNode *n = id2node (s.id);
  assert (s.bit < n->width);
  BTOR_PUSH_STACK (assertions, s);
  msg (3, "assertion '%s[%u]'", n->name, s.bit);
}

void
BtorIBV::addAssumption (BitRange r, bool initial)
{
  BTOR_IBV_REQUIRE_START ();

  assert (r.getWidth () == 1);
  BtorIBVRange s = r;
  BtorIBVAssumption a (s, initial);
  BtorIBVNode *n = id2node (s.id);
  assert (s.msb < n->width);
  BTOR_PUSH_STACK (assumptions, a);
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
  BtorIBVBitNext (const BtorIBVBit &b, bool n = false) : bit (b), next (n) {}
  BtorIBVBitNext (uint32_t id, uint32_t b, bool n = false)
      : bit (id, b), next (n)
  {
  }
};

extern "C" {
BTOR_DECLARE_STACK (BtorIBVBitNext, BtorIBVBitNext);
};

/*------------------------------------------------------------------------*/

static const char *
btor_ibv_classified_to_str (BtorIBVClassification c)
{
  switch (c)
  {
    default:
    case BTOR_IBV_UNCLASSIFIED: return "UNCLASSIFIED";
    case BTOR_IBV_CONSTANT: return "CONSTANT";
    case BTOR_IBV_ASSIGNED: return "ASSIGNED";
    case BTOR_IBV_ASSIGNED_IMPLICIT_CURRENT: return "ASSIGNED_IMPLICIT_CURRENT";
    case BTOR_IBV_ASSIGNED_IMPLICIT_NEXT: return "ASSIGNED_IMPLICIT_NEXT";
    case BTOR_IBV_CURRENT_STATE: return "CURRENT_STATE";
    case BTOR_IBV_TWO_PHASE_INPUT: return "TWO_PHASE_INPUT";
    case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
      return "ONE_PHASE_ONLY_CURRENT_INPUT";
    case BTOR_IBV_ONE_PHASE_ONLY_NEXT_INPUT: return "ONE_PHASE_ONLY_NEXT_INPUT";
    case BTOR_IBV_PHANTOM_CURRENT_INPUT: return "PHANTOM_CURRENT";
    case BTOR_IBV_PHANTOM_NEXT_INPUT: return "PHANTOM_NEXT";
    case BTOR_IBV_NOT_USED: return "NOT_USED";
  }
}

void
BtorIBV::analyze ()
{
  BTOR_ABORT (state == BTOR_IBV_ANALYZED,
              "can not analyze model a second time");

  BTOR_ABORT (state == BTOR_IBV_TRANSLATED,
              "can not analyze model after translation");

  assert (state == BTOR_IBV_START);

  msg (1, "starting to analyze IBV model ...");

  // general statistics first

  struct
  {
    uint32_t consts, nonconsts;
    struct
    {
      uint32_t state, nonstate;
    } assoc;
    struct
    {
      uint32_t nologic, current, next, both;
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
      uint32_t nonstate = 0, state = 0, nologic = 0, current = 0, next = 0,
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
          for (uint32_t i = a->range.lsb; i <= a->range.msb; i++)
          {
            int32_t cass = n->flags[i].assigned;
            int32_t nass =
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

  uint32_t nextstatebits = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    if (!n->is_next_state) continue;
    for (uint32_t i = 0; i < n->width; i++)
      BTOR_ABORT (
          n->flags[i].used && !n->flags[i].assigned && n->flags[i].state.next,
          "next state '%s[%u]' unassigned",
          n->name,
          i);
    nextstatebits += n->width;
  }
  if (nextstatebits)
    msg (1, "all %u next state function bits are assigned", nextstatebits);

  /*----------------------------------------------------------------------*/

  uint32_t sumassignedbits = 0, sumstatebits = 0, sumnonstatebits = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      for (uint32_t i = a->range.lsb; i <= a->range.msb; i++)
      {
        if (a->tag == BTOR_IBV_STATE)
        {
          if (!n->next) BTOR_CNEWN (btor->mm, n->next, n->width);
          assert (!n->next[i]);
          n->next[i] = a;
          assert (a->nranges == 2);
          BtorIBVNode *nextn = id2node (a->ranges[1].id);
          if (!nextn->prev) BTOR_CNEWN (btor->mm, nextn->prev, nextn->width);
          uint32_t k = i - a->range.lsb + a->ranges[1].lsb;
          assert (!nextn->prev[k]);
          nextn->prev[k] = a;
          sumstatebits++;
        }
        else if (a->tag == BTOR_IBV_NON_STATE)
        {
          if (!n->next) BTOR_CNEWN (btor->mm, n->next, n->width);
          assert (!n->next[i]);
          n->next[i] = a;
          assert (a->nranges == 1);
          BtorIBVNode *nextn = id2node (a->ranges[0].id);
          if (!nextn->prev) BTOR_CNEWN (btor->mm, nextn->prev, nextn->width);
          uint32_t k = i - a->range.lsb + a->ranges[0].lsb;
          assert (!nextn->prev[k]);
          nextn->prev[k] = a;
          sumnonstatebits++;
        }
        else
        {
          if (!n->assigned) BTOR_CNEWN (btor->mm, n->assigned, n->width);
          assert (!n->assigned[i]);
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
    for (uint32_t i = 0; i < n->width; i++)
    {
      // constants are implicitly all reachable (and used)
      if (n->is_constant)
        n->flags[i].depends.mark = 2;
      else
        assert (!n->flags[i].depends.mark);
    }
  }
  uint32_t used = 0;
  BtorIBVBitStack work;
  BTOR_INIT_STACK (btor->mm, work);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (uint32_t i = 0; i < n->width; i++)
    {
      int32_t mark = n->flags[i].depends.mark;
      if (mark)
      {
        assert (mark == 2);
        continue;
      }
      BTOR_PUSH_STACK (work, BtorIBVBit (n->id, i));
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
            //
            // TODO for BTOR_IBV_CONCAT we can determine the defining bit
            // exactly and for BTOR_IBV_{ADD,SUB,MUL} more precise
            // reasoning is possible too (restrict the 'k' below to bits
            // at smaller or equal position).
            //
            for (uint32_t j = 0; j < a->nranges; j++)
            {
              BtorIBVRange r = a->ranges[j];
              if (!r.id) continue;
              assert (b.bit >= a->range.lsb);
              if (a->tag == BTOR_IBV_COND && j)
                bitwise = true;
              else if (a->tag == BTOR_IBV_CASE)
              {
                if ((j & 1))
                  bitwise = true;
                else
                  bitwise = (r.getWidth () != 1);
              }
              BtorIBVNode *m = id2node (r.id);
              for (uint32_t k = 0; k < m->width; k++)
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
                    BTOR_PUSH_STACK (work, c);
                  }
                  else if (m->flags[k].depends.mark == 1)
                  {
                    BTOR_ABORT (
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
  BTOR_RELEASE_STACK (work);
  //
  // TODO: This is a 'quick' fix to handle 'forwarding' of assignments to
  // current non-state variables, if the corresponding next-state variable
  // is not assigned but used.  Then this assignment to the current
  // non-state variable has to be 'forwarded', which means to mark all the
  // current state variables in its cone to be 'forwarded' and used.  The
  // proper solution would be to implement a cone-of-influence reduction
  // which has an additional 'bit' to denote the context in which a variable
  // is used.  Then forwarding means using a current non-state variable in a
  // next context.  Even though it did not happen in the examples we tried,
  // the reverse might also be necessary, i.e.  'backwarding'.
  //
  BtorIBVBitStack forward;
  BTOR_INIT_STACK (btor->mm, forward);
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
      for (uint32_t i = a->range.lsb; i <= a->range.msb; i++)
      {
        if (!n->flags[i].assigned) continue;
        assert (i >= a->range.lsb);
        uint32_t k = i - a->range.lsb + r.lsb;
        // TODO coverage hole: have not seen the following condition.
        if (rn->flags[k].assigned) continue;
        BTOR_PUSH_STACK (forward, BtorIBVBit (n->id, i));
      }
    }
  }
  uint32_t forwarding = 0, forwarded = 0;
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
      msg (3, "forwarded id %u '%s[%u]'", bn->id, bn->name, b.bit);
      assert (bn->flags[b.bit].nonstate.next);
      assert (!bn->flags[b.bit].assigned);
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
#ifndef NDEBUG
      BtorIBVRange r = a->ranges[0];
      BtorIBVNode *m = id2node (r.id);
      uint32_t k     = b.bit - a->range.lsb + r.lsb;
      assert (m->flags[k].nonstate.next);
      assert (!m->flags[k].assigned);
#endif
      msg (3, "forwarding id %u '%s[%u]'", bn->id, bn->name, b.bit);
      forwarding++;
    }
    assert (b.bit >= a->range.lsb);
    bool bitwise = a->tag == BTOR_IBV_BUF || a->tag == BTOR_IBV_NOT
                   || a->tag == BTOR_IBV_OR || a->tag == BTOR_IBV_AND
                   || a->tag == BTOR_IBV_XOR || a->tag == BTOR_IBV_CONDBW;
    // TODO ditto as above ... (search for 'bitwise')
    for (uint32_t j = 0; j < a->nranges; j++)
    {
      BtorIBVRange r = a->ranges[j];
      if (!r.id) continue;
      assert (b.bit >= a->range.lsb);
      if (a->tag == BTOR_IBV_COND && j)
        bitwise = true;
      else if (a->tag == BTOR_IBV_CASE)
      {
        if ((j & 1))
          bitwise = true;
        else
          bitwise = (r.getWidth () != 1);
      }
      BtorIBVNode *m = id2node (r.id);
      for (uint32_t k = 0; k < m->width; k++)
      {
        if (bitwise && k != b.bit - a->range.lsb + r.lsb) continue;
        if (m->flags[k].forwarded) continue;
        BtorIBVBit c (m->id, k);
        BTOR_PUSH_STACK (forward, c);
      }
    }
  }
  BTOR_RELEASE_STACK (forward);
  if (forwarded)
    msg (2, "forwarded %u non-assigned current non-state bits", forwarded);
  // assert (forwarded == forwarding);
  //
  // After determining current and next dependencies print statistics.
  //
  uint32_t next = 0, current = 0, both = 0, none = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    for (uint32_t i = 0; i < n->width; i++)
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
  uint32_t onlyinassertions = 0;
  for (BtorIBVBit *a = assertions.start; a < assertions.top; a++)
  {
    BtorIBVNode *n = id2node (a->id);
    if (mark_used (n, a->bit)) onlyinassertions++, used++;
  }
  if (onlyinassertions)
    msg (2, "%u bits only used in assertions", onlyinassertions);
  //
  uint32_t onlyinassumptions = 0;
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
  uint32_t onlyinnext = 0, onlyininit = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (!n->used) continue;
    for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
         a++)
    {
      if (a->tag != BTOR_IBV_STATE) continue;
      uint32_t w = a->range.msb - a->range.lsb + 1;
      for (uint32_t i = 0; i < w; i++)
      {
        if (!n->flags[a->range.lsb + i].used) continue;
        if (mark_used (id2node (a->ranges[1].id), a->ranges[1].lsb + i))
          onlyinnext++, used++;
      }
      if (a->ranges[0].id)
        for (uint32_t i = 0; i < w; i++)
        {
          if (!n->flags[a->range.lsb + i].used) continue;
          if (mark_used (id2node (a->ranges[0].id), a->ranges[0].lsb + i))
            onlyininit++, used++;
        }
    }
  }
  uint32_t sum = next + current + both + none;
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
    for (uint32_t i = 0; i < n->width; i++)
      if (!n->flags[i].assigned && !n->flags[i].state.current)
        n->flags[i].input = 1;
  }
  uint32_t resetcurrent = 0, resetnext = 0;
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
      for (uint32_t i = a->range.lsb; i <= a->range.msb; i++)
      {
        uint32_t k = i - a->range.lsb + r.lsb;
        if (n->flags[i].input)
        {
          if (o->is_constant || o->flags[k].assigned)
          {
            msg (3,
                 "next of unassigned non-state '%s[%u]' actually assigned "
                 "(implicit current, so no input)",
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
                 "non-state '%s[%u]' with next '%s[%u]' actually assigned "
                 "(implicit next, so no input)",
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
    if (BTOR_EMPTY_STACK (n->assignments))
    {
    }
    else
    {
      for (BtorIBVAssignment *a = n->assignments.start; a < n->assignments.top;
           a++)
      {
        if (a->tag != BTOR_IBV_NON_STATE) continue;
        BtorIBVRange r = a->ranges[0];
        BtorIBVNode *o = id2node (r.id);
        for (uint32_t i = a->range.lsb; i <= a->range.msb; i++)
        {
          uint32_t k = i - a->range.lsb + r.lsb;
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
  }

  struct
  {
    struct
    {
      uint32_t current, next;
    } vars, bits;
  } inputs, onephase;
  BTOR_CLR (&inputs);
  BTOR_CLR (&onephase);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    uint32_t bits = 0, onephasebits = 0;
    for (uint32_t i = 0; i < n->width; i++)
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
    for (uint32_t i = 0; i < n->width; i++)
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

#define CLASSIFY(NAME)                        \
  do                                          \
  {                                           \
    assert (!n->flags[i].classified);         \
    n->flags[i].classified = BTOR_IBV_##NAME; \
    printf3 (" " #NAME);                      \
  } while (0)

      if (flags.used)
      {
        //
        // WARNING: this is kind of repeated in 'is_phantom_...'
        //
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
      else if (n->is_next_state && is_phantom_next (n, i))
        CLASSIFY (PHANTOM_NEXT_INPUT);
      else if (!n->is_next_state && is_phantom_current (n, i))
        CLASSIFY (PHANTOM_CURRENT_INPUT);
      else
        CLASSIFY (NOT_USED);

      if (!n->flags[i].classified) printf3 (" UNCLASSIFIED");
      if (flags.nonstate.current) printf3 (" current_non_state");
      if (flags.nonstate.next) printf3 (" next_non_state");
      if (flags.forwarded) printf3 (" forwarded");
      if (verbosity > 2) btoribv_msgtail ();

      if (n->flags[i].classified == BTOR_IBV_PHANTOM_NEXT_INPUT
          || n->flags[i].classified == BTOR_IBV_PHANTOM_CURRENT_INPUT)
        mark_used (n, i);

      BTOR_ABORT (
          !n->flags[i].classified, "unclassified bit %s[%u]", n->name, i);
    }
  }

  /*----------------------------------------------------------------------*/

  msg (1, "fixing original current state with two-phase next");

  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_next_state) continue;
    if (n->is_constant) continue;
    if (!n->next) continue;
    for (uint32_t i = 0; i < n->width; i++)
    {
      BtorIBVAssignment *na = n->next[i];
      if (!na) continue;
      if (na->tag != BTOR_IBV_STATE) continue;
      BtorIBVNode *next = id2node (na->ranges[1].id);
      assert (next);
      assert (i >= na->range.lsb);
      uint32_t k = i - na->range.lsb + na->ranges[1].lsb;
      assert (next->flags);
      assert (k < next->width);
      if (next->flags[k].classified != BTOR_IBV_TWO_PHASE_INPUT) continue;
      warn (
          "next state '%s[%u]' of current state '%s[%u]' became two-phase "
          "input",
          next->name,
          k,
          n->name,
          i);
      msg (3,
           "id %d current state '%s[%u]' reclassified as TWO_PHASE_INPUT",
           n->id,
           n->name,
           i);
      n->flags[i].classified = BTOR_IBV_TWO_PHASE_INPUT;
    }
  }

  /*----------------------------------------------------------------------*/

  msg (1, "determining actual cone-of-influence (COI) ...");

  BtorIBVBitNextStack bnwork;
  BTOR_INIT_STACK (btor->mm, bnwork);
  for (BtorIBVBit *a = assertions.start; a < assertions.top; a++)
    BTOR_PUSH_STACK (bnwork, *a);
  for (BtorIBVAssumption *a = assumptions.start; a < assumptions.top; a++)
  {
    BtorIBVNode *n = id2node (a->range.id);
    assert (a->range.msb == a->range.lsb);
    BTOR_PUSH_STACK (bnwork, BtorIBVBit (n->id, a->range.msb));
  }

  uint32_t coi = 0;
  while (!BTOR_EMPTY_STACK (bnwork))
  {
    BtorIBVBitNext bn = BTOR_POP_STACK (bnwork);
    BtorIBVBit b      = bn.bit;
    BtorIBVNode *n    = id2node (b.id);
    if (!mark_coi (n, b.bit)) continue;
    coi++;
    BtorIBVClassification c = n->flags[b.bit].classified;
    switch (c)
    {
      default:
        BTOR_ABORT (1,
                    "id %u unexpected '%s[%u]' classified as '%s' in COI",
                    b.id,
                    n->name,
                    b.bit,
                    btor_ibv_classified_to_str (c));
        break;

        // TODO need to handle this one too?
#if 0
      case BTOR_IBV_ASSIGNED_IMPLICIT_CURRENT:
#endif

      case BTOR_IBV_ASSIGNED_IMPLICIT_NEXT:
      {
        assert (n->prev);
        BtorIBVAssignment *a = n->prev[b.bit];
        assert (a);
        assert (a->tag == BTOR_IBV_NON_STATE);
        assert (a->nranges == 1);
        assert (a->ranges[0].msb >= b.bit && b.bit >= a->ranges[0].lsb);
        BtorIBVNode *prev = id2node (a->range.id);
        uint32_t k        = b.bit - a->ranges[0].lsb + a->range.lsb;
        assert (prev->id == a->range.id);
        BtorIBVBit b (prev->id, k);
        BTOR_PUSH_STACK (bnwork, b);
      }
      break;

      case BTOR_IBV_CONSTANT:
      case BTOR_IBV_TWO_PHASE_INPUT:
      case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
      case BTOR_IBV_ONE_PHASE_ONLY_NEXT_INPUT:
      case BTOR_IBV_PHANTOM_CURRENT_INPUT:
      case BTOR_IBV_PHANTOM_NEXT_INPUT: break;

      case BTOR_IBV_ASSIGNED:
      {
        assert (n->assigned);
        BtorIBVAssignment *a = n->assigned[b.bit];
        assert (a->range.msb >= b.bit && b.bit >= a->range.lsb);

        if (n->prev)
        {
          BtorIBVAssignment *pa = n->prev[b.bit];
          if (pa)
          {
            assert (pa->tag == BTOR_IBV_STATE || pa->tag == BTOR_IBV_NON_STATE);
            assert (pa->range.msb >= b.bit && b.bit >= a->range.lsb);
          }
        }

        // TODO if (n->next) ...

        switch (a->tag & BTOR_IBV_OPS)
        {
          case BTOR_IBV_AND:
          case BTOR_IBV_BUF:
          case BTOR_IBV_EQUAL:
          case BTOR_IBV_LT:
          case BTOR_IBV_LE:
          case BTOR_IBV_NOT:
          case BTOR_IBV_OR:
          case BTOR_IBV_XOR:

            for (uint32_t j = 0; j < a->nranges; j++)
            {
              uint32_t k = b.bit - a->range.lsb + a->ranges[j].lsb;
              BtorIBVBit o (a->ranges[j].id, k);
              BTOR_PUSH_STACK (bnwork, o);
            }
            break;

          case BTOR_IBV_CONCAT:
          {
            uint32_t k = b.bit - a->range.lsb, j;
            for (j = 0; j < a->nranges; j++)
            {
              uint32_t w = a->ranges[j].getWidth ();
              if (w > k) break;
              k -= w;
            }
            k += a->ranges[j].lsb;
            assert (j < a->nranges);
            BtorIBVBit o (a->ranges[j].id, k);
            BTOR_PUSH_STACK (bnwork, o);
          }
          break;

          case BTOR_IBV_SIGN_EXTEND:
          case BTOR_IBV_ZERO_EXTEND:
          {
            assert (a->nranges == 1);
            uint32_t k = b.bit - a->range.lsb;
            if (k < a->ranges[0].getWidth ())
            {
              k += a->ranges[0].lsb;
              BtorIBVBit o (a->ranges[0].id, k);
              BTOR_PUSH_STACK (bnwork, o);
            }
          }
          break;

          case BTOR_IBV_REPLICATE:
          {
            assert (a->nranges == 1);
            uint32_t k = b.bit - a->range.lsb;
            k %= a->ranges[0].getWidth ();
            k += a->ranges[0].lsb;
            BtorIBVBit o (a->ranges[0].id, k);
            BTOR_PUSH_STACK (bnwork, o);
          }
          break;

          case BTOR_IBV_CASE:
            for (uint32_t j = 0; j < a->nranges; j++)
            {
              if (!(j & 1) && !a->ranges[j].id) continue;
              uint32_t k;
              if (a->ranges[j].getWidth () == 1)
                k = a->ranges[j].lsb;
              else
                k = b.bit - a->range.lsb + a->ranges[j].lsb;
              BtorIBVBit o (a->ranges[j].id, k);
              BTOR_PUSH_STACK (bnwork, o);
            }
            break;

          case BTOR_IBV_COND:
            assert (a->nranges == 3);
            for (uint32_t j = 0; j < a->nranges; j++)
            {
              uint32_t k;
              if (!j && a->ranges[0].getWidth () == 1)
                k = a->ranges[0].lsb;
              else
                k = b.bit - a->range.lsb + a->ranges[j].lsb;
              BtorIBVBit o (a->ranges[j].id, k);
              BTOR_PUSH_STACK (bnwork, o);
            }
            break;

          case BTOR_IBV_DIV:
          case BTOR_IBV_SUB:
          case BTOR_IBV_SUM:
          case BTOR_IBV_MOD:
          case BTOR_IBV_MUL:
          case BTOR_IBV_LEFT_SHIFT:
          case BTOR_IBV_RIGHT_SHIFT:
            for (uint32_t j = 0; j < a->nranges; j++)
            {
              for (uint32_t l = a->range.lsb; l <= b.bit; l++)
              {
                uint32_t k = l - a->range.lsb + a->ranges[j].lsb;
                BtorIBVBit o (a->ranges[j].id, k);
                BTOR_PUSH_STACK (bnwork, o);
              }
            }
            break;

          default:
            BTOR_ABORT (1,
                        "id %u unexpected '%s[%u]' assignment tag '%s%s'",
                        b.id,
                        n->name,
                        b.bit,
                        btor_ibv_tag_to_str (a->tag),
                        (a->tag & BTOR_IBV_IS_PREDICATE) ? "_PRED" : "");
            break;
        }
      }
      break;

      case BTOR_IBV_CURRENT_STATE:
      {
        BtorIBVAssignment *next = n->next[b.bit];
        if (!n->next || !next)
          BTOR_ABORT (1,
                      "id %u current state '%s[%u]' without next state",
                      b.id,
                      n->name,
                      b.bit);
        assert (next->range.msb >= b.bit && b.bit >= next->range.lsb);
        {
          uint32_t k = b.bit - next->range.lsb + next->ranges[1].lsb;
          BtorIBVBit o (next->ranges[1].id, k);
          BTOR_PUSH_STACK (bnwork, o);
        }
        if (next->ranges[0].id)
        {
          uint32_t k = b.bit - next->range.lsb + next->ranges[0].lsb;
          BtorIBVBit o (next->ranges[0].id, k);
          BTOR_PUSH_STACK (bnwork, o);
        }
      }
      break;
    }
  }
  BTOR_RELEASE_STACK (bnwork);

  msg (1, "found %u bits in COI", coi);

  /*----------------------------------------------------------------------*/

  msg (1, "checking all bits in COI to be completely defined ...");

  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    if (!n->coi) continue;
    for (uint32_t i = 0; i < n->width; i++)
    {
      if (!n->flags[i].coi) continue;
      if (n->assigned && n->assigned[i]) continue;
      if (n->next && n->next[i]) continue;
      if (!n->prev || !n->prev[i])
        warn ("undefined '%s[%u]' (neither assigned, nor state, nor non-state)",
              n->name,
              i);
    }
  }

  msg (1, "finished analyzing IBV model.");
  state = BTOR_IBV_ANALYZED;
}

static void
btor_ibv_check_atom (BtorIBVNode *n, BtorIBVRange r)
{
#if 0
#ifndef NDEBUG
  assert (r.msb < n->width);
  for (uint32_t i = r.lsb + 1; i < r.msb; i++) {
    assert (n->flags[i].classified == n->flags[r.lsb].classified);
    if (n->assigned) assert (n->assigned[i] == n->assigned[r.lsb]);
    if (n->next) assert (n->next[i] == n->next[r.lsb]);
    if (n->prev) assert (n->prev[i] == n->prev[r.lsb]);
  }
#else
  (void) n, (void) r;
#endif
#else
  (void) n, (void) r;
#endif
}

static void
btor_ibv_check_atoms (BtorIBVNode *n)
{
#if 0
#ifndef NDEBUG
  BtorIBVAtom * last = 0;
  assert (!BTOR_EMPTY_STACK (n->atoms));
  for (BtorIBVAtom * a = n->atoms.start; a < n->atoms.top; a++) {
    if (last) assert (a->range.lsb == last->range.msb + 1);
    else assert (!a->range.lsb);
    last = a;
  }
  assert (last);
  assert (last->range.msb + 1 == n->width);
#else
  (void) n;
#endif
#else
  (void) n;
#endif
}

static bool
overlaps (BtorIBVRange a, BtorIBVRange b)
{
  if (a.msb < b.lsb) return false;
  if (a.lsb > b.msb) return false;
  return true;
}

bool
BtorIBV::is_relevant_atom_for_assigned_atom (BtorIBVAtom *lhs,
                                             uint32_t i,
                                             BtorIBVAtom *rhs,
                                             BtorIBVAssignment *ass)
{
  assert (ass->range.id == lhs->range.id);
  assert (i < ass->nranges);
  assert (rhs->range.id == ass->ranges[i].id);

  BtorIBVRange r (rhs->range.id,
                  lhs->range.msb - ass->range.lsb + ass->ranges[i].lsb,
                  lhs->range.lsb - ass->range.lsb + ass->ranges[i].lsb);

  switch ((int32_t) (ass->tag))
  {
    case BTOR_IBV_BUF:
    case BTOR_IBV_NOT:
    case BTOR_IBV_ZERO_EXTEND: assert (!i); return overlaps (r, rhs->range);

    case BTOR_IBV_AND:
    case BTOR_IBV_DIV:
    case BTOR_IBV_LE:
    case BTOR_IBV_LE | BTOR_IBV_IS_PREDICATE:
    case BTOR_IBV_LT:
    case BTOR_IBV_LT | BTOR_IBV_IS_PREDICATE:
    case BTOR_IBV_MOD:
    case BTOR_IBV_MUL:
    case BTOR_IBV_OR:
    case BTOR_IBV_SUB:
    case BTOR_IBV_SUM:
    case BTOR_IBV_XOR: assert (i <= 1); return overlaps (r, rhs->range);

    case BTOR_IBV_COND: assert (i <= 2); return overlaps (r, rhs->range);

    case BTOR_IBV_EQUAL:
    case BTOR_IBV_EQUAL | BTOR_IBV_IS_PREDICATE: assert (i <= 1); return true;

    case BTOR_IBV_SIGN_EXTEND:
      assert (!i);
      if (rhs->range.lsb > r.msb) return false;
      if (rhs->range.msb >= r.lsb) return true;
      assert (rhs->range.msb < r.lsb);
      // now check that 'rhs' contains the sign bit
      if (rhs->range.msb < ass->ranges[i].msb) return false;
      if (rhs->range.lsb > ass->ranges[i].msb) return false;
      return true;

    case BTOR_IBV_CASE:
      if (!(i & 1) && ass->ranges[i].getWidth () == 1)
      {
        assert (rhs->range.getWidth () == 1);
        return 1;
      }
      return overlaps (r, rhs->range);

    case BTOR_IBV_CONCAT:
    {
      uint32_t offset = 0;
      for (uint32_t j = 0; j < i; j++) offset += ass->ranges[j].getWidth ();
      BtorIBVRange s (r.id, r.msb + offset, r.lsb + offset);
      return overlaps (s, rhs->range);
    }

    case BTOR_IBV_LEFT_SHIFT:
    case BTOR_IBV_RIGHT_SHIFT:
      return true;  // TODO this is not precise if
                    // shift amount has < ld (w) bits for
                    // w the number of bits of the operand.
                    // Then in certain cases 'rhs' might
                    // not be relevant.
    case BTOR_IBV_REPLICATE:
    case BTOR_IBV_REPLICATE | BTOR_IBV_HAS_ARG:
      assert (!i);
      {
        BtorIBVRange s = rhs->range;
        uint32_t w     = ass->ranges[0].getWidth ();
        for (uint32_t j = 0; j < ass->arg; j++)
        {
          if (overlaps (r, s)) return true;
          s.lsb += w;
          if (s.lsb > r.msb) return false;
          s.msb += w;
        }
        return false;
      }
      break;

    case BTOR_IBV_LEFT_SHIFT | BTOR_IBV_HAS_ARG:
    case BTOR_IBV_RIGHT_SHIFT | BTOR_IBV_HAS_ARG:
      return true;  // TODO this is not precise at all since
                    // shift amount is constant and in principle
                    // we could calculate relevance.

    case BTOR_IBV_CONDBW:   // TODO not done yet ...
    case BTOR_IBV_PARCASE:  // TODO not done yet ...

    default:
      BTOR_ABORT (1,
                  "operator '%s%s' (%d) not handled yet",
                  btor_ibv_tag_to_str (ass->tag),
                  (ass->tag & BTOR_IBV_IS_PREDICATE) ? "_PRED" : "",
                  (int32_t) ass->tag);
      break;
  }
  return true;
}

void
BtorIBV::push_atom_ptr_next (BtorIBVAtom *b,
                             bool forward,
                             BtorIBVAtomPtrNextStack *apnwork)
{
  const long cycle_limit = 10;
  long pushed;
  if (!forward && b->current.exp) return;
  if (forward && b->next.exp) return;
  BtorIBVAtomPtrNext apn (b, forward);
  BTOR_PUSH_STACK (*apnwork, apn);
  BtorIBVRange r = b->range;
  msg (4,
       "btor_ibv_push_atom_ptr_next id %u [%u:%u] '%s[%u:%u]' %d",
       r.id,
       r.msb,
       r.lsb,
       id2node (r.id)->name,
       r.msb,
       r.lsb,
       forward);
  if (forward)
    pushed = ++b->next.pushed;
  else
    pushed = ++b->current.pushed;

  if (pushed >= cycle_limit && force >= 2)
  {
    BoolectorSort s    = boolector_bitvec_sort (btor, b->range.getWidth ());
    BoolectorNode *exp = boolector_zero (btor, s);
    boolector_release_sort (btor, s);
    if (forward)
      b->next.exp = exp;
    else
      b->current.exp = exp;
    warn (
        "forced cyclic synthesis for id %u [%u:%u] '%s[%u:%u]' %d to zero "
        "(pushed %" PRId64 ")",
        r.id,
        r.msb,
        r.lsb,
        id2node (r.id)->name,
        r.msb,
        r.lsb,
        forward,
        pushed);
  }
  else
  {
    BTOR_ABORT (pushed >= cycle_limit,
                "potential cyclic synthesis for id %u [%u:%u] '%s[%u:%u]' %d "
                "(giving up)",
                r.id,
                r.msb,
                r.lsb,
                id2node (r.id)->name,
                r.msb,
                r.lsb,
                forward);
    if (pushed >= 2)
      warn (
          "potential cyclic synthesis for id %u [%u:%u] '%s[%u:%u]' %d (pushed "
          "%" PRId64 ")",
          r.id,
          r.msb,
          r.lsb,
          id2node (r.id)->name,
          r.msb,
          r.lsb,
          forward,
          pushed);
  }
}

void
BtorIBV::translate_atom_divide (BtorIBVAtom *a,
                                bool forward,
                                BtorIBVAtomPtrNextStack *apnwork)
{
  if (!forward && a->current.exp) return;
  if (forward && a->next.exp) return;

  BtorIBVRange r = a->range;
  BtorIBVNode *n = id2node (r.id);

  msg (4,
       "translate_atom_divide id %u [%u:%u] '%s[%u:%u]' %d",
       r.id,
       r.msb,
       r.lsb,
       n->name,
       r.msb,
       r.lsb,
       forward);

  btor_ibv_check_atom (n, r);

  BtorIBVClassification c = n->flags[r.lsb].classified;
  switch (c)
  {
    case BTOR_IBV_NOT_USED: break;

    default:
      BTOR_ABORT (1, "%s not handled", btor_ibv_classified_to_str (c));
      break;

    case BTOR_IBV_TWO_PHASE_INPUT:
      if (n->is_next_state)
        assert (!a->current.exp), assert (!a->next.exp);
      else
        assert (a->current.exp), assert (a->next.exp);
      break;

    case BTOR_IBV_ASSIGNED_IMPLICIT_NEXT:
    {
      assert (!forward);
      assert (n->prev);
      BtorIBVAssignment *ass = n->prev[r.lsb];
      assert (ass);
      assert (ass->tag == BTOR_IBV_NON_STATE);
      assert (ass->nranges == 1);
      assert (ass->ranges[0].id == n->id);
      BtorIBVNode *prev = id2node (ass->range.id);
      BtorIBVRange pr (ass->range.id,
                       r.msb - ass->ranges[0].lsb + ass->range.lsb,
                       r.lsb - ass->ranges[0].lsb + ass->range.lsb);
      assert (pr.getWidth () == r.getWidth ());
      for (BtorIBVAtom *b = prev->atoms.start; b < prev->atoms.top; b++)
      {
        assert (b->range.id == prev->id);
        if (b->range.msb < pr.lsb) continue;
        if (b->range.lsb > pr.msb) continue;
        BTORIBV_COVER (!(b->range.lsb <= pr.lsb && pr.msb <= b->range.msb));
#if 1
        push_atom_ptr_next (b, true, apnwork);
#else
        push_atom_ptr_next (
            b, false, apnwork);  // TODO try NOT to forward to avoid cycle?
#endif
      }
    }
    break;

    case BTOR_IBV_CONSTANT:
      assert (a->current.exp);
      assert (a->next.exp);
      break;

    case BTOR_IBV_CURRENT_STATE:
      assert (a->current.exp);
      if (forward)
      {
        BtorIBVAssignment *ass = n->next[r.lsb];
        assert (ass);
        assert (ass->tag == BTOR_IBV_STATE);
        assert (ass->range.id == n->id);
        assert (ass->nranges == 2);
        BtorIBVRange nr (ass->ranges[1].id,
                         r.msb - ass->range.lsb + ass->ranges[1].lsb,
                         r.lsb - ass->range.lsb + ass->ranges[1].lsb);
        assert (nr.getWidth () == r.getWidth ());
        BtorIBVNode *next = id2node (nr.id);
        for (BtorIBVAtom *b = next->atoms.start; b < next->atoms.top; b++)
        {
          assert (b->range.id == next->id);
          if (nr.msb < b->range.lsb) continue;
          if (nr.lsb > b->range.msb) continue;
          push_atom_ptr_next (b, false, apnwork);
        }
      }
      break;

    case BTOR_IBV_ONE_PHASE_ONLY_NEXT_INPUT:
    case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
      assert (!forward);
      assert (a->current.exp);
      break;

    case BTOR_IBV_PHANTOM_NEXT_INPUT:
    case BTOR_IBV_PHANTOM_CURRENT_INPUT: break;

    case BTOR_IBV_ASSIGNED:
    {
      assert (n->assigned);
      BtorIBVAssignment *ass = n->assigned[r.lsb];
      assert (ass);
      for (uint32_t i = 0; i < ass->nranges; i++)
      {
        BtorIBVRange ar = ass->ranges[i];
        if (!ar.id) continue;
        BtorIBVNode *o = id2node (ar.id);
        for (BtorIBVAtom *b = o->atoms.start; b < o->atoms.top; b++)
          if (is_relevant_atom_for_assigned_atom (a, i, b, ass))
            push_atom_ptr_next (b, forward, apnwork);
      }
    }
    break;
  }
}

static bool
btor_ibv_atoms_in_range_have_exp (BtorIBVNode *n, BtorIBVRange r, bool forward)
{
  for (BtorIBVAtom *b = n->atoms.start; b < n->atoms.top; b++)
  {
    assert (b->range.id == r.id);
    if (!overlaps (b->range, r)) continue;
    if (!forward && !b->current.exp) return 0;
    if (forward && !b->next.exp) return 0;
  }
  return 1;
}

static BoolectorNode *
btor_ibv_atoms_in_range_collect_exp (Btor *btor,
                                     BtorIBVNode *n,
                                     BtorIBVRange r,
                                     bool forward)
{
  btor_ibv_check_atoms (n);
  BoolectorNode *exp = 0;
  for (BtorIBVAtom *b = n->atoms.start; b < n->atoms.top; b++)
  {
    BoolectorNode *tmp;
    if (b->range.msb < r.lsb || b->range.lsb > r.msb)
      tmp = 0;
    else
      tmp = forward ? b->next.exp : b->current.exp;
    if (tmp)
      tmp = boolector_copy (btor, tmp);
    else
    {
      BoolectorSort s = boolector_bitvec_sort (btor, b->range.getWidth ());
      tmp             = boolector_zero (btor, s);
      boolector_release_sort (btor, s);
    }
    if (exp)
    {
      BoolectorNode *concat = boolector_concat (btor, tmp, exp);
      boolector_release (btor, exp);
      boolector_release (btor, tmp);
      exp = concat;
    }
    else
      exp = tmp;
  }
  assert (exp);
  return exp;
}

BoolectorNode *
BtorIBV::translate_assignment_conquer (BtorIBVAtom *a,
                                       bool forward,
                                       BtorIBVAssignment *ass)
{
  BoolectorNodePtrStack stack;
#ifndef NDEBUG
  BtorIBVRange r = a->range;
#endif
  BoolectorNode *res;
  assert (ass);
  assert (ass->range.id == r.id);

  for (uint32_t i = 0; i < ass->nranges; i++)
  {
    BtorIBVRange ar = ass->ranges[i];
    if (!ar.id) continue;
    BtorIBVNode *o = id2node (ar.id);
    for (BtorIBVAtom *b = o->atoms.start; b < o->atoms.top; b++)
    {
      assert (b->range.id == o->id);
      if (ar.msb < b->range.lsb) continue;
      if (ar.lsb > b->range.msb) continue;
      if (!is_relevant_atom_for_assigned_atom (a, i, b, ass)) continue;
      if (!forward && !b->current.exp) return 0;
      if (forward && !b->next.exp) return 0;
    }
  }

  msg (4,
       "translate_assignment_conquer id %u [%u:%u] '%s[%u:%u]' %d",
       a->range.id,
       a->range.msb,
       a->range.lsb,
       id2node (a->range.id)->name,
       a->range.msb,
       a->range.lsb,
       forward);

  BTOR_INIT_STACK (btor->mm, stack);
  for (uint32_t i = 0; i < ass->nranges; i++)
  {
    BtorIBVRange r        = ass->ranges[i];
    BoolectorNode *argexp = 0;
    if (r.id)
    {
      BtorIBVNode *o = id2node (r.id);
      btor_ibv_check_atoms (o);
      BoolectorNode *exp = 0;
      for (BtorIBVAtom *b = o->atoms.start; b < o->atoms.top; b++)
      {
        assert (b->range.id == r.id);
        BoolectorNode *tmp = forward ? b->next.exp : b->current.exp;
        if (tmp)
          tmp = boolector_copy (btor, tmp);
        else
        {
          BoolectorSort s = boolector_bitvec_sort (btor, b->range.getWidth ());
          tmp             = boolector_zero (btor, s);
          boolector_release_sort (btor, s);
        }
        if (exp)
        {
          BoolectorNode *concat = boolector_concat (btor, tmp, exp);
          boolector_release (btor, exp);
          boolector_release (btor, tmp);
          exp = concat;
        }
        else
          exp = tmp;
      }
      assert (exp);
      argexp = boolector_slice (btor, exp, r.msb, r.lsb);
      boolector_release (btor, exp);
    }
    BTOR_PUSH_STACK (stack, argexp);
  }

  switch ((int32_t) ass->tag)
  {
    case BTOR_IBV_AND:
      res = boolector_and (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_BUF:
      res = boolector_copy (btor, BTOR_PEEK_STACK (stack, 0));
      break;
    case BTOR_IBV_CASE:
      assert (ass->nranges >= 2);
      assert (!(ass->nranges & 1));
      {
        int32_t j = BTOR_COUNT_STACK (stack) - 1;
        res       = 0;
        while (j >= 0)
        {
          BoolectorNode *d = BTOR_PEEK_STACK (stack, j);
          BoolectorNode *c = BTOR_PEEK_STACK (stack, j - 1);
          if (!c || !res)
            res = boolector_copy (btor, d);
          else if (boolector_get_width (btor, c) == 1)
          {
            BoolectorNode *tmp = boolector_cond (btor, c, d, res);
            boolector_release (btor, res);
            res = tmp;
          }
          else
          {
            BoolectorNode *inv = boolector_not (btor, c);
            BoolectorNode *l   = boolector_or (btor, inv, d);
            BoolectorNode *i   = boolector_not (btor, c);
            boolector_release (btor, inv);
            inv                = boolector_not (btor, i);
            BoolectorNode *r   = boolector_or (btor, inv, res);
            BoolectorNode *tmp = boolector_and (btor, l, r);
            boolector_release (btor, l);
            boolector_release (btor, i);
            boolector_release (btor, r);
            boolector_release (btor, res);
            res = tmp;
          }
          j -= 2;
        }
      }
      break;
    case BTOR_IBV_CONCAT:
    {
      assert (ass->nranges >= 1);
      res = 0;
      for (uint32_t i = 0; i < BTOR_COUNT_STACK (stack); i++)
      {
        BoolectorNode *arg = BTOR_PEEK_STACK (stack, i);
        if (res)
        {
          BoolectorNode *tmp = boolector_concat (btor, res, arg);
          boolector_release (btor, res);
          res = tmp;
        }
        else
          res = boolector_copy (btor, arg);
      }
    }
      assert (res);
      break;
    case BTOR_IBV_COND:
      res = boolector_cond (btor,
                            BTOR_PEEK_STACK (stack, 0),
                            BTOR_PEEK_STACK (stack, 1),
                            BTOR_PEEK_STACK (stack, 2));
      break;
    case BTOR_IBV_DIV:
      res = boolector_udiv (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_EQUAL:
    case BTOR_IBV_EQUAL | BTOR_IBV_IS_PREDICATE:
      res = boolector_eq (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_LE:
    case BTOR_IBV_LE | BTOR_IBV_IS_PREDICATE:
      res = boolector_ulte (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_LT:
    case BTOR_IBV_LT | BTOR_IBV_IS_PREDICATE:
      res = boolector_ult (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_MOD:
      res = boolector_urem (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_MUL:
      res = boolector_mul (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_NOT:
      res = boolector_not (btor, BTOR_PEEK_STACK (stack, 0));
      break;
    case BTOR_IBV_OR:
      res = boolector_or (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_SIGN_EXTEND:
    case BTOR_IBV_ZERO_EXTEND:
    {
      uint32_t dw      = a->range.getWidth ();
      BoolectorNode *n = BTOR_PEEK_STACK (stack, 0);
      uint32_t nw      = boolector_get_width (btor, n);
      if (dw == nw)
        res = boolector_copy (btor, n);
      else if (dw < nw)
        res = boolector_slice (btor, n, dw - 1, 0);
      else if (ass->tag == BTOR_IBV_SIGN_EXTEND)
        res = boolector_sext (btor, n, dw - nw);
      else
        res = boolector_uext (btor, n, dw - nw);
    }
    break;
    case BTOR_IBV_SUB:
      res = boolector_sub (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_SUM:
      res = boolector_add (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_XOR:
      res = boolector_xor (
          btor, BTOR_PEEK_STACK (stack, 0), BTOR_PEEK_STACK (stack, 1));
      break;
    case BTOR_IBV_REPLICATE | BTOR_IBV_HAS_ARG:
    case BTOR_IBV_REPLICATE:
    {
      res = 0;
      assert (BTOR_COUNT_STACK (stack) == 1);
      BoolectorNode *arg = BTOR_PEEK_STACK (stack, 0);
      for (uint32_t i = 0; i < ass->arg; i++)
      {
        if (res)
        {
          BoolectorNode *tmp = boolector_concat (btor, res, arg);
          boolector_release (btor, res);
          res = tmp;
        }
        else
          res = boolector_copy (btor, arg);
      }
    }
    break;
    case BTOR_IBV_LEFT_SHIFT:
    case BTOR_IBV_RIGHT_SHIFT:
    case BTOR_IBV_LEFT_SHIFT | BTOR_IBV_HAS_ARG:
    case BTOR_IBV_RIGHT_SHIFT | BTOR_IBV_HAS_ARG:
    {
      BoolectorNode *arg = BTOR_PEEK_STACK (stack, 0);
      uint32_t d, l, w = boolector_get_width (btor, arg);
      for (d = 0, l = 1; l < w; d++) l *= 2;
      assert (l == (1u << d));
      BoolectorNode *e;
      if (l > w)
        e = boolector_uext (btor, arg, l - w);
      else
        e = boolector_copy (btor, arg);
      BoolectorNode *s;
      if (ass->tag & BTOR_IBV_HAS_ARG)
      {
        assert (BTOR_COUNT_STACK (stack) == 1);
        uint32_t r         = ass->arg % l;
        BoolectorSort sort = boolector_bitvec_sort (btor, d);
        s                  = boolector_unsigned_int (btor, r, sort);
        boolector_release_sort (btor, sort);
      }
      else
      {
        assert (BTOR_COUNT_STACK (stack) == 2);
        BoolectorNode *shift = BTOR_PEEK_STACK (stack, 1);
        if (boolector_get_width (btor, shift) == d)
        {
          s = boolector_copy (btor, shift);
        }
        else
        {
          assert (boolector_get_width (btor, shift) > d);
          s = boolector_slice (btor, shift, d - 1, 0);
        }
      }
      BoolectorNode *t;
      if ((ass->tag & ~BTOR_IBV_HAS_ARG) == BTOR_IBV_LEFT_SHIFT)
        t = boolector_sll (btor, e, s);
      else
      {
        assert ((ass->tag & ~BTOR_IBV_HAS_ARG) == BTOR_IBV_RIGHT_SHIFT);
        t = boolector_srl (btor, e, s);
      }
      boolector_release (btor, e);
      boolector_release (btor, s);
      res = boolector_slice (btor, t, w - 1, 0);
      boolector_release (btor, t);
    }
    break;
    case BTOR_IBV_CONDBW:
    case BTOR_IBV_NON_STATE:
    case BTOR_IBV_PARCASE:
    case BTOR_IBV_STATE:
    default:
      res = 0;
      BTOR_ABORT (1,
                  "operator '%s%s' (%d) not handled yet",
                  btor_ibv_tag_to_str (ass->tag),
                  (ass->tag & BTOR_IBV_IS_PREDICATE) ? "_PRED" : "",
                  (int32_t) ass->tag);
      break;
  }
  assert (res);
  while (!BTOR_EMPTY_STACK (stack))
  {
    BoolectorNode *argexp = BTOR_POP_STACK (stack);
    if (argexp) boolector_release (btor, argexp);
  }
  assert (boolector_get_width (btor, res) >= a->range.getWidth ());
  if (boolector_get_width (btor, res) > a->range.getWidth ())
  {
    uint32_t lsb = a->range.lsb - ass->range.lsb;
    uint32_t msb = a->range.msb - ass->range.lsb;
    assert (lsb <= msb);
    BoolectorNode *tmp = boolector_slice (btor, res, msb, lsb);
    boolector_release (btor, res);
    res = tmp;
  }
  BTOR_RELEASE_STACK (stack);
  assert (boolector_get_width (btor, res) == a->range.getWidth ());
  assert (res);
  return res;
}

bool
BtorIBV::translate_atom_conquer (BtorIBVAtom *a, bool forward)
{
  if (!forward && a->current.exp) return true;
  if (forward && a->next.exp) return true;

  BtorIBVRange r = a->range;
  BtorIBVNode *n = id2node (r.id);

  btor_ibv_check_atom (n, r);

  BtorIBVClassification c = n->flags[r.lsb].classified;

  switch (c)
  {
    case BTOR_IBV_PHANTOM_CURRENT_INPUT:
    case BTOR_IBV_PHANTOM_NEXT_INPUT:
    case BTOR_IBV_NOT_USED:
    {
      BoolectorSort s    = boolector_bitvec_sort (btor, r.getWidth ());
      BoolectorNode *exp = boolector_zero (btor, s);
      boolector_release_sort (btor, s);
      if (forward)
        assert (!a->next.exp), a->next.exp = exp;
      else
        assert (!a->current.exp), a->current.exp = exp;
    }
    break;

    case BTOR_IBV_TWO_PHASE_INPUT:
      (void) forward;
      assert (!forward);
      assert (n->is_next_state);
      {
        assert (n->prev);
        BtorIBVAssignment *pa = n->prev[r.lsb];
        assert (pa);
        uint32_t pos = (pa->tag == BTOR_IBV_STATE);
        assert (pos < pa->nranges);
        assert (pa->ranges[pos].id == n->id);
        BtorIBVNode *prev = id2node (pa->range.id);
        assert (prev);
        assert (!prev->is_next_state);
        BtorIBVRange pr (prev->id,
                         r.msb - pa->ranges[pos].lsb + pa->range.lsb,
                         r.lsb - pa->ranges[pos].lsb + pa->range.lsb);
        if (!btor_ibv_atoms_in_range_have_exp (prev, pr, true)) return false;
        if (pos)
          warn ("next state id %u '%s[%u:%u]' used as two-phase input",
                n->id,
                n->name,
                r.msb,
                r.lsb);
        BoolectorNode *forwarded =
            btor_ibv_atoms_in_range_collect_exp (btor, prev, pr, true);
        a->current.exp = boolector_slice (btor, forwarded, pr.msb, pr.lsb);
        assert (boolector_get_width (btor, a->current.exp) == r.getWidth ());
        boolector_release (btor, forwarded);
      }
      break;

    case BTOR_IBV_ASSIGNED_IMPLICIT_NEXT:

      BTOR_ABORT (forward,
                  "can not forward implict next id %u [%u:%u] '%s[%u:%u]'",
                  r.id,
                  r.msb,
                  r.lsb,
                  id2node (r.id)->name,
                  r.msb,
                  r.lsb);

      assert (n->is_next_state);
      {
        assert (n->prev);
        BtorIBVAssignment *pa = n->prev[r.lsb];
        assert (pa);
        assert (pa->tag == BTOR_IBV_NON_STATE);
        assert (pa->nranges == 1);
        assert (pa->ranges[0].id == n->id);
        BtorIBVNode *prev = id2node (pa->range.id);
        assert (prev);
        assert (!prev->is_next_state);
        BtorIBVRange pr (prev->id,
                         r.msb - pa->ranges[0].lsb + pa->range.lsb,
                         r.lsb - pa->ranges[0].lsb + pa->range.lsb);
#if 1
        const int32_t norward = true;
#else
        const int32_t norward =
            false;  // TODO try NOT to forward to avoid cycle?
#endif
        if (!btor_ibv_atoms_in_range_have_exp (prev, pr, norward)) return false;
        BoolectorNode *forwarded =
            btor_ibv_atoms_in_range_collect_exp (btor, prev, pr, norward);
        a->current.exp = boolector_slice (btor, forwarded, pr.msb, pr.lsb);
        assert (boolector_get_width (btor, a->current.exp) == r.getWidth ());
        boolector_release (btor, forwarded);
      }
      break;

    case BTOR_IBV_CURRENT_STATE:
      assert (forward);
      assert (!n->is_next_state);
      {
        assert (n->next);
        BtorIBVAssignment *na = n->next[r.lsb];
        assert (na);
        assert (na->tag == BTOR_IBV_STATE);
        assert (na->nranges == 2);
        assert (na->range.id == n->id);
        BtorIBVNode *next = id2node (na->ranges[1].id);
        assert (next);
        BtorIBVRange nr (next->id,
                         r.msb - na->range.lsb + na->ranges[1].lsb,
                         r.lsb - na->range.lsb + na->ranges[1].lsb);
        if (!btor_ibv_atoms_in_range_have_exp (next, nr, false)) return false;
        BoolectorNode *cached =
            btor_ibv_atoms_in_range_collect_exp (btor, next, nr, false);
        a->next.exp = boolector_slice (btor, cached, nr.msb, nr.lsb);
        assert (boolector_get_width (btor, a->current.exp) == r.getWidth ());
        boolector_release (btor, cached);
      }
      break;

    default:
    case BTOR_IBV_ASSIGNED_IMPLICIT_CURRENT:
    case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
    case BTOR_IBV_ONE_PHASE_ONLY_NEXT_INPUT:
      BTOR_ABORT (1, "%s not handled yet", btor_ibv_classified_to_str (c));
      break;

    case BTOR_IBV_ASSIGNED:
    {
      BoolectorNode *exp;
      exp = translate_assignment_conquer (a, forward, n->assigned[r.lsb]);
      if (!exp) return false;
      assert (boolector_get_width (btor, exp) == a->range.getWidth ());
      if (forward)
        assert (!a->next.exp), a->next.exp = exp;
      else
        assert (!a->current.exp), a->current.exp = exp;
    }
    break;
  }
#ifndef NDEBUG
  if (a->current.exp && a->next.exp)
    assert (boolector_get_width (btor, a->current.exp)
            == boolector_get_width (btor, a->next.exp));
#endif

  msg (4,
       "translate_atom_conquer id %u [%u:%u] '%s[%u:%u]' %d",
       r.id,
       r.msb,
       r.lsb,
       n->name,
       r.msb,
       r.lsb,
       forward);

  return true;
}

static char *
btor_ibv_atom_base_name (Btor *btor,
                         BtorIBVNode *n,
                         BtorIBVRange r,
                         const char *prefix)
{
  char suffix[30], *res;
  int32_t len;
  if (n->width == r.getWidth ())
    suffix[0] = 0;
  else
    sprintf (suffix, "[%u:%u]", r.msb, r.lsb);
  len = strlen (n->name) + strlen (suffix) + 1;
  if (prefix) len += strlen (prefix) + 2;
  res = (char *) btor_mem_malloc (btor->mm, len);
  if (!prefix)
    sprintf (res, "%s%s", n->name, suffix);
  else
    sprintf (res, "%s(%s%s)", prefix, n->name, suffix);
  return res;
}

void
BtorIBV::translate_atom_base (BtorIBVAtom *a)
{
  assert (a);
  if (a->current.exp) return;
  BtorIBVRange r = a->range;
  BtorIBVNode *n = id2node (r.id);

  msg (4,
       "translate_atom_base id %u [%u:%u] '%s[%u:%u]'",
       r.id,
       r.msb,
       r.lsb,
       n->name,
       r.msb,
       r.lsb);

  btor_ibv_check_atom (n, r);
  BtorIBVClassification c = n->flags[r.lsb].classified;
  switch (c)
  {
    default:
      BTOR_ABORT (1, "%s not handled yet", btor_ibv_classified_to_str (c));
      break;

    case BTOR_IBV_CONSTANT:
    {
      if (!n->cached)
      {
        char *conststr, *p;
        BTOR_NEWN (btor->mm, conststr, n->width + 1);
        assert (strlen (n->name) == n->width);
        p = conststr + n->width;
        ;
        *p = 0;
        for (uint32_t i = 0; i < n->width; i++)
        {
          char c = bit (n->name, i, n->width);
          if (c != '0' && c != '1')
          {
            if (!n->flags[i].coi)
              warn (
                  "ignoring invalid constant bit '%s[%u] = %c' outside "
                  "cone-of-influence",
                  n->name,
                  i,
                  c);
            else if (force)
              warn (
                  "forced to ignore invalid constant bit '%s[%u] = %c' in "
                  "cone-of-influence",
                  n->name,
                  i,
                  c);
            else
              BTOR_ABORT (
                  1,
                  "invalid constant bit '%s[%u] = %c' in cone-of-influence",
                  n->name,
                  i,
                  c);
          }
          *--p = (c == '1') ? '1' : '0';  // overwrite 'x' not in COI with '0'
        }
        assert (p == conststr);
        assert (strlen (conststr) == n->width);
        assert (strlen (conststr) >= (size_t) r.getWidth ());
        n->cached = boolector_const (btor, conststr);
        assert (boolector_get_width (btor, n->cached) == n->width);
        BTOR_DELETEN (btor->mm, conststr, n->width + 1);
      }
      a->current.exp = boolector_slice (btor, n->cached, r.msb, r.lsb);
      assert (boolector_get_width (btor, a->current.exp) == r.getWidth ());
      a->next.exp = boolector_copy (btor, a->current.exp);
    }
    break;

    case BTOR_IBV_ONE_PHASE_ONLY_NEXT_INPUT:
    {
      char *nextname  = btor_ibv_atom_base_name (btor, n, r, 0);
      BoolectorSort s = boolector_bitvec_sort (btor, r.getWidth ());
      a->current.exp  = boolector_mc_input (btormc, s, nextname);
      boolector_release_sort (btor, s);
      btor_mem_freestr (btor->mm, nextname);
      (void) boolector_copy (btor, a->current.exp);
      stats.inputs++;
    }
    break;

    case BTOR_IBV_PHANTOM_CURRENT_INPUT: break;

    case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
    {
      char *name      = btor_ibv_atom_base_name (btor, n, r, 0);
      BoolectorSort s = boolector_bitvec_sort (btor, r.getWidth ());
      a->current.exp  = boolector_mc_state (btormc, s, name);
      boolector_release_sort (btor, s);
      btor_mem_freestr (btor->mm, name);
      (void) boolector_copy (btor, a->current.exp);
      stats.states++;
    }
    break;

    case BTOR_IBV_PHANTOM_NEXT_INPUT:
    {
      char *name      = btor_ibv_atom_base_name (btor, n, r, 0);
      BoolectorSort s = boolector_bitvec_sort (btor, r.getWidth ());
      a->current.exp  = boolector_mc_input (btormc, s, name);
      boolector_release_sort (btor, s);
      btor_mem_freestr (btor->mm, name);
      (void) boolector_copy (btor, a->current.exp);
      stats.inputs++;
    }
    break;

    case BTOR_IBV_TWO_PHASE_INPUT:
      if (!n->is_next_state)
      {
        {
          char *currentname = btor_ibv_atom_base_name (btor, n, r, 0);
          BoolectorSort s   = boolector_bitvec_sort (btor, r.getWidth ());
          a->current.exp    = boolector_mc_state (btormc, s, currentname);
          boolector_release_sort (btor, s);
          btor_mem_freestr (btor->mm, currentname);
          (void) boolector_copy (btor, a->current.exp);
          stats.states++;
        }
        if (n->next)
        {
          BtorIBVAssignment *na = n->next[r.lsb];
          assert (na);
          assert (na->tag == BTOR_IBV_NON_STATE || na->tag == BTOR_IBV_STATE);
          uint32_t pos = na->tag == BTOR_IBV_STATE;
          assert (pos < na->nranges);
          BtorIBVNode *next = id2node (na->ranges[pos].id);
#if 0
          BtorIBVRange nr (na->ranges[pos].id,
                           r.msb - r.lsb + na->ranges[pos].lsb,
                           na->ranges[pos].lsb);
#else
          BtorIBVRange nr (na->ranges[pos].id, r.msb, r.lsb);
#endif
          char *nextname =
              btor_ibv_atom_base_name (btor, next, nr, "BtorIBV::past1");
          BoolectorSort s = boolector_bitvec_sort (btor, nr.getWidth ());
          a->next.exp     = boolector_mc_input (btormc, s, nextname);
          boolector_release_sort (btor, s);
          btor_mem_freestr (btor->mm, nextname);
          (void) boolector_copy (btor, a->next.exp);
          stats.inputs++;
        }
        else
        {
          char *nextname = btor_ibv_atom_base_name (
              btor, n, r, "BtorIBV::past2");  // TODO Why?
          BoolectorSort s = boolector_bitvec_sort (btor, r.getWidth ());
          a->next.exp     = boolector_mc_input (btormc, s, nextname);
          boolector_release_sort (btor, s);
          btor_mem_freestr (btor->mm, nextname);
          (void) boolector_copy (btor, a->next.exp);
          stats.inputs++;
        }
      }
      break;

    case BTOR_IBV_CURRENT_STATE:
    {
      char *name      = btor_ibv_atom_base_name (btor, n, r, 0);
      BoolectorSort s = boolector_bitvec_sort (btor, r.getWidth ());
      a->current.exp  = boolector_mc_state (btormc, s, name);
      boolector_release_sort (btor, s);
      btor_mem_freestr (btor->mm, name);
      (void) boolector_copy (btor, a->current.exp);
      stats.states++;
    }
    break;
  }
#ifndef NDEBUG
  if (a->current.exp && a->next.exp)
    assert (boolector_get_width (btor, a->current.exp)
            == boolector_get_width (btor, a->next.exp));
#endif
}

bool
BtorIBV::is_phantom_next (BtorIBVNode *n, uint32_t i)
{
  assert (n);
  assert (n->is_next_state);
  assert (i < n->width);
  if (!n->prev) return 0;
  BtorIBVAssignment *a = n->prev[i];
  if (!a) return 0;
  if (a->tag != BTOR_IBV_NON_STATE) return 0;
  assert (a->nranges == 1);
  assert (a->ranges[0].lsb <= i && i <= a->ranges[0].msb);
  BtorIBVNode *pn    = id2node (a->range.id);
  uint32_t k         = i + a->range.lsb - a->ranges[0].lsb;
  BtorIBVFlags flags = pn->flags[k];
  if (flags.assigned) return 0;
  if (flags.implicit.current) return 0;  // TODO redundant?
  if (flags.implicit.next) return 0;
  if (!flags.input) return 0;
  if (!flags.onephase) return 0;
  return 1;
}

bool
BtorIBV::is_phantom_current (BtorIBVNode *n, uint32_t i)
{
  assert (n);
  assert (!n->is_next_state);
  assert (i < n->width);
  if (!n->next) return 0;
  BtorIBVAssignment *a = n->next[i];
  if (!a) return 0;
  assert (a->range.lsb <= i && i <= a->range.msb);
  if (a->tag != BTOR_IBV_NON_STATE) return 0;
  assert (a->nranges == 1);
  BtorIBVNode *nn    = id2node (a->ranges[0].id);
  uint32_t k         = i - a->range.lsb + a->ranges[0].lsb;
  BtorIBVFlags flags = nn->flags[k];
  if (flags.assigned) return 0;
  if (flags.implicit.current) return 0;
  if (flags.implicit.next) return 0;  // TODO redundant?
  if (!flags.input) return 0;
  if (!flags.onephase) return 0;
  return 1;
}

void
BtorIBV::translate ()
{
  BTOR_ABORT (state == BTOR_IBV_START,
              "model needs to be analyzed before it can be translated");

  BTOR_ABORT (state == BTOR_IBV_TRANSLATED, "can not translate model twice");

  assert (state == BTOR_IBV_ANALYZED);

  uint32_t atoms = 0;
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (!n->used) continue;
    uint32_t msb;
    for (uint32_t lsb = 0; lsb < n->width; lsb = msb + 1)
    {
      msb                              = lsb;
      BtorIBVClassification classified = n->flags[lsb].classified;
      assert (classified != BTOR_IBV_UNCLASSIFIED);
      for (;;)
      {
        if (msb + 1 >= n->width) break;
        if (n->flags[msb + 1].classified != classified) break;
        if (n->assigned && n->assigned[lsb] != n->assigned[msb + 1]) break;
        if (n->next && n->next[lsb] != n->next[msb + 1]) break;
        if (n->prev && n->prev[lsb] != n->prev[msb + 1]) break;
        msb++;
      }
      atoms++;
      BtorIBVAtom atom (BtorIBVRange (n->id, msb, lsb));
      BTOR_PUSH_STACK (n->atoms, atom);
      msg (3,
           "%s atom '%s[%u:%u]'",
           btor_ibv_classified_to_str (classified),
           n->name,
           msb,
           lsb);

      BTOR_ABORT (classified == BTOR_IBV_ASSIGNED_IMPLICIT_CURRENT,
                  "can not translate implicitly assigned current non-state");

      assert (classified != BTOR_IBV_UNCLASSIFIED);

      BtorIBVAtom *aptr = &BTOR_TOP_STACK (n->atoms);
      switch (classified)
      {
        case BTOR_IBV_CONSTANT:
        case BTOR_IBV_CURRENT_STATE:
        case BTOR_IBV_TWO_PHASE_INPUT:
        case BTOR_IBV_PHANTOM_NEXT_INPUT:
        case BTOR_IBV_PHANTOM_CURRENT_INPUT:
        case BTOR_IBV_ONE_PHASE_ONLY_NEXT_INPUT:
        case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
          translate_atom_base (aptr);
          break;
        default: break;
      }
    }
  }
  msg (1, "generated %u atoms", atoms);

  /*----------------------------------------------------------------------*/

  msg (1, "translating remaining atoms ... ");

  BtorIBVAtomPtrNextStack apnwork;
  BTOR_INIT_STACK (btor->mm, apnwork);
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (!n->used) continue;
    if (n->cached) continue;
    for (BtorIBVAtom *b = n->atoms.start; b < n->atoms.top; b++)
      push_atom_ptr_next (b, false, &apnwork);
    while (!BTOR_EMPTY_STACK (apnwork))
    {
      BtorIBVAtomPtrNext apn = BTOR_TOP_STACK (apnwork);
      if (translate_atom_conquer (apn.atom, apn.next))
        BTOR_POP_STACK (apnwork);
      else
        translate_atom_divide (apn.atom, apn.next, &apnwork);
    }
  }
  BTOR_RELEASE_STACK (apnwork);

  /*----------------------------------------------------------------------*/

  msg (1, "translating remaining nodes ... ");

  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (!n->used) continue;
    if (n->cached) continue;
    msg (4, "translate_node_conquer id %u '%s'", n->id, n->name);
#ifndef NDEBUG
    for (BtorIBVAtom *a = n->atoms.start; a < n->atoms.top; a++)
      assert (translate_atom_conquer (a, false));
#endif
    BoolectorNode *res = 0;
    for (BtorIBVAtom *a = n->atoms.start; a < n->atoms.top; a++)
    {
      BoolectorNode *exp = a->current.exp;
      assert (exp);
      BoolectorNode *tmp = res;
      if (tmp)
      {
        res = boolector_concat (btor, exp, res);
        boolector_release (btor, tmp);
      }
      else
        res = boolector_copy (btor, exp);
    }
    assert (res);
    assert (boolector_get_width (btor, res) == n->width);
    n->cached = res;
  }

  /*----------------------------------------------------------------------*/

  msg (1, "connecting next state and init state functions ... ");
  for (BtorIBVNode **p = idtab.start; p < idtab.top; p++)
  {
    BtorIBVNode *n = *p;
    if (!n) continue;
    if (n->is_constant) continue;
    if (!n->used) continue;
    if (!n->next) continue;
    for (BtorIBVAtom *at = n->atoms.start; at < n->atoms.top; at++)
    {
      BtorIBVAssignment *as = n->next[at->range.lsb];
      if (!as) continue;
      assert (as->range.id == at->range.id),
          assert (as->range.msb >= at->range.msb),
          assert (as->range.lsb <= at->range.lsb);
      switch (n->flags[at->range.lsb].classified)
      {
        case BTOR_IBV_CURRENT_STATE:
        {
          assert (as->nranges == 2);
          assert (boolector_get_width (btor, n->cached)
                  >= as->range.getWidth ());
          BoolectorNode *state =
              boolector_slice (btor, n->cached, at->range.msb, at->range.lsb);
          if (as->ranges[0].id)
          {
            BtorIBVNode *initnode = id2node (as->ranges[0].id);
            assert (initnode);
            uint32_t lsb0 = at->range.lsb - as->range.lsb + as->ranges[0].lsb;
            uint32_t msb0 = at->range.msb - as->range.lsb + as->ranges[0].lsb;
            assert (msb0 < initnode->width);
            assert (initnode->cached);
            assert (n->cached);
            BoolectorNode *initexp =
                boolector_slice (btor, initnode->cached, msb0, lsb0);
            boolector_mc_init (btormc, state, initexp);
            boolector_release (btor, initexp);
            stats.inits++;
          }
          BtorIBVNode *nextnode = id2node (as->ranges[1].id);
          assert (nextnode);
          uint32_t lsb = at->range.lsb - as->range.lsb + as->ranges[1].lsb;
          uint32_t msb = at->range.msb - as->range.lsb + as->ranges[1].lsb;
          assert (lsb <= msb), assert (msb < nextnode->width);
          assert (nextnode->cached);
          BoolectorNode *nextexp =
              boolector_slice (btor, nextnode->cached, msb, lsb);
          boolector_mc_next (btormc, state, nextexp);
          boolector_release (btor, state);
          boolector_release (btor, nextexp);
          stats.nexts++;
        }
        break;
        case BTOR_IBV_ONE_PHASE_ONLY_CURRENT_INPUT:
        {
          assert (as->tag == BTOR_IBV_NON_STATE);
          assert (as->nranges == 1);
          BtorIBVNode *nextnode = id2node (as->ranges[0].id);
          assert (nextnode);
          assert (nextnode->flags);
          uint32_t lsb = at->range.lsb - as->range.lsb + as->ranges[0].lsb;
          uint32_t msb = at->range.msb - as->range.lsb + as->ranges[0].lsb;
          assert (lsb <= msb), assert (msb < nextnode->width);
          assert (nextnode->flags[lsb].classified
                  == BTOR_IBV_PHANTOM_NEXT_INPUT);
          assert (nextnode->flags[msb].classified
                  == BTOR_IBV_PHANTOM_NEXT_INPUT);
          assert (nextnode->cached);
          BoolectorNode *nextexp =
              boolector_slice (btor, nextnode->cached, msb, lsb);
          BoolectorNode *curexp =
              boolector_slice (btor, n->cached, at->range.msb, at->range.lsb);
          boolector_mc_next (btormc, curexp, nextexp);
          boolector_release (btor, nextexp);
          boolector_release (btor, curexp);
          stats.nexts++;
        }
        break;
        case BTOR_IBV_TWO_PHASE_INPUT:
        {
          assert (as->tag == BTOR_IBV_NON_STATE || as->tag == BTOR_IBV_STATE);
          uint32_t pos          = as->tag == BTOR_IBV_STATE;
          BtorIBVNode *nextnode = id2node (as->ranges[pos].id);
          assert (nextnode);
          assert (nextnode->flags);
          uint32_t lsb = at->range.lsb - as->range.lsb + as->ranges[pos].lsb;
          uint32_t msb = at->range.msb - as->range.lsb + as->ranges[pos].lsb;
          assert (lsb <= msb), assert (msb < nextnode->width);
          assert (nextnode->flags[lsb].classified == BTOR_IBV_TWO_PHASE_INPUT);
          assert (nextnode->flags[msb].classified == BTOR_IBV_TWO_PHASE_INPUT);
          assert (nextnode->cached);
          BoolectorNode *nextexp =
              boolector_slice (btor, nextnode->cached, msb, lsb);
          BoolectorNode *curexp =
              boolector_slice (btor, n->cached, at->range.msb, at->range.lsb);
          boolector_mc_next (btormc, curexp, nextexp);
          boolector_release (btor, nextexp);
          boolector_release (btor, curexp);
          stats.nexts++;
        }
        break;
        case BTOR_IBV_PHANTOM_CURRENT_INPUT:
        case BTOR_IBV_PHANTOM_NEXT_INPUT:
        case BTOR_IBV_NOT_USED:
        case BTOR_IBV_ASSIGNED: break;
        default:
          BTOR_ABORT (
              1,
              "id %u '%s[%u:%u]' classified as '%s' not handled yet",
              n->id,
              n->name,
              at->range.msb,
              at->range.lsb,
              btor_ibv_classified_to_str (n->flags[at->range.lsb].classified));
          break;
      }
    }
  }

  /*----------------------------------------------------------------------*/

  for (BtorIBVBit *b = assertions.start; b < assertions.top; b++)
  {
    BtorIBVNode *n = id2node (b->id);
    assert (n);
    assert (n->cached);
    assert (n->used);
    assert (n->coi);
    BoolectorNode *good = boolector_slice (btor, n->cached, b->bit, b->bit);
    BoolectorNode *bad  = boolector_not (btor, good);
    boolector_release (btor, good);
    boolector_mc_bad (btormc, bad);
    boolector_release (btor, bad);
    stats.bads++;
  }

  /*----------------------------------------------------------------------*/

  BoolectorNode *initialized_state = 0;
  int32_t ninitialized             = 0;
  for (BtorIBVAssumption *a = assumptions.start; a < assumptions.top; a++)
  {
    BtorIBVRange r = a->range;
    assert (r.getWidth () == 1);
    BtorIBVNode *n = id2node (r.id);
    assert (n->cached);
    assert (n->used);
    assert (n->coi);
    BoolectorNode *constraint = boolector_slice (btor, n->cached, r.msb, r.lsb);
    assert (boolector_get_width (btor, constraint) == 1);
    if (a->initial)
    {
      if (!initialized_state)
      {
        assert (!ninitialized);
        BoolectorSort s = boolector_bitvec_sort (btor, 1);
        initialized_state =
            boolector_mc_state (btormc, s, "BtorIBV::initialized");
        BoolectorNode *zero = boolector_zero (btor, s);
        BoolectorNode *one  = boolector_one (btor, s);
        boolector_release_sort (btor, s);
        boolector_mc_init (btormc, initialized_state, zero);
        boolector_mc_next (btormc, initialized_state, one);
        boolector_release (btor, zero);
        boolector_release (btor, one);
      }
      BoolectorNode *inv = boolector_not (btor, initialized_state);
      BoolectorNode *tmp = boolector_implies (btor, inv, constraint);
      boolector_release (btor, inv);
      boolector_release (btor, constraint);
      constraint = tmp;
      ninitialized++;
    }

    boolector_mc_constraint (btormc, constraint);
    boolector_release (btor, constraint);
    stats.constraints++;
  }
  if (ninitialized)
    msg (3, "found %d initial states only assumptions", ninitialized);
  else if (stats.constraints)
    msg (3, "no initial states only assumptions");

  /*----------------------------------------------------------------------*/

  msg (2,
       "translated %u inputs, %u states, %u nexts, %u inits, "
       "%u bads, %u constraints",
       stats.inputs,
       stats.states,
       stats.nexts,
       stats.inits,
       stats.bads,
       stats.constraints);

  state = BTOR_IBV_TRANSLATED;
}

/*------------------------------------------------------------------------*/

void
BtorIBV::dump_btor (FILE *file)
{
  BTOR_ABORT (state == BTOR_IBV_START,
              "model needs to be translated before it can be dumped");

  boolector_mc_dump (btormc, file);
}

/*------------------------------------------------------------------------*/

int32_t
BtorIBV::bmc (int32_t mink, int32_t maxk)
{
  BTOR_ABORT (state == BTOR_IBV_START,
              "model needs to be translated before it can be checked");

  return boolector_mc_bmc (btormc, mink, maxk);
}

static string
repeat_char (Btor *btor, uint32_t length, char ch)
{
  char *cstr = (char *) btor_mem_malloc (btor->mm, length + 1);
  uint32_t i;
  for (i = 0; i < length; i++) cstr[i] = ch;
  cstr[i] = 0;
  string res (cstr);
  btor_mem_free (btor->mm, cstr, length + 1);
  return res;
}

string
BtorIBV::assignment (BitRange r, int32_t k)
{
  BTOR_ABORT (
      !gentrace,
      "'BtorIBV::enableTraceGeneration' was not called before checking");
  BtorIBVNode *n = id2node (r.m_nId);
  assert (n);
  if (!n->cached) return repeat_char (btor, r.getWidth (), 'x');
  BoolectorNode *sliced = boolector_slice (btor, n->cached, r.m_nMsb, r.m_nLsb);
  char *cres            = boolector_mc_assignment (btormc, sliced, k);
  boolector_release (btor, sliced);
  if (!cres) return repeat_char (btor, r.getWidth (), 'u');
  string res (cres);
  boolector_mc_free_assignment (btormc, cres);
  return res;
}
