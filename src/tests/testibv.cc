#include "btoribv.hh"

#include <cstring>
#include <iostream>
#include <map>
#include <string>

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>

using namespace std;

static map<string, unsigned> symtab;

static unsigned
mapsym (const string& str)
{
  return unsigned(symtab[str]);
}

static int nassertions;

//--------------------------------------------------------------------------------------
// These macros are a convenient hack to directly compile IBV models into C++.

#define addVariable(ID, NAME, WIDTH, ISNEXT, SRC, DIR, ...) \
  ibvm->addVariable (unsigned(ID),                          \
                     string (#NAME),                        \
                     unsigned(WIDTH),                       \
                     bool(ISNEXT),                          \
                     BitVector::BvVariableSource (SRC),     \
                     BitVector::DirectionKind (DIR));       \
  symtab[string (#NAME)] = unsigned(ID);

#define addRangeName(TOID, TOMSB, TOLSB, NAME, FROMMSB, FROMLSB)      \
  ibvm->addRangeName (                                                \
      BitVector::BitRange (                                           \
          mapsym (string (#TOID)), unsigned(TOMSB), unsigned(TOLSB)), \
      string (#NAME),                                                 \
      unsigned(FROMMSB),                                              \
      unsigned(FROMLSB));

#define addConstant(ID, VALUE, WIDTH)                                 \
  ibvm->addConstant (unsigned(ID), string (#VALUE), unsigned(WIDTH)); \
  symtab[string (#VALUE)] = (ID);

#define addUnaryOp(XX, OID, OMSB, OLSB, AID, AMSB, ALSB)                 \
  ibvm->XX (BitVector::BitRange (                                        \
                mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)), \
            BitVector::BitRange (                                        \
                mapsym (string (#AID)), unsigned(AMSB), unsigned(ALSB)));
#define addUnaryPred(XX, OID, OBIT, AID, AMSB, ALSB)                     \
  ibvm->XX (BitVector::BitRange (                                        \
                mapsym (string (#OID)), unsigned(OBIT), unsigned(OBIT)), \
            BitVector::BitRange (                                        \
                mapsym (string (#AID)), unsigned(AMSB), unsigned(ALSB)));

#define addAssignment(ARGS...) addUnaryOp (addAssignment, ##ARGS)
#define addBitNot(ARGS...) addUnaryOp (addBitNot, ##ARGS)
#define addZeroExtension(ARGS...) addUnaryOp (addZeroExtension, ##ARGS)
#define addSignExtension(ARGS...) addUnaryOp (addSignExtension, ##ARGS)
#define addLogicalNot(ARGS...) addUnaryPred (addLogicalNot, ##ARGS)

#define addBinaryOp(XX, OID, OMSB, OLSB, AID, AMSB, ALSB, BID, BMSB, BLSB) \
  ibvm->XX (BitVector::BitRange (                                          \
                mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)),   \
            BitVector::BitRange (                                          \
                mapsym (string (#AID)), unsigned(AMSB), unsigned(ALSB)),   \
            BitVector::BitRange (                                          \
                mapsym (string (#BID)), unsigned(BMSB), unsigned(BLSB)));

#define addBitOr(ARGS...) addBinaryOp (addBitOr, ##ARGS)
#define addBitAnd(ARGS...) addBinaryOp (addBitAnd, ##ARGS)
#define addBitXor(ARGS...) addBinaryOp (addBitXor, ##ARGS)
#define addSum(ARGS...) addBinaryOp (addSum, ##ARGS)
#define addSub(ARGS...) addBinaryOp (addSub, ##ARGS)
#define addMul(ARGS...) addBinaryOp (addMul, ##ARGS)
#define addDiv(ARGS...) addBinaryOp (addDiv, ##ARGS)
#define addMod(ARGS...) addBinaryOp (addMod, ##ARGS)
#define addLShiftNonConst(ARGS...) addBinaryOp (addLShiftNonConst, ##ARGS)
#define addRShiftNonConst(ARGS...) addBinaryOp (addRShiftNonConst, ##ARGS)

#define addBinaryPred(XX, OID, OBIT, AID, AMSB, ALSB, BID, BMSB, BLSB)   \
  ibvm->XX (BitVector::BitRange (                                        \
                mapsym (string (#OID)), unsigned(OBIT), unsigned(OBIT)), \
            BitVector::BitRange (                                        \
                mapsym (string (#AID)), unsigned(AMSB), unsigned(ALSB)), \
            BitVector::BitRange (                                        \
                mapsym (string (#BID)), unsigned(BMSB), unsigned(BLSB)));

#define addEqual(ARGS...) addBinaryPred (addEqual, ##ARGS)
#define addGreaterThan(ARGS...) addBinaryPred (addGreaterThan, ##ARGS)
#define addGreaterEqual(ARGS...) addBinaryPred (addGreaterEqual, ##ARGS)
#define addLessThan(ARGS...) addBinaryPred (addLessThan, ##ARGS)
#define addLessEqual(ARGS...) addBinaryPred (addLessEqual, ##ARGS)
#define addLogicalAnd(ARGS...) addBinaryPred (addLogicalAnd, ##ARGS)
#define addLogicalOr(ARGS...) addBinaryPred (addLogicalOr, ##ARGS)

#define addTernaryOp(                                                       \
    XX, OID, OMSB, OLSB, AID, AMSB, ALSB, BID, BMSB, BLSB, CID, CMSB, CLSB) \
  ibvm->XX (BitVector::BitRange (                                           \
                mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)),    \
            BitVector::BitRange (                                           \
                mapsym (string (#AID)), unsigned(AMSB), unsigned(ALSB)),    \
            BitVector::BitRange (                                           \
                mapsym (string (#BID)), unsigned(BMSB), unsigned(BLSB)),    \
            BitVector::BitRange (                                           \
                mapsym (string (#CID)), unsigned(CMSB), unsigned(CLSB)));

#define addCondition(ARGS...) addTernaryOp (addCondition, ##ARGS)

#define addUnaryOpArg(XX, OID, OMSB, OLSB, AID, AMSB, ALSB, ARG)         \
  ibvm->XX (BitVector::BitRange (                                        \
                mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)), \
            BitVector::BitRange (                                        \
                mapsym (string (#AID)), unsigned(AMSB), unsigned(ALSB)), \
            ARG);

#define addReplicate(ARGS...) addUnaryOpArg (addReplicate, ##ARGS, ARGS)
#define addLShift(ARGS...) addUnaryOpArg (addLShift, ##ARGS, ARGS)
#define addRShift(ARGS...) addUnaryOpArg (addRShift, ##ARGS, ARGS)

#define addVariadicOp4(                                                    \
    XX, OID, OMSB, OLSB, I1, M1, L1, I2, M2, L2, I3, M3, L3, I4, M4, L4)   \
  do                                                                       \
  {                                                                        \
    vector<BitVector::BitRange> args;                                      \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I1)), unsigned(M1), unsigned(L1)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I2)), unsigned(M2), unsigned(L2)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I3)), unsigned(M3), unsigned(L3)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I4)), unsigned(M4), unsigned(L4)));               \
    ibvm->XX (BitVector::BitRange (                                        \
                  mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)), \
              args);                                                       \
  } while (0);

#define addVariadicOp6(XX,                                                 \
                       OID,                                                \
                       OMSB,                                               \
                       OLSB,                                               \
                       I1,                                                 \
                       M1,                                                 \
                       L1,                                                 \
                       I2,                                                 \
                       M2,                                                 \
                       L2,                                                 \
                       I3,                                                 \
                       M3,                                                 \
                       L3,                                                 \
                       I4,                                                 \
                       M4,                                                 \
                       L4,                                                 \
                       I5,                                                 \
                       M5,                                                 \
                       L5,                                                 \
                       I6,                                                 \
                       M6,                                                 \
                       L6)                                                 \
  do                                                                       \
  {                                                                        \
    vector<BitVector::BitRange> args;                                      \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I1)), unsigned(M1), unsigned(L1)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I2)), unsigned(M2), unsigned(L2)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I3)), unsigned(M3), unsigned(L3)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I4)), unsigned(M4), unsigned(L4)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I5)), unsigned(M5), unsigned(L5)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I6)), unsigned(M6), unsigned(L6)));               \
    ibvm->XX (BitVector::BitRange (                                        \
                  mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)), \
              args);                                                       \
  } while (0);

#define addVariadicOp12(XX,                                                \
                        OID,                                               \
                        OMSB,                                              \
                        OLSB,                                              \
                        I1,                                                \
                        M1,                                                \
                        L1,                                                \
                        I2,                                                \
                        M2,                                                \
                        L2,                                                \
                        I3,                                                \
                        M3,                                                \
                        L3,                                                \
                        I4,                                                \
                        M4,                                                \
                        L4,                                                \
                        I5,                                                \
                        M5,                                                \
                        L5,                                                \
                        I6,                                                \
                        M6,                                                \
                        L6,                                                \
                        I7,                                                \
                        M7,                                                \
                        L7,                                                \
                        I8,                                                \
                        M8,                                                \
                        L8,                                                \
                        I9,                                                \
                        M9,                                                \
                        L9,                                                \
                        I10,                                               \
                        M10,                                               \
                        L10,                                               \
                        I11,                                               \
                        M11,                                               \
                        L11,                                               \
                        I12,                                               \
                        M12,                                               \
                        L12)                                               \
  do                                                                       \
  {                                                                        \
    vector<BitVector::BitRange> args;                                      \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I1)), unsigned(M1), unsigned(L1)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I2)), unsigned(M2), unsigned(L2)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I3)), unsigned(M3), unsigned(L3)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I4)), unsigned(M4), unsigned(L4)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I5)), unsigned(M5), unsigned(L5)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I6)), unsigned(M6), unsigned(L6)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I7)), unsigned(M7), unsigned(L7)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I8)), unsigned(M8), unsigned(L8)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I9)), unsigned(M9), unsigned(L9)));               \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I10)), unsigned(M10), unsigned(L10)));            \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I11)), unsigned(M11), unsigned(L11)));            \
    args.push_back (BitVector::BitRange (                                  \
        mapsym (string (#I12)), unsigned(M12), unsigned(L12)));            \
    ibvm->XX (BitVector::BitRange (                                        \
                  mapsym (string (#OID)), unsigned(OMSB), unsigned(OLSB)), \
              args);                                                       \
  } while (0);

#define addVariadicOp(XX, OID, OMSB, OLSB, NARGS, ARGS...) \
  addVariadicOp##NARGS (XX, OID, OMSB, OLSB, ##ARGS)

#define addCase(ARGS...) addVariadicOp (addCase, ##ARGS)
#define addParallelCase(ARGS...) addVariadicOp (addParallelCase, ##ARGS)

#define addState(ARGS...) addBinaryOp (addState, ##ARGS)
#define addNonState(ARGS...) addUnaryOp (addNonState, ##ARGS)

#define addAssertion(ID, BIT)                                \
  ibvm->addAssertion (BitVector::BitRange (                  \
      mapsym (string (#ID)), unsigned(BIT), unsigned(BIT))); \
  nassertions++;

#define addAssumption(ID, BIT, INITIAL)                         \
  ibvm->addAssumption (                                         \
      BitVector::BitRange (                                     \
          mapsym (string (#ID)), unsigned(BIT), unsigned(BIT)), \
      INITIAL);

//--------------------------------------------------------------------------------------

static void
model (BtorIBV* ibvm)
{
  //------ START of copy & pasted IBV file -------------------------------------

  addConstant (1, 00, 2) addVariable (3, counter, 2, 0, 0, 0) addVariable (
      4,
      next (counter),
      2,
      1,
      0,
      0) addState (counter,
                   1,
                   0,
                   00,
                   1,
                   0,
                   next (counter),
                   1,
                   0) addVariable (5,
                                   clock,
                                   1,
                                   0,
                                   0,
                                   0) addVariable (6, next (clock), 1, 1, 0, 0)
      addState (clock, 0, 0, 00, 0, 0, next (clock), 0, 0) addBitNot (
          next (clock),
          0,
          0,
          clock,
          0,
          0) addVariable (7,
                          succ (counter),
                          2,
                          0,
                          0,
                          0) addConstant (8, 01, 2) addSum (succ (counter),
                                                            1,
                                                            0,
                                                            counter,
                                                            1,
                                                            0,
                                                            01,
                                                            1,
                                                            0)
          addVariable (9, rising (clock), 1, 0, 0, 0) addVariable (
              10,
              !clock,
              1,
              0,
              0,
              0) addBitNot (!clock,
                            0,
                            0,
                            clock,
                            0,
                            0) addBitAnd (rising (clock),
                                          0,
                                          0,
                                          !clock,
                                          0,
                                          0,
                                          next (clock),
                                          0,
                                          0) addCondition (next (counter),
                                                           1,
                                                           0,
                                                           rising (clock),
                                                           0,
                                                           0,
                                                           succ (counter),
                                                           1,
                                                           0,
                                                           counter,
                                                           1,
                                                           0)

              addVariable (11, assert (counter == 0), 1, 0, 0, 0)
                  addVariable (12, assert (counter != 0), 1, 0, 0, 0) addEqual (
                      assert (counter == 0),
                      0,
                      counter,
                      1,
                      0,
                      00,
                      1,
                      0) addLogicalNot (assert (counter != 0),
                                        0,
                                        assert (counter == 0),
                                        0,
                                        0) addAssertion (assert (counter != 0),
                                                         0)

                      addConstant (13, 01, 2) addVariable (
                          14,
                          assert (counter < 1),
                          1,
                          0,
                          0,
                          0) addVariable (15, assert (counter >= 1), 1, 0, 0, 0)
                          addGreaterEqual (
                              assert (counter >= 1),
                              0,
                              counter,
                              1,
                              0,
                              01,
                              1,
                              0) addLogicalNot (assert (counter < 1),
                                                0,
                                                assert (counter >= 1),
                                                0,
                                                0) addAssertion (assert (counter
                                                                         < 1),
                                                                 0)

                              addConstant (16, 10, 2) addVariable (
                                  17,
                                  assert (counter == 2),
                                  1,
                                  0,
                                  0,
                                  0) addVariable (18,
                                                  assert (counter != 2),
                                                  1,
                                                  0,
                                                  0,
                                                  0) addEqual (assert (counter
                                                                       == 2),
                                                               0,
                                                               counter,
                                                               1,
                                                               0,
                                                               10,
                                                               1,
                                                               0)
                                  addLogicalNot (
                                      assert (counter != 2),
                                      0,
                                      assert (counter == 2),
                                      0,
                                      0) addAssertion (assert (counter != 2), 0)

                                      addVariable (
                                          19,
                                          assert (counter < 2),
                                          1,
                                          0,
                                          0,
                                          0) addVariable (20,
                                                          assert (counter >= 2),
                                                          1,
                                                          0,
                                                          0,
                                                          0)
                                          addGreaterEqual (
                                              assert (counter >= 2),
                                              0,
                                              counter,
                                              1,
                                              0,
                                              10,
                                              1,
                                              0) addLogicalNot (assert (counter
                                                                        < 2),
                                                                0,
                                                                assert (counter
                                                                        >= 2),
                                                                0,
                                                                0)
                                              addAssertion (
                                                  assert (counter < 2), 0)

                                                  addConstant (21, 11, 2) addVariable (
                                                      22,
                                                      assert (counter == 3),
                                                      1,
                                                      0,
                                                      0,
                                                      0)
                                                      addVariable (
                                                          23,
                                                          assert (counter != 3),
                                                          1,
                                                          0,
                                                          0,
                                                          0)
                                                          addEqual (assert (
                                                                        counter
                                                                        == 3),
                                                                    0,
                                                                    counter,
                                                                    1,
                                                                    0,
                                                                    11,
                                                                    1,
                                                                    0)
                                                              addLogicalNot (
                                                                  assert (
                                                                      counter
                                                                      != 3),
                                                                  0,
                                                                  assert (
                                                                      counter
                                                                      == 3),
                                                                  0,
                                                                  0)
                                                                  addAssertion (
                                                                      assert (
                                                                          counter
                                                                          != 3),
                                                                      0)

  //------ END of copy & pasted IBV file -------------------------------------
}

class Listener : virtual public BtorIBV::ReachedAtBoundListener
{
  vector<int> violated;

 public:
  void reachedAtBound (int i, int k)
  {
    assert (0 <= i), assert (0 <= k);
    while (violated.size () <= (size_t) i) violated.push_back (-1);
    if (violated[i] >= 0)
      cout << "listener: assertion " << i << " violated first at bound "
           << violated[i] << " and now again at bound " << k << endl;
    else
    {
      cout << "listener: assertion " << i << " violated at bound " << k << endl;
      violated[i] = k;
    }
  }
  int wasViolated (int i)
  {
    assert (0 <= i);
    if (i >= (int) violated.size ()) return -1;
    return violated[i];
  }
};

int
main ()
{
  const int k   = 10;  // Maximal bound for BMC run.
  BtorIBV* ibvm = new BtorIBV;
  // ibvm->setVerbosity (3);
  ibvm->setStop (false);
  model (ibvm);
  cout << "found " << nassertions << " assertions" << endl;
  ibvm->analyze ();
  cout << "analyzed model" << endl;
  ibvm->translate ();
  cout << "translated model" << endl;
  Listener* listener = new Listener;
  ibvm->setReachedAtBoundListener (listener);
  cout << "checking model up to bound " << k << endl;
  int r = ibvm->bmc (0, k);
  cout << "bounded model checker returns at bound " << r << endl;
  cout << "summarizing assertion violations" << endl;
  for (int i = 0; i < nassertions; i++)
  {
    int listener_violated = listener->wasViolated (i);
    int api_violated      = ibvm->hasAssertionBeenViolatedAtBound (i);
    assert (listener_violated == api_violated);
    if (listener_violated < 0)
      cout << "summary: assertion " << i << " not violated from bound 0 to "
           << k << endl;
    else
      cout << "summary: assertion " << i << " violated at bound "
           << listener_violated << endl;
  }
  delete listener;
  delete ibvm;
  return 0;
}
