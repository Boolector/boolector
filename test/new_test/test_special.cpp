/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
}

class TestSpecial : public TestFile
{
 protected:
  void run_sat_test (const char* name, const char* ext)
  {
    run_test (name, ext, BOOLECTOR_SAT);
  }

  void run_unsat_test (const char* name, const char* ext)
  {
    run_test (name, ext, BOOLECTOR_UNSAT);
  }
};

TEST_F (TestSpecial, const1) { run_sat_test ("const1", ".btor"); }

TEST_F (TestSpecial, const2) { run_unsat_test ("const2", ".btor"); }

TEST_F (TestSpecial, var1) { run_sat_test ("var1", ".btor"); }

TEST_F (TestSpecial, var2) { run_sat_test ("var2", ".btor"); }

TEST_F (TestSpecial, rw1) { run_sat_test ("rw1", ".btor"); }

TEST_F (TestSpecial, rw2) { run_sat_test ("rw2", ".btor"); }

TEST_F (TestSpecial, rw3) { run_sat_test ("rw3", ".btor"); }

TEST_F (TestSpecial, rw4) { run_sat_test ("rw4", ".btor"); }

TEST_F (TestSpecial, rw5) { run_sat_test ("rw5", ".btor"); }

TEST_F (TestSpecial, rw6) { run_sat_test ("rw6", ".btor"); }

TEST_F (TestSpecial, rw7) { run_sat_test ("rw7", ".btor"); }

TEST_F (TestSpecial, rw8) { run_sat_test ("rw8", ".btor"); }

TEST_F (TestSpecial, rw9) { run_sat_test ("rw9", ".btor"); }

TEST_F (TestSpecial, rw10) { run_sat_test ("rw10", ".btor"); }

TEST_F (TestSpecial, rw11) { run_sat_test ("rw11", ".btor"); }

TEST_F (TestSpecial, rw12) { run_sat_test ("rw12", ".btor"); }

TEST_F (TestSpecial, rw13) { run_sat_test ("rw13", ".btor"); }

TEST_F (TestSpecial, rw14) { run_sat_test ("rw14", ".btor"); }

TEST_F (TestSpecial, rw15) { run_sat_test ("rw15", ".btor"); }

TEST_F (TestSpecial, sqrt4) { run_sat_test ("sqrt4", ".btor"); }

TEST_F (TestSpecial, sqrt5) { run_unsat_test ("sqrt5", ".btor"); }

TEST_F (TestSpecial, sqrt7) { run_unsat_test ("sqrt7", ".btor"); }

TEST_F (TestSpecial, sqrt9) { run_sat_test ("sqrt9", ".btor"); }

TEST_F (TestSpecial, sqrt13) { run_unsat_test ("sqrt13", ".btor"); }

TEST_F (TestSpecial, sqrt25) { run_sat_test ("sqrt25", ".btor"); }

TEST_F (TestSpecial, sqrt29) { run_unsat_test ("sqrt29", ".btor"); }

TEST_F (TestSpecial, sqrt31) { run_unsat_test ("sqrt31", ".btor"); }

TEST_F (TestSpecial, sqrt49) { run_sat_test ("sqrt49", ".btor"); }

TEST_F (TestSpecial, sqrt53) { run_unsat_test ("sqrt53", ".btor"); }

TEST_F (TestSpecial, sqrt65537) { run_unsat_test ("sqrt65537", ".btor"); }

TEST_F (TestSpecial, sqrt4294967297)
{
  run_unsat_test ("sqrt4294967297", ".btor");
}

TEST_F (TestSpecial, sqrt4295098369)
{
  run_sat_test ("sqrt4295098369", ".btor");
}

TEST_F (TestSpecial, sqrt18446744073709551617)
{
  run_unsat_test ("sqrt18446744073709551617", ".btor");
}

TEST_F (TestSpecial, factor2209) { run_sat_test ("factor2209", ".btor"); }

TEST_F (TestSpecial, factor4294967295)
{
  run_sat_test ("factor4294967295", ".btor");
}

TEST_F (TestSpecial, factor4294967297)
{
  run_sat_test ("factor4294967297", ".btor");
}

TEST_F (TestSpecial, factor18446744073709551617const)
{
  run_sat_test ("factor18446744073709551617const", ".btor");
}

TEST_F (TestSpecial, factor18446744073709551617xconst)
{
  run_sat_test ("factor18446744073709551617xconst", ".btor");
}

TEST_F (TestSpecial, factor18446744073709551617yconst)
{
  run_sat_test ("factor18446744073709551617yconst", ".btor");
}

TEST_F (TestSpecial, read1) { run_unsat_test ("read1", ".btor"); }

TEST_F (TestSpecial, read2) { run_unsat_test ("read2", ".btor"); }

TEST_F (TestSpecial, read3) { run_sat_test ("read3", ".btor"); }

TEST_F (TestSpecial, read4) { run_unsat_test ("read4", ".btor"); }

TEST_F (TestSpecial, read5) { run_unsat_test ("read5", ".btor"); }

TEST_F (TestSpecial, read6) { run_unsat_test ("read6", ".btor"); }

TEST_F (TestSpecial, read7) { run_unsat_test ("read7", ".btor"); }

TEST_F (TestSpecial, read8) { run_unsat_test ("read8", ".btor"); }

TEST_F (TestSpecial, read9) { run_unsat_test ("read9", ".btor"); }

TEST_F (TestSpecial, read10) { run_unsat_test ("read10", ".btor"); }

TEST_F (TestSpecial, read11) { run_unsat_test ("read11", ".btor"); }

TEST_F (TestSpecial, read12) { run_sat_test ("read12", ".btor"); }

TEST_F (TestSpecial, read13) { run_sat_test ("read13", ".btor"); }

TEST_F (TestSpecial, read14) { run_sat_test ("read14", ".btor"); }

TEST_F (TestSpecial, read15) { run_sat_test ("read15", ".btor"); }

TEST_F (TestSpecial, read16) { run_unsat_test ("read16", ".btor"); }

TEST_F (TestSpecial, read17) { run_unsat_test ("read17", ".btor"); }

TEST_F (TestSpecial, read18) { run_sat_test ("read18", ".btor"); }

TEST_F (TestSpecial, read19) { run_unsat_test ("read19", ".btor"); }

TEST_F (TestSpecial, read20) { run_unsat_test ("read20", ".btor"); }

TEST_F (TestSpecial, read21) { run_unsat_test ("read21", ".btor"); }

TEST_F (TestSpecial, read22) { run_unsat_test ("read22", ".btor"); }

TEST_F (TestSpecial, write1) { run_unsat_test ("write1", ".btor"); }

TEST_F (TestSpecial, write2) { run_unsat_test ("write2", ".btor"); }

TEST_F (TestSpecial, write3) { run_unsat_test ("write3", ".btor"); }

TEST_F (TestSpecial, write4) { run_unsat_test ("write4", ".btor"); }

TEST_F (TestSpecial, write5) { run_sat_test ("write5", ".btor"); }

TEST_F (TestSpecial, write6) { run_unsat_test ("write6", ".btor"); }

TEST_F (TestSpecial, write7) { run_unsat_test ("write7", ".btor"); }

TEST_F (TestSpecial, write8) { run_unsat_test ("write8", ".btor"); }

TEST_F (TestSpecial, write9) { run_unsat_test ("write9", ".btor"); }

TEST_F (TestSpecial, write10) { run_unsat_test ("write10", ".btor"); }

TEST_F (TestSpecial, write11) { run_sat_test ("write11", ".btor"); }

TEST_F (TestSpecial, write12) { run_sat_test ("write12", ".btor"); }

TEST_F (TestSpecial, write13) { run_unsat_test ("write13", ".btor"); }

TEST_F (TestSpecial, write14) { run_unsat_test ("write14", ".btor"); }

TEST_F (TestSpecial, write15) { run_sat_test ("write15", ".btor"); }

TEST_F (TestSpecial, write16) { run_unsat_test ("write16", ".btor"); }

TEST_F (TestSpecial, write17) { run_unsat_test ("write17", ".btor"); }

TEST_F (TestSpecial, write18) { run_sat_test ("write18", ".btor"); }

TEST_F (TestSpecial, write19) { run_sat_test ("write19", ".btor"); }

TEST_F (TestSpecial, write20) { run_sat_test ("write20", ".btor"); }

TEST_F (TestSpecial, write21) { run_unsat_test ("write21", ".btor"); }

TEST_F (TestSpecial, write22) { run_unsat_test ("write22", ".btor"); }

TEST_F (TestSpecial, write23) { run_unsat_test ("write23", ".btor"); }

TEST_F (TestSpecial, write24) { run_unsat_test ("write24", ".btor"); }

TEST_F (TestSpecial, ext1) { run_sat_test ("ext1", ".btor"); }

TEST_F (TestSpecial, ext2) { run_unsat_test ("ext2", ".btor"); }

TEST_F (TestSpecial, ext3) { run_sat_test ("ext3", ".btor"); }

TEST_F (TestSpecial, ext4) { run_sat_test ("ext4", ".btor"); }

TEST_F (TestSpecial, ext5) { run_unsat_test ("ext5", ".btor"); }

TEST_F (TestSpecial, ext6) { run_sat_test ("ext6", ".btor"); }

TEST_F (TestSpecial, ext7) { run_unsat_test ("ext7", ".btor"); }

TEST_F (TestSpecial, ext8) { run_sat_test ("ext8", ".btor"); }

TEST_F (TestSpecial, ext9) { run_unsat_test ("ext9", ".btor"); }

TEST_F (TestSpecial, ext10) { run_unsat_test ("ext10", ".btor"); }

TEST_F (TestSpecial, ext11) { run_unsat_test ("ext11", ".btor"); }

TEST_F (TestSpecial, ext12) { run_sat_test ("ext12", ".btor"); }

TEST_F (TestSpecial, ext13) { run_unsat_test ("ext13", ".btor"); }

TEST_F (TestSpecial, ext14) { run_sat_test ("ext14", ".btor"); }

TEST_F (TestSpecial, ext15) { run_unsat_test ("ext15", ".btor"); }

TEST_F (TestSpecial, ext16) { run_unsat_test ("ext16", ".btor"); }

TEST_F (TestSpecial, ext17) { run_sat_test ("ext17", ".btor"); }

TEST_F (TestSpecial, ext18) { run_unsat_test ("ext18", ".btor"); }

TEST_F (TestSpecial, ext19) { run_unsat_test ("ext19", ".btor"); }

TEST_F (TestSpecial, ext20) { run_sat_test ("ext20", ".btor"); }

TEST_F (TestSpecial, ext21) { run_unsat_test ("ext21", ".btor"); }

TEST_F (TestSpecial, ext22) { run_unsat_test ("ext22", ".btor"); }

TEST_F (TestSpecial, ext23) { run_unsat_test ("ext23", ".btor"); }

TEST_F (TestSpecial, ext24) { run_unsat_test ("ext24", ".btor"); }

TEST_F (TestSpecial, ext25) { run_unsat_test ("ext25", ".btor"); }

TEST_F (TestSpecial, ext26) { run_unsat_test ("ext26", ".btor"); }

TEST_F (TestSpecial, ext27) { run_unsat_test ("ext27", ".btor"); }

TEST_F (TestSpecial, ext28) { run_unsat_test ("ext28", ".btor"); }

TEST_F (TestSpecial, ext29) { run_unsat_test ("ext29", ".btor"); }

TEST_F (TestSpecial, arraycond1) { run_sat_test ("arraycond1", ".btor"); }

TEST_F (TestSpecial, arraycond2) { run_sat_test ("arraycond2", ".btor"); }

TEST_F (TestSpecial, arraycond3) { run_unsat_test ("arraycond3", ".btor"); }

TEST_F (TestSpecial, arraycond4) { run_sat_test ("arraycond4", ".btor"); }

TEST_F (TestSpecial, arraycond5) { run_unsat_test ("arraycond5", ".btor"); }

TEST_F (TestSpecial, arraycond6) { run_unsat_test ("arraycond6", ".btor"); }

TEST_F (TestSpecial, arraycond7) { run_unsat_test ("arraycond7", ".btor"); }

TEST_F (TestSpecial, arraycond8) { run_unsat_test ("arraycond8", ".btor"); }

TEST_F (TestSpecial, arraycond9) { run_unsat_test ("arraycond9", ".btor"); }

TEST_F (TestSpecial, arraycond10) { run_sat_test ("arraycond10", ".btor"); }

TEST_F (TestSpecial, arraycond11) { run_unsat_test ("arraycond11", ".btor"); }

TEST_F (TestSpecial, arraycond12) { run_unsat_test ("arraycond12", ".btor"); }

TEST_F (TestSpecial, arraycond13) { run_unsat_test ("arraycond13", ".btor"); }

TEST_F (TestSpecial, arraycond14) { run_unsat_test ("arraycond14", ".btor"); }

TEST_F (TestSpecial, arraycond15) { run_sat_test ("arraycond15", ".btor"); }

TEST_F (TestSpecial, arraycond16) { run_sat_test ("arraycond16", ".btor"); }

TEST_F (TestSpecial, arraycond17) { run_sat_test ("arraycond17", ".btor"); }

TEST_F (TestSpecial, arraycond18) { run_unsat_test ("arraycond18", ".btor"); }

TEST_F (TestSpecial, substitute1) { run_sat_test ("substitute1", ".btor"); }

TEST_F (TestSpecial, substitute2) { run_unsat_test ("substitute2", ".btor"); }

TEST_F (TestSpecial, substitute3) { run_sat_test ("substitute3", ".btor"); }

TEST_F (TestSpecial, substitute4) { run_sat_test ("substitute4", ".btor"); }

TEST_F (TestSpecial, substitute5) { run_sat_test ("substitute5", ".btor"); }

TEST_F (TestSpecial, substitute6) { run_unsat_test ("substitute6", ".btor"); }

TEST_F (TestSpecial, substitute7) { run_unsat_test ("substitute7", ".btor"); }

TEST_F (TestSpecial, substitute8) { run_unsat_test ("substitute8", ".btor"); }

TEST_F (TestSpecial, substitute9) { run_unsat_test ("substitute9", ".btor"); }

TEST_F (TestSpecial, substitute10) { run_unsat_test ("substitute10", ".btor"); }

TEST_F (TestSpecial, substitute11) { run_unsat_test ("substitute11", ".btor"); }

TEST_F (TestSpecial, substitute12) { run_unsat_test ("substitute12", ".btor"); }

TEST_F (TestSpecial, substitute13) { run_unsat_test ("substitute13", ".btor"); }

TEST_F (TestSpecial, substitute14) { run_unsat_test ("substitute14", ".btor"); }

TEST_F (TestSpecial, substitute15) { run_unsat_test ("substitute15", ".btor"); }

TEST_F (TestSpecial, substitute16) { run_unsat_test ("substitute16", ".btor"); }

TEST_F (TestSpecial, substitute17) { run_unsat_test ("substitute17", ".btor"); }

TEST_F (TestSpecial, substitute18) { run_unsat_test ("substitute18", ".btor"); }

TEST_F (TestSpecial, substitute19) { run_unsat_test ("substitute19", ".btor"); }

TEST_F (TestSpecial, substitute20) { run_unsat_test ("substitute20", ".btor"); }

TEST_F (TestSpecial, substitute21) { run_unsat_test ("substitute21", ".btor"); }

TEST_F (TestSpecial, substitute22) { run_unsat_test ("substitute22", ".btor"); }

TEST_F (TestSpecial, substitute23) { run_unsat_test ("substitute23", ".btor"); }

TEST_F (TestSpecial, substitute24) { run_unsat_test ("substitute24", ".btor"); }

TEST_F (TestSpecial, substitute25) { run_unsat_test ("substitute25", ".btor"); }

TEST_F (TestSpecial, substitute26) { run_unsat_test ("substitute26", ".btor"); }

TEST_F (TestSpecial, substitute27) { run_unsat_test ("substitute27", ".btor"); }

TEST_F (TestSpecial, substitute28) { run_unsat_test ("substitute28", ".btor"); }

TEST_F (TestSpecial, substitute29) { run_unsat_test ("substitute29", ".btor"); }

TEST_F (TestSpecial, substitute30) { run_unsat_test ("substitute30", ".btor"); }

TEST_F (TestSpecial, substitute31) { run_unsat_test ("substitute31", ".btor"); }

TEST_F (TestSpecial, substitute32) { run_unsat_test ("substitute32", ".btor"); }

TEST_F (TestSpecial, substitute33) { run_unsat_test ("substitute33", ".btor"); }

TEST_F (TestSpecial, substitute34) { run_unsat_test ("substitute34", ".btor"); }

TEST_F (TestSpecial, substitute35) { run_unsat_test ("substitute35", ".btor"); }

TEST_F (TestSpecial, substitute36) { run_unsat_test ("substitute36", ".btor"); }

TEST_F (TestSpecial, substitute37) { run_unsat_test ("substitute37", ".btor"); }

TEST_F (TestSpecial, substitute38) { run_unsat_test ("substitute38", ".btor"); }

TEST_F (TestSpecial, substitute39) { run_unsat_test ("substitute39", ".btor"); }

TEST_F (TestSpecial, substitute40) { run_sat_test ("substitute40", ".btor"); }

TEST_F (TestSpecial, upprop1) { run_sat_test ("upprop1", ".btor"); }

TEST_F (TestSpecial, andopt1) { run_unsat_test ("andopt1", ".btor"); }

TEST_F (TestSpecial, andopt2) { run_unsat_test ("andopt2", ".btor"); }

TEST_F (TestSpecial, andopt3) { run_unsat_test ("andopt3", ".btor"); }
TEST_F (TestSpecial, andopt4) { run_unsat_test ("andopt4", ".btor"); }

TEST_F (TestSpecial, andopt5) { run_unsat_test ("andopt5", ".btor"); }

TEST_F (TestSpecial, andopt6) { run_unsat_test ("andopt6", ".btor"); }

TEST_F (TestSpecial, andopt7) { run_unsat_test ("andopt7", ".btor"); }

TEST_F (TestSpecial, andopt8) { run_unsat_test ("andopt8", ".btor"); }

TEST_F (TestSpecial, andopt9) { run_unsat_test ("andopt9", ".btor"); }

TEST_F (TestSpecial, andopt10) { run_unsat_test ("andopt10", ".btor"); }

TEST_F (TestSpecial, andopt11) { run_unsat_test ("andopt11", ".btor"); }

TEST_F (TestSpecial, andopt12) { run_unsat_test ("andopt12", ".btor"); }

TEST_F (TestSpecial, andopt13) { run_unsat_test ("andopt13", ".btor"); }

TEST_F (TestSpecial, andopt14) { run_unsat_test ("andopt14", ".btor"); }

TEST_F (TestSpecial, andopt15) { run_unsat_test ("andopt15", ".btor"); }

TEST_F (TestSpecial, andopt16) { run_unsat_test ("andopt16", ".btor"); }

TEST_F (TestSpecial, andopt17) { run_unsat_test ("andopt17", ".btor"); }

TEST_F (TestSpecial, regrrwbinexpconcatzeroconst)
{
  run_sat_test ("regrrwbinexpconcatzeroconst", ".btor");
}

TEST_F (TestSpecial, lambda1) { run_sat_test ("lambda1", ".btor"); }

TEST_F (TestSpecial, lambda2) { run_unsat_test ("lambda2", ".btor"); }

TEST_F (TestSpecial, regrmodel1) { run_sat_test ("regrmodel1", ".btor"); }

TEST_F (TestSpecial, regrmodel2) { run_unsat_test ("regrmodel2", ".btor"); }

TEST_F (TestSpecial, regrmodel3) { run_sat_test ("regrmodel3", ".btor"); }

TEST_F (TestSpecial, regrmodel4) { run_sat_test ("regrmodel4", ".btor"); }

TEST_F (TestSpecial, regrcalypto1) { run_unsat_test ("regrcalypto1", ".smt2"); }

TEST_F (TestSpecial, regrcalypto2) { run_unsat_test ("regrcalypto2", ".smt2"); }

TEST_F (TestSpecial, regrcalypto3) { run_unsat_test ("regrcalypto3", ".smt2"); }

TEST_F (TestSpecial, verbose1_1)
{
  run_test ("verbose1", ".btor", BOOLECTOR_UNKNOWN, 1);
}

TEST_F (TestSpecial, verbose1_2)
{
  run_test ("verbose1", ".btor", BOOLECTOR_UNKNOWN, 2);
}

TEST_F (TestSpecial, verbose1_3)
{
  run_test ("verbose1", ".btor", BOOLECTOR_UNKNOWN, 3);
}

TEST_F (TestSpecial, verbose2_1)
{
  run_test ("verbose2", ".btor", BOOLECTOR_UNKNOWN, 1);
}

TEST_F (TestSpecial, verbose2_2)
{
  run_test ("verbose2", ".btor", BOOLECTOR_UNKNOWN, 2);
}

TEST_F (TestSpecial, verbose2_3)
{
  run_test ("verbose2", ".btor", BOOLECTOR_UNKNOWN, 3);
}
