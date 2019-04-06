/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolector.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BTOR_TEST_SPECIAL_TEMP_OUTFILE_NAME "specialout.tmp"

static char *g_btor_str = NULL;
static FILE *g_fout     = NULL;
static Btor *g_btor;
static BtorMemMgr *g_mm;

void
init_special_tests (void)
{
  g_mm = btor_mem_mgr_new ();
  BTOR_NEWN (g_mm, g_btor_str, strlen (btor_bin_dir) + 20);
  sprintf (g_btor_str, "%sboolector", btor_bin_dir);
}

static void
run_test (char *name, int32_t expected)
{
  char *full_name;
  FILE *fin, *g_fout;
  int32_t parse_res, parse_status;
  char *parse_err;
  size_t len;

  g_btor = boolector_new ();
  boolector_set_opt (g_btor, BTOR_OPT_INCREMENTAL, 1);
  len = strlen (btor_log_dir) + strlen (name) + 1;
  BTOR_NEWN (g_mm, full_name, len);
  strcpy (full_name, btor_log_dir);
  strcat (full_name, name);
  fin = fopen (full_name, "r");
  assert (fin != NULL);
  g_fout = fopen (BTOR_TEST_SPECIAL_TEMP_OUTFILE_NAME, "w");
  assert (g_fout != NULL);
  parse_res = boolector_parse (
      g_btor, fin, full_name, g_fout, &parse_err, &parse_status);
  assert (parse_res != BOOLECTOR_PARSE_ERROR);
  assert (boolector_sat (g_btor) == expected);
  fclose (fin);
  fclose (g_fout);
  BTOR_DELETEN (g_mm, full_name, len);
  boolector_delete (g_btor);
}

static void
run_sat_test (char *name)
{
  run_test (name, BOOLECTOR_SAT);
}

static void
run_unsat_test (char *name)
{
  run_test (name, BOOLECTOR_UNSAT);
}

static void
test_const1_special ()
{
  run_sat_test ("const1.btor");
}

static void
test_const2_special ()
{
  run_unsat_test ("const2.btor");
}

static void
test_var1_special ()
{
  run_sat_test ("var1.btor");
}

static void
test_var2_special ()
{
  run_sat_test ("var2.btor");
}

static void
test_rw1_special ()
{
  run_sat_test ("rw1.btor");
}

static void
test_rw2_special ()
{
  run_sat_test ("rw2.btor");
}

static void
test_rw3_special ()
{
  run_sat_test ("rw3.btor");
}

static void
test_rw4_special ()
{
  run_sat_test ("rw4.btor");
}

static void
test_rw5_special ()
{
  run_sat_test ("rw5.btor");
}

static void
test_rw6_special ()
{
  run_sat_test ("rw6.btor");
}

static void
test_rw7_special ()
{
  run_sat_test ("rw7.btor");
}

static void
test_rw8_special ()
{
  run_sat_test ("rw8.btor");
}

static void
test_rw9_special ()
{
  run_sat_test ("rw9.btor");
}

static void
test_rw10_special ()
{
  run_sat_test ("rw10.btor");
}

static void
test_rw11_special ()
{
  run_sat_test ("rw11.btor");
}

static void
test_rw12_special ()
{
  run_sat_test ("rw12.btor");
}

static void
test_rw13_special ()
{
  run_sat_test ("rw13.btor");
}

static void
test_rw14_special ()
{
  run_sat_test ("rw14.btor");
}

static void
test_rw15_special ()
{
  run_sat_test ("rw15.btor");
}

static void
test_sqrt4_special ()
{
  run_sat_test ("sqrt4.btor");
}

static void
test_sqrt5_special ()
{
  run_unsat_test ("sqrt5.btor");
}

static void
test_sqrt7_special ()
{
  run_unsat_test ("sqrt7.btor");
}

static void
test_sqrt9_special ()
{
  run_sat_test ("sqrt9.btor");
}

static void
test_sqrt13_special ()
{
  run_unsat_test ("sqrt13.btor");
}

static void
test_sqrt25_special ()
{
  run_sat_test ("sqrt25.btor");
}

static void
test_sqrt29_special ()
{
  run_unsat_test ("sqrt29.btor");
}

static void
test_sqrt31_special ()
{
  run_unsat_test ("sqrt31.btor");
}

static void
test_sqrt49_special ()
{
  run_sat_test ("sqrt49.btor");
}

static void
test_sqrt53_special ()
{
  run_unsat_test ("sqrt53.btor");
}

static void
test_sqrt65537_special ()
{
  run_unsat_test ("sqrt65537.btor");
}

static void
test_sqrt4294967297_special ()
{
  run_unsat_test ("sqrt4294967297.btor");
}

static void
test_sqrt4295098369_special ()
{
  run_sat_test ("sqrt4295098369.btor");
}

static void
test_sqrt18446744073709551617_special ()
{
  run_unsat_test ("sqrt18446744073709551617.btor");
}

static void
test_factor2209_special ()
{
  run_sat_test ("factor2209.btor");
}

static void
test_factor4294967295_special ()
{
  run_sat_test ("factor4294967295.btor");
}

static void
test_factor4294967297_special ()
{
  run_sat_test ("factor4294967297.btor");
}

static void
test_factor18446744073709551617const_special ()
{
  run_sat_test ("factor18446744073709551617const.btor");
}

static void
test_factor18446744073709551617xconst_special ()
{
  run_sat_test ("factor18446744073709551617xconst.btor");
}

static void
test_factor18446744073709551617yconst_special ()
{
  run_sat_test ("factor18446744073709551617yconst.btor");
}

static void
test_read1_special ()
{
  run_unsat_test ("read1.btor");
}

static void
test_read2_special ()
{
  run_unsat_test ("read2.btor");
}

static void
test_read3_special ()
{
  run_sat_test ("read3.btor");
}

static void
test_read4_special ()
{
  run_unsat_test ("read4.btor");
}

static void
test_read5_special ()
{
  run_unsat_test ("read5.btor");
}

static void
test_read6_special ()
{
  run_unsat_test ("read6.btor");
}

static void
test_read7_special ()
{
  run_unsat_test ("read7.btor");
}

static void
test_read8_special ()
{
  run_unsat_test ("read8.btor");
}

static void
test_read9_special ()
{
  run_unsat_test ("read9.btor");
}

static void
test_read10_special ()
{
  run_unsat_test ("read10.btor");
}

static void
test_read11_special ()
{
  run_unsat_test ("read11.btor");
}

static void
test_read12_special ()
{
  run_sat_test ("read12.btor");
}

static void
test_read13_special ()
{
  run_sat_test ("read13.btor");
}

static void
test_read14_special ()
{
  run_sat_test ("read14.btor");
}

static void
test_read15_special ()
{
  run_sat_test ("read15.btor");
}

static void
test_read16_special ()
{
  run_unsat_test ("read16.btor");
}

static void
test_read17_special ()
{
  run_unsat_test ("read17.btor");
}

static void
test_read18_special ()
{
  run_sat_test ("read18.btor");
}

static void
test_read19_special ()
{
  run_unsat_test ("read19.btor");
}

static void
test_read20_special ()
{
  run_unsat_test ("read20.btor");
}

static void
test_read21_special ()
{
  run_unsat_test ("read21.btor");
}

static void
test_read22_special ()
{
  run_unsat_test ("read22.btor");
}

static void
test_write1_special ()
{
  run_unsat_test ("write1.btor");
}

static void
test_write2_special ()
{
  run_unsat_test ("write2.btor");
}

static void
test_write3_special ()
{
  run_unsat_test ("write3.btor");
}

static void
test_write4_special ()
{
  run_unsat_test ("write4.btor");
}

static void
test_write5_special ()
{
  run_sat_test ("write5.btor");
}

static void
test_write6_special ()
{
  run_unsat_test ("write6.btor");
}

static void
test_write7_special ()
{
  run_unsat_test ("write7.btor");
}

static void
test_write8_special ()
{
  run_unsat_test ("write8.btor");
}

static void
test_write9_special ()
{
  run_unsat_test ("write9.btor");
}

static void
test_write10_special ()
{
  run_unsat_test ("write10.btor");
}

static void
test_write11_special ()
{
  run_sat_test ("write11.btor");
}

static void
test_write12_special ()
{
  run_sat_test ("write12.btor");
}

static void
test_write13_special ()
{
  run_unsat_test ("write13.btor");
}

static void
test_write14_special ()
{
  run_unsat_test ("write14.btor");
}

static void
test_write15_special ()
{
  run_sat_test ("write15.btor");
}

static void
test_write16_special ()
{
  run_unsat_test ("write16.btor");
}

static void
test_write17_special ()
{
  run_unsat_test ("write17.btor");
}

static void
test_write18_special ()
{
  run_sat_test ("write18.btor");
}

static void
test_write19_special ()
{
  run_sat_test ("write19.btor");
}

static void
test_write20_special ()
{
  run_sat_test ("write20.btor");
}

static void
test_write21_special ()
{
  run_unsat_test ("write21.btor");
}

static void
test_write22_special ()
{
  run_unsat_test ("write22.btor");
}

static void
test_write23_special ()
{
  run_unsat_test ("write23.btor");
}

static void
test_write24_special ()
{
  run_unsat_test ("write24.btor");
}

static void
test_ext1_special ()
{
  run_sat_test ("ext1.btor");
}

static void
test_ext2_special ()
{
  run_unsat_test ("ext2.btor");
}

static void
test_ext3_special ()
{
  run_sat_test ("ext3.btor");
}

static void
test_ext4_special ()
{
  run_sat_test ("ext4.btor");
}

static void
test_ext5_special ()
{
  run_unsat_test ("ext5.btor");
}

static void
test_ext6_special ()
{
  run_sat_test ("ext6.btor");
}

static void
test_ext7_special ()
{
  run_unsat_test ("ext7.btor");
}

static void
test_ext8_special ()
{
  run_sat_test ("ext8.btor");
}

static void
test_ext9_special ()
{
  run_unsat_test ("ext9.btor");
}

static void
test_ext10_special ()
{
  run_unsat_test ("ext10.btor");
}

static void
test_ext11_special ()
{
  run_unsat_test ("ext11.btor");
}

static void
test_ext12_special ()
{
  run_sat_test ("ext12.btor");
}

static void
test_ext13_special ()
{
  run_unsat_test ("ext13.btor");
}

static void
test_ext14_special ()
{
  run_sat_test ("ext14.btor");
}

static void
test_ext15_special ()
{
  run_unsat_test ("ext15.btor");
}

static void
test_ext16_special ()
{
  run_unsat_test ("ext16.btor");
}

static void
test_ext17_special ()
{
  run_sat_test ("ext17.btor");
}

static void
test_ext18_special ()
{
  run_unsat_test ("ext18.btor");
}

static void
test_ext19_special ()
{
  run_unsat_test ("ext19.btor");
}

static void
test_ext20_special ()
{
  run_sat_test ("ext20.btor");
}

static void
test_ext21_special ()
{
  run_unsat_test ("ext21.btor");
}

static void
test_ext22_special ()
{
  run_unsat_test ("ext22.btor");
}

static void
test_ext23_special ()
{
  run_unsat_test ("ext23.btor");
}

static void
test_ext24_special ()
{
  run_unsat_test ("ext24.btor");
}

static void
test_ext25_special ()
{
  run_unsat_test ("ext25.btor");
}

static void
test_ext26_special ()
{
  run_unsat_test ("ext26.btor");
}

static void
test_ext27_special ()
{
  run_unsat_test ("ext27.btor");
}

static void
test_ext28_special ()
{
  run_unsat_test ("ext28.btor");
}

static void
test_ext29_special ()
{
  run_unsat_test ("ext29.btor");
}

static void
test_arraycond1_special ()
{
  run_sat_test ("arraycond1.btor");
}

static void
test_arraycond2_special ()
{
  run_sat_test ("arraycond2.btor");
}

static void
test_arraycond3_special ()
{
  run_unsat_test ("arraycond3.btor");
}

static void
test_arraycond4_special ()
{
  run_sat_test ("arraycond4.btor");
}

static void
test_arraycond5_special ()
{
  run_unsat_test ("arraycond5.btor");
}

static void
test_arraycond6_special ()
{
  run_unsat_test ("arraycond6.btor");
}

static void
test_arraycond7_special ()
{
  run_unsat_test ("arraycond7.btor");
}

static void
test_arraycond8_special ()
{
  run_unsat_test ("arraycond8.btor");
}

static void
test_arraycond9_special ()
{
  run_unsat_test ("arraycond9.btor");
}

static void
test_arraycond10_special ()
{
  run_sat_test ("arraycond10.btor");
}

static void
test_arraycond11_special ()
{
  run_unsat_test ("arraycond11.btor");
}

static void
test_arraycond12_special ()
{
  run_unsat_test ("arraycond12.btor");
}

static void
test_arraycond13_special ()
{
  run_unsat_test ("arraycond13.btor");
}

static void
test_arraycond14_special ()
{
  run_unsat_test ("arraycond14.btor");
}

static void
test_arraycond15_special ()
{
  run_sat_test ("arraycond15.btor");
}

static void
test_arraycond16_special ()
{
  run_sat_test ("arraycond16.btor");
}

static void
test_arraycond17_special ()
{
  run_sat_test ("arraycond17.btor");
}

static void
test_arraycond18_special ()
{
  run_unsat_test ("arraycond18.btor");
}

static void
test_substitute1_special ()
{
  run_sat_test ("substitute1.btor");
}

static void
test_substitute2_special ()
{
  run_unsat_test ("substitute2.btor");
}

static void
test_substitute3_special ()
{
  run_sat_test ("substitute3.btor");
}

static void
test_substitute4_special ()
{
  run_sat_test ("substitute4.btor");
}

static void
test_substitute5_special ()
{
  run_sat_test ("substitute5.btor");
}

static void
test_substitute6_special ()
{
  run_unsat_test ("substitute6.btor");
}

static void
test_substitute7_special ()
{
  run_unsat_test ("substitute7.btor");
}

static void
test_substitute8_special ()
{
  run_unsat_test ("substitute8.btor");
}

static void
test_substitute9_special ()
{
  run_unsat_test ("substitute9.btor");
}

static void
test_substitute10_special ()
{
  run_unsat_test ("substitute10.btor");
}

static void
test_substitute11_special ()
{
  run_unsat_test ("substitute11.btor");
}

static void
test_substitute12_special ()
{
  run_unsat_test ("substitute12.btor");
}

static void
test_substitute13_special ()
{
  run_unsat_test ("substitute13.btor");
}

static void
test_substitute14_special ()
{
  run_unsat_test ("substitute14.btor");
}

static void
test_substitute15_special ()
{
  run_unsat_test ("substitute15.btor");
}

static void
test_substitute16_special ()
{
  run_unsat_test ("substitute16.btor");
}

static void
test_substitute17_special ()
{
  run_unsat_test ("substitute17.btor");
}

static void
test_substitute18_special ()
{
  run_unsat_test ("substitute18.btor");
}

static void
test_substitute19_special ()
{
  run_unsat_test ("substitute19.btor");
}

static void
test_substitute20_special ()
{
  run_unsat_test ("substitute20.btor");
}

static void
test_substitute21_special ()
{
  run_unsat_test ("substitute21.btor");
}

static void
test_substitute22_special ()
{
  run_unsat_test ("substitute22.btor");
}

static void
test_substitute23_special ()
{
  run_unsat_test ("substitute23.btor");
}

static void
test_substitute24_special ()
{
  run_unsat_test ("substitute24.btor");
}

static void
test_substitute25_special ()
{
  run_unsat_test ("substitute25.btor");
}

static void
test_substitute26_special ()
{
  run_unsat_test ("substitute26.btor");
}

static void
test_substitute27_special ()
{
  run_unsat_test ("substitute27.btor");
}

static void
test_substitute28_special ()
{
  run_unsat_test ("substitute28.btor");
}

static void
test_substitute29_special ()
{
  run_unsat_test ("substitute29.btor");
}

static void
test_substitute30_special ()
{
  run_unsat_test ("substitute30.btor");
}

static void
test_substitute31_special ()
{
  run_unsat_test ("substitute31.btor");
}

static void
test_substitute32_special ()
{
  run_unsat_test ("substitute32.btor");
}

static void
test_substitute33_special ()
{
  run_unsat_test ("substitute33.btor");
}

static void
test_substitute34_special ()
{
  run_unsat_test ("substitute34.btor");
}

static void
test_substitute35_special ()
{
  run_unsat_test ("substitute35.btor");
}

static void
test_substitute36_special ()
{
  run_unsat_test ("substitute36.btor");
}

static void
test_substitute37_special ()
{
  run_unsat_test ("substitute37.btor");
}

static void
test_substitute38_special ()
{
  run_unsat_test ("substitute38.btor");
}

static void
test_substitute39_special ()
{
  run_unsat_test ("substitute39.btor");
}

static void
test_substitute40_special ()
{
  run_sat_test ("substitute40.btor");
}

static void
test_upprop1_special ()
{
  run_sat_test ("upprop1.btor");
}

static void
test_andopt1_special ()
{
  run_unsat_test ("andopt1.btor");
}

static void
test_andopt2_special ()
{
  run_unsat_test ("andopt2.btor");
}

static void
test_andopt3_special ()
{
  run_unsat_test ("andopt3.btor");
}
static void
test_andopt4_special ()
{
  run_unsat_test ("andopt4.btor");
}

static void
test_andopt5_special ()
{
  run_unsat_test ("andopt5.btor");
}

static void
test_andopt6_special ()
{
  run_unsat_test ("andopt6.btor");
}

static void
test_andopt7_special ()
{
  run_unsat_test ("andopt7.btor");
}

static void
test_andopt8_special ()
{
  run_unsat_test ("andopt8.btor");
}

static void
test_andopt9_special ()
{
  run_unsat_test ("andopt9.btor");
}

static void
test_andopt10_special ()
{
  run_unsat_test ("andopt10.btor");
}

static void
test_andopt11_special ()
{
  run_unsat_test ("andopt11.btor");
}

static void
test_andopt12_special ()
{
  run_unsat_test ("andopt12.btor");
}

static void
test_andopt13_special ()
{
  run_unsat_test ("andopt13.btor");
}

static void
test_andopt14_special ()
{
  run_unsat_test ("andopt14.btor");
}

static void
test_andopt15_special ()
{
  run_unsat_test ("andopt15.btor");
}

static void
test_andopt16_special ()
{
  run_unsat_test ("andopt16.btor");
}

static void
test_andopt17_special ()
{
  run_unsat_test ("andopt17.btor");
}

static void
test_regrrwbinexpconcatzeroconst_special ()
{
  run_sat_test ("regrrwbinexpconcatzeroconst.btor");
}

static void
test_lambda1_special ()
{
  run_sat_test ("lambda1.btor");
}

static void
test_lambda2_special ()
{
  run_unsat_test ("lambda2.btor");
}

static void
test_regrmodel1_special ()
{
  run_sat_test ("regrmodel1.btor");
}

static void
test_regrmodel2_special ()
{
  run_unsat_test ("regrmodel2.btor");
}

static void
test_regrmodel3_special ()
{
  run_sat_test ("regrmodel3.btor");
}

static void
test_regrmodel4_special ()
{
  run_sat_test ("regrmodel4.btor");
}

static void
test_regrcalypto1_special ()
{
  run_unsat_test ("regrcalypto1.smt2");
}

static void
test_regrcalypto2_special ()
{
  run_unsat_test ("regrcalypto2.smt2");
}

static void
test_regrcalypto3_special ()
{
  run_unsat_test ("regrcalypto3.smt2");
}

static int32_t
run_verbose_test (char *name, int32_t verbosity)
{
  assert (verbosity > 0);
  assert (verbosity <= 3);

  char *full_name;
  char *redirect_str, *v1_str, *v2_str, *v3_str, *v_str;
  char *syscall_str;
  int32_t res;
  size_t len, len_syscall_str;

  len = strlen (btor_log_dir) + strlen (name) + 1;
  BTOR_NEWN (g_mm, full_name, len);

  redirect_str = "> /dev/null";
  v1_str       = "-v";
  v2_str       = "-v -v";
  v3_str       = "-v -v -v";

  strcpy (full_name, btor_log_dir);
  strcat (full_name, name);

  switch (verbosity)
  {
    case 1: v_str = v1_str; break;
    case 2: v_str = v2_str; break;
    default:
      assert (verbosity == 3);
      v_str = v3_str;
      break;
  }

  len_syscall_str = strlen (g_btor_str) + 1 + strlen (full_name) + 1
                    + strlen (v_str) + 1 + strlen (redirect_str) + 1;
  BTOR_NEWN (g_mm, syscall_str, len_syscall_str);
  sprintf (
      syscall_str, "%s %s %s %s", g_btor_str, full_name, v_str, redirect_str);
  /* we are not interested in the output,
   * we just want to run 'verbosity' code
   * A system call is used, as verbose messages
   * are always written to stdout and we have
   * to redirect them.
   */
  res = system (syscall_str);
  BTOR_DELETEN (g_mm, syscall_str, len_syscall_str);
  BTOR_DELETEN (g_mm, full_name, len);
  return res;
}

static void
test_verbose1_special ()
{
  run_verbose_test ("verbose1.btor", 1);
  run_verbose_test ("verbose1.btor", 2);
  run_verbose_test ("verbose1.btor", 3);
}

static void
test_verbose2_special ()
{
  run_verbose_test ("verbose2.btor", 1);
  run_verbose_test ("verbose2.btor", 2);
  run_verbose_test ("verbose2.btor", 3);
}

void
run_special_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (const1_special);
  BTOR_RUN_TEST (const2_special);
  BTOR_RUN_TEST (var1_special);
  BTOR_RUN_TEST (var2_special);
  BTOR_RUN_TEST (rw1_special);
  BTOR_RUN_TEST (rw2_special);
  BTOR_RUN_TEST (rw3_special);
  BTOR_RUN_TEST (rw4_special);
  BTOR_RUN_TEST (rw5_special);
  BTOR_RUN_TEST (rw6_special);
  BTOR_RUN_TEST (rw7_special);
  BTOR_RUN_TEST (rw8_special);
  BTOR_RUN_TEST (rw9_special);
  BTOR_RUN_TEST (rw10_special);
  BTOR_RUN_TEST (rw11_special);
  BTOR_RUN_TEST (rw12_special);
  BTOR_RUN_TEST (rw13_special);
  BTOR_RUN_TEST (rw14_special);
  BTOR_RUN_TEST (rw15_special);
  BTOR_RUN_TEST (sqrt4_special);
  BTOR_RUN_TEST (sqrt5_special);
  BTOR_RUN_TEST (sqrt7_special);
  BTOR_RUN_TEST (sqrt9_special);
  BTOR_RUN_TEST (sqrt13_special);
  BTOR_RUN_TEST (sqrt25_special);
  BTOR_RUN_TEST (sqrt29_special);
  BTOR_RUN_TEST (sqrt31_special);
  BTOR_RUN_TEST (sqrt49_special);
  BTOR_RUN_TEST (sqrt53_special);
  BTOR_RUN_TEST (sqrt65537_special);
  BTOR_RUN_TEST (sqrt4294967297_special);
  BTOR_RUN_TEST (sqrt4295098369_special);
  BTOR_RUN_TEST (sqrt18446744073709551617_special);
  BTOR_RUN_TEST (factor2209_special);
  BTOR_RUN_TEST (factor4294967295_special);
  BTOR_RUN_TEST (factor4294967297_special);
  BTOR_RUN_TEST (factor18446744073709551617const_special);
  BTOR_RUN_TEST (factor18446744073709551617xconst_special);
  BTOR_RUN_TEST (factor18446744073709551617yconst_special);
  BTOR_RUN_TEST (read1_special);
  BTOR_RUN_TEST (read2_special);
  BTOR_RUN_TEST (read3_special);
  BTOR_RUN_TEST (read4_special);
  BTOR_RUN_TEST (read5_special);
  BTOR_RUN_TEST (read6_special);
  BTOR_RUN_TEST (read7_special);
  BTOR_RUN_TEST (read8_special);
  BTOR_RUN_TEST (read9_special);
  BTOR_RUN_TEST (read10_special);
  BTOR_RUN_TEST (read11_special);
  BTOR_RUN_TEST (read12_special);
  BTOR_RUN_TEST (read13_special);
  BTOR_RUN_TEST (read14_special);
  BTOR_RUN_TEST (read15_special);
  BTOR_RUN_TEST (read16_special);
  BTOR_RUN_TEST (read17_special);
  BTOR_RUN_TEST (read18_special);
  BTOR_RUN_TEST (read19_special);
  BTOR_RUN_TEST (read20_special);
  BTOR_RUN_TEST (read21_special);
  BTOR_RUN_TEST (read22_special);
  BTOR_RUN_TEST (write1_special);
  BTOR_RUN_TEST (write2_special);
  BTOR_RUN_TEST (write3_special);
  BTOR_RUN_TEST (write4_special);
  BTOR_RUN_TEST (write5_special);
  BTOR_RUN_TEST (write6_special);
  BTOR_RUN_TEST (write7_special);
  BTOR_RUN_TEST (write8_special);
  BTOR_RUN_TEST (write9_special);
  BTOR_RUN_TEST (write10_special);
  BTOR_RUN_TEST (write11_special);
  BTOR_RUN_TEST (write12_special);
  BTOR_RUN_TEST (write13_special);
  BTOR_RUN_TEST (write14_special);
  BTOR_RUN_TEST (write15_special);
  BTOR_RUN_TEST (write16_special);
  BTOR_RUN_TEST (write17_special);
  BTOR_RUN_TEST (write18_special);
  BTOR_RUN_TEST (write19_special);
  BTOR_RUN_TEST (write20_special);
  BTOR_RUN_TEST (write21_special);
  BTOR_RUN_TEST (write22_special);
  BTOR_RUN_TEST (write23_special);
  BTOR_RUN_TEST (write24_special);
  BTOR_RUN_TEST (ext1_special);
  BTOR_RUN_TEST (ext2_special);
  BTOR_RUN_TEST (ext3_special);
  BTOR_RUN_TEST (ext4_special);
  BTOR_RUN_TEST (ext5_special);
  BTOR_RUN_TEST (ext6_special);
  BTOR_RUN_TEST (ext7_special);
  BTOR_RUN_TEST (ext8_special);
  BTOR_RUN_TEST (ext9_special);
  BTOR_RUN_TEST (ext10_special);
  BTOR_RUN_TEST (ext11_special);
  BTOR_RUN_TEST (ext12_special);
  BTOR_RUN_TEST (ext13_special);
  BTOR_RUN_TEST (ext14_special);
  BTOR_RUN_TEST (ext15_special);
  BTOR_RUN_TEST (ext16_special);
  BTOR_RUN_TEST (ext17_special);
  BTOR_RUN_TEST (ext18_special);
  BTOR_RUN_TEST (ext19_special);
  BTOR_RUN_TEST (ext20_special);
  BTOR_RUN_TEST (ext21_special);
  BTOR_RUN_TEST (ext22_special);
  BTOR_RUN_TEST (ext23_special);
  BTOR_RUN_TEST (ext24_special);
  BTOR_RUN_TEST (ext25_special);
  BTOR_RUN_TEST (ext26_special);
  BTOR_RUN_TEST (ext27_special);
  BTOR_RUN_TEST (ext28_special);
  BTOR_RUN_TEST (ext29_special);
  BTOR_RUN_TEST (arraycond1_special);
  BTOR_RUN_TEST (arraycond2_special);
  BTOR_RUN_TEST (arraycond3_special);
  BTOR_RUN_TEST (arraycond4_special);
  BTOR_RUN_TEST (arraycond5_special);
  BTOR_RUN_TEST (arraycond6_special);
  BTOR_RUN_TEST (arraycond7_special);
  BTOR_RUN_TEST (arraycond8_special);
  BTOR_RUN_TEST (arraycond9_special);
  BTOR_RUN_TEST (arraycond10_special);
  BTOR_RUN_TEST (arraycond11_special);
  BTOR_RUN_TEST (arraycond12_special);
  BTOR_RUN_TEST (arraycond13_special);
  BTOR_RUN_TEST (arraycond14_special);
  BTOR_RUN_TEST (arraycond15_special);
  BTOR_RUN_TEST (arraycond16_special);
  BTOR_RUN_TEST (arraycond17_special);
  BTOR_RUN_TEST (arraycond18_special);
  BTOR_RUN_TEST (substitute1_special);
  BTOR_RUN_TEST (substitute2_special);
  BTOR_RUN_TEST (substitute3_special);
  BTOR_RUN_TEST (substitute4_special);
  BTOR_RUN_TEST (substitute5_special);
  BTOR_RUN_TEST (substitute6_special);
  BTOR_RUN_TEST (substitute7_special);
  BTOR_RUN_TEST (substitute8_special);
  BTOR_RUN_TEST (substitute9_special);
  BTOR_RUN_TEST (substitute10_special);
  BTOR_RUN_TEST (substitute11_special);
  BTOR_RUN_TEST (substitute12_special);
  BTOR_RUN_TEST (substitute13_special);
  BTOR_RUN_TEST (substitute14_special);
  BTOR_RUN_TEST (substitute15_special);
  BTOR_RUN_TEST (substitute16_special);
  BTOR_RUN_TEST (substitute17_special);
  BTOR_RUN_TEST (substitute18_special);
  BTOR_RUN_TEST (substitute19_special);
  BTOR_RUN_TEST (substitute20_special);
  BTOR_RUN_TEST (substitute21_special);
  BTOR_RUN_TEST (substitute22_special);
  BTOR_RUN_TEST (substitute23_special);
  BTOR_RUN_TEST (substitute24_special);
  BTOR_RUN_TEST (substitute25_special);
  BTOR_RUN_TEST (substitute26_special);
  BTOR_RUN_TEST (substitute27_special);
  BTOR_RUN_TEST (substitute28_special);
  BTOR_RUN_TEST (substitute29_special);
  BTOR_RUN_TEST (substitute30_special);
  BTOR_RUN_TEST (substitute31_special);
  BTOR_RUN_TEST (substitute32_special);
  BTOR_RUN_TEST (substitute33_special);
  BTOR_RUN_TEST (substitute34_special);
  BTOR_RUN_TEST (substitute35_special);
  BTOR_RUN_TEST (substitute36_special);
  BTOR_RUN_TEST (substitute37_special);
  BTOR_RUN_TEST (substitute38_special);
  BTOR_RUN_TEST (substitute39_special);
  BTOR_RUN_TEST (substitute40_special);
  BTOR_RUN_TEST (upprop1_special);
  BTOR_RUN_TEST (andopt1_special);
  BTOR_RUN_TEST (andopt2_special);
  BTOR_RUN_TEST (andopt3_special);
  BTOR_RUN_TEST (andopt4_special);
  BTOR_RUN_TEST (andopt5_special);
  BTOR_RUN_TEST (andopt6_special);
  BTOR_RUN_TEST (andopt7_special);
  BTOR_RUN_TEST (andopt8_special);
  BTOR_RUN_TEST (andopt9_special);
  BTOR_RUN_TEST (andopt10_special);
  BTOR_RUN_TEST (andopt11_special);
  BTOR_RUN_TEST (andopt12_special);
  BTOR_RUN_TEST (andopt13_special);
  BTOR_RUN_TEST (andopt14_special);
  BTOR_RUN_TEST (andopt15_special);
  BTOR_RUN_TEST (andopt16_special);
  BTOR_RUN_TEST (andopt17_special);
  BTOR_RUN_TEST (verbose1_special);
  BTOR_RUN_TEST (verbose2_special);
  BTOR_RUN_TEST (regrrwbinexpconcatzeroconst_special);
  BTOR_RUN_TEST (lambda1_special);
  BTOR_RUN_TEST (lambda2_special);
  BTOR_RUN_TEST (regrmodel1_special);
  BTOR_RUN_TEST (regrmodel2_special);
  BTOR_RUN_TEST (regrmodel3_special);
  BTOR_RUN_TEST (regrmodel4_special);
  BTOR_RUN_TEST (regrcalypto1_special);
  BTOR_RUN_TEST (regrcalypto2_special);
  BTOR_RUN_TEST (regrcalypto3_special);
}

void
finish_special_tests (void)
{
  assert (!g_fout || remove (BTOR_TEST_SPECIAL_TEMP_OUTFILE_NAME) == 0);
  BTOR_DELETEN (g_mm, g_btor_str, strlen (btor_bin_dir) + 20);
  btor_mem_mgr_delete (g_mm);
}
