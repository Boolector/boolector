#include "boolector.h"
#include "boolectormc.h"

#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if 0

int year = 1977;
while (days > 365) {
  if ((year % 100) && (year % 4) == 0) {
    if (days > 366) {
      days -= 366;      
      year += 1;
    }
#ifdef FIXED
    else break;
#endif
  } else {
    days -= 365;
    year += 1;
  }
}

We want to know whether the 32-bit variable days strictly decreases
during an iteration of the loop. A counterexample is days = 1461 which
causes an infinite loop.

int prev_days, prev_days_valid = 0, break_out_of_loop = 0;
int year = 1977;
while (days > 365 && !break_out_of_loop) {
  if (prev_days_valid) assert (prev_days > days);
  prev_days_valid = 1, prev_days = days;
  if ((year % 100) && (year % 4) == 0) {
    if (days > 366) {
      days -= 366;      
      year += 1;
    }
#ifdef FIXED
    else break_out_of_loop = 1;
#endif
  } else {
    days -= 365;
    year += 1;
  }
}

#endif

static long
bv2dec (const char* str)
{
  long res = 0;
  int i;
  assert (strlen (str) == 32);
  for (i = 0; i < 32; i++)
    if (str[i] == '1') res += (1ll << (31 - i));
  if (str[0] == '1') res = res - (1ll << 32);
  return res;
}

int
main (int argc, char** argv)
{
  int i, fixed = 0, dump = 0, res = 0, verbosity = 0, witness = 1;
  const char* daystr = 0;
  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("usage: leapyear [-h][-v][-n][--fixed][--dump] [<days>]\n");
      exit (1);
    }
    else if (!strcmp (argv[i], "--fixed"))
      fixed = 1;
    else if (!strcmp (argv[i], "-v"))
      verbosity++;
    else if (!strcmp (argv[i], "-n"))
      witness = 0;
    else if (!strcmp (argv[i], "--dump"))
      dump = 1;
    else if (argv[i][0] == '-')
    {
      fprintf (
          stderr, "*** leapyear: invalid option '%s' (try '-h')\n", argv[i]);
      exit (1);
    }
    else if (daystr)
    {
      fprintf (stderr, "*** leapyear: too many options(try '-h')\n");
      exit (1);
    }
    else
    {
      const char* p;
      for (p = argv[i]; *p; p++)
        if (*p < '0' || *p > '9') break;
      if (!argv[i][0] || *p)
      {
        fprintf (stderr,
                 "*** leapyear: invalid days argument '%s' (try '-h')\n",
                 argv[i]);
        exit (1);
      }
      daystr = argv[i];
    }
  }

  BtorMC* mc = boolector_mc_new ();
  boolector_mc_set_opt (mc, BTOR_MC_OPT_VERBOSITY, verbosity);
  if (witness) boolector_mc_enable_trace_gen (mc);
  Btor* btor = boolector_mc_get_btor (mc);

  BoolectorNode* year  = boolector_latch (mc, 32, "year");
  BoolectorNode* c1977 = boolector_int (btor, 1977, 32);
  boolector_mc_init (mc, year, c1977);
  boolector_release (btor, c1977);

  BoolectorNode* prev_days       = boolector_latch (mc, 32, "prev(days)");
  BoolectorNode* prev_days_valid = boolector_latch (mc, 1, "valid(prev(days))");
  BoolectorNode* ff              = boolector_int (btor, 0, 1);
  BoolectorNode* tt              = boolector_int (btor, 1, 1);
  boolector_mc_init (mc, prev_days_valid, ff);
  boolector_mc_next (mc, prev_days_valid, tt);
  BoolectorNode* break_out_of_loop;
  if (fixed)
  {
    break_out_of_loop = boolector_copy (btor, boolector_latch (mc, 1, "break"));
    boolector_mc_init (mc, break_out_of_loop, ff);
  }
  else
    break_out_of_loop = boolector_copy (btor, ff);
  boolector_release (btor, ff);
  boolector_release (btor, tt);

  BoolectorNode* days = boolector_latch (mc, 32, "days");

  BoolectorNode* c365             = boolector_int (btor, 365, 32);
  BoolectorNode* days_greater_365 = boolector_sgt (btor, days, c365);
  BoolectorNode* days_sub_365     = boolector_sub (btor, days, c365);
  boolector_release (btor, c365);

  if (daystr)
  {
    int daysinitval = atoi (daystr);
    printf ("; constant initialization of days to %d\n", daysinitval);
    BoolectorNode* daysinit = boolector_int (btor, daysinitval, 32);
    boolector_mc_init (mc, days, daysinit);
    boolector_release (btor, daysinit);
  }
  else
    printf ("; non-deterministic arbitrary initialization of days\n");
  fflush (stdout);

  BoolectorNode* c366             = boolector_int (btor, 366, 32);
  BoolectorNode* days_greater_366 = boolector_sgt (btor, days, c366);
  BoolectorNode* days_sub_366     = boolector_sub (btor, days, c366);
  boolector_release (btor, c366);

  BoolectorNode* prev_days_greater_days = boolector_sgt (btor, prev_days, days);
  BoolectorNode* days_decreases =
      boolector_implies (btor, prev_days_valid, prev_days_greater_days);
  boolector_release (btor, prev_days_greater_days);

  BoolectorNode* one      = boolector_int (btor, 1, 32);
  BoolectorNode* inc_year = boolector_add (btor, year, one);
  boolector_release (btor, one);

  BoolectorNode* zero = boolector_zero (btor, 32);

  BoolectorNode* c100         = boolector_int (btor, 100, 32);
  BoolectorNode* year_mod_100 = boolector_urem (btor, year, c100);
  boolector_release (btor, c100);

  BoolectorNode* year_mod_100_ne_zero = boolector_ne (btor, year_mod_100, zero);
  boolector_release (btor, year_mod_100);

  BoolectorNode* c4         = boolector_int (btor, 4, 32);
  BoolectorNode* year_mod_4 = boolector_urem (btor, year, c4);
  boolector_release (btor, c4);

  BoolectorNode* year_mod_4_eq_zero = boolector_eq (btor, year_mod_4, zero);
  boolector_release (btor, year_mod_4);
  boolector_release (btor, zero);

  BoolectorNode* complex_condition =
      boolector_and (btor, year_mod_100_ne_zero, year_mod_4_eq_zero);
  boolector_release (btor, year_mod_100_ne_zero);
  boolector_release (btor, year_mod_4_eq_zero);

  BoolectorNode *tmp1, *tmp2, *tmp3, *tmp4;

  BoolectorNode* not_break_out_of_loop =
      boolector_not (btor, break_out_of_loop);
  boolector_release (btor, break_out_of_loop);

  if (fixed)
  {
    BoolectorNode* next_break_out_of_loop = boolector_or (
        btor,
        break_out_of_loop,
        tmp1 = boolector_and (
            btor,
            tmp2 =
                boolector_and (btor, days_greater_365, not_break_out_of_loop),
            tmp3 =
                boolector_and (btor,
                               complex_condition,
                               tmp4 = boolector_not (btor, days_greater_366))));
    boolector_mc_next (mc, break_out_of_loop, next_break_out_of_loop);
    boolector_release (btor, tmp1);
    boolector_release (btor, tmp2);
    boolector_release (btor, tmp3);
    boolector_release (btor, tmp4);
    boolector_release (btor, next_break_out_of_loop);
  }

  BoolectorNode* next_year = boolector_cond (
      btor,
      tmp1 = boolector_and (btor, days_greater_365, not_break_out_of_loop),
      tmp2 = boolector_cond (
          btor,
          complex_condition,
          tmp3 = boolector_cond (btor, days_greater_366, inc_year, year),
          inc_year),
      year);

  boolector_mc_next (mc, year, next_year);
  boolector_release (btor, next_year);
  boolector_release (btor, tmp1);
  boolector_release (btor, tmp2);
  boolector_release (btor, tmp3);
  boolector_release (btor, inc_year);

  BoolectorNode* next_days = boolector_cond (
      btor,
      tmp1 = boolector_and (btor, days_greater_365, not_break_out_of_loop),
      tmp2 = boolector_cond (
          btor,
          complex_condition,
          tmp3 = boolector_cond (btor, days_greater_366, days_sub_366, days),
          days_sub_365),
      days);

  boolector_mc_next (mc, days, next_days);
  boolector_release (btor, next_days);
  boolector_release (btor, tmp1);
  boolector_release (btor, tmp2);
  boolector_release (btor, tmp3);
  boolector_release (btor, days_sub_365);
  boolector_release (btor, days_sub_366);
  boolector_release (btor, days_greater_366);
  boolector_release (btor, complex_condition);

  BoolectorNode* next_prev_days =
      boolector_cond (btor, days_greater_365, days, prev_days);
  boolector_mc_next (mc, prev_days, next_prev_days);
  boolector_release (btor, next_prev_days);

  BoolectorNode* good = boolector_implies (
      btor,
      tmp1 = boolector_and (btor, days_greater_365, not_break_out_of_loop),
      days_decreases);
  boolector_release (btor, tmp1);
  boolector_release (btor, days_decreases);
  boolector_release (btor, days_greater_365);
  BoolectorNode* bad = boolector_not (btor, good);
  boolector_release (btor, good);
  boolector_mc_bad (mc, bad);
  boolector_release (btor, bad);

  boolector_release (btor, not_break_out_of_loop);

  // all nodes (except latches and inputs) should have been released at this
  // point

  if (dump)
  {
    printf ("; printing BTOR model\n");
    boolector_mc_dump (mc, stdout);
    fflush (stdout);
  }
  else
  {
    const int maxk = 100;
    printf ("; running bounded model checker up to bound %d\n", maxk);
    fflush (stdout);
    int k = boolector_mc_bmc (mc, 0, maxk);
    if (0 <= k && k <= maxk)
    {
      printf ("; days does NOT decrease at bound %d\n", k);
      if (witness)
      {
        for (i = 0; i <= k; i++)
        {
          char* val_year      = boolector_mc_assignment (mc, year, i);
          char* val_days      = boolector_mc_assignment (mc, days, i);
          char* val_prev_days = boolector_mc_assignment (mc, prev_days, i);
          printf ("time=%d year=%" PRId64 " days=%" PRId64
                  " prev(days)=%" PRId64 "\n",
                  i,
                  bv2dec (val_year),
                  bv2dec (val_days),
                  bv2dec (val_prev_days));
          boolector_mc_free_assignment (mc, val_days);
          boolector_mc_free_assignment (mc, val_year);
          boolector_mc_free_assignment (mc, val_prev_days);
        }
      }
    }
    else
      printf ("; days decreases always up to bound %d\n", maxk);
    res = (0 <= k);
  }

  // latches (and inputs) are owned by 'mc', e.g., do not release

  boolector_mc_delete (mc);

  return res;
}
