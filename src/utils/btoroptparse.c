/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btoroptparse.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

void
btor_optparse_parse (BtorMemMgr *mm,
                     int32_t argc,
                     char **argv,
                     BtorParsedOptPtrStack *opts,
                     BtorParsedInputPtrStack *infiles,
                     BtorOpt *btor_opts,
                     bool (*has_str_arg) (const char *, BtorOpt *))
{
  assert (mm);
  assert (argc);
  assert (argv);
  assert (opts);
  assert (infiles);
  assert (BTOR_COUNT_STACK (*opts) == 0);
  assert (BTOR_COUNT_STACK (*infiles) == 0);

  int32_t i, j, len;
  BtorParsedOpt *o;
  BtorParsedInput *in;
  char *arg, *tmp;

  for (i = 1; i < argc; i++)
  {
    arg = argv[i];
    len = strlen (argv[i]);

    if (arg[0] != '-')
    {
      BTOR_CNEW (mm, in);
      in->mm   = mm;
      in->name = arg;
      BTOR_PUSH_STACK (*infiles, in);
    }
    else
    {
      BTOR_CNEW (mm, o);
      o->mm = mm;

      /* save original option string (without arguments)
       * for error messages */
      BTOR_INIT_STACK (mm, o->orig);
      for (j = 0; j < len && arg[j] != '='; j++)
        BTOR_PUSH_STACK (o->orig, arg[j]);
      BTOR_PUSH_STACK (o->orig, '\0');

      /* extract option name */
      BTOR_INIT_STACK (mm, o->name);
      o->isshrt = arg[1] != '-';
      j         = o->isshrt ? 1 : 2;
      o->isdisable =
          len > 3 && arg[j] == 'n' && arg[j + 1] == 'o' && arg[j + 2] == '-';
      for (j = o->isdisable ? j + 3 : j; j < len && arg[j] != '='; j++)
        BTOR_PUSH_STACK (o->name, arg[j]);
      BTOR_PUSH_STACK (o->name, '\0');

      /* extract option argument (if any) */
      if (arg[j] == '=')
      {
        o->readval = BTOR_ARG_READ_NONE_VIA_EQ;
        o->valstr  = arg + j + 1;
        if (o->valstr[0] != 0)
        {
          o->readval = BTOR_ARG_READ_STR_VIA_EQ;
          o->val     = (uint32_t) strtol (o->valstr, &tmp, 10);
          if (tmp[0] == 0) o->readval = BTOR_ARG_READ_INT_VIA_EQ;
        }
      }
      else
      {
        if (i + 1 < argc && argv[i + 1][0] != '-')
        {
          o->readval = BTOR_ARG_READ_STR;
          o->valstr  = argv[i + 1];
          o->val     = (uint32_t) strtol (o->valstr, &tmp, 10);
          if (tmp[0] == 0)
          {
            o->readval = BTOR_ARG_READ_INT;
            i += 1;
          }
          else if (has_str_arg && has_str_arg (o->name.start, btor_opts))
          {
            i += 1;
          }
          else
          {
            o->readval = BTOR_ARG_READ_NONE;
            o->valstr  = 0;
          }
        }
      }
      BTOR_PUSH_STACK (*opts, o);
    }
  }
}
