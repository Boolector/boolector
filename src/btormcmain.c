#include "boolectormc.h"
#include "btormc.h"

#include <assert.h>
#include "utils/btormem.h"
#include "utils/btoroptparse.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#define LEN_OPTSTR 38
#define LEN_PARAMSTR 16
#define LEN_HELPSTR 80

#define BTORMC_SUCC_EXIT 0
#define BTORMC_ERR_EXIT 1

/*------------------------------------------------------------------------*/

static void
print_opt (FILE *out,
           BtorMemMgr *mm,
           const char *lng,
           const char *shrt,
           bool isflag,
           uint32_t dflt,
           const char *desc,
           bool print_dflt)
{
  assert (lng);
  assert (desc);

  char optstr[LEN_OPTSTR], paramstr[LEN_PARAMSTR];
  char *descstr, descstrline[LEN_HELPSTR], *word;
  int32_t i, j, len;
  BtorCharPtrStack words;

  if (!isflag)
    sprintf (paramstr, "<n>");
  else
    paramstr[0] = '\0';

  /* option string ------------------------------------------ */
  memset (optstr, ' ', LEN_OPTSTR * sizeof (char));
  optstr[LEN_OPTSTR - 1] = '\0';
  len                    = strlen (lng);
  sprintf (optstr,
           "  %s%s%s%s%s--%s%s%s",
           shrt ? "-" : "",
           shrt ? shrt : "",
           shrt && strlen (paramstr) > 0 ? " " : "",
           shrt ? paramstr : "",
           shrt ? ", " : "",
           lng,
           strlen (paramstr) > 0 ? "=" : "",
           paramstr);
  len = strlen (optstr);
  for (i = len; i < LEN_OPTSTR - 1; i++) optstr[i] = ' ';
  optstr[LEN_OPTSTR - 1] = '\0';

  /* formatted description ---------------------------------- */
  /* append default value to description */
  if (print_dflt)
  {
    len = strlen (desc) + 3 + btor_util_num_digits (dflt);
    BTOR_CNEWN (mm, descstr, len + 1);
    sprintf (descstr, "%s [%u]", desc, dflt);
  }
  else
  {
    len = strlen (desc);
    BTOR_CNEWN (mm, descstr, len + 1);
    sprintf (descstr, "%s", desc);
  }
  BTOR_INIT_STACK (mm, words);
  word = strtok (descstr, " ");
  while (word)
  {
    BTOR_PUSH_STACK (words, btor_mem_strdup (mm, word));
    word = strtok (0, " ");
  }
  BTOR_DELETEN (mm, descstr, len + 1);

  BTOR_CLRN (descstrline, LEN_HELPSTR);
  sprintf (descstrline, "%s ", optstr);
  i = 0;
  do
  {
    j = LEN_OPTSTR;
    for (; i < BTOR_COUNT_STACK (words); i++)
    {
      word = BTOR_PEEK_STACK (words, i);
      len  = strlen (word);

      /* word does not fit into remaining line */
      if (j + 1 + len >= LEN_HELPSTR) break;

      strcpy (descstrline + j, word);
      j += len;
      descstrline[j++] = ' ';
    }
    descstrline[j] = 0;
    fprintf (out, "%s\n", descstrline);
    BTOR_CLRN (descstrline, LEN_HELPSTR);
    memset (descstrline, ' ', LEN_OPTSTR * sizeof (char));
  } while (i < BTOR_COUNT_STACK (words));

  /* cleanup */
  while (!BTOR_EMPTY_STACK (words))
    btor_mem_freestr (mm, BTOR_POP_STACK (words));
  BTOR_RELEASE_STACK (words);
}

static void
print_help (FILE *out, BtorMC *mc)
{
  assert (mc);

  int32_t i;
  BtorMCOpt *o;

  fprintf (out, "usage: boolectormc [<option>...][<input>]\n");
  fprintf (out, "\n");
  fprintf (out, "where <option> is one of the following:\n");
  fprintf (out, "\n");

  print_opt (
      out, mc->mm, "help", "h", true, 0, "print this message and exit", false);
  print_opt (out, mc->mm, "copyright", 0, true, 0, "print copyright", false);
  print_opt (out, mc->mm, "version", 0, true, 0, "print version", false);

  fprintf (out, "\n");

  for (i = 0; i < BTOR_MC_OPT_NUM_OPTS; i++)
  {
    o = &mc->options[i];
    print_opt (out, mc->mm, o->lng, o->shrt, o->isflag, o->dflt, o->desc, true);
  }
}

static int32_t
error (char *msg, ...)
{
  va_list list;
  va_start (list, msg);
  fputs ("boolectormc: ", stderr);
  vfprintf (stderr, msg, list);
  fprintf (stderr, "\n");
  va_end (list);
  return BTORMC_ERR_EXIT;
}

int32_t
main (int32_t argc, char **argv)
{
  int32_t i, j, len, close_infile, res;
  char *arg, *infile_name, *cmd;
  FILE *infile, *out;
  BtorParsedOpt *po;
  BtorParsedOptPtrStack opts;
  BtorParsedInput *pin;
  BtorParsedInputPtrStack infiles;
  BtorMemMgr *mm;
  BtorMCOption opt;
  BtorMCOpt *o;
  BtorMC *mc;

  out = stdout;
  res = BTORMC_SUCC_EXIT;
  mm  = btor_mem_mgr_new ();
  mc  = boolector_mc_new ();

  BTOR_INIT_STACK (mm, opts);
  BTOR_INIT_STACK (mm, infiles);

  btor_optparse_parse (mm, argc, argv, &opts, &infiles, 0);

  /* input file ======================================================= */

  if (BTOR_COUNT_STACK (infiles) > 1)
  {
    res = error ("multiple input files");
    goto DONE;
  }
  else if (BTOR_COUNT_STACK (infiles) == 1)
  {
    infile_name = BTOR_PEEK_STACK (infiles, 0)->name;
    if (!btor_util_file_exists (infile_name))
    {
      infile = 0;
    }
    else if (btor_util_file_has_suffix (infile_name, ".gz")
             || btor_util_file_has_suffix (infile_name, ".bz2")
             || btor_util_file_has_suffix (infile_name, ".7z")
             || btor_util_file_has_suffix (infile_name, ".zip"))
    {
      len = strlen (infile_name);
      BTOR_NEWN (mm, cmd, len + 40);
      if (btor_util_file_has_suffix (infile_name, ".gz"))
        sprintf (cmd, "gunzip -c %s", infile_name);
      else if (btor_util_file_has_suffix (infile_name, ".bz2"))
        sprintf (cmd, "bzcat %s", infile_name);
      else if (btor_util_file_has_suffix (infile_name, ".7z"))
        sprintf (cmd, "7z x -so %s 2> /dev/null", infile_name);
      else if (btor_util_file_has_suffix (infile_name, ".zip"))
        sprintf (cmd, "unzip -p %s", infile_name);

      if ((infile = popen (cmd, "r"))) close_infile = 2;

      BTOR_DELETEN (mm, cmd, len + 40);
    }
    else if ((infile = fopen (infile_name, "r")))
    {
      close_infile = 1;
    }

    if (!infile)
    {
      res = error ("can not read '%s'", infile_name);
      goto DONE;
    }
  }

  /* options ========================================================== */

  for (i = 0; i < BTOR_COUNT_STACK (opts); i++)
  {
    po = BTOR_PEEK_STACK (opts, i);

    if (strcmp (po->name.start, "h") == 0
        || strcmp (po->name.start, "help") == 0)
    {
      print_help (out, mc);
      return 0;
    }
    else if (strcmp (po->name.start, "copyright") == 0)
    {
      fprintf (out, "%s", boolector_copyright (mc->btor));
      return 0;
    }
    else if (strcmp (po->name.start, "version") == 0)
    {
      fprintf (out, "%s\n", boolector_version (mc->btor));
    }
    else
    {
      for (opt = 0; opt < BTOR_MC_OPT_NUM_OPTS; opt++)
      {
        o = &mc->options[opt];
        if (strcmp (po->name.start, o->shrt) == 0
            || strcmp (po->name.start, o->lng) == 0)
        {
          break;
        }
        o = 0;
      }
      if (!o)
      {
        res = error ("invalid option '%s'", po->orig.start);
        goto DONE;
      }
      if (BTOR_ARG_IS_MISSING (BTOR_ARG_EXPECT_INT, o->isflag, po->readval))
      {
        res = error ("missing argument for '%s'", po->orig.start);
        goto DONE;
      }
      if (BTOR_ARG_IS_INVALID (BTOR_ARG_EXPECT_INT, o->isflag, po->readval))
      {
        res = error ("invalid argument for '%s', expected int", po->orig.start);
        goto DONE;
      }
      if (o->isflag)
      {
        if (po->isdisable)
        {
          boolector_set_opt (mc, opt, 0);
        }
        else
        {
          switch (opt)
          {
            case BTOR_OPT_VERBOSITY:
              if (BTOR_ARG_READ_IS_INT (po->readval))
                btor_mc_set_opt (mc, opt, po->val);
              else
                btor_mc_set_opt (mc, opt, btor_mc_get_opt (mc, opt) + 1);
              break;
            default:
              assert (opt != BTOR_OPT_NUM_OPTS);
              if (BTOR_ARG_READ_IS_INT (po->readval))
                btor_mc_set_opt (mc, opt, po->val);
              else
                btor_mc_set_opt (mc, opt, 1);
          }
        }
      }
      else
      {
        assert (BTOR_ARG_READ_IS_INT (po->readval));
        btor_mc_set_opt (mc, opt, po->val);
      }
    }
  }

DONE:
  boolector_mc_delete (mc);
  btor_mem_mgr_delete (mm);
  return res;
}
