#include "boolectormc.h"
#include "btormc.h"

#include <assert.h>
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#define LEN_OPTSTR 38
#define LEN_PARAMSTR 16
#define LEN_HELPSTR 80

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
print_help (BtorMC *mc)
{
  assert (mc);

  int32_t i;
  BtorMCOpt *o;
  FILE *out;

  out = stdout;

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

int32_t
main (int32_t argc, char **argv)
{
  int32_t i;
  BtorMC *btormc;

  btormc = boolector_mc_new ();

  for (i = 1; i < argc; i++)
  {
    if (strcmp (argv[i], "-h") == 0 || strcmp (argv[i], "--help") == 0)
    {
      print_help (btormc);
      return 0;
    }
  }
}
