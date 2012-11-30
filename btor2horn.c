#include "btorfmt.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int
main (int argc, char** argv)
{
  const char *name = 0, *errmsg;
  BtorFormatReader* reader;
  BtorFormatLine** lines;
  FILE* file;
  int i;
  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("usage: btor2horn [-h] [<btor>]\n");
      exit (0);
    }
    if (argv[i][0] == '-')
    {
      fprintf (stderr,
               "*** btor2horn: invalid command line option '%s' (try '-h')\n",
               argv[i]);
      exit (1);
    }
    if (name)
    {
      fprintf (stderr, "*** btor2horn: multiple BTOR files (try '-h')\n");
      exit (1);
    }
    name = argv[i];
  }
  if (!name)
    file = stdin;
  else if (!(file = fopen (name, "r")))
  {
    fprintf (stderr, "*** btor2horn: can not read '%s'\n", name);
    exit (1);
  }
  reader = new_btor_format_reader ();
  if (!(lines = read_btor_format_lines (reader, file)))
  {
    errmsg = error_btor_format_reader (reader);
    assert (errmsg);
    fprintf (stderr, "*** btor2horn: parser error at %s\n", errmsg);
    exit (1);
  }
  if (name) fclose (file);
  delete_btor_format_reader (reader);
  return 0;
}
