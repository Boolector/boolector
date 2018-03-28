/*
The BtorFMT software provides a generic parser for the BTOR format.
In contrast to Boolector it falls under the following MIT style license:

Copyright (c) 2012-2015, Armin Biere, Johannes Kepler University, Linz
Copyright (c) 2017, Mathias Preiner
Copyright (c) 2017, Aina Niemetz

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.
*/

#include "btorfmt.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int close_input;
static FILE* input_file;
static const char* input_name;

int
main (int argc, char** argv)
{
  BtorFormatReader* reader;
  BtorFormatLineIterator it;
  BtorFormatLine* l;
  int i, verbosity = 0;
  const char* err;
  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: catbtor [-h|-v] [ <btorfile> ]\n");
      exit (1);
    }
    else if (!strcmp (argv[i], "-v"))
      verbosity++;
    else if (argv[i][0] == '-')
    {
      fprintf (
          stderr, "*** catbtor: invalid option '%s' (try '-h')\n", argv[i]);
      exit (1);
    }
    else if (input_name)
    {
      fprintf (stderr, "*** catbtor: too many inputs (try '-h')\n");
      exit (1);
    }
    else
      input_name = argv[i];
  }
  if (!input_name)
  {
    input_file = stdin;
    assert (!close_input);
    input_name = "<stdin>";
  }
  else
  {
    input_file = fopen (input_name, "r");
    if (!input_file)
    {
      fprintf (
          stderr, "*** catbtor: can not open '%s' for reading\n", input_name);
      exit (1);
    }
    close_input = 1;
  }
  if (verbosity)
  {
    fprintf (stderr,
             "; [catbor] simple CAT for BTOR files\n"
             "; [catbor] reading '%s'\n",
             input_name);
    fflush (stderr);
  }
  reader = btorfmt_new ();
  if (!btorfmt_read_lines (reader, input_file))
  {
    err = btorfmt_error (reader);
    assert (err);
    fprintf (stderr, "*** catbtor: parse error in '%s' %s\n", input_name, err);
    btorfmt_delete (reader);
    if (close_input) fclose (input_file);
    exit (1);
  }
  if (close_input) fclose (input_file);
  if (verbosity)
  {
    fprintf (stderr, "; [catbor] finished parsing '%s'\n", input_name);
    fflush (stderr);
  }
  if (verbosity)
  {
    fprintf (stderr, "; [catbor] starting to dump BTOR model to '<stdout>'\n");
    fflush (stderr);
  }
  it = btorfmt_iter_init (reader);
  while ((l = btorfmt_iter_next (&it)))
  {
    printf ("%ld %s", l->id, l->name);
    if (l->tag == BTOR_FORMAT_TAG_sort)
    {
      printf (" %s", l->sort.name);
      switch (l->sort.tag)
      {
        case BTOR_FORMAT_TAG_SORT_bitvec:
          printf (" %u", l->sort.bitvec.width);
          break;
        case BTOR_FORMAT_TAG_SORT_array:
          printf (" %ld %ld", l->sort.array.index, l->sort.array.element);
          break;
        default:
          assert (0);
          fprintf (stderr, "*** catbtor: invalid sort encountered\n");
          exit (1);
      }
    }
    else if (l->sort.id)
      printf (" %ld", l->sort.id);
    for (i = 0; i < l->nargs; i++) printf (" %ld", l->args[i]);
    if (l->tag == BTOR_FORMAT_TAG_slice)
      printf (" %ld %ld", l->args[1], l->args[2]);
    if (l->tag == BTOR_FORMAT_TAG_sext || l->tag == BTOR_FORMAT_TAG_uext)
      printf (" %ld", l->args[1]);
    if (l->constant) printf (" %s", l->constant);
    if (l->symbol) printf (" %s", l->symbol);
    fputc ('\n', stdout);
  }
  btorfmt_delete (reader);
  if (verbosity)
  {
    fprintf (stderr, "; [catbor] finished dumping BTOR model to '<stdout>'\n");
    fflush (stderr);
  }
  return 0;
}
