/*
The BtorFMT software provides a generic parser for the BTOR format.
In contrast to Boolector it falls under the following MIT style license:

Copyright (c) 2012-2015, Armin Biere, Johannes Kepler University, Linz

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
  BtorFormatLine** lines;
  const char* err;
  int i;
  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: catbtor [-h] [ <btorfile> ]\n");
      exit (1);
    }
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
  reader = new_btor_format_reader ();
  lines  = read_btor_format_lines (reader, input_file);
  if (!lines)
  {
    err = error_btor_format_reader (reader);
    assert (err);
    fprintf (stderr, "*** catbtor: parse error in '%s' %s\n", input_name, err);
    exit (1);
  }
  delete_btor_format_reader (reader);
  if (close_input) fclose (input_file);
  return 0;
}
