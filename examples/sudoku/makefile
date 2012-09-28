LIBS=$(shell sed -e '/^LIBS=/!d' -e 's,^LIBS=,,' -e 's,-L,-L../../,g' ../../makefile)
CC=gcc
CFLAGS=-g -Wall -W -Wextra
sudoku: sudoku.c ../../boolector.h ../../btormem.h ../../btorexp.h ../../btorconst.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ sudoku.c -L../.. -lboolector $(LIBS)
clean:
	rm -f sudoku 
