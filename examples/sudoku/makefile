CC=gcc
CFLAGS=-g -Wall -W -Wextra
sudoku: sudoku.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ sudoku.c -L../.. -lboolector
clean:
	rm -f sudoku 
