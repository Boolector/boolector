CC=gcc
CFLAGS=-g -Wall -W -Wextra
ispowerof2: ispowerof2.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ ispowerof2.c -L../.. -lboolector
clean:
	rm -f ispowerof2
