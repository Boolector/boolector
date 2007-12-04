CC=gcc
CFLAGS=-g -Wall -W -Wextra
genmatrixmult: genmatrixmultcomm.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genmatrixmultcomm.c -L../.. -lboolector
clean:
	rm -f genmatrixmultcomm
