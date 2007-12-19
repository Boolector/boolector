CC=gcc
CFLAGS=-g -Wall -W -Wextra
genextmatrixmultcomm: genextmatrixmultcomm.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genextmatrixmultcomm.c -L../.. -lboolector
clean:
	rm -f genextmatrixmultcomm
