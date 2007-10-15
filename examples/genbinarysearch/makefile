CC=gcc
CFLAGS=-g -Wall -W
genbinarysearch: genbinarysearch.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genbinarysearch.c -L../.. -lboolector
clean:
	rm -f genbinarysearch
