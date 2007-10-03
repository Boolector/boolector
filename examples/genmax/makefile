CC=gcc
CFLAGS=-g -Wall -W
genmax: genmax.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genmax.c -L../.. -lboolector
clean:
	rm -f genmax
