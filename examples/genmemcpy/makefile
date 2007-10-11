CC=gcc
CFLAGS=-g -Wall -W
genmemcpy: genmemcpy.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genmemcpy.c -L../.. -lboolector
clean:
	rm -f genmemcpy
