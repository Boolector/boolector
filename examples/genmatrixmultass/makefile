CC=gcc
CFLAGS=-g -Wall -W -Wextra
genmatrixmultass: genmatrixmultass.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genmatrixmultass.c -L../.. -lboolector
clean:
	rm -f genmatrixmultass
