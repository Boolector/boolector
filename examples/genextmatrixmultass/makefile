CC=gcc
CFLAGS=-g -Wall -W -Wextra
genextmatrixmultass: genextmatrixmultass.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genextmatrixmultass.c -L../.. -lboolector
clean:
	rm -f genextmatrixmultass
