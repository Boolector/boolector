CC=gcc
CFLAGS=-g -Wall -W -Wextra
matrixmultass: matrixmultass.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ matrixmultass.c -L../.. -lboolector
clean:
	rm -f matrixmultass
