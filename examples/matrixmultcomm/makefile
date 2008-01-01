CC=gcc
CFLAGS=-g -Wall -W -Wextra
matrixmultcomm: matrixmultcomm.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ matrixmultcomm.c -L../.. -lboolector
clean:
	rm -f matrixmultcomm
