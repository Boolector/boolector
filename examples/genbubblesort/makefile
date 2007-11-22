CC=gcc
CFLAGS=-g -Wall -W -Wextra
genbubblesort: genbubblesort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genbubblesort.c -L../.. -lboolector
clean:
	rm -f genbubblesort
