CC=gcc
CFLAGS=-g -Wall -W
genselectionsort: genselectionsort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genselectionsort.c -L../.. -lboolector
clean:
	rm -f genselectionsort
