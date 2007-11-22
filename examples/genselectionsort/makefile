CC=gcc
CFLAGS=-g -Wall -W -Wextra
genselectionsort: genselectionsort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genselectionsort.c -L../.. -lboolector
clean:
	rm -f genselectionsort
