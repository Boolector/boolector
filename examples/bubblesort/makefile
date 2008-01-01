CC=gcc
CFLAGS=-g -Wall -W -Wextra
bubblesort: bubblesort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ bubblesort.c -L../.. -lboolector
clean:
	rm -f bubblesort
