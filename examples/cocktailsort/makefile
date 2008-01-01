CC=gcc
CFLAGS=-g -Wall -W -Wextra
gencocktailsort: gencocktailsort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ gencocktailsort.c -L../.. -lboolector
clean:
	rm -f gencocktailsort
