CC=gcc
CFLAGS=-g -Wall -W -Wextra
cocktailsort: cocktailsort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ cocktailsort.c -L../.. -lboolector
clean:
	rm -f cocktailsort
