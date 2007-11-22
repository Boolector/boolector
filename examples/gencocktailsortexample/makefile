CC=gcc
CFLAGS=-g -Wall -W -Wextra
gencocktailsortexample: gencocktailsortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ gencocktailsortexample.c -L../.. -lboolector
clean:
	rm -f gencocktailsortexample
