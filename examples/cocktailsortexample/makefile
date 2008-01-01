CC=gcc
CFLAGS=-g -Wall -W -Wextra
cocktailsortexample: cocktailsortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ cocktailsortexample.c -L../.. -lboolector
clean:
	rm -f cocktailsortexample
