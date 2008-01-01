CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: cocktailsort.c cocktailsortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o cocktailsort cocktailsort.c -L../.. -lboolector
	$(CC) $(CFLAGS) -o cocktailsortexample cocktailsortexample.c -L../.. -lboolector
clean:
	rm -f cocktailsort cocktailsortexample
