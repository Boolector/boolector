CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: selectionsort.c selectionsortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o selectionsort selectionsort.c -L../.. -lboolector
	$(CC) $(CFLAGS) -o selectionsortexample selectionsortexample.c -L../.. -lboolector
clean:
	rm -f selectionsort selectionsortexample
