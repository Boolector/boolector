CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: bubblesort.c bubblesortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o bubblesort bubblesort.c -L../.. -lboolector
	$(CC) $(CFLAGS) -o bubblesortexample bubblesortexample.c -L../.. -lboolector
clean:
	rm -f bubblesort bubblesortexample
