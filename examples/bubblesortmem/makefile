CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: bubblesortmem.c bubblesortmemexample.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o bubblesortmem bubblesortmem.c -L../.. -lboolector
	$(CC) $(CFLAGS) -o bubblesortmemexample bubblesortmemexample.c -L../.. -lboolector
clean:
	rm -f bubblesortmem bubblesortmemexample
