CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: selectionsortmem.c selectionsortmemexample.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o selectionsortmem selectionsortmem.c -L../.. -lboolector
	$(CC) $(CFLAGS) -o selectionsortmemexample selectionsortmemexample.c -L../.. -lboolector
clean:
	rm -f selectionsortmem selectionsortmemexample
