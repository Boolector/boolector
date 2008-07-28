CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: selectionsortmem.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o selectionsortmem selectionsortmem.c -L../.. -lboolector
clean:
	rm -f selectionsortmem
