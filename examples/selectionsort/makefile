CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: selectionsort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o selectionsort selectionsort.c -L../.. -lboolector
clean:
	rm -f selectionsort
