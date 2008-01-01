CC=gcc
CFLAGS=-g -Wall -W -Wextra
selectionsort: selectionsort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ selectionsort.c -L../.. -lboolector
clean:
	rm -f selectionsort
