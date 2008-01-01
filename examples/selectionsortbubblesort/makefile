CC=gcc
CFLAGS=-g -Wall -W -Wextra
selectionsortbubblesort: selectionsortbubblesort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ selectionsortbubblesort.c -L../.. -lboolector
clean:
	rm -f selectionsortbubblesort
