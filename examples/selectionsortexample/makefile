CC=gcc
CFLAGS=-g -Wall -W -Wextra
selectionsortexample: selectionsortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ selectionsortexample.c -L../.. -lboolector
clean:
	rm -f selectionsortexample
