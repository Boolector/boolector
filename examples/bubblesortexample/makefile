CC=gcc
CFLAGS=-g -Wall -W -Wextra
bubblesortexample: bubblesortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ bubblesortexample.c -L../.. -lboolector
clean:
	rm -f bubblesortexample
