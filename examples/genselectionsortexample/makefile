CC=gcc
CFLAGS=-g -Wall -W
genselectionsortexample: genselectionsortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genselectionsortexample.c -L../.. -lboolector
clean:
	rm -f genselectionsortexample
