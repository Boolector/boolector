CC=gcc
CFLAGS=-g -Wall -W
genbubblesortexample: genbubblesortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genbubblesortexample.c -L../.. -lboolector
clean:
	rm -f genbubblesortexample
