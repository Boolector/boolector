CC=gcc
CFLAGS=-g -Wall -W -Wextra
genbubblesortexample: genbubblesortexample.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genbubblesortexample.c -L../.. -lboolector
clean:
	rm -f genbubblesortexample
