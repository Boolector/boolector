CC=gcc
CFLAGS=-g -Wall -W -Wextra
genselectionbubblesort: genselectionbubblesort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genselectionbubblesort.c -L../.. -lboolector
clean:
	rm -f genselectionbubblesort
