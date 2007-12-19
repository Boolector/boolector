CC=gcc
CFLAGS=-g -Wall -W -Wextra
genextselectionsortbubblesort: genextselectionsortbubblesort.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genextselectionsortbubblesort.c -L../.. -lboolector
clean:
	rm -f genextselectionsortbubblesort
