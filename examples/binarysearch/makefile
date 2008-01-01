CC=gcc
CFLAGS=-g -Wall -W -Wextra
binarysearch: binarysearch.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ binarysearch.c -L../.. -lboolector
clean:
	rm -f binarysearch
