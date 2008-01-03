CC=gcc
CFLAGS=-g -Wall -W -Wextra
swapmemxor: swapmemxor.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ swapmemxor.c -L../.. -lboolector
clean:
	rm -f swapmemxor
