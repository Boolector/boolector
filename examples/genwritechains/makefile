CC=gcc
CFLAGS=-g -Wall -W -Wextra
genwritechains: genwritechains.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genwritechains.c -L../.. -lboolector
clean:
	rm -f genwritechains
