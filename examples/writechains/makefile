CC=gcc
CFLAGS=-g -Wall -W -Wextra
genextwritechains: genextwritechains.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genextwritechains.c -L../.. -lboolector
clean:
	rm -f genextwritechains
