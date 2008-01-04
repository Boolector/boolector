CC=gcc
CFLAGS=-g -Wall -W -Wextra
swapmem: swapmem.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ swapmem.c -L../.. -lboolector
clean:
	rm -f swapmem
