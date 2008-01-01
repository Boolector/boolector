CC=gcc
CFLAGS=-g -Wall -W -Wextra
writechains: writechains.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ writechains.c -L../.. -lboolector
clean:
	rm -f writechains
