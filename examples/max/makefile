CC=gcc
CFLAGS=-g -Wall -W -Wextra
max: max.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ max.c -L../.. -lboolector
clean:
	rm -f max
