CC=gcc
CFLAGS=-g -Wall -W -Wextra
linearsearch: linearsearch.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ linearsearch.c -L../.. -lboolector
clean:
	rm -f linearsearch
