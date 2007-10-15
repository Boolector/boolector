CC=gcc
CFLAGS=-g -Wall -W
genlinearsearch: genlinearsearch.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genlinearsearch.c -L../.. -lboolector
clean:
	rm -f genlinearsearch
