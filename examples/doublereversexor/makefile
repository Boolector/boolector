CC=gcc
CFLAGS=-g -Wall -W -Wextra
doublereversexor: doublereversexor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ doublereversexor.c -L../.. -lboolector
clean:
	rm -f doublereversexor
