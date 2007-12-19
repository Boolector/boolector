CC=gcc
CFLAGS=-g -Wall -W -Wextra
genextdoublereversexor: genextdoublereversexor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ genextdoublereversexor.c -L../.. -lboolector
clean:
	rm -f genextdoublereversexor
