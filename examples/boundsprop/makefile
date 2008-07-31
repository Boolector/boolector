CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(MAKE) minor
	$(MAKE) maxor

minor: minor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minor.c -L../.. -lboolector

maxor: maxor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxor.c -L../.. -lboolector

clean:
	rm -f minor maxor
