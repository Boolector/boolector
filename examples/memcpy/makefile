CC=gcc
CFLAGS=-g -Wall -W -Wextra
memcpy: memcpy.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ memcpy.c -L../.. -lboolector
clean:
	rm -f memcpy
