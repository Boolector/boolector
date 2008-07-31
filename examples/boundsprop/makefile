CC=gcc
CFLAGS=-g -Wall -W -Wextra
minor: minor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minor.c -L../.. -lboolector
clean:
	rm -f minor 
