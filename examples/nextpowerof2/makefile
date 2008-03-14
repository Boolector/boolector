CC=gcc
CFLAGS=-g -Wall -W -Wextra
nextpowerof2: nextpowerof2.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ nextpowerof2.c -L../.. -lboolector
clean:
	rm -f nextpowerof2 
