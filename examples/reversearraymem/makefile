CC=gcc
CFLAGS=-g -Wall -W -Wextra
reversearraymem: reversearraymem.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ reversearraymem.c -L../.. -lboolector
clean:
	rm -f reversearraymem
