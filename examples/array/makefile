LIBS=-L../.. -lboolector $(shell sed -e '/^LIBS=/!d' -e 's,^LIBS=,,' -e 's,-L,-L../../,g' ../../makefile)
CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(CC) $(CFLAGS)  array1.c -o array1 $(LIBS)
	$(CC) $(CFLAGS)  array2.c -o array2 $(LIBS)
	$(CC) $(CFLAGS)  array3.c -o array3 $(LIBS)
clean:
	rm -f array1 array2 array3
