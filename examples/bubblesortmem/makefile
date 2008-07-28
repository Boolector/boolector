CC=gcc
CFLAGS=-g -Wall -W -Wextra

all: bubblesortmem.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o bubblesortmem bubblesortmem.c -L../.. -lboolector
clean:
	rm -f bubblesortmem
