LIBPATH=../..
CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(CC) $(CFLAGS)  bv1.c -L$(LIBPATH) -lboolector -o bv1
	$(CC) $(CFLAGS)  bv2.c -L$(LIBPATH) -lboolector -o bv2
clean:
	rm -f bv1 bv2
