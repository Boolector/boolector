LIBPATH=../..
CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(CC) $(CFLAGS)  array1.c -L$(LIBPATH) -lboolector -o array1 
	$(CC) $(CFLAGS)  array2.c -L$(LIBPATH) -lboolector -o array2 
clean:
	rm -f array1 array2
