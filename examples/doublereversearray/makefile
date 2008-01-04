CC=gcc
CFLAGS=-g -Wall -W -Wextra
doublereversearray: doublereversearray.c ../../boolector.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ doublereversearray.c -L../.. -lboolector
clean:
	rm -f doublereversearray
