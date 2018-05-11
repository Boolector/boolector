include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o matrixmultcomm matrixmultcomm.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f matrixmultcomm *.smt2
