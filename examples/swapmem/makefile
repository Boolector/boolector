include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o swapmem swapmem.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f swapmem *.smt2
