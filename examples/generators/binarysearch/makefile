include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o binarysearch binarysearch.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f binarysearch *.smt2
