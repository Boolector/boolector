include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o selectionsortmem selectionsortmem.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f selectionsortmem *.smt2
