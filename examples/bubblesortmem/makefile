include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o bubblesortmem bubblesortmem.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f bubblesortmem *.smt2
