include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o nextpowerof2 nextpowerof2.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f nextpowerof2 *.smt2
