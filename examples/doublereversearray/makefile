include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o doublereversearray doublereversearray.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f doublereversearray *.smt2
