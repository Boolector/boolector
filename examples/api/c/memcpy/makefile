include ../makefile.common
all:
	$(CC) $(CFLAGS) $(INC) -o memcpy memcpy.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f memcpy *.smt2
