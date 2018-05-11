include ../makefile.common
all:
	$(CC) $(CFLAGS) -o writechains writechains.c $(LIBS)
	./genbenchmarks.sh
clean:
	rm -f writechains *.smt2
