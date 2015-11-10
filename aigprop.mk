all: aigprop

aigprop: aigprop.c libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) $(INCS) -o $@ aigprop.o -L. -lboolector $(LIBS)

clean: aigprop.clean

aigprop-clean:
	rm -f aigprop

