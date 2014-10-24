all: synthebtor

synthebtor: synthebtor.o libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) $(INCS) -o $@ synthebtor.o -L. -lboolector $(LIBS)

clean: synthebtor-clean
synthebtor-clean:
	rm -f synthebtor
