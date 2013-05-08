LIBOBJS+=btoribv.o
all: btorimc
btorimc: btorimc.o libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) -o $@ btorimc.o -L. -lboolector $(LIBS)
clean: ibv.clean
ibv.clean:
	rm -f btorimc
