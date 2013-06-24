LIBOBJ+=btoribv.o
all: btorimc
btorimc: btorimc.o libboolector.a $(LDEPS)
	$(CXX) $(CFLAGS) -o $@ btorimc.o -L. -lboolector $(LIBS)
clean: ibv.clean
ibv.clean:
	rm -f btorimc
