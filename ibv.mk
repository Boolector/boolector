LIBOBJ+=btoribv.o
all: btorimc testibv
btorimc: btorimc.o libboolector.a $(LDEPS)
	$(CXX) $(CFLAGS) -o $@ btorimc.o -L. -lboolector $(LIBS)
testibv: testibv.o libboolector.a $(LDEPS)
	$(CXX) $(CFLAGS) -o $@ testibv.o -L. -lboolector $(LIBS)
clean: ibv.clean
ibv.clean:
	rm -f btorimc
