all: $(BINDIR)/testibv

$(BUILDIR)/$(TESTDIR)/testibv.o: $(SRCDIR)/$(TESTDIR)/testibv.cc $(SRCDIR)/btoribv.cc
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(BINDIR)/testibv: $(BUILDIR)/$(TESTDIR)/testibv.o $(BUILDIR)/btoribv.o $(LDEPS)
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/$(TESTDIR)/testibv.o $(BUILDIR)/btoribv.o -L$(BUILDIR) -lboolector $(LIBS)

clean: testibv.clean

testibv.clean:
	rm -f $(BUILDIR)/$(TESTDIR)/testibv $(BUILDIR)/$(TESTDIR)/testibv.o
