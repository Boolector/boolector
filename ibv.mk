LIBOBJ+=$(BUILDIR)/btoribv.o

all: $(BINDIR)/btorimc $(BINDIR)/testibv

$(BINDIR)/btorimc: $(BUILDIR)/btorimc.o $(BUILDIR)/btoribv.o $(LDEPS)
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btorimc.o $(BUILDIR)/btoribv.o -L$(BUILDIR) -lboolector $(LIBS)

$(BUILDIR)/$(TESTDIR)/testibv.o: $(SRCDIR)/$(TESTDIR)/testibv.cc $(SRCDIR)/btoribv.cc
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(BINDIR)/testibv: $(BUILDIR)/$(TESTDIR)/testibv.o $(BUILDIR)/btoribv.o $(LDEPS)
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/$(TESTDIR)/testibv.o $(BUILDIR)/btoribv.o -L$(BUILDIR) -lboolector $(LIBS)

clean: ibv.clean

ibv.clean:
	rm -f $(BUILDIR)/btorimc $(BUILDIR)/btorimc.o
	rm -f $(BUILDIR)/$(TESTDIR)/testibv $(BUILDIR)/$(TESTDIR)/testibv.o
