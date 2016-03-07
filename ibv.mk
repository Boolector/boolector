LIBOBJ+=$(BUILDIR)/btoribv.o

all: $(BUILDIR)/btorimc $(BUILDIR)/$(TESTDIR)/testibv

$(BUILDIR)/btorimc: $(BUILDIR)/btorimc.o $(BUILDIR)/libboolector.a $(LDEPS)
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btorimc.o -L$(BUILDIR) -lboolector $(LIBS)

$(BUILDIR)/$(TESTDIR)/testibv.o: testibv.cc
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@

$(BUILDIR)/$(TESTDIR)/testibv: $(BUILDIR)/$(TESTDIR)/testibv.o $(BUILDIR)/libboolector.a $(LDEPS)
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -o $@ -L$(BUILDIR) -lboolector $(LIBS)

clean: ibv.clean

ibv.clean:
	rm -f $(BUILDIR)/btorimc $(BUILDIR)/btorimc.o
	rm -f $(BUILDIR)/$(TESTDIR)/testibv $(BUILDIR)/$(TESTDIR)/testibv.o
