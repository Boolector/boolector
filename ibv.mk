LIBOBJ+=$(BUILDIR)/btoribv.o

all: $(BINDIR)/btorimc

$(BINDIR)/btorimc: $(BUILDIR)/btorimc.o $(BUILDIR)/btoribv.o $(LDEPS)
	@mkdir -p $(@D)
	$(CXX) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btorimc.o $(BUILDIR)/btoribv.o -L$(BUILDIR) -lboolector $(LIBS)

clean: ibv.clean

ibv.clean:
	rm -f $(BUILDIR)/btorimc $(BUILDIR)/btorimc.o
