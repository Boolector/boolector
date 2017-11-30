all: $(BINDIR)/boolectormc

$(BINDIR)/boolectormc: $(BUILDIR)/btormcmain.o $(LDEPS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btormcmain.o -L$(BUILDIR) -lboolector $(LIBS)


clean: boolectormc.clean

boolectormc.clean:
	rm -f $(BUILDIR)/boolectormc $(BUILDIR)/boolectormc.o $(BUILDIR)/btormcmain.o

