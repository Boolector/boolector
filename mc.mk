all: $(BINDIR)/btormc

$(BINDIR)/btormc: $(BUILDIR)/btormcmain.o $(LDEPS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btormcmain.o -L$(BUILDIR) -lboolector $(LIBS)


clean: btormc.clean

btormc.clean:
	rm -f $(BUILDIR)/btormc $(BUILDIR)/btormc.o $(BUILDIR)/btormcmain.o

