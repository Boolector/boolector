
all: $(BINDIR)/btoruntrace $(BINDIR)/btormbt

$(BINDIR)/btormbt: $(BUILDIR)/btormbt.o $(LDEPS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btormbt.o -L$(BUILDIR) -lboolector $(LIBS)

$(BINDIR)/btoruntrace: $(BUILDIR)/btoruntrace.o $(LDEPS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -o $@ $(BUILDIR)/btoruntrace.o -L$(BUILDIR) -lboolector $(LIBS)

clean: btormbt-clean

btormbt-clean:
	rm -f $(BUILDIR)/btoruntrace $(BUILDIR)/btormbt
	rm -f $(BUILDIR)/btoruntrace.o $(BUILDIR)/btormbt.o
