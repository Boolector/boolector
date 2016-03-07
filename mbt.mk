
all: $(BUILDIR)/btoruntrace $(BUILDIR)/btormbt

$(BUILDIR)/btormbt.o: btormbt.c
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -c $< -o $@

$(BUILDIR)/btormbt: $(BUILDIR)/btormbt.o $(BUILDIR)/libboolector.a $(LDEPS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -o $@ -L$(BUILDIR) -lboolector $(LIBS)

$(BUILDIR)/btoruntrace.o: btoruntrace.c
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -c $< -o $@

$(BUILDIR)/btoruntrace: $(BUILDIR)/btoruntrace.o $(BUILDIR)/libboolector.a $(LDEPS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(INCS) -o $@ -L$(BUILDIR) -lboolector $(LIBS)

clean: btormbt-clean

btormbt-clean:
	rm -f $(BUILDIR)/btoruntrace $(BUILDIR)/btormbt
	rm -f $(BUILDIR)/btoruntrace.o $(BUILDIR)/btormbt.o
