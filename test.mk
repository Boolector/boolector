TESTSRC=$(wildcard $(TESTDIR)/test*.c $(TESTDIR)/test*.cc )
TESTOBJ=$(patsubst %.c, $(BUILDIR)/%.o, $(TESTSRC))

all: $(BINDIR)/test

-include $(BUILDIR)/$(TESTDIR)/test.dep

$(BUILDIR)/$(TESTDIR)/test.dep: $(BUILDIR)/btorconfig.h $(SRC) $(TESTSRC) makefile test.mk
	@mkdir -p $(@D)
	rm -f $@; \
	$(CC) $(CFLAGS) $(INCS) -MM $(TESTSRC) | \
	sed -e 's,:,: makefile,' -e 's,^test,$(BUILDIR)/$(TESTDIR)/test,' >$@

$(BINDIR)/test: $(TESTOBJ) $(BUILDIR)/libboolector.a  $(LDEPS) makefile
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -o $@ $(TESTOBJ) $(INCS) -L$(BUILDIR) -lboolector $(LIBS)

clean: test-clean

test-clean:
	rm -f $(BUILDIR)/$(TESTDIR)/*.o
	rm -f $(BUILDIR)/$(TESTDIR)/test.dep

