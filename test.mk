TESTSRCS=$(wildcard $(SRCDIR)/$(TESTDIR)/test*.c)
TESTOBJS=$(subst $(SRCDIR), $(BUILDIR), $(patsubst %.c, %.o, $(TESTSRCS)))

all: $(BINDIR)/test

-include $(BUILDIR)/$(TESTDIR)/test.dep

$(BUILDIR)/$(TESTDIR)/test.dep: $(BUILDIR)/btorconfig.h $(SRCS) $(TESTSRCS) makefile test.mk
	@mkdir -p $(@D)
	rm -f $@; \
	$(CC) $(CFLAGS) $(INCS) -MM $(TESTSRCS) | \
	sed -e 's,:,: makefile,' -e 's,^test,$(BUILDIR)/$(TESTDIR)/test,' >$@

$(BINDIR)/test: $(TESTOBJS) $(BUILDIR)/libboolector.a  $(LDEPS) makefile
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -o $@ $(TESTOBJS) $(INCS) -L$(BUILDIR) -lboolector $(LIBS)

clean: test-clean

test-clean:
	rm -f $(BUILDIR)/$(TESTDIR)/*.o
	rm -f $(BUILDIR)/$(TESTDIR)/test.dep

