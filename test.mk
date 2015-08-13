TESTDIR=tests
TESTSRC=$(wildcard $(TESTDIR)/test*.c $(TESTDIR)/test*.cc )
TESTOBJ=$(addsuffix .o,$(basename $(TESTSRC)))

all: test

-include test.dep

clean: test-clean

test-clean:
	rm -f $(TESTDIR)/*.o
	rm -f test.dep

test.dep: btorconfig.h $(SRC) $(TESTSRC) makefile test.mk
	rm -f $@; \
	$(CC) $(CFLAGS) -MM $(TESTSRC) -I. | \
	sed -e 's,:,: makefile,' -e 's,^test,tests/test,' >$@

test: $(TESTOBJ) libboolector.a  $(LDEPS)
	$(CC) $(CFLAGS) -o $@ $(TESTOBJ) -L. -lboolector $(LIBS)
