TESTDIR=tests
TESTOBJ=$(addsuffix .o,$(basename $(wildcard $(TESTDIR)/test*.c )))
SRC+=$(shell ls $(TESTDIR)/*.c)
CFLAGS+=-I"$(shell pwd)"

all: test

clean: test-clean
test-clean:
	rm -f $(TESTDIR)/*.o
	rm -f test.dep

test: $(TESTOBJ) libboolector.a  $(LDEPS)
	$(CC) $(CFLAGS) -o $@ $(TESTOBJ) -L. -lboolector $(LIBS)
