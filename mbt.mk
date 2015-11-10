LIBOBJ+=aigprop.o

all: btoruntrace btormbt

btoruntrace: btoruntrace.c libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) $(INCS) -o $@ btoruntrace.o -L. -lboolector $(LIBS)
btormbt: btormbt.c libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) $(INCS) -o $@ btormbt.o -L. -lboolector $(LIBS)

clean: btormbt-clean
btormbt-clean:
	rm -f btoruntrace btormbt
