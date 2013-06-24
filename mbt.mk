
all: btoruntrace btormbt

btoruntrace: btoruntrace.c libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) -o $@ btoruntrace.o -L. -lboolector $(LIBS)
btormbt: btormbt.c libboolector.a $(LDEPS)
	$(CC) $(CFLAGS) -o $@ btormbt.o -L. -lboolector $(LIBS)

clean-mbt:
	rm -f btoruntrace btormbt
	rm -f btoruntrace.o btormbt.o
