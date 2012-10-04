include ../makefile.common

all:
	$(MAKE) all-minor
	$(MAKE) all-maxor
	$(MAKE) all-minand
	$(MAKE) all-maxand
	$(MAKE) all-minxor
	$(MAKE) all-maxxor
	$(MAKE) all-theorems

all-minor:
	$(CC) $(CFLAGS) -o minor minor.c minormain.c $(LIBS)

all-maxor:
	$(CC) $(CFLAGS) -o maxor maxor.c maxormain.c $(LIBS)

all-minand:
	$(CC) $(CFLAGS) -o minand minand.c minandmain.c $(LIBS)

all-maxand:
	$(CC) $(CFLAGS) -o maxand maxand.c maxandmain.c $(LIBS)

all-minxor:
	$(CC) $(CFLAGS) -o minxor minxor.c minxormain.c $(LIBS)

all-maxxor:
	$(CC) $(CFLAGS) -o maxxor maxxor.c maxxormain.c $(LIBS)

all-theorems:
	$(CC) $(CFLAGS) -o theorems theorems.c minor.c minand.c maxor.c maxand.c minxor.c maxxor.c $(LIBS)

clean:
	rm -f minor maxor minand maxand minxor maxxor theorems
