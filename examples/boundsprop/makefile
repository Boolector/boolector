CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(MAKE) minor
	$(MAKE) maxor
	$(MAKE) minand
	$(MAKE) maxand
	$(MAKE) minxor
	$(MAKE) maxxor

minor: minormain.c minor.c minor.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minor.c minormain.c -L../.. -lboolector

maxor: maxormain.c maxor.c maxor.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxor.c maxormain.c -L../.. -lboolector

minand: minandmain.c minand.c minand.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minand.c minandmain.c -L../.. -lboolector

maxand: maxandmain.c maxand.c maxand.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxand.c maxandmain.c -L../.. -lboolector

minxor: minxormain.c minxor.c minxor.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minxor.c minxormain.c -L../.. -lboolector

maxxor: maxxormain.c maxxor.c maxxor.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxxor.c maxxormain.c -L../.. -lboolector


clean:
	rm -f minor maxor minand maxand minxor maxxor
