CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(MAKE) minor
	$(MAKE) maxor
	$(MAKE) minand
	$(MAKE) maxand

minor: minormain.c minor.c minor.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minor.c minormain.c -L../.. -lboolector

maxor: maxormain.c maxor.c maxor.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxor.c maxormain.c -L../.. -lboolector

minand: minandmain.c minand.c minand.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minand.c minandmain.c -L../.. -lboolector

maxand: maxandmain.c maxand.c maxand.h ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxand.c maxandmain.c -L../.. -lboolector


clean:
	rm -f minor maxor minand maxand
