CC=gcc
CFLAGS=-g -Wall -W -Wextra

all:
	$(MAKE) minor
	$(MAKE) maxor
	$(MAKE) minand
	$(MAKE) maxand

minor: minor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minor.c -L../.. -lboolector

maxor: maxor.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxor.c -L../.. -lboolector

minand: minand.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ minand.c -L../.. -lboolector

maxand: maxand.c ../../boolector.h ../../btorutil.h ../../libboolector.a
	$(CC) $(CFLAGS) -o $@ maxand.c -L../.. -lboolector


clean:
	rm -f minor maxor minand maxand
