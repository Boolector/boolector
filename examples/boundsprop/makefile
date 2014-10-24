include ../makefile.common

all: minor maxor minand maxand minxor maxxor theorems

minor:
	$(CC) $(CFLAGS) $(INC) -o minor minor.c minormain.c $(LIBS)

maxor:
	$(CC) $(CFLAGS) $(INC) -o maxor maxor.c maxormain.c $(LIBS)

minand:
	$(CC) $(CFLAGS) $(INC) -o minand minand.c minandmain.c $(LIBS)

maxand:
	$(CC) $(CFLAGS) $(INC) -o maxand maxand.c maxandmain.c $(LIBS)

minxor:
	$(CC) $(CFLAGS) $(INC) -o minxor minxor.c minxormain.c $(LIBS)

maxxor:
	$(CC) $(CFLAGS) $(INC) -o maxxor maxxor.c maxxormain.c $(LIBS)

theorems:
	$(CC) $(CFLAGS) $(INC) -o theorems theorems.c minor.c minand.c maxor.c maxand.c minxor.c maxxor.c $(LIBS)

clean:
	rm -f minor maxor minand maxand minxor maxxor theorems
