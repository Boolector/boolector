SRC=$(HOME)/src
BOOLECTOR=$(SRC)/boolector
LINGELING=$(SRC)/lingeling
COMPILE=gcc -Wall -g -I$(BOOLECTOR) -L$(BOOLECTOR) -L$(LINGELING)
all: leapyear
leapyear: leapyear.c $(BOOLECTOR)/libboolector.a $(LINGELING)/liblgl.a makefile
	$(COMPILE) -o $@ leapyear.c -lboolector -llgl -lm
clean:
	rm -f leapyear
