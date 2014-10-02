all: btor2horn

btor2horn: btor2horn.o btorfmt.o makefile
	$(CC) $(CFLAGS) $(INCS) -o $@ btor2horn.o btorfmt.o

clean: btor2horn-clean
btor2horn-clean:
	rm -f btor2horn
