CFLAGS="-I../.."
LDFLAGS="-L../.. -L../../../lingeling"

all: pyboolector

pyboolector:
	CFLAGS=$(CFLAGS) LDFLAGS=$(LDFLAGS) python setup.py build_ext -i

clean:
	rm -rf build
	rm -f *.c *.so
