all:
	 for m in `find * -name makefile`; do d=`dirname $$m`; make -C $$d all; done
clean:
	 for m in `find * -name makefile`; do d=`dirname $$m`; make -C $$d clean; done
