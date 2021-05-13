FROM quay.io/pypa/manylinux2010_x86_64

RUN for py in /opt/python/cp3{6,7,8,9}-*; do  $py/bin/pip install cython wheel twine; done

CMD /boolector/pypi/build.sh
