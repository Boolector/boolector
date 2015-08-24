#!/bin/sh
make clean && ./configure.sh -g -c && make && ./runtests.sh && gcov btorfmt.c
echo "vi btorfmt.c.gcov"
