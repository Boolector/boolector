#!/bin/sh
make || exit 1
inputs="1011001"
echo $inputs | ./twocount32 && exit 1
echo $inputs | ./twocount32cout && exit 1
exit 0
