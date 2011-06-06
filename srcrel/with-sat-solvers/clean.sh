#!/bin/sh
for component in boolector picosat precosat lingeling
do
  rm -rf $component
done
