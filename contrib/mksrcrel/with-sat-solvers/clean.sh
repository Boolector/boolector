#!/bin/sh
for component in boolector cadical picosat precosat lingeling
do
  rm -rf $component
done
