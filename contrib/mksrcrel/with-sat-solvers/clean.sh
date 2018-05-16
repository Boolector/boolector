#!/bin/sh
for component in boolector cadical picosat precosat lingeling btor2tools
do
  rm -rf $component
done
