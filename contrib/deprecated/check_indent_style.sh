#!/bin/sh
file=$1
pcregrep -Mn "(^[\t\ ]*)(if|while|else|for|switch) .*\n\1\{" $file
pcregrep -Mn "(^[\t\ ]*)(if|while|else|for|switch).* {" $file
