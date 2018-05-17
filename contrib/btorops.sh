#!/bin/sh

# Count the number of operators that occur in a BTOR file.
exec awk '{a[$2]++}END{for(k in a)printf "%-7s%d\n", k, a[k]|"sort -n -k 2";}' $*
