#!/bin/sh

# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

# Count the number of operators that occur in a BTOR file.
exec awk '{a[$2]++}END{for(k in a)printf "%-7s%d\n", k, a[k]|"sort -n -k 2";}' $*
