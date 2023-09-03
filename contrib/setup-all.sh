#!/usr/bin/env bash

# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

set -e -o pipefail

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./contrib/setup-cms.sh
./contrib/setup-lingeling.sh
./contrib/setup-minisat.sh
./contrib/setup-picosat.sh
