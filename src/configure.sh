#!/bin/sh
exec $(dirname "$(readlink -f $0)")/../configure.sh
