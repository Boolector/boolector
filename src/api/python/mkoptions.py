#
# Generate pyboolector_options.pxd from btortypes.h
#
# Usage: mkoptions.py path/to/btortypes.h path/to/outputfile
#
import sys

def die(msg):
    sys.stderr.write('{}\n'.format(msg))
    sys.exit(1)

if len(sys.argv) != 3:
    die('invalid number of arguments')
if not sys.argv[1].endswith('btortypes.h'):
    die('btortypes.h not specified')

with open(sys.argv[1], 'r') as btortypes:
    with open(sys.argv[2], 'w') as outfile:
        outfile.write("cdef extern from \"btortypes.h\":\n")
        outfile.write("    cpdef enum BtorOption:")
        i = 0
        for line in btortypes:
            line = line.strip()
            if line.startswith('BTOR_OPT_') and line.endswith(','):
                outfile.write('{}\n        {}'.format(',' if i > 0 else '', line.strip(',')))
                i += 1
