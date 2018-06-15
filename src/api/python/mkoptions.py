#
# Generate pyboolector_options.pxd from btortypes.h
#
import sys

if len(sys.argv) != 3 or not sys.argv[1].endswith('btortypes.h'):
    print('btortypes.h not specified', file=sys.stderr)
    sys.exit(1)

with open(sys.argv[1], 'r') as btortypes:
    with open(sys.argv[2], 'w') as outfile:
        i = 0
        for line in btortypes:
            line = line.strip()
            if line.startswith('BTOR_OPT_') and line.endswith(','):
                print('{}={}'.format(line.strip(','), i),file=outfile)
                i += 1
