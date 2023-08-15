#
# Generate pyboolector_enums.pxd from btortypes.h
#
# Usage: mkenums.py path/to/btortypes.h path/to/outputfile
#

import sys
import os
from collections import OrderedDict


class BtorTypesParseError(Exception):
    def __init__(self, btor_enum):
        self.message = "Failed to parse btortypes.h when handling enum '{:s}'".format(
            btor_enum
        )
        super(Exception, self).__init__(self.message)


def extract_enums(btortypes):
    """
    Given the file "btortypes.h", constructs a dictionary representing the set
    of all Boolector enums and corresponding values
    """

    # We want to get only non-empty, stripped lines from our input file
    lines = [
        line
        for line in [line.strip() for line in open(btortypes, "r").readlines()]
        if line
    ]

    # Manually create an iterator as we want to be able to move this forwards ourselves
    line_iter = iter(lines)

    # Dictionary of all our enums and their values
    btor_enums = OrderedDict()

    # For each line ...
    for line in line_iter:

        # Do we see the _start_ of an enum?
        if line.startswith("enum Btor"):

            # Obtain the enum name by splitting the line and taking the second
            # part
            enum_name = line.split(" ")[1]

            # Get the next line
            line = next(line_iter)

            # We expect this to be an opening curly, given Boolector's style
            if line != "{":
                raise BtorTypesParseError(enum_name)

            # List to collect up all of the enum values for this enum
            enum_vals = []

            # Keep iterating until our line starts with the closing curly
            while not line.startswith("};"):

                # If our line starts with the prefix `BTOR_` and ends with
                # a comma, then we have an enum value
                if line.startswith("BTOR_") and line.endswith(","):

                    # Some lines have " = <value>", in them, so we need to
                    # get the left-hand side and strip the space
                    enum_value = line.rstrip(",").split("=")[0].strip()

                    # Store our enum value
                    enum_vals.append(enum_value)

                # Consume the next line
                line = next(line_iter)

            # Store this enum with its associated set of values
            btor_enums[enum_name] = enum_vals

    # Return our dictionary of enums
    return btor_enums


# Template for one enum
ENUM_TEMPLATE = """
    cpdef enum {btor_enum:s}:
        {values:s}
"""

# Template for the whole file
FILE_TEMPLATE = """
cdef extern from \"btortypes.h\":
    {enums:s}"""


def generate_output(btor_enums, output_file):
    """
    Given a dictionary of enums, formats each enum into `ENUM_TEMPLATE` and
    then all the enums into `FILE_TEMPLATE` and writes into "output_file"
    """

    # List of strings for all our enums
    all_enums = []

    # Iterate on each enum and its associated values
    for btor_enum, values in btor_enums.items():

        # Construct the formatted list of all values
        formatted_values = ",\n        ".join(values)

        # Construct the enum string
        curr_enum_string = ENUM_TEMPLATE.format(
            btor_enum=btor_enum, values=formatted_values
        )

        # Store it
        all_enums.append(curr_enum_string)

    # Open-up our output file
    with open(output_file, "w") as output_fd:

        # Write the whole template
        output_fd.write(FILE_TEMPLATE.format(enums="\n".join(all_enums)))


def main():
    """
    Entry point
    """

    # We expect to only have three arguments
    if len(sys.argv) != 3:
        raise ValueError("invalid number of arguments")

    # Script arguments
    input_file = sys.argv[1]
    output_file = sys.argv[2]

    # We expect our last argument to be a file 'btortypes.h'
    if os.path.basename(output_file) == "btortypes.h":
        raise ValueError("btortypes.h not specified")

    # Extract all of our enums
    btor_enums = extract_enums(input_file)

    # Generate our output file
    generate_output(btor_enums, output_file)

    return 0


if __name__ == "__main__":
    sys.exit(main())

# EOF
