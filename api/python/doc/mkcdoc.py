import sys, re

class DocString:

    def __init__(self, fun, string):
#        self.fun = fun
        self.docstring = string

    def to_rst(self):
        # substitute function references
        s = re.sub(r'\\ref\s+(boolector_[a-z0-9_]+)', r':c:func:`\1`',
                   self.docstring, re.MULTILINE)
        # substitute macro references
        s = re.sub(r'\\ref\s+(BOOLECTOR_[A-Z0-9_]+)', r':c:macro:`\1`',
                   s, re.MULTILINE)
        # substitute \e
        s = re.sub(r'\\e\s+([a-z0-9_]+)', r'``\1``',
                   s, re.MULTILINE)
        # substitute \param
        s = re.sub(r'\\param\s+([a-z0-9_]+)', r':param \1:',
                   s, re.MULTILINE)
        # substitute \return
        s = s.replace('\\return', ':return:')


#        new_lines = []
#        lines = s.split('\n')
#        p = re.compile(r':param ([a-z0-9_]+):')
#        for i in range(len(lines)):
#            new_lines.append(lines[i])
#            m = p.search(lines[i])
#            if m:
#                param = m.group(1)
#                if param not in self.fun.params:
#                    raise Exception(
#                        "Parameter '{}' not found in parameter list of "\
#                        "function '{}'.".format(param, self.fun.name))
#                new_lines.append(":type {}: {}".format(param, self.fun.params[param]))
#
#        s = '\n'.join(new_lines)

        return s

    def __str__(self):
        return self.docstring

    def __repr__(self):
        return self.__str__()

class Macro:

    def __init__(self, definition):
        l = definition.split()
        self.name = l[1]
        assert("BOOLECTOR_" in self.name)
        self.value = l[2]

    def to_rst(self):
        return ".. c:macro:: {}".format(self.name)

class FunDef:

    def __init__(self, signature):
        p_name = re.compile(r'boolector_([a-z0-9_]+)') 
        m = p_name.search(signature)
        assert(m is not None)
        assert(m.group(0))
        self.name = m.group(0)
        self.signature = signature

        p_params = re.compile(r'\((.*)\)')
        m = p_params.search(signature)
        params = m.group(1).split(',')

        self.params = dict()

        # extract param with type
        if len(params) > 0 and params[0] != "void":
            for param in params:
                p = param.split()
                name = p[-1]
                type = " ".join(p[:-1])
                assert(name not in self.params)
                self.params[name] = type 

    def to_rst(self):
        return ".. c:function:: {}".format(self.signature.replace(';', ''))

    def __str__(self):
        return self.signature

    def __repr__(self):
        return self.__str__()

if __name__ == "__main__":

    if len(sys.argv) != 2:
        raise Exception("Invalid number of arguments")

    macros = dict()
    functions = dict()
    docstrings = dict()
    deprecated = dict()
    with open(sys.argv[1], "r") as file:
        fun_open = False
        doc_open = False
        fun = []
        doc = []
        for line in file:
            line = line.strip()

            assert(not fun_open or not doc_open)
            assert(not doc_open or not fun_open)

            if line.startswith("/**"):  # start doc string
                doc = []
                doc_open = True
            elif not doc_open and "boolector_" in line:  # open function
                fun = []
                fun_open = True

            # collect doc string
            if doc_open and line.startswith("*/"):  # end doc string
                assert(line == "*/")
                doc_open = False
            elif doc_open and line.startswith("*"): # contents doc string
                doc.append(line[2:])

            # collect function signature
            if fun_open:
                fun.append(line)

            if fun_open and ");" in line:  # end function
                fun_open = False
                fd = FunDef(" ".join(fun))
                if len(doc) == 0:
                    raise Exception(
                        "No docstring found for function '{}'".format(fd.name))
                ds = DocString(fd, "\n".join(doc))
                if ".. deprecated::" in ds.docstring:
                    deprecated[fd.name] = fd
                else:
                    functions[fd.name] = fd
                docstrings[fd.name] = ds
                fun = []
                doc = []

            l = line.split()
            if len(l) > 2 and "#define" == l[0] and "BOOLECTOR_" in l[1]:
                m = Macro(line)
                ds = DocString(None, "\n".join(doc))
                macros[m.name] = m 
                docstrings[m.name] = ds

    with open('cfunctions.rst', 'w') as file:
        for f in sorted(functions.keys()):
            file.write("{}\n\n".format(functions[f].to_rst()))
            for line in docstrings[f].to_rst().split('\n'):
                file.write("    {}\n".format(line))
            file.write("\n")
    print("generated cfunctions.rst")

    with open('cdeprecated.rst', 'w') as file:
        for f in sorted(deprecated.keys()):
            file.write("{}\n\n".format(deprecated[f].to_rst()))
            for line in docstrings[f].to_rst().split('\n'):
                file.write("    {}\n".format(line))
            file.write("\n")
    print("generated cdeprecated.rst")

    with open('cmacros.rst', 'w') as file:
        for m in sorted(macros.keys()):
            file.write("{}\n\n".format(macros[m].to_rst()))
            for line in docstrings[m].to_rst().split('\n'):
                file.write("    {}\n".format(line))
            file.write("\n")
    print("generated cmacros.rst")

    sys.exit(0)
