#!/usr/bin/env python3

import sys

def shape(kind):
    if kind == "root":
        return "none"
    elif "const" in kind or kind in ["array", "var", "param"]:
        return "box"
    else:
        return "oval"

def arrow(from_id, to_id, label = ""):
    arrowshape="normal"
    if to_id < 0:
        to_id = -to_id
        arrowshape="dot"
    print("{} -> {} [arrowhead=\"{}\", taillabel=\"{}\"]".format(
          from_id, to_id, arrowshape, label))

def node(id, shape, label, style = "", fillcolor = ""):
    s = "{} [shape={}, label=\"{}\"".format(id, shape, label)
    if style != "":
        s += ", style={}".format(style)
    if fillcolor != "":
        s += ", fillcolor={}".format(fillcolor)
    s += "]"
    print(s)

if __name__ == "__main__":

    print("digraph G {")

    try:
        for line in sys.stdin:
            t = line.split()
            id = t[0]
            kind = t[1]
            label = "{}: {}".format(id, kind)
            style = ""
            fillcolor = ""

            if kind == "root":
                label = ""
            elif kind == "array":
                style = "filled"
                fillcolor = "lightblue"
            elif kind == "lambda": 
                style = "filled"
                fillcolor = "lightgray"
            elif kind == "apply":
                style = "filled"
                fillcolor = "lightyellow"

            node(id, shape(kind), label, style, fillcolor)
            
            if "const" in kind:
                continue
            if kind in ["array", "var", "param"]:
                continue

            offset = 3
            if kind in ["array", "lambda"]:
                offset += 1

            children = t[offset:]
            i = 1
            for c in children:
                try:
                    label = ""
                    if len(children) > 1:
                        label = str(i) 
                    arrow(id, int(c), label) 
                except ValueError:
                    break
                i += 1

    except IOError as err:
        sys.exit(err)

    print("}")
