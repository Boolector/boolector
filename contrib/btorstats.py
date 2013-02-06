#!/usr/bin/env python3

import sys

if __name__ == "__main__":
    infile = sys.stdin

    if len(sys.argv) == 2:
        try:
            infile = open(sys.argv[1], 'r')
        except IOError as err:
            sys.exit(err)
    elif len(sys.argv) > 2:
        sys.exit("invalid number of arguments")

    id2symbol = {}
    nodes_cnt = {}
    nodes_ref = {}

    writes = []
    aconds = []
    arrays = []
    lambdas = []
    params = []

    num_total_nodes = 0
    reads_on_arrays = 0
    reads_on_aconds = 0
    reads_on_writes = 0
    reads_on_lambdas = 0
    reads_on_write_node = {}
    reads_on_lambda_node = {}

    for line in infile:
        tokens = line.split() 

        if len(tokens) == 0 or line[0] == ';':
            continue

        id = int(tokens[0])
        symbol = tokens[1]
        num_total_nodes += 1

        assert(id not in id2symbol)
        id2symbol[id] = symbol

        if symbol == "cond" and len(tokens) == 7: 
            symbol = "acond"

        if symbol == "slice":
            children = [abs(int(tokens[3]))]
        elif symbol == "acond" or symbol == "array" or symbol == "write":
            children = [abs(int(s)) for s in tokens[4:]]
        elif symbol != "var" and symbol != "const":
            children = [abs(int(s)) for s in tokens[3:]]
        else:
            children = []
        
        if symbol not in nodes_ref:
            nodes_ref[symbol] = 0

        for cid in children:
            nodes_ref[id2symbol[cid]] += 1

        if symbol not in nodes_cnt:
            nodes_cnt[symbol] = 0
        nodes_cnt[symbol] += 1


        if symbol == "read":
            if children[0] in aconds:
                reads_on_aconds += 1
            elif children[0] in arrays: 
                reads_on_arrays += 1
            elif children[0] in writes:
                reads_on_writes += 1
                if children[0] not in reads_on_write_node:
                    reads_on_write_node[children[0]] = 0
                reads_on_write_node[children[0]] += 1
            elif children[0] in lambdas:
                reads_on_lambdas += 1
                if children[0] not in reads_on_lambda_node:
                    reads_on_lambda_node[children[0]] = 0
                reads_on_lambda_node[children[0]] += 1
            else:
                print(children[0])

        if symbol == "write":
            writes.append(id)
        elif symbol == "array":
            arrays.append(id)
        elif symbol == "acond":
            aconds.append(id)
        elif symbol == "lambda":
            lambdas.append(id)
        elif symbol == "param":
            params.append(id)
    

    if infile != sys.stdin:
        infile.close()

    for symbol, cnt in sorted(nodes_cnt.items()):
        print("{0:8s} {1:5d} ({2:d})".format(symbol + ":", cnt, 
              nodes_ref[symbol]))
    print("{0:8s} {1:5d}".format("total:", num_total_nodes))

    print("")
    print("reads on aconds: {0:d}".format(reads_on_aconds))
    print("reads on arrays: {0:d}".format(reads_on_arrays))
    # top 5 writes with most read references
    print("reads on writes: {0:d} {1:s}".format(reads_on_writes, 
        str(sorted(reads_on_write_node.items(), 
                   key=lambda t: t[1], reverse=True)[:5])))
    print("reads on lambdas: {0:d} {1:s}".format(reads_on_lambdas,
        str(sorted(reads_on_lambda_node.items(), 
                   key=lambda t: t[1], reverse=True)[:5])))
