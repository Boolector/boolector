#!/usr/bin/env python3

import sys

#def find_dominated_conds():
#    global num_dominated_conds
#
#    for cond in conds:
#        visit = [cond]
#        visited = {}
#        if node_ref[cond] > 1:
#            continue
#
#        while len(visit) > 0:
#            cur = visit.pop()
#            if cur in visited:
#                continue
#
#            visited[cur] = 1
#            if cur in node_parents:
#                for parent in node_parents[cur]:
#                    visit.append(parent)
#                    if parent in conds:
#                        if node_children[parent][0] == node_children[cond][0]:
#                            num_dominated_conds += 1
#
#def find_dominated_aconds():
#    global num_dominated_aconds
#
#    for acond in aconds:
#        visit = [acond]
#        visited = {}
#        if node_ref[acond] > 1:
#            continue
#
#        while len(visit) > 0:
#            cur = visit.pop()
#            if cur in visited:
#                continue
#
#            visited[cur] = 1
#            if cur in node_parents:
#                for parent in node_parents[cur]:
#                    visit.append(parent)
#                    if parent in aconds:
#                        if node_children[parent][0] == node_children[acond][0]:
#                            num_dominated_aconds += 1

            
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
    node_ref = {}
    node_parents = {}
    node_children = {}

    writes = []
    aconds = []
    conds = []
    arrays = []
    lambdas = []
    params = []
    roots = []

    num_dominated_aconds = 0
    num_dominated_conds = 0
    num_total_nodes = 0
    num_const_index_reads = 0
    num_const_index_writes = 0
    num_const_value_writes = 0
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

        node_children[id] = children
        
        if symbol not in nodes_ref:
            nodes_ref[symbol] = 0
        if id not in node_ref:
            node_ref[id] = 0

        for cid in children:
            nodes_ref[id2symbol[cid]] += 1
            node_ref[cid] += 1
            if not cid in node_parents:
                node_parents[cid] = []
            node_parents[cid].append(id)

        if symbol not in nodes_cnt:
            nodes_cnt[symbol] = 0
        nodes_cnt[symbol] += 1


        if symbol == "read":
            if id2symbol[children[1]] == "const":
                num_const_index_reads += 1

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
        elif symbol == "write":
            if id2symbol[children[1]] == "const":
                num_const_index_writes += 1
            if id2symbol[children[2]] == "const":
                num_const_value_writes += 1

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
        elif symbol == "cond":
            conds.append(id)
        elif symbol == "root":
            roots.append(id)
    

    if infile != sys.stdin:
        infile.close()

    
#    find_dominated_conds()
#    find_dominated_aconds()


    writes_with_one_ref = 0
    for write in writes:
        if node_ref[write] == 1:
            writes_with_one_ref += 1

    lambdas_with_one_ref = 0
    for l in lambdas:
        if node_ref[l] == 1:
            lambdas_with_one_ref += 1


    for symbol, cnt in sorted(nodes_cnt.items()):
        print("{0:8s} {1:5d} ({2:d})".format(symbol + ":", cnt, 
              nodes_ref[symbol]))
    print("{0:8s} {1:5d}".format("total:", num_total_nodes))

    print("")
    print("writes with constant indices: {}".format(num_const_index_writes))
    print("writes with constant values: {}".format(num_const_value_writes))
    print("reads with constant indices: {}".format(num_const_index_reads))
    print("reads on aconds: {0:d}".format(reads_on_aconds))
    print("reads on arrays: {0:d}".format(reads_on_arrays))
    # top 5 writes with most read references
    print("reads on writes: {0:d} {1:s}".format(reads_on_writes, 
        str(sorted(reads_on_write_node.items(), 
                   key=lambda t: t[1], reverse=True)[:5])))
    print("reads on lambdas: {0:d} {1:s}".format(reads_on_lambdas,
        str(sorted(reads_on_lambda_node.items(), 
                   key=lambda t: t[1], reverse=True)[:5])))

    print("writes with one ref: {0:d}".format(writes_with_one_ref))
    print("lambdas with one ref: {0:d}".format(lambdas_with_one_ref))
#    print("dominated aconds: {}".format(num_dominated_aconds))
#    print("dominated conds: {}".format(num_dominated_conds))

