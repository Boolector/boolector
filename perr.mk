all:
	boolector `ls log/smt2perr*.smt2|sort -n |tail -1`
