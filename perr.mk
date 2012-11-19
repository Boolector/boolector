all:
	#boolector log/smt2perr007.smt2
	boolector `ls log/smt2perr*.smt2|sort -n |tail -1`
