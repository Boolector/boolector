function print_unary_child_arrow(id, child_id) {
  if (child_id < 0){
    printf "%d -> %d [arrowhead = \"dot\"]\n", id, -child_id;
  } else {
    printf "%d -> %d [arrowhead = \"normal\"]\n", id, child_id;
  }
}

function print_child_arrows (id, child_id, op) {
  if (child_id < 0){
      printf "%d -> %d [arrowhead = \"dot\", taillabel=\"%d\"];\n", id,
                                             -child_id, op;
  } else {
      printf "%d -> %d [arrowhead = \"normal\", taillabel=\"%d\"];\n", 
                                              id, child_id, op;
  }
}

BEGIN {print "digraph G {"} 
{ if ($3 == "const") { 
    printf "%d [label=\"const\\n%s\"];\n", $1, $4; 
  } else if ($3 == "var") {
    printf "%d [label=\"var\\n%s\"];\n", $1, $2; 
  } else if ($3 == "array") {
    printf "%d [label=\"array\"];\n", $1;
  } else if ($3 == "neg" || $3 == "redor" || $3 == "redxor" || $3 == "redand") {
    printf "%d [label=\"%s\"];\n", $1, $3;
    print_unary_child_arrow($1, $4);
  } else if ($3 == "slice"){
    printf "%d [label=\"slice\\n%d %d\"];\n", $1, $5, $6;
    print_unary_child_arrow($1, $4);
  } else if ($3 == "cond"){
    printf "%d [label=\"cond\"];\n", $1;
    print_child_arrows($1, $4, 1);
    print_child_arrows($1, $5, 2);
    print_child_arrows($1, $6, 3);
  } else if ($3 == "root"){
    printf "%d [shape=\"none\", label=\"\"];\n", $1;
    print_unary_child_arrow($1, $4);
  } else {
    printf "%d [label=\"%s\"];\n", $1, $3;
    print_child_arrows($1, $4, 1);
    print_child_arrows($1, $5, 2);
  }
}
END {print "}"}
