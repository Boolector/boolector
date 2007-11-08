function print_unary_child_arrow(id, child_id) {
  if (child_id < 0){
    printf "%d -> %d [arrowhead = \"dot\"]\n", id, -child_id;
  } else {
    printf "%d -> %d [arrowhead = \"normal\"]\n", id, child_id;
  }
}

function print_child_arrow (id, child_id, op) {
  if (child_id < 0){
      printf "%d -> %d [arrowhead = \"dot\", taillabel=\"%d\"];\n", id,
                                             -child_id, op;
  } else {
      printf "%d -> %d [arrowhead = \"normal\", taillabel=\"%d\"];\n", 
                                              id, child_id, op;
  }
}

BEGIN {print "digraph G {"} 
{ if ($2 == "const" || $2 == "constd" || $2 == "consth") { 
    printf "%d [label=\"%s\\n%s\"];\n", $1, $2, $4; 
  } else if ($2 == "zero") {
    printf "%d [label=\"zero\\n\"];\n", $1;
  } else if ($2 == "var") {
    printf "%d [label=\"var\\n%s\"];\n", $1, $2; 
  } else if ($2 == "array") {
    printf "%d [label=\"array\"];\n", $1;
  } else if ($2 == "neg" || $2 == "not" || $2 == "redor" || 
             $2 == "redxor" || $2 == "redand") {
    printf "%d [label=\"%s\"];\n", $1, $2;
    print_unary_child_arrow($1, $4);
  } else if ($2 == "slice"){
    printf "%d [label=\"slice\\n%d %d\"];\n", $1, $5, $6;
    print_unary_child_arrow($1, $4);
  } else if ($2 == "cond" || $2 == "write"){
    printf "%d [label=\"%s\"];\n", $1, $2;
    print_child_arrow($1, $4, 1);
    print_child_arrow($1, $5, 2);
    print_child_arrow($1, $6, 3);
  } else if ($2 == "root"){
    printf "%d [shape=\"none\", label=\"\"];\n", $1;
    print_unary_child_arrow($1, $4);
  } else {
    printf "%d [label=\"%s\"];\n", $1, $2;
    print_child_arrow($1, $4, 1);
    print_child_arrow($1, $5, 2);
  }
}
END {print "}"}
