#!/usr/bin/env python
import sys, getopt

QUEENS_MODE = 0
QUEENS_MODE_NP1 = 1
QUEENS_MODE_GTN = 2
NO_THREE_IN_LINE_MODE = 3
NO_THREE_IN_LINE_MODE_2NP1 = 4
NO_THREE_IN_LINE_MODE_GT2N = 5

def usage():
  print ("usage: queenslia [-h] [-s <size>] [-m <mode>]")
  sys.exit(0)

def die(msg):
  assert msg != None
  print (msg)
  sys.exit(1)

def board_field (x, y):
  assert x >= 0
  assert y >= 0
  return "board" + str(x) + "_" + str(y)

mode = QUEENS_MODE
size = 8
id = 1
constraints = [] 

try:
  opts, args = getopt.getopt(sys.argv[1:], "hm:s:")
except getopt.GetoptError as err:
  print (str(err))
  usage()

for o, a in opts:
  if o in ("-h"):
    usage()
  elif o in ("-m"):
    if a == "0":
      mode = QUEENS_MODE
    elif a == "1":
      mode = QUEENS_MODE_NP1
    elif a == "2":
      mode = QUEENS_MODE_GTN
    elif a == "3":
      mode = NO_THREE_IN_LINE_MODE 
    elif a == "4":
      mode = NO_THREE_IN_LINE_MODE_2NP1
    elif a == "5":
      mode = NO_THREE_IN_LINE_MODE_GT2N
    else:
      die ("mode must be >= 0 and <= 5")
  elif o in ("-s"):
    size = int (a)
    if size < 4:
      die ("size must be >= 4")

if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
   mode == NO_THREE_IN_LINE_MODE_GT2N:
  print ("(benchmark queensNoThreeInLine" + str(size) + "x" + str(size))
else:
  print ("(benchmark queens" + str(size) + "x" + str(size))
print (":source {")
if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
   mode == NO_THREE_IN_LINE_MODE_GT2N:
  print ("LIA encoding of no-three-in-line problem")
else:
  print ("LIA encoding of n-queens problem")
if mode == QUEENS_MODE:
  print ("We try to place " + str(size) + \
         " queens on a " + str(size) + " x " + str(size) + " board")
elif mode == QUEENS_MODE_NP1: 
  print ("We try to place n + 1 queens on an n x n board")
elif mode == QUEENS_MODE_GTN:
  print ("We try to place m queens on an n x n board with m > n")
elif mode == NO_THREE_IN_LINE_MODE:
  print ("We try to place " + str(2 * size) + \
         " queens on a " + str(size) + " x " + str(size) + " board")
elif mode == NO_THREE_IN_LINE_MODE_2NP1:
  print ("We try to place " + str(2 * size + 1) + \
         " queens on a " + str(size) + " x " + str(size) + " board")
elif mode == NO_THREE_IN_LINE_MODE_GT2N:
  print ("We try to place m queens on an n x n board with m > 2n")
print ("Contributed by Robert Brummayer (robert.brummayer@gmail.com)")
print ("}")
if mode == QUEENS_MODE:
  print (":status sat")
elif mode == NO_THREE_IN_LINE_MODE:
  print (":status unknown")
else:
  print (":status unsat")
print (":logic QF_LIA")
for i in range(size):
  for j in range(size):
    print (":extrafuns ((" + board_field(i, j) + " Int))")
print (":formula")

# generate row constraints 
for i in range(size):
  last = board_field(i, 0) 
  for j in range(1, size):
    print ("(let (?e" + str(id) + " (+ " + last + " " + board_field(i,j) + "))")
    last = "?e" + str(id)
    id += 1
  if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
     mode == NO_THREE_IN_LINE_MODE_GT2N:
    print ("(flet ($e" + str(id) + " (= " + last + " 2))")
  else:
    print ("(flet ($e" + str(id) + " (= " + last + " 1))")
  constraints.append ("$e" + str(id))
  id += 1

# generate col constraints 
for i in range(size):
  last = board_field(0, i) 
  for j in range(1, size):
    print ("(let (?e" + str(id) + " (+ " + last + " " + board_field(j,i) + "))")
    last = "?e" + str(id)
    id += 1
  if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
     mode == NO_THREE_IN_LINE_MODE_GT2N:
    print ("(flet ($e" + str(id) + " (= " + last + " 2))")
  else:
    print ("(flet ($e" + str(id) + " (= " + last + " 1))")
  constraints.append ("$e" + str(id))
  id += 1

#generate diagonal constraints
for i in range(1, size):
  last = board_field(i, 0)
  row = i - 1
  col = 1
  assert row >= 0 and col < size 
  while row >= 0 and col < size:
    print ("(let (?e" + str(id) + " (+ " + last + " " + \
           board_field(row, col) + "))")
    last = "?e" + str(id)
    id += 1
    row -= 1
    col += 1
  if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
     mode == NO_THREE_IN_LINE_MODE_GT2N:
    print ("(flet ($e" + str(id) + " (< " + last + " 3))")
  else:
    print ("(flet ($e" + str(id) + " (<= " + last + " 1))")
  constraints.append ("$e" + str(id))
  id += 1

for i in range(1, size - 1):
  last = board_field(size - 1, i)
  row = size - 1 - 1
  col = i + 1
  assert row >= 0 and col < size 
  while row >= 0 and col < size: 
    print ("(let (?e" + str(id) + " (+ " + last + " " + \
           board_field(row, col) + "))")
    last = "?e" + str(id)
    id += 1
    row -= 1
    col += 1
  if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
     mode == NO_THREE_IN_LINE_MODE_GT2N:
    print ("(flet ($e" + str(id) + " (< " + last + " 3))")
  else:
    print ("(flet ($e" + str(id) + " (<= " + last + " 1))")
  constraints.append ("$e" + str(id))
  id += 1

for i in range(1, size):
  last = board_field(i, size - 1)
  row = i - 1
  col = size - 1 - 1
  assert row >= 0 and col >= 0 
  while row >= 0 and col >= 0:
    print ("(let (?e" + str(id) + " (+ " + last + " " + \
           board_field(row, col) + "))")
    last = "?e" + str(id)
    id += 1
    row -= 1
    col -= 1
  if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
     mode == NO_THREE_IN_LINE_MODE_GT2N:
    print ("(flet ($e" + str(id) + " (< " + last + " 3))")
  else:
    print ("(flet ($e" + str(id) + " (<= " + last + " 1))")
  constraints.append ("$e" + str(id))
  id += 1

for i in range(1, size - 1):
  last = board_field(size - 1, size - 1 - i)
  row = size - 1 - 1
  col = size - 1 - i - 1 
  assert row >= 0 and col >= 0 
  while row >= 0 and col >= 0: 
    print ("(let (?e" + str(id) + " (+ " + last + " " + \
           board_field(row, col) + "))")
    last = "?e" + str(id)
    id += 1
    row -= 1
    col -= 1
  if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
     mode == NO_THREE_IN_LINE_MODE_GT2N:
    print ("(flet ($e" + str(id) + " (< " + last + " 3))")
  else:
    print ("(flet ($e" + str(id) + " (<= " + last + " 1))")
  constraints.append ("$e" + str(id))
  id += 1

# generate additional constraints
if mode == QUEENS_MODE_NP1 or mode == QUEENS_MODE_GTN or \
   mode ==  NO_THREE_IN_LINE_MODE_2NP1 or mode == NO_THREE_IN_LINE_MODE_GT2N:
  print ("(let (?e" + str(id) + " 0)")
  last = "?e" + str(id)
  id += 1
  for i in range(size):
    for j in range(size):
      print ("(let (?e" + str(id) + " (+ " + last + " " + \
             board_field(i, j) + "))")
      last = "?e" + str(id)
      id += 1
  if mode == QUEENS_MODE_NP1:
    print ("(flet ($e" + str(id) + " (= " + last + " " + str(size + 1) + "))")
  elif mode == QUEENS_MODE_GTN:
    print ("(flet ($e" + str(id) + " (> " + last + " " + str(size) + "))")
  elif mode == NO_THREE_IN_LINE_MODE_2NP1:
    print ("(flet ($e" + str(id) + " (= " + last + " " + str(2 * size + 1) + "))")
  else:
    assert mode == NO_THREE_IN_LINE_MODE_GT2N
    print ("(flet ($e" + str(id) + " (> " + last + " " + str(2 * size) + "))")
  constraints.append ("$e" + str(id))
  id += 1

# generate domain constraints for integer variables
for i in range(size):
  for j in range(size):
    print ("(flet ($e" + str(id) + " (or (= " + board_field(i, j) + \
           " 0) (= " + board_field(i, j) + " 1)))")
    constraints.append ("$e" + str(id))
    id += 1 

# combine all constraints by AND
assert len(constraints) >= 2
last = constraints[0]
for i in range(1, len(constraints)):
  print ("(flet ($e" + str(id) + " (and " + last + " " + constraints[i] + "))")
  last = "$e" + str(id)
  id += 1
print (last)
pars = ""
for i in range(id):
  pars = pars + ")"
print (pars)
