#!/usr/bin/env python
import sys, getopt

QUEENS_MODE = 0
QUEENS_MODE_NP1 = 1
QUEENS_MODE_GTN = 2
NO_THREE_IN_LINE_MODE = 3
NO_THREE_IN_LINE_MODE_2NP1 = 4
NO_THREE_IN_LINE_MODE_GT2N = 5

SEQ_ADDER_ENCODING = 0
PAR_ADDER_ENCODING = 1
ITE_ENCODING = 2
LOOKUP_ENCODING = 3
SHIFTER_ENCODING = 4

def usage():
  print ("usage: queensbv [-h] [-s <size>] [-m <mode>] [-e <encoding>]")
  print ("")
  print (" available modes: ")
  print ("   0:  regular queens mode (default)")
  print ("   1:  try to place n + 1 queens on an n x n board")
  print ("   2:  try to place m queens on an n x n board with m > n")
  print ("   3:  regular no-3-in-line mode")
  print ("   4:  no-3-in-line mode with 2 * n + 1 queens on an n x n board")
  print ("   5:  no-3-in-line mode with m queens on an n x n board with m > 2n")
  print ("")
  print (" available encodings: ")
  print ("   0:  simple adder encoding (default)")
  print ("   1:  parallel adder encoding")
  print ("   2:  if-then-else encoding")
  print ("   3:  lookup encoding")
  print ("   4:  shifter encoding")
  print ("")
  sys.exit(0)

def die(msg):
  assert msg != None
  print (msg)
  sys.exit(1)

def is_power_of_2 (x):
  assert x > 0
  return (x & (x - 1)) == 0

def next_power_of_2 (x):
  assert x > 0
  x -= 1
  i = 1
  while i < 32:
    x = x | (x >> i)
    i *= 2
  return x + 1

def log2 (x):
  result = 0
  assert x > 0
  assert is_power_of_2 (x)
  while x > 1:
    x >>= 1
    result += 1
  assert result >= 0
  return result

def board_field (x, y):
  assert x >= 0
  assert y >= 0
  return "board" + str(x) + "_" + str(y)

mode = QUEENS_MODE
encoding = SEQ_ADDER_ENCODING
size = 8
id = 1
constraints = [] 
num_bits_size = 0
num_bits_fields = 0
shiftvarslistmap = {}
shiftvarscounter = 0
logsize = -1 

def add_seq (list, ext):
  global id

  assert list != None
  assert len (list) >= 2
  assert ext >= 0

  print ("(let (?e" + str(id) + " (zero_extend[" + str(ext) + \
         "] " + list[0] + "))")
  last = "?e" + str(id)
  id += 1
  for i in range(1, len(list)):
    print ("(let (?e" + str(id) + " (bvadd " + last + " (zero_extend[" + \
           str(ext) + "] " + list[i] + ")))")
    last = "?e" + str(id)
    id += 1
  return last, ext + 1

def add_par (list, bw):
  global id

  assert list != None
  assert len (list) >= 2
  assert bw > 0

  while len(list) != 1:
    i = 0
    next = []
    while i < len(list):
      if i != len(list) - 1:
        print ("(let (?e" + str(id) + " (bvadd (zero_extend[1] " + \
               list[i] + ") (zero_extend[1] " + list[i + 1] + ")))")
      else:
        print ("(let (?e" + str(id) + " (zero_extend[1] " + list[i] + "))")
      last = "?e" + str(id)
      next.append(last)
      id += 1
      i += 2
    list = next
    bw += 1
  return last, bw 

def or_par (list, bw):
  global id

  assert list != None
  assert len (list) >= 2
  assert bw > 0

  while len(list) != 1:
    i = 0
    next = []
    while i < len(list):
      if i != len(list) - 1:
        print ("(let (?e" + str(id) + " (bvor " + list[i] + " " + list[i + 1] + \
               "))")
      else:
        print ("(let (?e" + str(id) + " (bvor " + list[i] + " " + \
               "bv0[" + str(bw) + "]))")
      last = "?e" + str(id)
      next.append(last)
      id += 1
      i += 2
    list = next
  return last 

def and_par (list, bw):
  global id

  assert list != None
  assert len (list) >= 2
  assert bw > 0

  bits = ""
  for i in range(bw):
    bits += "1"
  while len(list) != 1:
    i = 0
    next = []
    while i < len(list):
      if i != len(list) - 1:
        print ("(let (?e" + str(id) + " (bvand " + list[i] + " " + \
               list[i + 1] + "))")
      else:
        print ("(let (?e" + str(id) + " (bvand " + list[i] + " " + \
               "bv" + str(int(bits, 2)) + "[" + str(bw) + "]))")
      last = "?e" + str(id)
      next.append(last)
      id += 1
      i += 2
    list = next
  return last 

def add_lookup_8_4 (list):
  global id
  global lookup

  assert list != None
  assert len(list) != 1

  addlist = []
  numloops = len(list) / 8 
  if (len(list) % 8) > 0:
    numloops += 1
  for i in range(numloops):
    concatlist = []
    for j in range(8):
      if i * 8 + j < len(list):
        concatlist.append (list[i * 8 + j])
      else:
        concatlist.append ("bv0[1]")
    last = concat_list (concatlist)
    print ("(let (?e" + str(id) + " (select " + lookup + " " + last + "))")
    last = "?e" + str(id)
    id += 1
    addlist.append (last)
  assert len(addlist) > 0
  if len(addlist) == 1:
    return addlist[0], 4
  else:
    return add_par (addlist, 4)

def ite_encode_eq_rec (list, pos, k):
  assert list != None
  assert pos >= 0

  if pos == len(list): 
    if k == 0:
      return "true"
    return "false"
  if len(list) - pos < k or k < 0:
    return "false"
  result = "(if_then_else (= " + list[pos] + " bv1[1]) "
  result += ite_encode_eq_rec (list, pos + 1, k - 1) + " "
  result += ite_encode_eq_rec (list, pos + 1, k) + ")"
  return result

def ite_encode_eq (list, k):
  global id

  assert list != None
  assert len(list) >= 2
  assert k > 0
  result = ite_encode_eq_rec (list, 0, k)
  sys.stdout.write("(flet ($e" + str(id) + " " + result +")\n")

def ite_encode_lt_rec (list, pos, counter, k):
  assert list != None
  assert pos >= 0
  assert counter >= 0

  if len(list) - pos + counter < k:
    return "true"
  if counter >= k:
    return "false"
  result = "(if_then_else (= " + list[pos] + " bv1[1]) "
  result += ite_encode_lt_rec (list, pos + 1, counter + 1, k) + " "
  result += ite_encode_lt_rec (list, pos + 1, counter, k) + ")"
  return result

def ite_encode_lt (list, k):
  global id

  assert list != None
  assert len(list) >= 2
  assert k > 0
  result = ite_encode_lt_rec (list, 0, 0, k)
  sys.stdout.write("(flet ($e" + str(id) + " " + result +")\n")

def ite_encode_ge (list, k):
  global id

  assert list != None
  assert len(list) >= 2
  assert k > 0
  result = ite_encode_lt_rec (list, 0, 0, k)
  sys.stdout.write("(flet ($e" + str(id) + " (not " + result +"))\n")

def concat_list (list):
  global id

  assert list != None
  assert len(list) >= 2

  while len(list) != 1:
    i = 0
    next = []
    while i < len(list):
      if i != len(list) - 1:
        print ("(let (?e" + str(id) + " (concat " + list[i] + " " + \
               list[i + 1] + "))")
      else:
        next.pop()
        print ("(let (?e" + str(id) + " (concat " + last + " " + list[i] + "))")
      last = "?e" + str(id)
      next.append(last)
      id += 1
      i += 2
    list = next
  return last 

def shift_encode_eq_1 (list, shiftvarlist):
  global id
  global logsize

  assert list != None
  assert len(list) >= 2
  assert shiftvarlist != None
  assert len(shiftvarlist) >= 1
  
  listlen = len(list)
  print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
         "(zero_extend[" + str(listlen - logsize) + "] " + \
         shiftvarlist.pop() + ")))")
  last = "?e" + str(id)
  id += 1
  vec = concat_list (list)
  print ("(flet ($e" + str(id) + " (= " + last + " " + vec + "))")

def shift_encode_eq_2 (list, shiftvarlist):
  global id
  global logsize

  assert list != None
  assert len(list) >= 2
  assert shiftvarlist != None
  assert len(shiftvarlist) >= 1
  
  listlen = len(list)
  print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
         "(zero_extend[" + str(listlen - logsize) + "] " + \
         shiftvarlist.pop() + ")))")
  shift1 = "?e" + str(id)
  id += 1
  print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
         "(zero_extend[" + str(listlen - logsize) + "] " + \
         shiftvarlist.pop() + ")))")
  shift2 = "?e" + str(id)
  id += 1
  print ("(let (?e" + str(id) + " (bvor " + shift1 + " " + shift2 + "))")
  orshift = "?e" + str(id)
  id += 1
  vec = concat_list (list)
  print ("(flet ($e" + str(id) + " (= " + orshift + " " + vec + "))")
  and1 = "$e" + str(id)
  id += 1
  print ("(flet ($e" + str(id) + " (not (= " + shift1 + " " + shift2 + ")))")
  and2 = "$e" + str(id)
  id += 1
  print ("(flet ($e" + str(id) + " (and " + and1 + " " + and2 + "))")

def shift_encode_eq_k (list, shiftvarlist, k):
  global id

  assert list != None
  assert len(list) >= 2
  assert shiftvarlist != None
  assert k > 2
  assert len(shiftvarlist) >= k

  listlen = len(list)
  log2listlen = log2(listlen)
  orlist = []
  for i in range (k):
    print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
           "(zero_extend[" + str(listlen - log2listlen) + "] " + \
           shiftvarlist.pop() + ")))")
    last = "?e" + str(id)
    id += 1
    orlist.append (last)
  orshift = or_par (orlist, listlen)
  vec = concat_list (list)
  print ("(flet ($e" + str(id) + " (= " + orshift + " " + vec + "))")
  and1 = "$e" + str(id)
  id += 1
  print ("(flet ($e" + str(id) + " (distinct")
  for i in range(len(orlist)):
    print (orlist[i])
  print ("))")
  and2 = "$e" + str(id)
  id += 1
  print ("(flet ($e" + str(id) + " (and " + and1 + " " + and2 + "))")

def shift_encode_gt_k (list, shiftvarlist, shiftvarlistone, k):
  global id

  assert list != None
  assert len(list) >= 2
  assert shiftvarlist != None
  assert shiftvarlistone != None
  assert len(shiftvarlistone) > 0
  assert k > 2
  assert len(shiftvarlist) >= len(list) - k - 1 - 1

  listlen = len(list)
  log2listlen = log2(listlen)
  andlist = []
  bits = "10"
  for i in range(2, listlen):
    bits += "1"

  print ("(let (?e" + str(id) + " (concat " + shiftvarlistone.pop() + " bv" + \
         str(2 ** (listlen - 2)) + "[" + str(listlen - 1) + "]))")
  last = "?e" + str(id)
  id += 1
  andlist.append (last)

  for i in range (1, len(list) - k - 1):
    print ("(let (?e" + str(id) + " (bvashr bv" + str(int(bits, 2)) + "[" + \
           str(listlen) + "] " + shiftvarlist.pop() + "))")
    last = "?e" + str(id)
    id += 1
    andlist.append (last)
  andshift = and_par (andlist, listlen)
  vec = concat_list (list)
  print ("(flet ($e" + str(id) + " (= " + andshift + " " + vec + "))")

def shift_encode_le_1 (list, shiftvarlist):
  global id

  assert list != None
  assert len(list) >= 2
  assert shiftvarlist != None
  assert len(shiftvarlist) >= 1

  listlen = len(list)
  print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
         shiftvarlist.pop() + "))")
  last = "?e" + str(id)
  id += 1
  vec = concat_list (list)
  print ("(flet ($e" + str(id) + " (= " + last + " " + vec + "))")

def shift_encode_le_2 (list, shiftvarlist):
  global id

  assert list != None
  assert len(list) >= 2
  assert shiftvarlist != None
  assert len(shiftvarlist) >= 1
  
  listlen = len(list)
  print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
         shiftvarlist.pop() + "))")
  shift1 = "?e" + str(id)
  id += 1
  print ("(let (?e" + str(id) + " (bvshl bv1[" + str(listlen) + "] " + \
         shiftvarlist.pop() + "))")
  shift2 = "?e" + str(id)
  id += 1
  print ("(let (?e" + str(id) + " (bvor " + shift1 + " " + shift2 + "))" )
  orshift = "?e" + str(id)
  id += 1
  vec = concat_list (list)
  print ("(flet ($e" + str(id) + " (= " + orshift + " " + vec + "))")
  and1 = "$e" + str(id)
  id += 1
  print ("(flet ($e" + str(id) + " (not (= " + shift1 + " " + shift2 + ")))")
  and2 = "$e" + str(id)
  id += 1
  print ("(flet ($e" + str(id) + " (and " + and1 + " " + and2 + "))")


try:
  opts, args = getopt.getopt(sys.argv[1:], "hm:s:e:")
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
  elif o in ("-e"):
    if a == "0":
      encoding = SEQ_ADDER_ENCODING
    elif a == "1":
      encoding = PAR_ADDER_ENCODING
    elif a == "2":
      encoding = ITE_ENCODING
    elif a == "3":
      encoding = LOOKUP_ENCODING
    elif a == "4":
      encoding = SHIFTER_ENCODING
    else:
      die ("encoding must be >= 0 and <= 4")
  elif o in ("-s"):
    size = int (a)
    if size < 4:
      die ("size must be >= 4")

if encoding == SHIFTER_ENCODING:  
  if not is_power_of_2 (size):
    die ("shifter encoding needs that the board size is a power of two")
  logsize = log2(size)

sizesqr = size * size
num_bits_size = log2 (next_power_of_2 (size + 1))
num_bits_fields = log2 (next_power_of_2 (sizesqr + 1))

if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
   mode == NO_THREE_IN_LINE_MODE_GT2N:
  print ("(benchmark queensNoThreeInLine" + str(size) + "x" + str(size) )
else:
  print ("(benchmark queens" + str(size) + "x" + str(size))
print (":source {")
if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
   mode == NO_THREE_IN_LINE_MODE_GT2N:
  print ("BV encoding of no three-in-line problem")
else:
  print ("BV encoding of n-queens problem")
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
if encoding == SEQ_ADDER_ENCODING:
  print ("Cardinality constraints are encoded by simple adder circuits")
elif encoding == PAR_ADDER_ENCODING:
  print ("Cardinality constraints are encoded by parallel adder circuits")
elif encoding == ITE_ENCODING:
  print ("Cardinality constraints are encoded by ITEs")
elif encoding == SHIFTER_ENCODING:
  print ("Cardinality constraints are encoded by shifters")
else:
  assert encoding == LOOKUP_ENCODING
  print ("Cardinality constraints are encoded by lookups and parallel adders")
print ("Contributed by Robert Brummayer (robert.brummayer@gmail.com)")
print ("}")
if mode == QUEENS_MODE:
  print (":status sat")
elif mode == NO_THREE_IN_LINE_MODE:
  print (":status unknown")
else:
  print (":status unsat")
if encoding == LOOKUP_ENCODING:
  print (":logic QF_AUFBV")
  print (":extrafuns ((lookup Array[8:4]))")
else:
  print (":logic QF_BV")
for i in range(size):
  for j in range(size):
    print (":extrafuns ((" + board_field(i, j) + " BitVec[1]))")

#generate additional variables for shifters
if encoding == SHIFTER_ENCODING:
  varlist = [] 
  assert is_power_of_2 (size)
  if mode == QUEENS_MODE or mode == QUEENS_MODE_NP1 or \
     mode == QUEENS_MODE_GTN:
    #generate variables for rows and cols
    for i in range(2 * size):
      var = "v" + str(shiftvarscounter)
      print (":extrafuns ((" + var + " BitVec[" + str(logsize) + "]))")
      shiftvarscounter += 1
      varlist.append(var)
    shiftvarslistmap[str(logsize)] = varlist

    for i in range (2, size + 1):
      istring = str(i)
      if shiftvarslistmap.has_key (istring):
        varlist = shiftvarslistmap[istring]
      else:
        varlist = []
      if i == size:
        limit = 2
      else:
        limit = 4
      for j in range(limit):
        var = "v" + str(shiftvarscounter)
        print (":extrafuns ((" + var + " BitVec[" + istring + "]))")
        shiftvarscounter += 1
        varlist.append(var)
      shiftvarslistmap[istring] = varlist

    if mode == QUEENS_MODE_NP1:
      log2sizesqr = log2 (sizesqr)
      if shiftvarslistmap.has_key (str(log2sizesqr)):
        varlist = shiftvarslistmap[str(log2sizesqr)]
      else:
        varlist = []
      for i in range(size + 1):
        var = "v" + str(shiftvarscounter)
        print (":extrafuns ((" + var + " BitVec[" + str(log2sizesqr) + "]))")
        shiftvarscounter += 1
        varlist.append(var)
      shiftvarslistmap[str(log2sizesqr)] = varlist
    elif mode == QUEENS_MODE_GTN:
      if shiftvarslistmap.has_key ("1"):
        varlist = shiftvarslistmap["1"]
      else:
        varlist = []
      var = "v" + str(shiftvarscounter)
      print (":extrafuns ((" + var + " BitVec[1]))")
      shiftvarscounter += 1
      varlist.append(var)
      shiftvarslistmap["1"] = varlist

      if shiftvarslistmap.has_key (str(sizesqr)):
        varlist = shiftvarslistmap[str(sizesqr)]
      else:
        varlist = []
      for i in range(1, sizesqr - size - 1):
        var = "v" + str(shiftvarscounter)
        print (":extrafuns ((" + var + " BitVec[" + str(sizesqr) + "]))")
        shiftvarscounter += 1
        varlist.append(var)
      shiftvarslistmap[str(sizesqr)] = varlist
  else:
    assert mode == NO_THREE_IN_LINE_MODE or \
           mode == NO_THREE_IN_LINE_MODE_2NP1 or \
           mode == NO_THREE_IN_LINE_MODE_GT2N
    #generate variables for rows and cols
    for i in range(4 * size):
      var = "v" + str(shiftvarscounter)
      print (":extrafuns ((" + var + " BitVec[" + str(logsize) + "]))")
      shiftvarscounter += 1
      varlist.append(var)
    shiftvarslistmap[str(logsize)] = varlist

    for i in range (3, size + 1):
      istring = str(i)
      if shiftvarslistmap.has_key (istring):
        varlist = shiftvarslistmap[istring]
      else:
        varlist = []
      if i == size:
        limit = 4
      else:
        limit = 8
      for j in range(limit):
        var = "v" + str(shiftvarscounter)
        print (":extrafuns ((" + var + " BitVec[" + istring + "]))")
        shiftvarscounter += 1
        varlist.append(var)
      shiftvarslistmap[istring] = varlist

    if mode == NO_THREE_IN_LINE_MODE_2NP1:
      log2sizesqr = log2 (sizesqr)
      if shiftvarslistmap.has_key (str(log2sizesqr)):
        varlist = shiftvarslistmap[str(log2sizesqr)]
      else:
        varlist = []
      for i in range(2 * size + 1):
        var = "v" + str(shiftvarscounter)
        print (":extrafuns ((" + var + " BitVec[" + str(log2sizesqr) + "]))")
        shiftvarscounter += 1
        varlist.append(var)
      shiftvarslistmap[str(log2sizesqr)] = varlist
    elif mode == NO_THREE_IN_LINE_MODE_GT2N:
      if shiftvarslistmap.has_key ("1"):
        varlist = shiftvarslistmap["1"]
      else:
        varlist = []
      var = "v" + str(shiftvarscounter)
      print (":extrafuns ((" + var + " BitVec[1]))")
      shiftvarscounter += 1
      varlist.append(var)
      shiftvarslistmap["1"] = varlist

      if shiftvarslistmap.has_key (str(sizesqr)):
        varlist = shiftvarslistmap[str(sizesqr)]
      else:
        varlist = []
      for i in range(1, sizesqr - 2 * size - 1):
        var = "v" + str(shiftvarscounter)
        print (":extrafuns ((" + var + " BitVec[" + str(sizesqr) + "]))")
        shiftvarscounter += 1
        varlist.append(var)
      shiftvarslistmap[str(sizesqr)] = varlist


print (":formula")

#generate lookup table
if encoding == LOOKUP_ENCODING:
  last = "lookup"
  for i in range(2):
    for j in range(2):
      for k in range(2):
        for l in range(2):
          for m in range(2):
            for n in range(2):
              for o in range(2):
                for p in range(2):
                  index = str(i) + str(j) + str(k) + str(l) + str(m) + \
                          str(n) + str(o) + str(p)
                  sum = 0
                  for bit in index:
                    if bit == '1':
                      sum += 1
                  print ("(let (?e" + str(id) + " (store " + last + " bv" + \
                         str(int(index, 2)) + "[8]" + " bv" + str(sum) + \
                         "[4]))")
                  last = "?e" + str(id)
                  id += 1
  lookup = last

# generate row constraints 
for i in range(size):
  list = []
  for j in range(size):
    list.append(board_field(i, j)) 
  if encoding == ITE_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      ite_encode_eq (list, 2);
    else:
      ite_encode_eq (list, 1);
  elif encoding == SHIFTER_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      shift_encode_eq_2 (list, shiftvarslistmap[str(logsize)]);
    else:
      shift_encode_eq_1 (list, shiftvarslistmap[str(logsize)]);
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_size - 1) 
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else: 
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1) 
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      print ("(flet ($e" + str(id) + " (= " + last + " bv2[" + \
             str(bw_adder) + "]))")
    else:
      print ("(flet ($e" + str(id) + " (= " + last + " bv1[" + \
             str(bw_adder) + "]))")
  constraints.append ("$e" + str(id))
  id += 1

# generate col constraints 
for i in range(size):
  list = []
  for j in range(size):
    list.append(board_field(j, i))
  if encoding == ITE_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      ite_encode_eq (list, 2)
    else:
      ite_encode_eq (list, 1)
  elif encoding == SHIFTER_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      shift_encode_eq_2 (list, shiftvarslistmap[str(logsize)]);
    else:
      shift_encode_eq_1 (list, shiftvarslistmap[str(logsize)]);
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_size - 1) 
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else:
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1) 
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      print ("(flet ($e" + str(id) + " (= " + last + " bv2[" + \
             str(bw_adder) + "]))")
    else:
      print ("(flet ($e" + str(id) + " (= " + last + " bv1[" + \
             str(bw_adder) + "]))")
  constraints.append ("$e" + str(id))
  id += 1

#generate diagonal constraints
for i in range(1, size):
  list = []
  list.append (board_field(i, 0))
  row = i - 1
  col = 1
  assert row >= 0 and col < size 
  while row >= 0 and col < size:
    list.append(board_field(row, col))
    row -= 1
    col += 1
  if (mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
      mode == NO_THREE_IN_LINE_MODE_GT2N) and len(list) < 3:
    continue
  if encoding == ITE_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      ite_encode_lt (list, 3)
    else:
      ite_encode_lt (list, 2)
  elif encoding == SHIFTER_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      shift_encode_le_2 (list, shiftvarslistmap[str(len(list))])
    else:
      shift_encode_le_1 (list, shiftvarslistmap[str(len(list))])
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_size - 1)
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else:
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1)
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      print ("(flet ($e" + str(id) + " (bvult " + last + " bv3[" + \
             str(bw_adder) + "]))")
    else:
      print ("(flet ($e" + str(id) + " (bvule " + last + " bv1[" + \
             str(bw_adder) + "]))")
  constraints.append ("$e" + str(id))
  id += 1

for i in range(1, size - 1):
  list = []
  list.append(board_field(size - 1, i))
  row = size - 1 - 1
  col = i + 1
  assert row >= 0 and col < size 
  while row >= 0 and col < size: 
    list.append(board_field(row, col))
    row -= 1
    col += 1
  if (mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
      mode == NO_THREE_IN_LINE_MODE_GT2N) and len(list) < 3:
    continue
  if encoding == ITE_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      ite_encode_lt (list, 3)
    else:
      ite_encode_lt (list, 2)
  elif encoding == SHIFTER_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      shift_encode_le_2 (list, shiftvarslistmap[str(len(list))])
    else:
      shift_encode_le_1 (list, shiftvarslistmap[str(len(list))])
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_size - 1)
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else:
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1)
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      print ("(flet ($e" + str(id) + " (bvult " + last + " bv3[" + \
             str(bw_adder) + "]))")
    else:
      print ("(flet ($e" + str(id) + " (bvule " + last + " bv1[" + \
             str(bw_adder) + "]))")
  constraints.append ("$e" + str(id))
  id += 1

for i in range(1, size):
  list = []
  list.append (board_field(i, size - 1))
  row = i - 1
  col = size - 1 - 1
  assert row >= 0 and col >= 0 
  while row >= 0 and col >= 0:
    list.append (board_field(row, col))
    row -= 1
    col -= 1
  if (mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
      mode == NO_THREE_IN_LINE_MODE_GT2N) and len(list) < 3:
    continue
  if encoding == ITE_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      ite_encode_lt (list, 3)
    else:
      ite_encode_lt (list, 2)
  elif encoding == SHIFTER_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      shift_encode_le_2 (list, shiftvarslistmap[str(len(list))])
    else:
      shift_encode_le_1 (list, shiftvarslistmap[str(len(list))])
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_size - 1)
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else:
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1)
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      print ("(flet ($e" + str(id) + " (bvult " + last + " bv3[" + \
             str(bw_adder) + "]))")
    else:
      print ("(flet ($e" + str(id) + " (bvule " + last + " bv1[" + \
             str(bw_adder) + "]))")
  constraints.append ("$e" + str(id))
  id += 1

for i in range(1, size - 1):
  list = []
  list.append (board_field(size - 1, size - 1 - i))
  row = size - 1 - 1
  col = size - 1 - i - 1 
  assert row >= 0 and col >= 0 
  while row >= 0 and col >= 0: 
    list.append (board_field(row, col))
    row -= 1
    col -= 1
  if (mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
      mode == NO_THREE_IN_LINE_MODE_GT2N) and len(list) < 3:
    continue
  if encoding == ITE_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      ite_encode_lt (list, 3)
    else:
      ite_encode_lt (list, 2)
  elif encoding == SHIFTER_ENCODING:
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      shift_encode_le_2 (list, shiftvarslistmap[str(len(list))])
    else:
      shift_encode_le_1 (list, shiftvarslistmap[str(len(list))])
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_size - 1)
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else:
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1)
    if mode == NO_THREE_IN_LINE_MODE or mode == NO_THREE_IN_LINE_MODE_2NP1 or \
       mode == NO_THREE_IN_LINE_MODE_GT2N:
      print ("(flet ($e" + str(id) + " (bvult " + last + " bv3[" + \
             str(bw_adder) + "]))")
    else:
      print ("(flet ($e" + str(id) + " (bvule " + last + " bv1[" + \
             str(bw_adder) + "]))")
  constraints.append ("$e" + str(id))
  id += 1

# generate additional constraints
if mode == QUEENS_MODE_NP1 or mode == QUEENS_MODE_GTN or \
   mode ==  NO_THREE_IN_LINE_MODE_2NP1 or mode == NO_THREE_IN_LINE_MODE_GT2N:
  list = []
  for i in range(size):
    for j in range(size):
      list.append (board_field(i, j))
  if encoding == ITE_ENCODING:
    if mode == QUEENS_MODE_NP1:
      ite_encode_eq (list, size + 1)
    elif mode == QUEENS_MODE_GTN:
      ite_encode_ge (list, size + 1)
    elif mode == NO_THREE_IN_LINE_MODE_2NP1:
      ite_encode_eq (list, 2 * size + 1)
    else:
      ite_encode_ge (list, 2 * size + 1)
      assert mode == NO_THREE_IN_LINE_MODE_GT2N
  elif encoding == SHIFTER_ENCODING:
    if mode == QUEENS_MODE_NP1:
      shift_encode_eq_k (list, shiftvarslistmap[str(log2(sizesqr))], size + 1)
    elif mode == QUEENS_MODE_GTN:
      shift_encode_gt_k (list, shiftvarslistmap[str(sizesqr)], \
                         shiftvarslistmap["1"], size)
    elif mode == NO_THREE_IN_LINE_MODE_2NP1:
      shift_encode_eq_k (list, shiftvarslistmap[str(log2(sizesqr))], \
                         2 *size + 1)
    else:
      assert mode == NO_THREE_IN_LINE_MODE_GT2N
      shift_encode_gt_k (list, shiftvarslistmap[str(sizesqr)], \
                         shiftvarslistmap["1"], 2 * size)
  else:
    if encoding == SEQ_ADDER_ENCODING:
      last, bw_adder = add_seq (list, num_bits_fields - 1)
    elif encoding == LOOKUP_ENCODING:
      last, bw_adder = add_lookup_8_4 (list)
    else:
      assert encoding == PAR_ADDER_ENCODING
      last, bw_adder = add_par (list, 1)
    if mode == QUEENS_MODE_NP1:
      print ("(flet ($e" + str(id) + " (= " + last + " bv" + str(size + 1) + \
              "[" + str(bw_adder) + "]))")
    elif mode == QUEENS_MODE_GTN:
      print ("(flet ($e" + str(id) + " (bvugt " + last + " bv" + str(size) + \
              "[" + str(bw_adder) + "]))")
    elif mode == NO_THREE_IN_LINE_MODE_2NP1:
      print ("(flet ($e" + str(id) + " (= " + last + " bv" + \
             str(2 * size + 1) + "[" + str(bw_adder) + "]))")
    else:
      assert mode == NO_THREE_IN_LINE_MODE_GT2N
      print ("(flet ($e" + str(id) + " (bvugt " + last + " bv" + \
             str(2 * size) + "[" + str(bw_adder) + "]))")
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

if encoding == SHIFTER_ENCODING:
  assert shiftvarslistmap != None
  for list in shiftvarslistmap.values(): 
    assert len(list) == 0
