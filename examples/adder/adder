#!/usr/bin/env python2
import sys, getopt

def usage():
  print "usage: adder [-h] [-n <n>]"
  sys.exit(0)

def die(msg):
  assert msg != None
  print msg
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

n = 32 
id = 1

def add_seq (list, ext):
  global id

  assert list != None
  assert len (list) >= 2
  assert ext >= 0

  print "(let (?e" + str(id) + " (zero_extend[" + str(ext) + \
        "] " + list[0] + "))"
  last = "?e" + str(id)
  id += 1
  for i in range(1, len(list)):
    print "(let (?e" + str(id) + " (bvadd " + last + " (zero_extend[" + \
          str(ext) + "] " + list[i] + ")))"
    last = "?e" + str(id)
    id += 1
  return last, ext + 1

def add_par (list):
  global id
  bw = 1

  assert list != None
  assert len (list) >= 2

  while len(list) != 1:
    i = 0
    next = []
    while i < len(list):
      if i != len(list) - 1:
        print "(let (?e" + str(id) + " (bvadd (zero_extend[1] " + \
              list[i] + ") (zero_extend[1] " + list[i + 1] + ")))"
      else:
        print "(let (?e" + str(id) + " (zero_extend[1] " + list[i] + "))" 
      last = "?e" + str(id)
      next.append(last)
      id += 1
      i += 2
    list = next
    bw += 1
  return last, bw 

try:
  opts, args = getopt.getopt(sys.argv[1:], "hn:")
except getopt.GetoptError, err:
  print str(err)
  usage()

for o, a in opts:
  if o in ("-h"):
    usage()
  elif o in ("-n"):
    n = int (a)
    if n < 2:
      die ("n must be >= 2")

num_bits_n = log2 (next_power_of_2 (n + 1))

print "(benchmark adderEqCheck" + str(n) 
print ":source {"
print "Equivalence checking of adder circuits on " + str(n) + " inputs of BW 1"
print "We verifiy the equivalence of tree-like and linear circuit layout"
print "Contributed by Robert Brummayer (robert.brummayer@gmail.com)"
print "}"
print ":status unsat"
print ":logic QF_BV"
list = []
for i in range(n):
  print ":extrafuns ((v" + str(i) + " BitVec[1]))"
  list.append("v" + str(i))
print ":formula"
result_simple, bw_simple = add_seq (list, num_bits_n - 1)
result_par, bw_par = add_par (list)
if bw_par < bw_simple:
  ext = bw_simple - bw_par
  print "(not (= " + result_simple + " (zero_extend[" + str(ext) + "] " + \
        result_par + ")))"
elif bw_par > bw_simple:
  ext = bw_par - bw_simple 
  print "(not (= (zero_extend[" + str(ext) + "] " + result_simple + ") " + \
        result_par + "))"
else:
  print "(not (= " + result_simple + " " + result_par + "))"
pars = ""
for i in range(id):
  pars = pars + ")"
print pars
