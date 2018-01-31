#!/bin/sh

path=../../bin

btormc=$path/btormc
btorsim=$path/btorsim

set -x

 $btormc  -kmax 20  count2.btor                  > count2.witnessmc
 $btormc  -kmax 20  count4.btor                  > count4.witnessmc
 $btormc  -kmax 20  factorial4even.btor          > factorial4even.witnessmc
 $btormc  -kmax 20  noninitstate.btor            > noninitstate.witnessmc
 $btormc  -kmax 20  recount4.btor                > recount4.witnessmc
 $btormc  -kmax 20  twocount2.btor               > twocount2.witnessmc
 $btormc  -kmax 20  twocount2c.btor              > twocount2c.witnessmc
 $btormc  -kmax 20  twocount32.btor              > twocount32.witnessmc
#$btormc -kmax 231 ponylink-slaveTXlen-sat.btor > ponylink-slaveTXlen.witnessmc

 $btorsim    -r 20  count2.btor                  > count2.witnesssim
 $btorsim    -r 20  count4.btor                  > count4.witnesssim
 $btorsim    -r 20  factorial4even.btor          > factorial4even.witnesssim
 $btorsim    -r 20  noninitstate.btor            > noninitstate.witnesssim
 $btorsim    -r 20  recount4.btor                > recount4.witnesssim
 $btorsim    -r 20  twocount2.btor               > twocount2.witnesssim
 $btorsim    -r 20  twocount2c.btor              > twocount2c.witnesssim
 $btorsim    -r 20  twocount32.btor              > twocount32.witnesssim
#btorsim    -r 231 ponylink-slaveTXlen-sat.btor > ponylink-slaveTXlen.witnesssim
