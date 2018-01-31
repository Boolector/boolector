#!/bin/sh

path=../../bin

btormc=$path/btormc
btorsim=$path/btorsim

set -x

 $btormc    -kmax 20  count2.btor                  > count2.witnessmc
 $btormc    -kmax 20  count4.btor                  > count4.witnessmc
 $btormc    -kmax 20  factorial4even.btor          > factorial4even.witnessmc
 $btormc    -kmax 20  noninitstate.btor            > noninitstate.witnessmc
 $btormc    -kmax 20  recount4.btor                > recount4.witnessmc
 $btormc    -kmax 20  twocount2.btor               > twocount2.witnessmc
 $btormc    -kmax 20  twocount2c.btor              > twocount2c.witnessmc
 $btormc    -kmax 20  twocount32.btor              > twocount32.witnessmc
#$btormc    -kmax 231 ponylink-slaveTXlen-sat.btor > ponylink-slaveTXlen.witnessmc
           
 $btorsim -b 0 -r 20  count2.btor                  > count2.witnesssim
 $btorsim -b 0 -r 20  count4.btor                  > count4.witnesssim
 $btorsim -b 0 -r 20  factorial4even.btor          > factorial4even.witnesssim
 $btorsim -b 0 -r 20  noninitstate.btor            > noninitstate.witnesssim
 $btorsim -b 0 -r 20  recount4.btor                > recount4.witnesssim
 $btorsim -b 0 -r 20  twocount2.btor               > twocount2.witnesssim
 $btorsim -b 0 -r 20  twocount2c.btor              > twocount2c.witnesssim
 $btorsim -b 0 -r 20  twocount32.btor              > twocount32.witnesssim
#$btorsim -b 0 -r 231 ponylink-slaveTXlen-sat.btor > ponylink-slaveTXlen.witnesssim
           
 $btorsim      -c     count2.btor                    count2.witnesssim
 $btorsim      -c     count4.btor                    count4.witnesssim
 $btorsim      -c     factorial4even.btor            factorial4even.witnesssim
 $btorsim      -c     noninitstate.btor              noninitstate.witnesssim
 $btorsim      -c     recount4.btor                  recount4.witnesssim
 $btorsim      -c     twocount2.btor                 twocount2.witnesssim
 $btorsim      -c     twocount2c.btor                twocount2c.witnesssim
 $btorsim      -c     twocount32.btor                twocount32.witnesssim
#$btorsim      -c     ponylink-slaveTXlen-sat.btor   ponylink-slaveTXlen.witnesssim
           
 $btorsim      -c     count2.btor                    count2.witnesssim
 $btorsim      -c     count4.btor                    count4.witnesssim
 $btorsim      -c     factorial4even.btor            factorial4even.witnesssim
 $btorsim      -c     noninitstate.btor              noninitstate.witnesssim
 $btorsim      -c     recount4.btor                  recount4.witnesssim
 $btorsim      -c     twocount2.btor                 twocount2.witnesssim
 $btorsim      -c     twocount2c.btor                twocount2c.witnesssim
 $btorsim      -c     twocount32.btor                twocount32.witnesssim
#$btorsim             ponylink-slaveTXlen-sat.btor   ponylink-slaveTXlen.witnesssim
