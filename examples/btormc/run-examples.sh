#!/bin/sh

dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

btormc=$dir/../../bin/btormc
btorsim=$dir/../../src/btorfmt/bin/btorsim

invalid () {
  echo invalid
}

set -x

 $btormc    -kmax 20  count2.btor2                  > count2.witnessmc
 $btormc    -kmax 20  count4.btor2                  > count4.witnessmc
 $btormc    -kmax 20  factorial4even.btor2          > factorial4even.witnessmc
 $btormc    -kmax 20  noninitstate.btor2            > noninitstate.witnessmc
 $btormc    -kmax 20  recount4.btor2                > recount4.witnessmc
 $btormc    -kmax 20  twocount2.btor2               > twocount2.witnessmc
 $btormc    -kmax 20  twocount2c.btor2              > twocount2c.witnessmc
 $btormc    -kmax 20  twocount32.btor2              > twocount32.witnessmc
           
 $btorsim -b 0 -r 20  count2.btor2                  > count2.witnesssim
 $btorsim -b 0 -r 20  count4.btor2                  > count4.witnesssim
 $btorsim -b 0 -r 20  factorial4even.btor2          > factorial4even.witnesssim
 $btorsim -b 0 -r 20  noninitstate.btor2 -s 1       > noninitstate.witnesssim
 $btorsim -b 0 -r 20  twocount2.btor2               > twocount2.witnesssim
 $btorsim -b 0 -r 20  twocount2c.btor2   -s 11      > twocount2c.witnesssim
 $btorsim -b 0 -r 20  twocount32.btor2              > twocount32.witnesssim

           
 $btorsim      -c     count2.btor2                    count2.witnessmc
 $btorsim      -c     count4.btor2                    count4.witnessmc
 $btorsim      -c     factorial4even.btor2            factorial4even.witnessmc
 $btorsim      -c     noninitstate.btor2              noninitstate.witnessmc
 $btorsim      -c     recount4.btor2                  recount4.witnessmc
 $btorsim      -c     twocount2.btor2                 twocount2.witnessmc
 $btorsim      -c     twocount2c.btor2                twocount2c.witnessmc
 $btorsim      -c     twocount32.btor2                twocount32.witnessmc
           
 $btorsim      -c     count2.btor2                    count2.witnesssim
 $btorsim      -c     count4.btor2                    count4.witnesssim
 $btorsim      -c     factorial4even.btor2            factorial4even.witnesssim
 $btorsim      -c     noninitstate.btor2              noninitstate.witnesssim
 $btorsim      -c     twocount2.btor2                 twocount2.witnesssim
 $btorsim      -c     twocount2c.btor2                twocount2c.witnesssim
 $btorsim      -c     twocount32.btor2                twocount32.witnesssim

 $btorsim -b 0 -r 20  noninitstate.btor2            > noninitstate.nowitnesssim
 $btorsim      -c     noninitstate.btor2              noninitstate.nowitnesssim 2>/dev/null && invalid

 $btorsim -b 0 -r 20  recount4.btor2                > recount4.nowitnesssim
 $btorsim      -c     recount4.btor2                  recount4.witnesssim       2>/dev/null && invalid

 $btorsim -b 0 -r 20  twocount2c.btor2              > twocount2c.witnesssim
 $btorsim      -c     twocount2c.btor2                twocount2c.witnesssim     2>/dev/null && invalid



 $btorsim -b 0 -r 999 ponylink-slaveTXlen-sat.btor2 > ponylink-slaveTXlen.nowitnesssim
 $btorsim      -c     ponylink-slaveTXlen-sat.btor2   ponylink-slaveTXlen.nowitnesssim 2>/dev/null && invalid

 $btormc    -kmax 229 ponylink-slaveTXlen-sat.btor2 > ponylink-slaveTXlen.witnessmc
 $btorsim      -c     ponylink-slaveTXlen-sat.btor2   ponylink-slaveTXlen.witnessmc
