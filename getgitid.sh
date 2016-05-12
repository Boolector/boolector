#!/bin/sh
id=""
if [ -d .git -a -f .git/HEAD ]
then
  head="`awk 'NF == 1' .git/HEAD`"
  if [ x"$head" = x ]
  then
    head="`awk '{print $2}' .git/HEAD`"
    if [ ! x"$head" = x -a -f ".git/$head" ]
    then
      id="`cat .git/$head`"
    fi
  else
    id="$head"
  fi
fi
echo $id
