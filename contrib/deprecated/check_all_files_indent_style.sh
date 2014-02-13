#!/bin/bash
for i in *.h *.c */*.c */*.h */*/*.c */*/*.h
do
  cnt=$(./contrib/check_indent_style.sh $i | egrep "[0-9]:" -c)
  if [[ $cnt > 0 ]]; then
    echo "$i ($cnt)"
  fi
done

