#!/bin/bash

readonly TMPDIR=/tmp
readonly TMPFILE_NAME="btorvis$$"

readonly tmpfile_pdf="$TMPDIR/$TMPFILE_NAME".pdf
readonly tmpfile_ps="$TMPDIR/$TMPFILE_NAME".ps

inputfile=/dev/stdin
pdfreader=unknown
ps2pdf=unknown
contribdir=$(dirname "$(readlink -f $0)")
btor2dot=$(readlink -f "$contribdir/btor2dot.py")
btor2dotopts=""

trap "rm -f $tmpfile_ps $tmpfile_pdf; exit" SIGHUP SIGINT SIGTERM

function info
{
  echo "*** btorvis: $1"
}

function die
{
  info "$1"
  exit 1
}
       
while [ $# -gt 0 ]
do
  case $1 in
#        --ids)     btor2dot=$(readlink -f "$contribdir/btorids2dot");;
        -h|--help) echo -n "usage: $(basename $0)"
                   echo -e " [ -h | --help | --ids] [<file>]\n"
                   exit 0;;
	-*)        btor2dotopts="$btor2dotopts $1" ;;
        *)         break;;
  esac
  shift
done

if [ $# -gt 1 ]; then
  die "invalid number of arguments: '$#'"
fi

if [ $# -eq 1 ]; then
  inputfile="$*"
  if [ ! -f "$inputfile" ]; then
    die "invalid input file: '$inputfile'"
  fi
fi

if [ ! -f "$btor2dot" ]; then
  die "could not find 'btor2dot'"
fi

for ps2pdf in epstopdf ps2pdf unknown
do
  which "$ps2pdf"
  if [ $? = 0 ]; then
    case $ps2pdf in 
      epstopdf) ps2pdfoutputopt="--outfile=";;
    esac
    break
  fi
done

if [ x"$ps2pdf" = xunknown ]; then
  die "could not find 'ps2pdf' nor 'epstopdf'"
fi

for pdfreader in  "zathura" "acroread" "evince" unknown
do
  which "$pdfreader"
  if [ $? = 0 ]; then
    break
  fi
done

if [ x"$pdfreader" = xunknown ]
then
  die "no pdf reader found"
fi


## run

info "temp file: $tmpfile_pdf"
info "generating dot file"
cat "$inputfile" | "$btor2dot" $btor2dotopts | dot -Tps2 > "$tmpfile_ps"

info "generating pdf file"
"$ps2pdf" "$tmpfile_ps" "${ps2pdfoutputopt}${tmpfile_pdf}"
if [ $? = 1 ]; then
  die "failed to generate pdf file"
fi

"$pdfreader" "$tmpfile_pdf"


## cleanup

rm -f "$tmpfile_ps" "$tmpfile_pdf"
exit 0
