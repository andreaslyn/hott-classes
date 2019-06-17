
if [ -z "$1" ]; then
  echo Missing HoTT dir >&2
  exit 1
fi

make COQC="$1"/hoqc COQTOP="$1"/hoqtop COQDEP="$1"/hoqdep
