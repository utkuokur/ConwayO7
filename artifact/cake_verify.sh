#!/bin/bash
# cake_lpr (HOL4-verified) verification of the complete certificate.
# Layout: proof i = proofs/<i>.lrat.zst, cube i = line i+1 of cubes_all.txt.
# For each index: (optionally) sha256-pin the proof, rebuild F_i = o7.cnf + cube_i,
# decompress, run cake_lpr. Resumable: OK lines in cake_report.txt are skipped.
# Usage: ./cake_verify.sh [start] [end]   Env: CAKE=checker, P=jobs, TMP=scratch
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
CAKE="${CAKE:-apptainer exec $HERE/cake_lpr.sif cake_lpr}"
P="${P:-$(nproc)}"
TMP="${TMP:-${TMPDIR:-/tmp}}"
START="${1:-0}"; END="${2:-98536}"
REP="$HERE/cake_report.txt"; touch "$REP"
[ -f "$HERE/SHA256SUMS" ] || echo "note: SHA256SUMS absent — hash pinning skipped" >&2
read _ _ V C0 < <(head -1 "$HERE/o7.cnf")
tail -n +2 "$HERE/o7.cnf" > "$TMP/cv_base.cnf"
export HERE CAKE V C0 TMP REP
vone() {
  i="$1"
  grep -q "^OK $i$" "$REP" && return 0
  pf="$HERE/proofs/$i.lrat.zst"
  [ -s "$pf" ] && [ "$(stat -c%s "$pf")" -ge 100 ] || { echo "MISSING $i" >> "$REP"; return 0; }
  if [ -f "$HERE/SHA256SUMS" ]; then
    want=$(grep -F "./proofs/$i.lrat.zst" "$HERE/SHA256SUMS" | awk '{print $1}' | head -1)
    got=$(sha256sum "$pf" | awk '{print $1}')
    [ -n "$want" ] && [ "$want" = "$got" ] || { echo "BADHASH $i" >> "$REP"; return 0; }
  fi
  cube=$(sed -n "$((i+1))p" "$HERE/cubes_all.txt"); n=$(echo $cube | wc -w)
  fi="$TMP/cv_${i}.cnf"; pr="$TMP/cv_${i}.lrat"
  { echo "p cnf $V $((C0+n))"; cat "$TMP/cv_base.cnf"; for l in $cube; do echo "$l 0"; done; } > "$fi"
  zstd -dqf "$pf" -o "$pr"
  if CML_HEAP_SIZE=1400 CML_STACK_SIZE=200 $CAKE "$fi" "$pr" 2>/dev/null \
      | grep -q "s VERIFIED UNSAT"; then
    echo "OK $i" >> "$REP"
  else
    echo "FAIL $i" >> "$REP"
  fi
  rm -f "$fi" "$pr"
}
export -f vone
seq "$START" "$((END-1))" | xargs -P "$P" -I{} bash -c 'vone {}'
ok=$(grep -c "^OK " "$REP")
echo "report: $ok OK of 98536; FAIL=$(grep -c '^FAIL ' "$REP"), MISSING=$(grep -c '^MISSING ' "$REP"), BADHASH=$(grep -c '^BADHASH ' "$REP")"
