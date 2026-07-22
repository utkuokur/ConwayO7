#!/bin/bash
# Verify ONE certificate end to end. Usage: ./check_one.sh <index>   (default 0)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
i="${1:-0}"
CAKE="${CAKE:-apptainer exec $HERE/cake_lpr.sif cake_lpr}"
read _ _ V C0 < <(head -1 "$HERE/o7.cnf")
cube=$(sed -n "$((i+1))p" "$HERE/cubes_all.txt"); n=$(echo $cube | wc -w)
{ echo "p cnf $V $((C0+n))"; tail -n +2 "$HERE/o7.cnf"; for l in $cube; do echo "$l 0"; done; } > /tmp/F_one.cnf
zstd -dqf "$HERE/proofs/$i.lrat.zst" -o /tmp/one.lrat
echo "cube $i fixes $n variables: $cube"
$CAKE /tmp/F_one.cnf /tmp/one.lrat
rm -f /tmp/F_one.cnf /tmp/one.lrat
