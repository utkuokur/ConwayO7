#!/bin/bash
# Rebuild the coverage formula: one clause per cube of ../cubes_all.txt, each the
# negation of the cube. Its unsatisfiability says: every valuation of the split
# variables satisfies some cube — i.e., the 98,536 cells cover the whole space.
HERE="$(cd "$(dirname "$0")" && pwd)"
awk '{n=NF; line=""; for(i=1;i<=NF;i++){line=line (-$i) " "}; print line "0"}' "$HERE/../cubes_all.txt" > /tmp/cover_body
vars=$(tr ' ' '\n' < "$HERE/../cubes_all.txt" | tr -d '-' | sort -n | tail -1)
{ echo "p cnf $vars $(wc -l < /tmp/cover_body)"; cat /tmp/cover_body; } 
rm -f /tmp/cover_body
