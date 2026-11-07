#!/bin/sh
# Writes the inputs of SEC-06 of the security audit of 2026-11-07 to the
# directory given (default: the current directory):
#   p<N>.hpeg   a grammar with N nested groups: %module M / S <- ((...'a'...))
#   dj<N>.json  an analyze request of the wasm whose grammar is N nested arrays
# Time them with, for example, `time peg-hs gen p4000.hpeg -o P.hs`.
set -eu
out=${1:-.}
mkdir -p "$out"
for n in 1000 2000 4000 8000; do
  awk -v n="$n" 'BEGIN {
    printf "%%module M\nS <- "
    for (i = 0; i < n; i++) printf "("
    printf "%c%s%c", 39, "a", 39
    for (i = 0; i < n; i++) printf ")"
    printf "\n"
  }' > "$out/p$n.hpeg"
done
for n in 10000 100000 1000000; do
  awk -v n="$n" 'BEGIN {
    printf "{\"grammar\":"
    for (i = 0; i < n; i++) printf "["
    for (i = 0; i < n; i++) printf "]"
    printf "}"
  }' > "$out/dj$n.json"
done
