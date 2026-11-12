# Accept Happy 2.1.7 debug records up to a single EOF accept. The synthetic
# error token is permitted only in GHC's "close -> error" layout reduction.
function fail() { print "unexpected Happy record at line " NR ": " $0 > "/dev/stderr"; bad=1; exit 1 }
function listAppend(xs, n) { return xs (xs == "" ? "" : ",") n }
function pushCode(n) { codes = listAppend(codes,n); count++ }
function stackLiteral(    s,i) {
  s=""; for(i=depth;i>0;i--) s=listAppend(s,stack[i]); return "[" s "]"
}
function emitChunk() {
  if(!count) return
  print "def input" part " : List Nat := [" tokens "]"
  print "def stack" (part+1) " : List Symbol := " stackLiteral()
  print "theorem checked" part " : replay productions ⟨stack" part ", input" part "⟩ (([" codes "] : List Nat).map decodeAction) = some ⟨stack" (part+1) ", []⟩ := by rfl"
  part++; codes=""; tokens=""; count=0
}
BEGIN {
  part=0
  print "import GHCGrammar\nimport TraceChunks\nopen PegHs.CFG PegHs.GHCGrammar"
  print "set_option maxRecDepth 16384\nset_option maxHeartbeats 5000000"
  print "def stack0 : List Symbol := []"
}
NR==FNR { lhs[$1]=$2; arity[$1]=$3; next }
function shiftToken(n) { tokens = tokens (tokens == "" ? "" : ",") n; pushCode(0) }
{
  if (accepted) fail()
  if (fixup == 1) {
    if ($0 != "entering `error` fixup.") fail()
    fixup=2; next
  }
  if (fixup == 3) {
    if (!sub(/^shifting the error token/, "")) fail()
  }
  if ($0 !~ /^state: [0-9]+,\ttoken: [0-9]+,\taction: /) fail()
  tok=$4; sub(/,$/,"",tok)
  if (fixup == 2 && !(tok == 0 && $6 == "shift,")) fail()
  if (fixup == 3 && !(tok == saved && $6 == "reduce" && $8 == "835),")) fail()
  if (fixup == 3) fixup=0
  if ($6 == "shift," && NF == 9 && $7 == "enter" && $8 == "state" && $9 ~ /^[0-9]+$/) {
    if (tok == 159 || tok == 1 || (tok == 0 && fixup != 2)) fail()
    stack[++depth]=".terminal " tok; shiftToken(tok); if (fixup == 2) fixup=3
  } else if ($6 == "reduce" && NF == 11 && $7 == "(rule" && $8 ~ /^[0-9]+\),$/ && $9 == "goto" && $10 == "state" && $11 ~ /^[0-9]+$/) {
    rule=$8; sub(/\),$/,"",rule); if (!(rule in arity) || depth < arity[rule]) fail()
    depth-=arity[rule]; stack[++depth]=".nonterminal " lhs[rule]; pushCode(rule+1)
  } else if ($6 == "failing." && NF == 6 && !fixup) {
    saved=tok; fixup=1
  } else if ($6 == "accept." && NF == 6 && tok == 159 && !fixup) {
    accepted=1
  } else fail()
  if(count >= 96) emitChunk()
}
END {
  if (bad || !accepted || fixup) exit 1
  emitChunk()
  print "def rest" part " : List Nat := []"
  print "theorem segment" part " : Segments productions stack" part " rest" part " [.nonterminal moduleStart] := .done _"
  for(i=part-1;i>=0;i--) {
    print "def rest" i " := input" i " ++ rest" (i+1)
    print "theorem segment" i " : Segments productions stack" i " rest" i " [.nonterminal moduleStart] := .next _ checked" i " segment" (i+1)
  }
  print "theorem invariant3_module_trace : Derives productions [.nonterminal moduleStart] (rest0.map Symbol.terminal) := invariant3_segments segment0"
}
