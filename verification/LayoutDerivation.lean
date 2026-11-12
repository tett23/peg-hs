import TraceChunks

namespace PegHs.CFG

-- Happy inserts terminal zero for GHC's "close -> error" production. It has
-- no source token. The raw proof retains the parser-directed layout decision.
def sourceSymbols (word : List Symbol) : List Symbol :=
  word.filter (· != .terminal 0)

def layoutGrammar (g : Grammar) : Grammar := fun id =>
  (g id).map fun (lhs, rhs) => (lhs, sourceSymbols rhs)

theorem Derives.eraseLayout {g a b} (d : Derives g a b) :
    Derives (layoutGrammar g) (sourceSymbols a) (sourceSymbols b) := by
  induction d with
  | refl => exact .refl _
  | @production id lhs rhs pre post result rule _ ih =>
    have row : layoutGrammar g id = some (lhs, sourceSymbols rhs) := by
      simp [layoutGrammar, rule]
    simpa [sourceSymbols, List.filter_append] using
      (Derives.production (pre := sourceSymbols pre) (post := sourceSymbols post)
        row (by simpa [sourceSymbols, List.filter_append] using ih))

theorem invariant3_layout_tokens {g start tokens}
    (cert : Segments g [] tokens [.nonterminal start]) :
    Derives (layoutGrammar g) [.nonterminal start]
      (sourceSymbols (tokens.map Symbol.terminal)) := by
  simpa [sourceSymbols] using (invariant3_segments cert).eraseLayout

end PegHs.CFG
