import HaskellDerivation

namespace PegHs.CFG

-- A zero represents a shift. A positive number represents rule (n - 1).
def decodeAction : Nat → Action
  | 0 => .shift
  | n + 1 => .reduce n

theorem Derives.trans {g a b c} (ab : Derives g a b) (bc : Derives g b c) :
    Derives g a c := by
  induction ab with
  | refl => exact bc
  | production rule _ ih => exact .production rule (ih bc)

-- A segment may carry only the tokens consumed by that segment. This avoids
-- repeating the remaining module in every intermediate state of a certificate.
theorem Derives.append_context {g a b} (d : Derives g a b) (tail : List Symbol) :
    Derives g (a ++ tail) (b ++ tail) := by
  induction d with
  | refl => exact .refl _
  | @production id lhs rhs pre post result rule _ ih =>
    simpa [List.append_assoc] using
      (Derives.production (pre := pre) (post := post ++ tail) rule
        (by simpa [List.append_assoc] using ih))

inductive Segments (g : Grammar) : List Symbol → List Nat → List Symbol → Prop where
  | done (s) : Segments g s [] s
  | next {s mid t consumed suffix} (codes : List Nat)
      (chunk : replay g ⟨s, consumed⟩ (codes.map decodeAction) = some ⟨mid, []⟩)
      (tail : Segments g mid suffix t) : Segments g s (consumed ++ suffix) t

theorem Segments.sound {g s tokens t} (cert : Segments g s tokens t) :
    Derives g t.reverse (s.reverse ++ tokens.map Symbol.terminal) := by
  induction cert with
  | done => simp only [List.map_nil, List.append_nil]; exact .refl _
  | @next s mid t consumed suffix codes chunk _ ih =>
    have d := (replay_sound chunk).append_context (suffix.map Symbol.terminal)
    apply ih.trans
    simpa [State.word, List.map_append, List.append_assoc] using d

theorem invariant3_segments {g start tokens}
    (cert : Segments g [] tokens [.nonterminal start]) :
    Derives g [.nonterminal start] (tokens.map Symbol.terminal) := by
  simpa using cert.sound

example : Segments (fun i => if i = 0 then some (0, [.terminal 2]) else none) [] [2] [.nonterminal 0] := by
  exact .next (consumed := [2]) (suffix := []) [0] rfl
    (.next (consumed := []) (suffix := []) [1] rfl (.done _))

end PegHs.CFG
