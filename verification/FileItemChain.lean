import FileEnd
import InitialWhitespaceCall

namespace PegHs.MetaExecution
open EnvironmentEval

-- Offsets count remaining characters, including the lookahead of the next item.
-- Each successful call in the two concrete files returns the empty environment.
def ItemSteps (ctx : Inputs) (fromPos : Nat) : List Nat → Prop
  | [] => fromPos = 0
  | next :: tail =>
    Derives ctx (.call 1 1) fromPos {} (.ok next {}) ∧
      next < fromPos ∧ ItemSteps ctx next tail

theorem invariant1_steps_to_items (mode : Bool) (input : List Char) (n : Nat)
    (ends : List Nat) (steps : ItemSteps (context mode input) n ends) :
    TopItems (context mode input) n {} 0 {} := by
  induction ends generalizing n with
  | nil =>
    change n = 0 at steps
    subst n
    exact invariant1_top_items_end mode input {}
  | cons next tail ih =>
    obtain ⟨succeeded, progress, more⟩ := steps
    exact .next succeeded progress (ih next more)

theorem invariant1_file_from_item_steps (mode : Bool) (extra : List Char) (ends : List Nat)
    (steps : ItemSteps (context mode (wsWindow ++ extra)) (1 + extra.length) ends) :
    FileResult mode (wsWindow ++ extra) (.ok 0 {}) :=
  invariant1_file_from_top_items mode _ (invariant1_initial_whitespace_call mode extra)
    (invariant1_steps_to_items mode _ _ ends steps) (invariant1_eof_terminal _ _)

#print axioms invariant1_file_from_item_steps
end PegHs.MetaExecution
