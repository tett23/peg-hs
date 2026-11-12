import FileEnd
import InitialWhitespaceCall

namespace PegHs.MetaExecution
open EnvironmentEval

-- Offsets count remaining characters, including the lookahead of the next item.
-- Each successful call in the two concrete files returns the empty environment.
def ItemStepsTo (ctx : Inputs) (stopPos fromPos : Nat) : List Nat → Prop
  | [] => fromPos = stopPos
  | next :: tail =>
    Derives ctx (.call 1 1) fromPos {} (.ok next {}) ∧
      next < fromPos ∧ ItemStepsTo ctx stopPos next tail

abbrev ItemSteps (ctx : Inputs) := ItemStepsTo ctx 0

theorem invariant2_steps_to_throw (ctx : Inputs) (fromPos stopPos : Nat) (ends : List Nat)
    (steps : ItemStepsTo ctx stopPos fromPos ends) {pos name msg}
    (failed : Derives ctx (.call 1 1) stopPos {} (.throwLabel pos name msg)) :
    Derives ctx (.starLoop (.call 1 1)) fromPos {} (.throwLabel pos name msg) := by
  induction ends generalizing fromPos with
  | nil =>
    change fromPos = stopPos at steps
    exact steps.symm ▸ Derives.loopThrow failed
  | cons next tail ih =>
    obtain ⟨item, progress, more⟩ := steps
    exact .loopMore item progress (ih next more)

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
