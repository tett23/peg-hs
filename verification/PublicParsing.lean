import Pipeline

namespace PegHs.PublicParsing
open PegHs.Pipeline

inductive StartResult (T : Type) where
  | ok (byteOffset : Nat) (tops : T)
  | fail
  | throwLabel (location : Nat) (label : String) (message : Option String)
  deriving DecidableEq, Repr

inductive Failure where
  | expectedEnd (offset : Nat)
  | ordinary
  | labelled (label : String) (message : Option String)
  deriving DecidableEq, Repr

-- The farthest position and formatted diagnostic come from currentError.
-- parseTops always constructs one diagnostic for a failed parse.
def entry {T} (inputBytes : Nat) (start : StartResult T)
    (diagnostic : Failure → String) : Except Diagnostics T :=
  match start with
  | .ok pos tops =>
    if pos = inputBytes then .ok tops else .error [diagnostic (.expectedEnd pos)]
  | .fail => .error [diagnostic .ordinary]
  | .throwLabel _ l m => .error [diagnostic (.labelled l m)]

theorem invariant1_parseTops_iff {T} (bytes : Nat) (r : StartResult T)
    (d : Failure → String) (tops : T) :
    entry bytes r d = .ok tops ↔ r = .ok bytes tops := by
  cases r with
  | ok pos value => by_cases h : pos = bytes <;> simp [entry, h]
  | fail => simp [entry]
  | throwLabel => simp [entry]

theorem invariant2_parseTops_singleton {T} (bytes : Nat) (r : StartResult T)
    (d : Failure → String) (ds : Diagnostics) (h : entry bytes r d = .error ds) :
    ∃ msg, ds = [msg] := by
  cases r with
  | ok pos value =>
    by_cases same : pos = bytes <;> simp [entry, same] at h
    exact ⟨_, h.symm⟩
  | fail => cases h; exact ⟨_, rfl⟩
  | throwLabel => cases h; exact ⟨_, rfl⟩

theorem invariant2_parseFailure_no_module {T G} (bytes : Nat) (r : StartResult T)
    (d : Failure → String) (ds : Diagnostics) (h : entry bytes r d = .error ds)
    (assemble : T → Except Diagnostics G)
    (resolve expand : G → Except Diagnostics G) (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics) (strip : Option (G → G))
    (warnings : G → G → Diagnostics) (generate : G → Except Diagnostics String) :
    ∃ msg, visible (pipeline ((entry bytes r d).bind assemble) resolve expand check notes
      strip warnings generate) = .error [msg] := by
  obtain ⟨msg, rfl⟩ := invariant2_parseTops_singleton bytes r d ds h
  rw [h]
  exact ⟨msg, rfl⟩

end PegHs.PublicParsing
