-- A rule number identifies one distinguished name in the extracted grammar.
namespace PegHs.Signatures

abbrev Signature := Nat × Nat

-- The second component is the number of value arguments.
def WellFormed (defs calls : List Signature) : Prop :=
  (defs.map Prod.fst).Nodup ∧ ∀ call ∈ calls, call ∈ defs

def accepts (defs calls : List Signature) : Bool :=
  decide (defs.map Prod.fst).Nodup && calls.all defs.contains

theorem invariant2_signatures (defs calls : List Signature) :
    accepts defs calls = true ↔ WellFormed defs calls := by
  simp [accepts, WellFormed, List.all_eq_true]

example : accepts [(0, 0), (1, 1)] [(0, 0), (1, 1)] = true := by decide
example : accepts [(0, 0)] [(1, 0)] = false := by decide
example : accepts [(0, 0)] [(0, 1)] = false := by decide
example : accepts [(0, 0), (0, 1)] [] = false := by decide

end PegHs.Signatures
