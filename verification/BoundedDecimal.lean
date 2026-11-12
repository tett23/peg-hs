namespace PegHs.BoundedDecimal

-- Digits are decoded separately. This step can be evaluated with a bounded
-- accumulator because its guard precedes multiplication and addition.
def step (limit acc digit : Nat) : Option Nat :=
  if digit ≤ limit ∧ acc ≤ (limit - digit) / 10 then some (acc * 10 + digit) else none

theorem step_eq (limit acc digit : Nat) :
    step limit acc digit = if acc * 10 + digit ≤ limit then some (acc * 10 + digit) else none := by
  unfold step
  split <;> split <;> first | rfl | omega

def parse (limit acc : Nat) : List Nat → Option Nat
  | [] => if acc ≤ limit then some acc else none
  | d :: ds => (step limit acc d).bind fun n => parse limit n ds

theorem invariant2_bounded_decimal (limit acc : Nat) (ds : List Nat) :
    let value := ds.foldl (fun n d => n * 10 + d) acc
    parse limit acc ds = if value ≤ limit then some value else none := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    simp only [parse, step_eq, List.foldl_cons]
    split
    · exact ih _
    · have grows (n : Nat) (xs : List Nat) : n ≤ xs.foldl (fun a b => a * 10 + b) n := by
        induction xs generalizing n with
        | nil => exact Nat.le_refl _
        | cons a xs h =>
          simp only [List.foldl_cons]
          exact Nat.le_trans (by omega : n ≤ n * 10 + a) (h _)
      have bound := grows (acc * 10 + d) ds
      simp [show ¬ ds.foldl (fun n d => n * 10 + d) (acc * 10 + d) ≤ limit by omega]

def positive (limit : Nat) (text : String) : Option Nat := do
  let ds ← text.toList.mapM fun c =>
    if c.isDigit then some (c.toNat - '0'.toNat) else none
  let n ← parse limit 0 ds
  if n > 0 then some n else none

#print axioms invariant2_bounded_decimal
end PegHs.BoundedDecimal
