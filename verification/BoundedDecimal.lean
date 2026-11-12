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

private def digitValue (c : Char) := c.toNat - '0'.toNat

private def decode (c : Char) : Option Nat :=
  if c.isDigit then some (digitValue c) else none

private theorem decode_all (cs : List Char) :
    cs.mapM decode = if cs.all Char.isDigit then some (cs.map digitValue) else none := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases h : c.isDigit <;> cases rest : cs.all Char.isDigit <;>
      simp [List.mapM_cons, decode, h, ih, rest]

def positive (limit : Nat) (text : String) : Option Nat := do
  let ds ← text.toList.mapM decode
  let n ← parse limit 0 ds
  if n > 0 then some n else none

theorem invariant2_positive_text (limit : Nat) (text : String) :
    let value := text.toList.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    positive limit text =
      if text.toList.all Char.isDigit && 0 < value && value ≤ limit then some value else none := by
  unfold positive
  rw [decode_all]
  cases text.toList.all Char.isDigit <;>
    simp [invariant2_bounded_decimal, List.foldl_map, digitValue] <;> split <;> simp_all

-- The assembler decodes one character at a time and can stop before the end.
def checkedChar (limit acc : Nat) (c : Char) : Option Nat :=
  (decode c).bind (step limit acc)

theorem invariant2_foldM_decode (limit acc : Nat) (within : acc ≤ limit) (cs : List Char) :
    cs.foldlM (checkedChar limit) acc =
      (cs.mapM decode).bind (parse limit acc) := by
  induction cs generalizing acc with
  | nil => simp [parse, within]
  | cons c cs ih =>
    simp only [List.foldlM_cons, List.mapM_cons, checkedChar]
    cases h : decode c with
    | none => simp
    | some d =>
      cases hs : step limit acc d with
      | none =>
        cases cs.mapM decode <;> simp [parse, hs]
      | some n =>
        have bound : n ≤ limit := by
          rw [step_eq] at hs
          split at hs <;> simp_all
        cases tailEq : cs.mapM decode <;> simp [parse, hs, ih n bound, tailEq]

theorem invariant2_streaming_positive (limit : Nat) (text : String) :
    ((text.toList.foldlM (checkedChar limit) 0).bind fun n =>
      if n > 0 then some n else none) = positive limit text := by
  rw [invariant2_foldM_decode limit 0 (Nat.zero_le _)]
  unfold positive
  cases text.toList.mapM decode <;> rfl

#print axioms invariant2_positive_text
#print axioms invariant2_bounded_decimal
end PegHs.BoundedDecimal
