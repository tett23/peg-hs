import Std

set_option maxRecDepth 4096

namespace PegHs.ExpressionDepth

-- Depth of the written syntax. A template argument which the semantic action
-- turns into an implicit EGroup contributes the depth of its items.
inductive Shape where
  | atom
  | children (first rest : Shape)
  | enter (inner : Shape)
  | postOps (inner : Shape) (count : Nat)

def height : Shape → Nat
  | .atom => 0
  | .children x y => max (height x) (height y)
  | .enter x => height x + 1
  | .postOps x n => height x + n

-- PostOp and LabelPart check their inherited depth before adding each layer.
def postChecks (d : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => decide (d < 256) && postChecks (d + 1) n

theorem postChecks_iff (d n : Nat) (bound : d ≤ 256) :
    postChecks d n = true ↔ d + n ≤ 256 := by
  induction n generalizing d with
  | zero => simp [postChecks, bound]
  | succ n ih =>
    by_cases h : d < 256
    · simp [postChecks, h, ih (d + 1) (by omega)]; omega
    · simp [postChecks, h]; omega

def checked (d : Nat) : Shape → Option Nat
  | .atom => some 0
  | .children x y => do
      let hx ← checked d x
      let hy ← checked d y
      pure (max hx hy)
  | .enter x => if d < 256 then (checked (d + 1) x).map (· + 1) else none
  | .postOps x n => do
      let hx ← checked d x
      if postChecks (d + hx) n then pure (hx + n) else none

theorem invariant1_depth (e : Shape) (d : Nat) (bound : d ≤ 256) :
    checked d e = if d + height e ≤ 256 then some (height e) else none := by
  induction e generalizing d with
  | atom => simp [checked, height, bound]
  | children x y ix iy =>
    simp only [checked, height, ix d bound, iy d bound]
    have hm : d + max (height x) (height y) ≤ 256 ↔
        d + height x ≤ 256 ∧ d + height y ≤ 256 := by omega
    by_cases hx : d + height x ≤ 256 <;> by_cases hy : d + height y ≤ 256 <;>
      simp [hx, hy, hm]
  | enter x ih =>
    by_cases h : d < 256
    · have eq : d + 1 + height x = d + (height x + 1) := by omega
      simp only [checked, h, ite_true, ih (d + 1) (by omega), height, eq]
      by_cases fits : d + (height x + 1) ≤ 256 <;> simp [fits]
    · have hn : ¬ d + (height x + 1) ≤ 256 := by omega
      simp [checked, h, height, hn]
  | postOps x n ih =>
    simp only [checked, height, ih d bound]
    by_cases hx : d + height x ≤ 256
    · by_cases hn : d + (height x + n) ≤ 256 <;> simp [hx, postChecks_iff _ _ hx, Nat.add_assoc, hn]
    · have hn : ¬ d + (height x + n) ≤ 256 := by omega
      simp [hx, hn]

example : checked 0 (.enter (.postOps .atom 255)) = some 256 := by decide
example : checked 0 (.postOps (.enter .atom) 256) = none := by decide
example : checked 0 (.children (.postOps .atom 256) (.postOps .atom 256)) = some 256 := by decide

end PegHs.ExpressionDepth
