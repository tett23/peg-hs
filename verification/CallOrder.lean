import Std

namespace PegHs.CallOrder

-- This abstraction tracks how many characters successful evaluations consume.
-- A token may match any positive number of characters; predicates and semantic actions may succeed
-- without moving. Ordered choice is overapproximated by either branch.
inductive Body where
  | eps | token | call (rule : Nat)
  | seq (a b : Body) | alt (a b : Body)
  | look (a : Body) | star (a : Body)
  deriving Repr, DecidableEq

def mayBeEmpty (known : Nat → Bool) : Body → Bool
  | .eps | .look _ | .star _ => true
  | .token => false
  | .call n => known n
  | .seq a b => mayBeEmpty known a && mayBeEmpty known b
  | .alt a b => mayBeEmpty known a || mayBeEmpty known b

def beforeConsumption (known : Nat → Bool) : Body → List Nat
  | .eps | .token => []
  | .call n => [n]
  | .seq a b => beforeConsumption known a ++
      (if mayBeEmpty known a then beforeConsumption known b else [])
  | .alt a b => beforeConsumption known a ++ beforeConsumption known b
  | .look a | .star a => beforeConsumption known a

def validRule (known : Nat → Bool) (rank : Nat → Nat) (n : Nat) (body : Body) : Bool :=
  (!mayBeEmpty known body || known n) &&
    (beforeConsumption known body).all (fun j => rank j < rank n)

inductive Consumes (rules : Nat → Body) : Body → Nat → Prop where
  | empty : Consumes rules .eps 0
  | token (k) : Consumes rules .token (k+1)
  | call {n k} : Consumes rules (rules n) k → Consumes rules (.call n) k
  | seq {a b i j} : Consumes rules a i → Consumes rules b j → Consumes rules (.seq a b) (i+j)
  | left {a b k} : Consumes rules a k → Consumes rules (.alt a b) k
  | right {a b k} : Consumes rules b k → Consumes rules (.alt a b) k
  | look {a} : Consumes rules (.look a) 0
  | stop {a} : Consumes rules (.star a) 0
  | more {a i j} : Consumes rules a i → Consumes rules (.star a) j →
      Consumes rules (.star a) (i+j)

theorem invariant1_zero_consumption {rules known rank}
    (checked : ∀ n, validRule known rank n (rules n) = true)
    {e k} (evaluated : Consumes rules e k) : k = 0 → mayBeEmpty known e = true := by
  induction evaluated with
  | empty | look | stop | more => simp [mayBeEmpty]
  | token => simp
  | @call n k h ih =>
    have check := (Bool.and_eq_true_iff.mp (checked n)).1
    intro zero
    simpa [ih zero, mayBeEmpty] using check
  | seq _ _ ih₁ ih₂ =>
    intro zero
    simp [mayBeEmpty, ih₁ (by omega), ih₂ (by omega)]
  | left _ ih | right _ ih => intro zero; simp [mayBeEmpty, ih zero]

-- Calls encountered within a rule before its first consumed character.
-- These include failed alternatives and lookahead attempts. To start the
-- right half of a sequence at the same offset the left must succeed at zero.
inductive Starts (rules : Nat → Body) : Body → Nat → Prop where
  | call (n) : Starts rules (.call n) n
  | seqLeft {a b n} : Starts rules a n → Starts rules (.seq a b) n
  | seqRight {a b n} : Consumes rules a 0 → Starts rules b n → Starts rules (.seq a b) n
  | altLeft {a b n} : Starts rules a n → Starts rules (.alt a b) n
  | altRight {a b n} : Starts rules b n → Starts rules (.alt a b) n
  | look {a n} : Starts rules a n → Starts rules (.look a) n
  | star {a n} : Starts rules a n → Starts rules (.star a) n

theorem invariant1_first_call {rules known rank}
    (checked : ∀ n, validRule known rank n (rules n) = true)
    {e n} (started : Starts rules e n) : n ∈ beforeConsumption known e := by
  induction started with
  | call => simp [beforeConsumption]
  | seqLeft _ ih | altLeft _ ih | altRight _ ih => simp [beforeConsumption, ih]
  | seqRight h _ ih => simp [beforeConsumption, invariant1_zero_consumption checked h rfl, ih]
  | look _ ih | star _ ih => exact ih

theorem invariant1_rank_decreases {rules known rank}
    (checked : ∀ n, validRule known rank n (rules n) = true)
    {caller callee} (started : Starts rules (rules caller) callee) : rank callee < rank caller := by
  have all := (Bool.and_eq_true_iff.mp (checked caller)).2
  exact of_decide_eq_true (List.all_eq_true.mp all callee (invariant1_first_call checked started))

-- A call encountered at any offset, including in a lookahead or on a later
-- repetition. An ordered choice can rewind on failure, so either branch may
-- start at the original offset.
inductive Reaches (rules : Nat → Body) : Body → Nat → Nat → Prop where
  | call (n) : Reaches rules (.call n) n 0
  | seqLeft {a b n k} : Reaches rules a n k → Reaches rules (.seq a b) n k
  | seqRight {a b n i j} : Consumes rules a i → Reaches rules b n j →
      Reaches rules (.seq a b) n (i+j)
  | altLeft {a b n k} : Reaches rules a n k → Reaches rules (.alt a b) n k
  | altRight {a b n k} : Reaches rules b n k → Reaches rules (.alt a b) n k
  | look {a n k} : Reaches rules a n k → Reaches rules (.look a) n k
  | first {a n k} : Reaches rules a n k → Reaches rules (.star a) n k
  | later {a n i j} : 0 < i → Consumes rules a i → Reaches rules (.star a) n j →
      Reaches rules (.star a) n (i+j)

theorem invariant1_zero_offset {rules e n k} (h : Reaches rules e n k) :
    k = 0 → Starts rules e n := by
  induction h with
  | call => exact fun _ => .call _
  | seqLeft _ ih => exact fun zero => .seqLeft (ih zero)
  | @seqRight a b n i j h _ ih =>
    intro zero
    have hi : i = 0 := by omega
    exact .seqRight (hi ▸ h) (ih (by omega))
  | altLeft _ ih => exact fun zero => .altLeft (ih zero)
  | altRight _ ih => exact fun zero => .altRight (ih zero)
  | look _ ih => exact fun zero => .look (ih zero)
  | first _ ih => exact fun zero => .star (ih zero)
  | later pos _ _ _ => omega

-- States are (remaining input length, rule number). Subtraction is
-- represented by addition, so the call cannot lie beyond the input.
def Nested (rules : Nat → Body) (child parent : Nat × Nat) : Prop :=
  ∃ k, parent.1 = child.1 + k ∧ Reaches rules (rules parent.2) child.2 k

theorem invariant1_call_wellFounded {rules known rank}
    (checked : ∀ n, validRule known rank n (rules n) = true) :
    WellFounded (Nested rules) := by
  let measure := fun p : Nat × Nat => (p.1, rank p.2)
  apply Subrelation.wf (r := InvImage (Prod.Lex Nat.lt Nat.lt) measure)
  · rintro ⟨remaining, callee⟩ ⟨initial, caller⟩ ⟨k, lengthEq, called⟩
    change initial = remaining+k at lengthEq
    change Prod.Lex Nat.lt Nat.lt (remaining, rank callee) (initial, rank caller)
    cases k with
    | zero =>
      simp only [Nat.add_zero] at lengthEq
      subst initial
      exact .right _ (invariant1_rank_decreases checked (invariant1_zero_offset called rfl))
    | succ k => exact .left _ _ (by change remaining < initial; omega)
  · exact InvImage.wf measure (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

-- Without consuming input, a self call and a two-rule cycle must fail the check.
example : validRule (fun _ => true) (fun _ => 0) 0 (.call 0) = false := by decide
example : validRule (fun _ => false) (fun _ => 0) 0 (.seq .token (.call 0)) = true := by decide
end PegHs.CallOrder
