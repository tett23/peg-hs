import Nullable
import RuleRejectionRepeat

namespace PegHs.RuleRejectionNullable

open PegHs.RuleRejectionRefs

-- The names of finite rules are assigned distinct Fin indices. A reference
-- to a name outside that universe is false, as S.member is on the known set.
abbrev RuleLookup (n : Nat) := String → Option (Fin n)
abbrev RecoveryLookup (n : Nat) := String → Option (Fin n)

private def sequencePositive {n : Nat} (expressions : List (Peg.Verification.PositiveExpr n)) :
    Peg.Verification.PositiveExpr n :=
  expressions.foldr Peg.Verification.PositiveExpr.both .empty

private def alternativesPositive {n : Nat} (expressions : List (Peg.Verification.PositiveExpr n)) :
    Peg.Verification.PositiveExpr n :=
  expressions.foldr Peg.Verification.PositiveExpr.either .nonempty

private theorem sequencePositive_correct {n : Nat} (known : Fin n → Bool)
    (expressions : List (Peg.Verification.PositiveExpr n)) :
    Peg.Verification.acceptsEmpty known (sequencePositive expressions) =
      expressions.all (Peg.Verification.acceptsEmpty known) := by
  induction expressions with
  | nil => rfl
  | cons x xs ih =>
    change Peg.Verification.acceptsEmpty known (.both x (sequencePositive xs)) = _
    simp only [Peg.Verification.acceptsEmpty, List.all_cons, ih]

private theorem alternativesPositive_correct {n : Nat} (known : Fin n → Bool)
    (expressions : List (Peg.Verification.PositiveExpr n)) :
    Peg.Verification.acceptsEmpty known (alternativesPositive expressions) =
      expressions.any (Peg.Verification.acceptsEmpty known) := by
  induction expressions with
  | nil => rfl
  | cons x xs ih =>
    change Peg.Verification.acceptsEmpty known (.either x (alternativesPositive xs)) = _
    simp only [Peg.Verification.acceptsEmpty, List.any_cons, ih]

private theorem any_eq_of_mem {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (by simp), ih (by
      intro y hy
      exact h y (by simp [hy]))]

private theorem all_eq_of_mem {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x (by simp), ih (by
      intro y hy
      exact h y (by simp [hy]))]

def toPositive {n : Nat} (lookup : RuleLookup n) (recovery : RecoveryLookup n) :
    Expr → Peg.Verification.PositiveExpr n
  | .lit value _ => if value.isEmpty then .empty else .nonempty
  | .charClass _ => .nonempty
  | .any => .nonempty
  | .ref _ name _ => match lookup name with
    | none => .nonempty
    | some rule => .ref rule
  | .group alts => alternativesPositive
      (alts.map fun items => sequencePositive (items.map (toPositive lookup recovery)))
  | .star _ => .empty
  | .plus x => toPositive lookup recovery x
  | .opt _ => .empty
  | .and _ => .empty
  | .not _ => .empty
  | .capture x => toPositive lookup recovery x
  | .label _ x name =>
    match recovery name with
    | none => toPositive lookup recovery x
    | some rule => .either (toPositive lookup recovery x) (.ref rule)
  | .predicate _ _ => .empty
  | .template _ _ _ _ => .empty
  | .discard x => toPositive lookup recovery x
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega

-- Independent Boolean reading of the Check.hs clauses.
def directNullable {n : Nat} (lookup : RuleLookup n) (recovery : RecoveryLookup n)
    (known : Fin n → Bool) : Expr → Bool
  | .lit value _ => value.isEmpty
  | .charClass _ => false
  | .any => false
  | .ref _ name _ => match lookup name with
    | none => false
    | some rule => known rule
  | .group alts => (alts.map fun items =>
      (items.map (directNullable lookup recovery known)).all id).any id
  | .star _ => true
  | .plus x => directNullable lookup recovery known x
  | .opt _ => true
  | .and _ => true
  | .not _ => true
  | .capture x => directNullable lookup recovery known x
  | .label _ x name =>
    directNullable lookup recovery known x ||
      (match recovery name with | none => false | some rule => known rule)
  | .predicate _ _ => true
  | .template _ _ _ _ => true
  | .discard x => directNullable lookup recovery known x
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega

theorem toPositive_correct {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (known : Fin n → Bool) (e : Expr) :
    Peg.Verification.acceptsEmpty known (toPositive lookup recovery e) =
      directNullable lookup recovery known e := by
  induction e using toPositive.induct (lookup := lookup) (recovery := recovery) with
  | _ =>
    try simp_all [toPositive, directNullable, Peg.Verification.acceptsEmpty,
      alternativesPositive_correct]
    all_goals try (split <;> simp_all [Peg.Verification.acceptsEmpty])
    all_goals
      rename_i alts ih
      apply any_eq_of_mem
      intro items hi
      simp only [Function.comp_apply, sequencePositive_correct, List.all_map]
      apply all_eq_of_mem
      intro x hx
      exact ih items hi x hx

-- Each rule is a choice of sequences. The order and undefined-reference
-- behavior agree with nullableRulesWith's set membership semantics.
def positiveRules {n : Nat} (lookup : RuleLookup n) (recovery : RecoveryLookup n)
    (rules : Fin n → List (List Expr)) : Fin n → Peg.Verification.PositiveExpr n :=
  fun i => toPositive lookup recovery (.group (rules i))

def directNext {n : Nat} (lookup : RuleLookup n) (recovery : RecoveryLookup n)
    (rules : Fin n → List (List Expr)) (known : Fin n → Bool) : Fin n → Bool :=
  fun i => directNullable lookup recovery known (.group (rules i))

theorem directNext_correct {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr))
    (known : Fin n → Bool) :
    Peg.Verification.next (positiveRules lookup recovery rules) known =
      directNext lookup recovery rules known := by
  funext i
  exact toPositive_correct lookup recovery known (.group (rules i))

def directRounds {n : Nat} (lookup : RuleLookup n) (recovery : RecoveryLookup n)
    (rules : Fin n → List (List Expr)) : Nat → Fin n → Bool
  | 0 => fun _ => false
  | k + 1 => directNext lookup recovery rules (directRounds lookup recovery rules k)

theorem directRounds_correct {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr)) (k : Nat) :
    directRounds lookup recovery rules k =
      Peg.Verification.rounds (positiveRules lookup recovery rules) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [directRounds, Peg.Verification.rounds, ← ih]
    exact (directNext_correct lookup recovery rules _).symm

theorem direct_least_fixed {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr)) :
    ∃ k ≤ n, directNext lookup recovery rules
        (directRounds lookup recovery rules k) = directRounds lookup recovery rules k ∧
      ∀ fixed, directNext lookup recovery rules fixed = fixed →
        Peg.Verification.Included (directRounds lookup recovery rules k) fixed := by
  obtain ⟨k, bound, stable⟩ :=
    Peg.Verification.invariant2_nullable_stops (positiveRules lookup recovery rules)
  refine ⟨k, bound, ?_, ?_⟩
  · rw [directRounds_correct, ← directNext_correct]
    exact stable
  · intro fixed hfixed
    have fixedPositive : Peg.Verification.next (positiveRules lookup recovery rules) fixed = fixed := by
      rw [directNext_correct]
      exact hfixed
    rw [directRounds_correct]
    exact Peg.Verification.rounds_below_fixed _ fixed fixedPositive k

theorem direct_rounds_after_fixed {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr)) (k : Nat)
    (stable : directNext lookup recovery rules (directRounds lookup recovery rules k) =
      directRounds lookup recovery rules k) (extra : Nat) :
    directRounds lookup recovery rules (k + extra) = directRounds lookup recovery rules k := by
  induction extra with
  | zero => simp
  | succ extra ih =>
    rw [Nat.add_succ, directRounds, ih, stable]

theorem invariant2_language_repeat_stabilizes {n : Nat} (lookup : RuleLookup n)
    (rules : Fin n → List (List Expr)) :
    ∃ k ≤ n, ∀ (extra location : Nat) (e : Expr),
      RuleRejectionRepeat.repeatCandidates
        (directNullable lookup (fun _ => none) (directRounds lookup (fun _ => none) rules (k + extra)))
        location e =
      RuleRejectionRepeat.repeatCandidates
        (directNullable lookup (fun _ => none) (directRounds lookup (fun _ => none) rules k)) location e := by
  obtain ⟨k, bound, stable, _⟩ := direct_least_fixed lookup (fun _ => none) rules
  refine ⟨k, bound, ?_⟩
  intro extra location e
  rw [direct_rounds_after_fixed lookup (fun _ => none) rules k stable extra]

#print axioms direct_rounds_after_fixed
#print axioms invariant2_language_repeat_stabilizes

theorem both_least_fixed {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr)) :
    (∃ k ≤ n, directNext lookup (fun _ => none) rules
        (directRounds lookup (fun _ => none) rules k) =
        directRounds lookup (fun _ => none) rules k ∧
      ∀ fixed, directNext lookup (fun _ => none) rules fixed = fixed →
        Peg.Verification.Included (directRounds lookup (fun _ => none) rules k) fixed) ∧
    (∃ k ≤ n, directNext lookup recovery rules
        (directRounds lookup recovery rules k) = directRounds lookup recovery rules k ∧
      ∀ fixed, directNext lookup recovery rules fixed = fixed →
        Peg.Verification.Included (directRounds lookup recovery rules k) fixed) := by
  exact ⟨direct_least_fixed lookup (fun _ => none) rules,
    direct_least_fixed lookup recovery rules⟩

def languageNullable {n : Nat} (lookup : RuleLookup n)
    (rules : Fin n → List (List Expr)) (k : Nat) : Expr → Bool :=
  directNullable lookup (fun _ => none) (directRounds lookup (fun _ => none) rules k)

theorem invariant2_languageRepeatCandidate {n : Nat}
    (lookup : RuleLookup n) (rules : Fin n → List (List Expr))
    (k location : Nat) (e : Expr)
    (found : RuleRejectionRepeat.HasNullableRepeat
      (languageNullable lookup rules k) e) :
    (location, true) ∈ RuleRejectionRepeat.repeatCandidates
      (languageNullable lookup rules k) location e := by
  exact RuleRejectionRepeat.invariant2_nullableRepeat_candidate _ _ _ found

theorem invariant2_languageRepeatVisible {n : Nat} {G : Type}
    (lookup : RuleLookup n) (rules : Fin n → List (List Expr)) (k : Nat)
    (parsed g0 g : G)
    (resolve expand : G → Except RuleRejection.Diagnostics G)
    (notes : G → RuleRejection.Diagnostics → RuleRejection.Diagnostics)
    (strip : Option (G → G))
    (warningFor : G → G → RuleRejection.Diagnostics)
    (generate : G → Except RuleRejection.Diagnostics String)
    (undefined before after : List RuleRejection.Diagnostic)
    (location : Nat) (expression : Expr)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hn : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (found : RuleRejectionRepeat.HasNullableRepeat
      (languageNullable lookup rules k) expression) :
    ∃ ds, ds ≠ [] ∧
      PegHs.Pipeline.visible
        (PegHs.Pipeline.pipeline (.ok parsed) resolve expand
          (fun _ => RuleRejection.checkRoot undefined
            (RuleRejection.repetitionFromNullable
              (RuleRejectionRepeat.repeatCandidates
                (languageNullable lookup rules k) location expression)) before after)
          notes strip warningFor generate) = .error ds := by
  exact RuleRejectionRepeat.invariant2_nullableRepeatVisible parsed g0 g resolve expand
    notes strip warningFor generate undefined before after
    (languageNullable lookup rules k) location expression hr he hn found

-- A recovery-only empty path changes the recovery fixed point, but does not
-- make the language's repetition check accept that path as nullable.
example : directRounds (n := 2)
    (fun name => if name == "R" then some ⟨1, by omega⟩ else none)
    (fun _ => none)
    (fun i => if i.val == 0 then [[.label 0 (.lit "x" "") "L"]] else [[.lit "" ""]])
    2 ⟨0, by omega⟩ = false := by native_decide
example : directRounds (n := 2)
    (fun name => if name == "R" then some ⟨1, by omega⟩ else none)
    (fun name => if name == "L" then some ⟨1, by omega⟩ else none)
    (fun i => if i.val == 0 then [[.label 0 (.lit "x" "") "L"]] else [[.lit "" ""]])
    2 ⟨0, by omega⟩ = true := by native_decide

-- Invariant 2 boundary examples were added before the translator.
example : toPositive (n := 0) (fun _ => none) (fun _ => none)
    (.predicate true "p") = Peg.Verification.PositiveExpr.empty := by simp [toPositive]
example : toPositive (n := 0) (fun _ => none) (fun _ => none)
    (.ref 0 "Missing" 0) = Peg.Verification.PositiveExpr.nonempty := by simp [toPositive]

end PegHs.RuleRejectionNullable

#print axioms PegHs.RuleRejectionNullable.toPositive_correct
#print axioms PegHs.RuleRejectionNullable.both_least_fixed
#print axioms PegHs.RuleRejectionNullable.invariant2_languageRepeatVisible
