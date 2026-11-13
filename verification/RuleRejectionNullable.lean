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

-- Multiple declarations of a name contribute alternatives to the same set member.
def mergedNamedRules {n : Nat} (names : Fin n → String)
    (declarations : List (String × List (List Expr))) (i : Fin n) : List (List Expr) :=
  (declarations.filter fun declaration => declaration.1 == names i).flatMap Prod.snd

theorem merged_named_rule_nullable {n : Nat} (names : Fin n → String)
    (declarations : List (String × List (List Expr))) (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (known : Fin n → Bool) (i : Fin n) :
    directNullable lookup recovery known (.group (mergedNamedRules names declarations i)) = true ↔
      ∃ declaration ∈ declarations, declaration.1 = names i ∧
        directNullable lookup recovery known (.group declaration.2) = true := by
  simp [directNullable, mergedNamedRules, List.any_eq_true]

#print axioms merged_named_rule_nullable

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

def uniqueRuleNames : List String → List String
  | [] => []
  | name :: rest =>
    let tail := uniqueRuleNames rest
    if name ∈ tail then tail else name :: tail

theorem uniqueRuleNames_nodup (names : List String) : (uniqueRuleNames names).Nodup := by
  induction names with
  | nil => simp [uniqueRuleNames]
  | cons name rest ih =>
    simp only [uniqueRuleNames]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨by assumption, ih⟩

theorem uniqueRuleNames_member (names : List String) (name : String) :
    name ∈ uniqueRuleNames names ↔ name ∈ names := by
  induction names generalizing name with
  | nil => simp [uniqueRuleNames]
  | cons first rest ih =>
    simp only [uniqueRuleNames]
    split <;> simp_all

def declarationNames (declarations : List (String × List (List Expr))) : List String :=
  uniqueRuleNames (declarations.map Prod.fst)

def indexedDeclarationName (declarations : List (String × List (List Expr)))
    (i : Fin (declarationNames declarations).length) : String :=
  (declarationNames declarations)[i]

theorem indexedDeclarationName_injective (declarations : List (String × List (List Expr))) :
    Function.Injective (indexedDeclarationName declarations) := by
  intro i j same
  apply Fin.ext
  exact (uniqueRuleNames_nodup (declarations.map Prod.fst)).getElem_inj.mp same

#print axioms uniqueRuleNames_member
#print axioms indexedDeclarationName_injective

def knownRuleNames {n : Nat} (names : Fin n → String) (known : Fin n → Bool) : List String :=
  ((List.finRange n).filter fun i => known i).map names

theorem knownRuleNames_member {n : Nat} (names : Fin n → String)
    (known : Fin n → Bool) (name : String) :
    name ∈ knownRuleNames names known ↔ ∃ i, names i = name ∧ known i = true := by
  simp [knownRuleNames, List.mem_map, List.mem_filter, and_comm]

def lookupRuleNames {n : Nat} (names : Fin n → String) : RuleLookup n :=
  fun name => (List.finRange n).find? fun i => names i == name

theorem lookupRuleNames_correct {n : Nat} (names : Fin n → String)
    (distinct : Function.Injective names) (name : String) (i : Fin n) :
    lookupRuleNames names name = some i ↔ names i = name := by
  constructor
  · intro found
    exact beq_iff_eq.mp (List.find?_some (p := fun k => names k == name) found)
  · intro target
    have existsResult : ∃ j, lookupRuleNames names name = some j := by
      cases result : lookupRuleNames names name with
      | some j => exact ⟨j, rfl⟩
      | none =>
        have absent := List.find?_eq_none.mp result
        have impossible := absent i (by simp)
        simp [target] at impossible
    obtain ⟨j, found⟩ := existsResult
    have named : names j = name := beq_iff_eq.mp (List.find?_some (p := fun k => names k == name) found)
    have same := distinct (named.trans target.symm)
    simpa [same] using found

#print axioms lookupRuleNames_correct

theorem knownRuleNames_lookup {n : Nat} (names : Fin n → String)
    (lookup : RuleLookup n)
    (indexed : ∀ name i, lookup name = some i ↔ names i = name)
    (known : Fin n → Bool) (name : String) :
    (name ∈ knownRuleNames names known) ↔ (lookup name).any known = true := by
  rw [knownRuleNames_member]
  cases found : lookup name with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, iff_false]
    rintro ⟨i, hi, _⟩
    have := (indexed name i).mpr hi
    simp [found] at this
  | some i =>
    simp only [Option.any_some]
    constructor
    · rintro ⟨j, nameOk, value⟩
      have same : j = i := Option.some.inj (((indexed name j).mpr nameOk).symm.trans found)
      simpa [same] using value
    · intro value
      exact ⟨i, (indexed name i).mp found, value⟩

theorem knownRuleNames_equality {n : Nat} (names : Fin n → String)
    (distinct : Function.Injective names) (left right : Fin n → Bool) :
    (∀ name, name ∈ knownRuleNames names left ↔ name ∈ knownRuleNames names right) ↔ left = right := by
  constructor
  · intro same
    funext i
    have atIndex (known : Fin n → Bool) :
        names i ∈ knownRuleNames names known ↔ known i = true := by
      rw [knownRuleNames_member]
      constructor
      · rintro ⟨j, eq, value⟩
        simpa [distinct eq] using value
      · intro value
        exact ⟨i, rfl, value⟩
    have h := same (names i)
    rw [atIndex left, atIndex right] at h
    cases hl : left i <;> cases hr : right i <;> simp_all
  · rintro rfl name
    rfl

#print axioms knownRuleNames_member
#print axioms knownRuleNames_lookup
#print axioms knownRuleNames_equality

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

theorem direct_rounds_rule_count_fixed {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr)) :
    directNext lookup recovery rules (directRounds lookup recovery rules n) =
      directRounds lookup recovery rules n := by
  obtain ⟨k, bound, stable, _⟩ := direct_least_fixed lookup recovery rules
  have same := direct_rounds_after_fixed lookup recovery rules k stable (n - k)
  rw [Nat.add_sub_of_le bound] at same
  rw [same, stable]

-- The loop tests equality before continuing, as nullableRulesWith.go does.
def nullableUntilStable {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr))
    (k : Nat) (bound : k ≤ n) : Fin n → Bool :=
  let known := directRounds lookup recovery rules k
  let next := directNext lookup recovery rules known
  if same : ∀ i, next i = known i then known
  else
    have less : k < n := by
      apply Nat.lt_of_le_of_ne bound
      intro eq
      subst k
      exact same (congrFun (direct_rounds_rule_count_fixed lookup recovery rules))
    nullableUntilStable lookup recovery rules (k + 1) (by omega)
termination_by n - k

theorem nullableUntilStable_correct {n : Nat} (lookup : RuleLookup n)
    (recovery : RecoveryLookup n) (rules : Fin n → List (List Expr))
    (k : Nat) (bound : k ≤ n) :
    nullableUntilStable lookup recovery rules k bound = directRounds lookup recovery rules n := by
  rw [nullableUntilStable]
  split
  next same =>
    have stable := funext same
    have eventual := direct_rounds_after_fixed lookup recovery rules k stable (n - k)
    rw [Nat.add_sub_of_le bound] at eventual
    exact eventual.symm
  next different =>
    apply nullableUntilStable_correct
termination_by n - k
decreasing_by
  have different : ¬ ∀ i, directNext lookup recovery rules (directRounds lookup recovery rules k) i =
      directRounds lookup recovery rules k i := by assumption
  have less : k < n := by
    apply Nat.lt_of_le_of_ne bound
    intro eq
    subst k
    exact different (congrFun (direct_rounds_rule_count_fixed lookup recovery rules))
  omega

#print axioms nullableUntilStable_correct

theorem invariant2_named_nullable_result {n : Nat} (names : Fin n → String)
    (distinct : Function.Injective names) (recovery : RecoveryLookup n)
    (rules : Fin n → List (List Expr)) :
    let lookup := lookupRuleNames names
    let result := nullableUntilStable lookup recovery rules 0 (Nat.zero_le n)
    (∀ name, name ∈ knownRuleNames names result ↔
      (lookup name).any (directRounds lookup recovery rules n) = true) ∧
    (∀ name, name ∈ knownRuleNames names (directNext lookup recovery rules result) ↔
      name ∈ knownRuleNames names result) := by
  dsimp only
  rw [nullableUntilStable_correct]
  constructor
  · intro name
    exact knownRuleNames_lookup names (lookupRuleNames names)
      (lookupRuleNames_correct names distinct) _ name
  · rw [direct_rounds_rule_count_fixed]
    intro name
    rfl

#print axioms invariant2_named_nullable_result

def nullableDeclarationNames (declarations : List (String × List (List Expr))) : List String :=
  let names := indexedDeclarationName declarations
  let rules := mergedNamedRules names declarations
  knownRuleNames names (nullableUntilStable (lookupRuleNames names) (fun _ => none) rules 0 (by omega))

theorem nullableDeclarationNames_fixed (declarations : List (String × List (List Expr))) :
    let names := indexedDeclarationName declarations
    let lookup := lookupRuleNames names
    let rules := mergedNamedRules names declarations
    ∀ i, names i ∈ nullableDeclarationNames declarations ↔
      ∃ declaration ∈ declarations, declaration.1 = names i ∧
        directNullable lookup (fun _ => none) (directRounds lookup (fun _ => none) rules
          (declarationNames declarations).length) (.group declaration.2) = true := by
  dsimp only
  intro i
  unfold nullableDeclarationNames
  dsimp only
  rw [nullableUntilStable_correct, knownRuleNames_lookup _ _ (lookupRuleNames_correct _
    (indexedDeclarationName_injective declarations))]
  rw [(lookupRuleNames_correct _ (indexedDeclarationName_injective declarations) _ i).mpr rfl]
  simp only [Option.any_some]
  have fixed := congrFun (direct_rounds_rule_count_fixed
    (lookupRuleNames (indexedDeclarationName declarations)) (fun _ => none)
    (mergedNamedRules (indexedDeclarationName declarations) declarations)) i
  rw [← fixed]
  exact merged_named_rule_nullable _ _ _ _ _ i

theorem nullableDeclarationNames_iff (declarations : List (String × List (List Expr))) (name : String) :
    name ∈ nullableDeclarationNames declarations ↔
      ∃ declaration ∈ declarations, declaration.1 = name ∧
        directNullable (lookupRuleNames (indexedDeclarationName declarations)) (fun _ => none)
          (directRounds (lookupRuleNames (indexedDeclarationName declarations)) (fun _ => none)
            (mergedNamedRules (indexedDeclarationName declarations) declarations)
            (declarationNames declarations).length) (.group declaration.2) = true := by
  constructor
  · intro member
    obtain ⟨i, named, _⟩ := (knownRuleNames_member _ _ _).mp member
    rw [← named]
    exact (nullableDeclarationNames_fixed declarations i).mp (named ▸ member)
  · rintro ⟨declaration, member, named, valid⟩
    have inNames : name ∈ declarationNames declarations := by
      apply (uniqueRuleNames_member _ _).mpr
      exact List.mem_map.mpr ⟨declaration, member, named⟩
    obtain ⟨i, bound, atIndex⟩ := List.getElem_of_mem inNames
    have eq : indexedDeclarationName declarations ⟨i, bound⟩ = name := atIndex
    rw [← eq]
    exact (nullableDeclarationNames_fixed declarations ⟨i, bound⟩).mpr
      ⟨declaration, member, named.trans eq.symm, valid⟩

theorem nullableDeclarationNames_least (declarations : List (String × List (List Expr)))
    (candidate : Fin (declarationNames declarations).length → Bool)
    (closed : directNext (lookupRuleNames (indexedDeclarationName declarations)) (fun _ => none)
      (mergedNamedRules (indexedDeclarationName declarations) declarations) candidate = candidate) :
    ∀ name ∈ nullableDeclarationNames declarations,
      name ∈ knownRuleNames (indexedDeclarationName declarations) candidate := by
  let lookup := lookupRuleNames (indexedDeclarationName declarations)
  let rules := mergedNamedRules (indexedDeclarationName declarations) declarations
  have positiveFixed : Peg.Verification.next (positiveRules lookup (fun _ => none) rules) candidate = candidate := by
    rw [directNext_correct]
    exact closed
  have below := Peg.Verification.rounds_below_fixed
    (positiveRules lookup (fun _ => none) rules) candidate positiveFixed (declarationNames declarations).length
  intro name member
  unfold nullableDeclarationNames at member
  dsimp only at member
  rw [nullableUntilStable_correct, knownRuleNames_member] at member
  obtain ⟨i, named, nullable⟩ := member
  apply (knownRuleNames_member _ _ _).mpr
  refine ⟨i, named, ?_⟩
  exact below i (by simpa [directRounds_correct] using nullable)

#print axioms nullableDeclarationNames_least

#print axioms nullableDeclarationNames_iff

#print axioms nullableDeclarationNames_fixed

def computedLanguageNullable {n : Nat} (lookup : RuleLookup n)
    (rules : Fin n → List (List Expr)) : Expr → Bool :=
  directNullable lookup (fun _ => none) (directRounds lookup (fun _ => none) rules n)

theorem invariant2_computed_language_repeat {n : Nat} (lookup : RuleLookup n)
    (rules : Fin n → List (List Expr)) (location extra : Nat) (e : Expr) :
    ((location, true) ∈ RuleRejectionRepeat.repeatCandidates
      (computedLanguageNullable lookup rules) location e ↔
      RuleRejectionRepeat.HasNullableRepeat (computedLanguageNullable lookup rules) e) ∧
    RuleRejectionRepeat.repeatCandidates
      (directNullable lookup (fun _ => none) (directRounds lookup (fun _ => none) rules (n + extra))) location e =
      RuleRejectionRepeat.repeatCandidates (computedLanguageNullable lookup rules) location e := by
  constructor
  · exact ⟨RuleRejectionRepeat.invariant2_candidate_has_nullable_repeat _ _ e,
      RuleRejectionRepeat.invariant2_nullableRepeat_candidate _ _ e⟩
  · rw [direct_rounds_after_fixed lookup (fun _ => none) rules n
      (direct_rounds_rule_count_fixed lookup (fun _ => none) rules) extra]
    rfl

#print axioms direct_rounds_rule_count_fixed
#print axioms invariant2_computed_language_repeat

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
