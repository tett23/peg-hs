import Lean.Elab.Tactic.Omega
-- PEG control operators used by the self-hosted grammar.
-- Predicate results are supplied as Bool values. This model omits rule calls,
-- repetition, recovery, lexical categories, actions, and input positions.
-- Theorems below do not establish equivalence with parseTops.
namespace PegVerification

inductive Expr where
  | char : Char → Expr
  | seq : Expr → Expr → Expr
  | choice : Expr → Expr → Expr
  | ahead : Expr → Expr
  | notAhead : Expr → Expr
  | eof : Expr
  | predicate : Bool → Expr
  | label : String → Expr → Expr
  deriving DecidableEq

abbrev Result := Except (Option String) (List Char)

def run : Expr → List Char → Result
  | .char _, [] => .error none
  | .char c, x :: xs => if x = c then .ok xs else .error none
  | .seq a b, xs => (run a xs).bind (run b)
  | .choice a b, xs => match run a xs with
      | .ok ys => .ok ys
      | .error none => run b xs
      | .error (some name) => .error (some name)
  | .ahead a, xs => match run a xs with
      | .ok _ => .ok xs
      | .error _ => .error none
  | .notAhead a, xs => match run a xs with
      | .ok _ => .error none
      | .error _ => .ok xs
  | .eof, [] => .ok []
  | .eof, _ :: _ => .error none
  | .predicate true, xs => .ok xs
  | .predicate false, _ => .error none
  | .label name a, xs => match run a xs with
      | .ok ys => .ok ys
      | .error none => .error (some name)
      | .error (some old) => .error (some old)

-- A relation independent of the evaluator, with failure as a first-class result.
inductive Eval : Expr → List Char → Result → Prop where
  | charOk {c xs} : Eval (.char c) (c :: xs) (.ok xs)
  | charEmpty {c} : Eval (.char c) [] (.error none)
  | charDifferent {c d xs} : d ≠ c → Eval (.char c) (d :: xs) (.error none)
  | seqOk {a b xs ys r} : Eval a xs (.ok ys) → Eval b ys r → Eval (.seq a b) xs r
  | seqFail {a b xs err} : Eval a xs (.error err) → Eval (.seq a b) xs (.error err)
  | choiceFirst {a b xs ys} : Eval a xs (.ok ys) → Eval (.choice a b) xs (.ok ys)
  | choiceSecond {a b xs r} : Eval a xs (.error none) → Eval b xs r → Eval (.choice a b) xs r
  | choiceThrow {a b xs name} : Eval a xs (.error (some name)) → Eval (.choice a b) xs (.error (some name))
  | aheadOk {a xs ys} : Eval a xs (.ok ys) → Eval (.ahead a) xs (.ok xs)
  | aheadFail {a xs err} : Eval a xs (.error err) → Eval (.ahead a) xs (.error none)
  | notAheadOk {a xs err} : Eval a xs (.error err) → Eval (.notAhead a) xs (.ok xs)
  | notAheadFail {a xs ys} : Eval a xs (.ok ys) → Eval (.notAhead a) xs (.error none)
  | eofOk : Eval .eof [] (.ok [])
  | eofFail {c xs} : Eval .eof (c :: xs) (.error none)
  | predicateOk {xs} : Eval (.predicate true) xs (.ok xs)
  | predicateFail {xs} : Eval (.predicate false) xs (.error none)
  | labelOk {name a xs ys} : Eval a xs (.ok ys) → Eval (.label name a) xs (.ok ys)
  | labelFail {name a xs} : Eval a xs (.error none) → Eval (.label name a) xs (.error (some name))
  | labelThrow {name a xs old} : Eval a xs (.error (some old)) → Eval (.label name a) xs (.error (some old))

theorem run_sound {e xs r} (h : Eval e xs r) : run e xs = r := by
  induction h with
  | charOk => simp [run]
  | charEmpty => simp [run]
  | charDifferent neq => simp [run, neq]
  | seqOk _ _ ih1 ih2 => simp [run, ih1, ih2, Except.bind]
  | seqFail _ ih => simp [run, ih, Except.bind]
  | choiceFirst _ ih => simp [run, ih]
  | choiceSecond _ _ ih1 ih2 => simp [run, ih1, ih2]
  | choiceThrow _ ih => simp [run, ih]
  | aheadOk _ ih => simp [run, ih]
  | aheadFail _ ih => simp [run, ih]
  | notAheadOk _ ih => simp [run, ih]
  | notAheadFail _ ih => simp [run, ih]
  | eofOk => simp [run]
  | eofFail => simp [run]
  | predicateOk => simp [run]
  | predicateFail => simp [run]
  | labelOk _ ih => simp [run, ih]
  | labelFail _ ih => simp [run, ih]
  | labelThrow _ ih => simp [run, ih]

theorem run_complete (e : Expr) (xs : List Char) : Eval e xs (run e xs) := by
  induction e generalizing xs with
  | char c =>
      cases xs with
      | nil => exact .charEmpty
      | cons d ds =>
          by_cases h : d = c
          · subst d; simpa [run] using (Eval.charOk (c := c) (xs := ds))
          · simpa [run, h] using (Eval.charDifferent (c := c) (d := d) (xs := ds) h)
  | seq a b iha ihb =>
      cases h : run a xs with
      | ok ys =>
          have ha : Eval a xs (.ok ys) := by simpa [h] using iha xs
          simpa [run, h, Except.bind] using (Eval.seqOk ha (ihb ys))
      | error err =>
          have ha : Eval a xs (.error err) := by simpa [h] using iha xs
          simpa [run, h, Except.bind] using (Eval.seqFail (b := b) ha)
  | choice a b iha ihb =>
      cases h : run a xs with
      | ok ys =>
          have ha : Eval a xs (.ok ys) := by simpa [h] using iha xs
          simpa [run, h] using (Eval.choiceFirst (b := b) ha)
      | error err =>
          cases err with
          | none =>
              have ha : Eval a xs (.error none) := by simpa [h] using iha xs
              simpa [run, h] using (Eval.choiceSecond ha (ihb xs))
          | some name =>
              have ha : Eval a xs (.error (some name)) := by simpa [h] using iha xs
              simpa [run, h] using (Eval.choiceThrow (b := b) ha)
  | ahead a iha =>
      cases h : run a xs with
      | ok ys =>
          have ha : Eval a xs (.ok ys) := by simpa [h] using iha xs
          simpa [run, h] using (Eval.aheadOk ha)
      | error err =>
          have ha : Eval a xs (.error err) := by simpa [h] using iha xs
          simpa [run, h] using (Eval.aheadFail ha)
  | notAhead a iha =>
      cases h : run a xs with
      | ok ys =>
          have ha : Eval a xs (.ok ys) := by simpa [h] using iha xs
          simpa [run, h] using (Eval.notAheadFail ha)
      | error err =>
          have ha : Eval a xs (.error err) := by simpa [h] using iha xs
          simpa [run, h] using (Eval.notAheadOk ha)
  | eof =>
      cases xs with
      | nil => exact .eofOk
      | cons c cs => exact .eofFail
  | predicate b =>
      cases b with
      | true => exact .predicateOk
      | false => exact .predicateFail
  | label name a iha =>
      cases h : run a xs with
      | ok ys =>
          have ha : Eval a xs (.ok ys) := by simpa [h] using iha xs
          simpa [run, h] using (Eval.labelOk (name := name) ha)
      | error err =>
          cases err with
          | none =>
              have ha : Eval a xs (.error none) := by simpa [h] using iha xs
              simpa [run, h] using (Eval.labelFail (name := name) ha)
          | some old =>
              have ha : Eval a xs (.error (some old)) := by simpa [h] using iha xs
              simpa [run, h] using (Eval.labelThrow (name := name) ha)

theorem invariant1_core_iff (e : Expr) (xs : List Char) (r : Result) :
    Eval e xs r ↔ run e xs = r := by
  constructor
  · exact run_sound
  · intro h; rw [← h]; exact run_complete e xs

-- The semantic predicate in Peg.hpeg tests d < 256 before increasing d.
def withinDepth (d : Nat) : Bool := d < 256

theorem invariant1_depth_boundary : withinDepth 255 = true ∧ withinDepth 256 = false := by
  decide

def prefixesAccepted (count : Nat) : Prop := ∀ d < count, withinDepth d = true

theorem invariant1_prefix_count (count : Nat) :
    prefixesAccepted count ↔ count ≤ 256 := by
  constructor
  · intro h
    by_cases within : count ≤ 256
    · exact within
    have beyond : 256 < count := by omega
    have accepted := h 256 beyond
    simp [withinDepth] at accepted
  · intro within d smaller
    simp [withinDepth]
    omega

theorem invariant1_256_257 :
    prefixesAccepted 256 ∧ ¬ prefixesAccepted 257 := by
  constructor
  · exact (invariant1_prefix_count 256).2 (by omega)
  · intro accepted
    have h := (invariant1_prefix_count 257).1 accepted
    omega

theorem invariant1_depth_exact (d : Nat) : withinDepth d = true ↔ d < 256 := by
  simp [withinDepth]

end PegVerification

#print axioms PegVerification.run_sound
#print axioms PegVerification.run_complete
#print axioms PegVerification.invariant1_core_iff
#print axioms PegVerification.invariant1_depth_boundary
#print axioms PegVerification.invariant1_prefix_count
#print axioms PegVerification.invariant1_256_257
#print axioms PegVerification.invariant1_depth_exact

-- Nested counterexamples for Runtime.Internal's choice, andP and labeledWith.
example : PegVerification.run (.choice (.label "inner" (.char 'a')) (.char 'b')) ['b'] =
    .error (some "inner") := by simp [PegVerification.run]
example : PegVerification.run (.ahead (.label "inner" (.char 'a'))) ['b'] =
    .error none := by simp [PegVerification.run]
example : PegVerification.run (.label "outer" (.label "inner" (.char 'a'))) ['b'] =
    .error (some "inner") := by simp [PegVerification.run]
