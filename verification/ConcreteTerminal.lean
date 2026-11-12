import Std

namespace PegHs.ConcreteTerminal

inductive Terminal where
  | lit (chars : List Char)
  | cls (ranges : List (Char × Char))
  | any
  deriving DecidableEq, Repr

def classHas (ranges : List (Char × Char)) (c : Char) : Bool :=
  ranges.any fun (lo, hi) => decide (lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat)

def matchLiteral : List Char → List Char → Option (List Char)
  | [], xs => some xs
  | _ :: _, [] => none
  | c :: cs, x :: xs => if c == x then matchLiteral cs xs else none

def matchTerm : Terminal → List Char → Option (List Char)
  | .lit chars, xs => matchLiteral chars xs
  | .cls _ranges, [] => none
  | .cls ranges, c :: xs => if classHas ranges c then some xs else none
  | .any, [] => none
  | .any, _ :: xs => some xs

inductive Matches : Terminal → List Char → List Char → Prop where
  | lit (chars tail) : Matches (.lit chars) (chars ++ tail) tail
  | cls {ranges c tail} :
      (∃ lo hi, (lo, hi) ∈ ranges ∧ lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat) →
      Matches (.cls ranges) (c :: tail) tail
  | any (c tail) : Matches .any (c :: tail) tail

private theorem matchLiteral_iff (chars xs ys : List Char) :
    matchLiteral chars xs = some ys ↔ xs = chars ++ ys := by
  induction chars generalizing xs ys with
  | nil => simp [matchLiteral]
  | cons c cs ih =>
      cases xs with
      | nil => simp [matchLiteral]
      | cons x rest =>
          by_cases same : c = x
          · subst x
            simpa [matchLiteral] using ih rest ys
          · have different : x ≠ c := Ne.symm same
            simp [matchLiteral, same, different, List.cons.injEq]

private theorem classHas_iff (ranges : List (Char × Char)) (c : Char) :
    classHas ranges c = true ↔
      ∃ lo hi, (lo, hi) ∈ ranges ∧ lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat := by
  simp only [classHas, List.any_eq_true]
  constructor
  · rintro ⟨⟨lo, hi⟩, member, within⟩
    simp only [decide_eq_true_eq] at within
    exact ⟨lo, hi, member, within.1, within.2⟩
  · rintro ⟨lo, hi, member, lower, upper⟩
    exact ⟨(lo, hi), member, by simp [lower, upper]⟩

theorem invariant1_matchTerm_iff (term : Terminal) (xs ys : List Char) :
    matchTerm term xs = some ys ↔ Matches term xs ys := by
  cases term with
  | lit chars =>
      constructor
      · intro h
        have eq := (matchLiteral_iff chars xs ys).mp h
        subst xs
        exact .lit chars ys
      · intro h
        cases h with
        | lit => exact (matchLiteral_iff _ _ _).mpr rfl
  | cls ranges =>
      cases xs with
      | nil => simp [matchTerm]; intro h; cases h
      | cons c tail =>
          constructor
          · intro h
            have both : classHas ranges c = true ∧ tail = ys := by
              by_cases condition : classHas ranges c = true
              · simpa [matchTerm, condition] using h
              · simp [matchTerm, condition] at h
            have matched : Matches (.cls ranges) (c :: tail) tail :=
              .cls ((classHas_iff ranges c).mp both.1)
            simpa [both.2] using matched
          · intro h
            cases h with
            | cls member =>
                simp [matchTerm, (classHas_iff ranges c).mpr member]
  | any =>
      cases xs with
      | nil => simp [matchTerm]; intro h; cases h
      | cons c tail =>
          constructor
          · intro h
            simp [matchTerm] at h
            subst ys
            exact .any c tail
          · intro h
            cases h
            rfl

theorem invariant1_reject_iff (term : Terminal) (xs : List Char) :
    matchTerm term xs = none ↔ ¬∃ ys, Matches term xs ys := by
  constructor
  · intro rejected ⟨ys, matched⟩
    have accepted := (invariant1_matchTerm_iff term xs ys).mpr matched
    rw [rejected] at accepted
    contradiction
  · intro unmatched
    cases result : matchTerm term xs with
    | none => rfl
    | some ys =>
        exact False.elim (unmatched ⟨ys, (invariant1_matchTerm_iff term xs ys).mp result⟩)

-- Positions count Char elements. The parser's byte-offset representation is
-- outside this lexical model and requires a separate UTF-8 bridge.
def matchAt (term : Terminal) (input : List Char) (start : Nat) : Option Nat :=
  if start ≤ input.length then
    match matchTerm term (input.drop start) with
    | some tail => some (input.length - tail.length)
    | none => none
  else none

def MatchesAt (term : Terminal) (input : List Char) (start finish : Nat) : Prop :=
  start ≤ input.length ∧
    ∃ tail, Matches term (input.drop start) tail ∧
      finish = input.length - tail.length

theorem invariant1_matchAt_iff (term : Terminal) (input : List Char)
    (start finish : Nat) :
    matchAt term input start = some finish ↔ MatchesAt term input start finish := by
  unfold matchAt MatchesAt
  by_cases within : start ≤ input.length
  · simp only [within, true_and, ite_true]
    cases h : matchTerm term (input.drop start) with
    | none =>
        have rejected := (invariant1_reject_iff term (input.drop start)).mp h
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨other, otherMatched, _⟩
          exact False.elim (rejected ⟨other, otherMatched⟩)
    | some tail =>
        have matched := (invariant1_matchTerm_iff term (input.drop start) tail).mp h
        constructor
        · intro eq
          exact ⟨tail, matched, (Option.some.inj eq).symm⟩
        · rintro ⟨other, otherMatched, finishEq⟩
          have accepted := (invariant1_matchTerm_iff term (input.drop start) other).mpr otherMatched
          rw [h] at accepted
          cases accepted
          exact congrArg some finishEq.symm
  · simp [within]

theorem invariant1_matchAt_reject (term : Terminal) (input : List Char)
    (start : Nat) :
    matchAt term input start = none ↔ ¬∃ finish, MatchesAt term input start finish := by
  constructor
  · intro rejected ⟨finish, matched⟩
    have accepted := (invariant1_matchAt_iff term input start finish).mpr matched
    rw [rejected] at accepted
    contradiction
  · intro unmatched
    cases result : matchAt term input start with
    | none => rfl
    | some finish =>
        exact False.elim (unmatched ⟨finish,
          (invariant1_matchAt_iff term input start finish).mp result⟩)

private theorem matches_suffix {term xs ys} (h : Matches term xs ys) :
    ys.IsSuffix xs := by
  cases h with
  | lit chars tail => exact ⟨chars, rfl⟩
  | cls member => exact ⟨[_], rfl⟩
  | any c tail => exact ⟨[c], rfl⟩

theorem invariant1_matchAt_bounds {term input start finish}
    (h : matchAt term input start = some finish) :
    start ≤ finish ∧ finish ≤ input.length := by
  obtain ⟨within, tail, matched, finishEq⟩ :=
    (invariant1_matchAt_iff term input start finish).mp h
  have shorter := (matches_suffix matched).length_le
  rw [List.length_drop] at shorter
  omega

-- The Nat → Option Nat shape is the token oracle of RecursiveEval. A table
-- index must still be assigned to each Body.token occurrence separately.
def terminalOracle (term : Terminal) (input : List Char) (remaining : Nat) : Option Nat :=
  if remaining ≤ input.length then
    (matchAt term input (input.length - remaining)).map (input.length - ·)
  else none

def TerminalStep (term : Terminal) (input : List Char)
    (remaining rest : Nat) : Prop :=
  remaining ≤ input.length ∧
    ∃ finish, MatchesAt term input (input.length - remaining) finish ∧
      rest = input.length - finish

theorem invariant1_terminalOracle_iff (term : Terminal) (input : List Char)
    (remaining rest : Nat) :
    terminalOracle term input remaining = some rest ↔
      TerminalStep term input remaining rest := by
  unfold terminalOracle TerminalStep
  by_cases within : remaining ≤ input.length
  · simp only [within, true_and, ite_true]
    cases h : matchAt term input (input.length - remaining) with
    | none =>
        have rejected := (invariant1_matchAt_reject term input (input.length - remaining)).mp h
        constructor
        · intro impossible; cases impossible
        · rintro ⟨finish, matched, _⟩
          exact False.elim (rejected ⟨finish, matched⟩)
    | some finish =>
        have matched := (invariant1_matchAt_iff term input (input.length - remaining) finish).mp h
        constructor
        · intro equal
          exact ⟨finish, matched, (Option.some.inj equal).symm⟩
        · rintro ⟨other, otherMatched, restEq⟩
          have accepted :=
            (invariant1_matchAt_iff term input (input.length - remaining) other).mpr otherMatched
          rw [h] at accepted
          cases accepted
          exact congrArg some restEq.symm
  · simp [within]

theorem invariant1_terminalOracle_reject (term : Terminal) (input : List Char)
    (remaining : Nat) :
    terminalOracle term input remaining = none ↔
      ¬∃ rest, TerminalStep term input remaining rest := by
  constructor
  · intro rejected ⟨rest, matched⟩
    have accepted := (invariant1_terminalOracle_iff term input remaining rest).mpr matched
    rw [rejected] at accepted
    contradiction
  · intro unmatched
    cases result : terminalOracle term input remaining with
    | none => rfl
    | some rest =>
        exact False.elim (unmatched ⟨rest,
          (invariant1_terminalOracle_iff term input remaining rest).mp result⟩)

-- Empty, newline, multi-character literal, inclusive class, and any-char boundaries.
example : matchTerm (.lit ['\n']) ['\n', 'x'] = some ['x'] := by rfl
example : matchTerm (.lit ['\n']) ['x'] = none := by rfl
example : matchTerm (.lit ['a', 'b']) ['a'] = none := by rfl
example : matchTerm (.lit []) ['x'] = some ['x'] := by rfl
example : matchTerm (.cls [('0', '9')]) ['0', 'x'] = some ['x'] := by rfl
example : matchTerm (.cls [('0', '9')]) [':'] = none := by rfl
example : matchTerm .any [] = none := by rfl
example : matchTerm .any ['\n'] = some [] := by rfl
example : matchAt (.lit ['\n']) ['x', '\n', 'y'] 1 = some 2 := by rfl
example : matchAt (.lit ['\n']) ['x', '\n', 'y'] 0 = none := by rfl
example : matchAt .any ['x'] 2 = none := by rfl
example : terminalOracle (.lit ['\n']) ['x', '\n', 'y'] 2 = some 1 := by rfl
example : terminalOracle (.lit ['\n']) ['x', '\n', 'y'] 3 = none := by rfl

#print axioms invariant1_matchTerm_iff
#print axioms invariant1_reject_iff
#print axioms invariant1_matchAt_iff
#print axioms invariant1_matchAt_reject
#print axioms invariant1_matchAt_bounds
#print axioms invariant1_terminalOracle_iff
#print axioms invariant1_terminalOracle_reject

end PegHs.ConcreteTerminal
