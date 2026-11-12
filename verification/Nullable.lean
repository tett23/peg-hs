import Lean.Elab.Tactic.Omega

namespace Peg.Verification

inductive PositiveExpr (n : Nat) where
  | empty
  | nonempty
  | ref : Fin n → PositiveExpr n
  | both : PositiveExpr n → PositiveExpr n → PositiveExpr n
  | either : PositiveExpr n → PositiveExpr n → PositiveExpr n

def acceptsEmpty {n : Nat} (known : Fin n → Bool) : PositiveExpr n → Bool
  | .empty => true
  | .nonempty => false
  | .ref i => known i
  | .both a b => acceptsEmpty known a && acceptsEmpty known b
  | .either a b => acceptsEmpty known a || acceptsEmpty known b

def Included {n : Nat} (a b : Fin n → Bool) : Prop :=
  ∀ i, a i = true → b i = true

def next {n : Nat} (rules : Fin n → PositiveExpr n)
    (known : Fin n → Bool) : Fin n → Bool :=
  fun i => acceptsEmpty known (rules i)

def rounds {n : Nat} (rules : Fin n → PositiveExpr n) :
    Nat → Fin n → Bool
  | 0 => fun _ => false
  | k + 1 => next rules (rounds rules k)

private theorem acceptsEmpty_mono {n : Nat} (a b : Fin n → Bool)
    (hab : Included a b) (e : PositiveExpr n) :
    acceptsEmpty a e = true → acceptsEmpty b e = true := by
  induction e with
  | empty => simp [acceptsEmpty]
  | nonempty => simp [acceptsEmpty]
  | ref i => exact hab i
  | both x y ihx ihy =>
      intro h
      have parts := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨ihx parts.1, ihy parts.2⟩
  | either x y ihx ihy =>
      intro h
      have choice := Bool.or_eq_true_iff.mp h
      exact Bool.or_eq_true_iff.mpr (choice.elim (fun hx => Or.inl (ihx hx)) (fun hy => Or.inr (ihy hy)))

theorem invariant2_nullable_monotone {n : Nat}
    (rules : Fin n → PositiveExpr n) (a b : Fin n → Bool)
    (hab : Included a b) : Included (next rules a) (next rules b) := by
  intro i hi
  exact acceptsEmpty_mono a b hab (rules i) hi

theorem rounds_ascending {n : Nat} (rules : Fin n → PositiveExpr n) :
    ∀ k, Included (rounds rules k) (rounds rules (k + 1)) := by
  intro k
  induction k with
  | zero =>
      intro i h
      simp [rounds] at h
  | succ k ih =>
      exact invariant2_nullable_monotone rules (rounds rules k)
        (rounds rules (k + 1)) ih

theorem rounds_below_fixed {n : Nat} (rules : Fin n → PositiveExpr n)
    (fixed : Fin n → Bool) (hfixed : next rules fixed = fixed) :
    ∀ k, Included (rounds rules k) fixed := by
  intro k
  induction k with
  | zero =>
      intro i h
      simp [rounds] at h
  | succ k ih =>
      intro i hi
      rw [← hfixed]
      exact invariant2_nullable_monotone rules (rounds rules k) fixed ih i hi

theorem invariant2_nullable_least_fixed {n : Nat}
    (rules : Fin n → PositiveExpr n) (k : Nat)
    (stable : rounds rules (k + 1) = rounds rules k) :
    next rules (rounds rules k) = rounds rules k ∧
      ∀ fixed, next rules fixed = fixed → Included (rounds rules k) fixed := by
  constructor
  · exact stable
  · intro fixed hfixed
    exact rounds_below_fixed rules fixed hfixed k

theorem invariant2_nullable_stable_is_fixed {n : Nat}
    (rules : Fin n → PositiveExpr n) (k : Nat)
    (stable : rounds rules (k + 1) = rounds rules k) :
    next rules (rounds rules k) = rounds rules k := by
  exact stable

def knownCount {n : Nat} (known : Fin n → Bool) : Nat :=
  List.countP known (List.finRange n)

private theorem count_mono {n : Nat} (a b : Fin n → Bool)
    (xs : List (Fin n))
    (hab : ∀ i ∈ xs, a i = true → b i = true) :
    List.countP a xs ≤ List.countP b xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have tail := ih (by
        intro i mem yes
        exact hab i (by simp [mem]) yes)
      by_cases ha : a x = true
      · have hb := hab x (by simp) ha
        have ca : List.countP a (x :: xs) = List.countP a xs + 1 := by
          simp [ ha]
        have cb : List.countP b (x :: xs) = List.countP b xs + 1 := by
          simp [ hb]
        omega
      · have ca : List.countP a (x :: xs) = List.countP a xs := by
          simp [ha]
        have cb : List.countP b xs ≤ List.countP b (x :: xs) := by
          simp [List.countP_cons]
        omega

private theorem count_strict {n : Nat} (a b : Fin n → Bool)
    (xs : List (Fin n))
    (hab : ∀ i ∈ xs, a i = true → b i = true)
    (w : Fin n) (member : w ∈ xs) (aw : a w = false) (bw : b w = true) :
    List.countP a xs < List.countP b xs := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
      have tail := count_mono a b xs (by
        intro i mem yes
        exact hab i (by simp [mem]) yes)
      by_cases eq : w = x
      · subst w
        have ca : List.countP a (x :: xs) = List.countP a xs := by
          simp [ aw]
        have cb : List.countP b (x :: xs) = List.countP b xs + 1 := by
          simp [ bw]
        omega
      · have tailMember : w ∈ xs := by
          simpa [eq] using member
        have strict := ih (by
          intro i mem yes
          exact hab i (by simp [mem]) yes) tailMember
        by_cases ha : a x = true
        · have hb := hab x (by simp) ha
          have ca : List.countP a (x :: xs) = List.countP a xs + 1 := by
            simp [ ha]
          have cb : List.countP b (x :: xs) = List.countP b xs + 1 := by
            simp [ hb]
          omega
        · have ca : List.countP a (x :: xs) = List.countP a xs := by
            simp [ ha]
          have cb : List.countP b xs ≤ List.countP b (x :: xs) := by
            simp [List.countP_cons]
          omega

private theorem witness_of_included_ne {n : Nat} (a b : Fin n → Bool)
    (hab : Included a b) (ne : a ≠ b) :
    ∃ w, a w = false ∧ b w = true := by
  classical
  by_cases hex : ∃ w, a w = false ∧ b w = true
  · exact hex
  exfalso
  apply ne
  funext i
  cases ha : a i <;> cases hb : b i
  · rfl
  · exfalso
    apply hex
    exact ⟨i, ha, hb⟩
  · have impossible := hab i ha
    simp [hb] at impossible
  · rfl

private theorem count_rises {n : Nat} (rules : Fin n → PositiveExpr n)
    (k : Nat) (ne : rounds rules k ≠ rounds rules (k + 1)) :
    knownCount (rounds rules k) < knownCount (rounds rules (k + 1)) := by
  have inclusion := rounds_ascending rules k
  obtain ⟨w, aw, bw⟩ := witness_of_included_ne _ _ inclusion ne
  exact count_strict _ _ _ (by
    intro i _ yes
    exact inclusion i yes) w (List.mem_finRange w) aw bw

private theorem count_lower {n : Nat} (rules : Fin n → PositiveExpr n) :
    ∀ k, (∀ j < k, rounds rules j ≠ rounds rules (j + 1)) →
      k ≤ knownCount (rounds rules k) := by
  intro k
  induction k with
  | zero => intro _; omega
  | succ k ih =>
      intro never
      have prev := ih (by
        intro j hj
        exact never j (by omega))
      have rise := count_rises rules k (never k (by omega))
      omega

private theorem count_bound {n : Nat} (known : Fin n → Bool) :
    knownCount known ≤ n := by
  simpa [knownCount, List.length_finRange] using
    (List.countP_le_length (p := known) (l := List.finRange n))

theorem invariant2_nullable_stops {n : Nat}
    (rules : Fin n → PositiveExpr n) :
    ∃ k ≤ n, rounds rules (k + 1) = rounds rules k := by
  classical
  by_cases found : ∃ k ≤ n, rounds rules (k + 1) = rounds rules k
  · exact found
  · have never : ∀ j < n + 1, rounds rules j ≠ rounds rules (j + 1) := by
      intro j hj equal
      apply found
      exact ⟨j, by omega, equal.symm⟩
    have lower := count_lower rules (n + 1) never
    have upper := count_bound (rounds rules (n + 1))
    omega

#print axioms invariant2_nullable_monotone
#print axioms invariant2_nullable_least_fixed
#print axioms invariant2_nullable_stable_is_fixed
#print axioms invariant2_nullable_stops

end Peg.Verification
