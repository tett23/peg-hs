/-!
The character sets of packages/peg-grammar/src/Peg/Grammar/Labels.hs (the
section "Character sets"): `CharSet`, `ranges`, `normalise`, `union`,
`intersect`, `minus`, `isEmpty` and `meets`, translated function by function.

A code point is a natural number. Haskell's `fromEnum` of a `Char` is in
`0 .. 0x10FFFF`; the model takes class ranges as such numbers (`HChar`), so
surrogate code points, which a Haskell `Char` can hold, are representable.
`sortOn fst` is a stable sort by the first component, which `sortFst`
(insertion from the right, before the first element whose start is not
smaller) also is, so the two give the same list.

The theorems show that every set the operations build from well-formed sets
is well formed (`RangesWF`: the ranges are in order, separated by at least
one code point, and within `0 .. 0x10FFFF`), and that every well-formed set
is in the finite list `charSetUniverse`. The label check of LabelCheckModel
uses this to bound the contexts it visits (LabelCheckTermination).
-/

namespace PegHs.LabelCheck

def maxCode : Nat := 0x10FFFF

-- A Haskell `Char`, as its code point.
structure HChar where
  val : Nat
  le : val ≤ maxCode

instance : BEq HChar := ⟨fun a b => a.val == b.val⟩
instance : Repr HChar := ⟨fun c _ => repr c.val⟩

structure CharSet where
  rs : List (Nat × Nat)
  eof : Bool
  deriving DecidableEq, Repr

def CharSet.none : CharSet := ⟨[], false⟩
def everything : CharSet := ⟨[(0, maxCode)], true⟩
def anyChar : CharSet := ⟨[(0, maxCode)], false⟩
def endOfInput : CharSet := ⟨[], true⟩

-- sortOn fst
def insertFst (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertFst x ys

def sortFst : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => insertFst x (sortFst xs)

-- merge of normalise
def mergeR : List (Nat × Nat) → List (Nat × Nat)
  | (a, b) :: (c, d) :: rest =>
    if c ≤ b + 1 then mergeR ((a, max b d) :: rest) else (a, b) :: mergeR ((c, d) :: rest)
  | rs => rs
termination_by l => l.length

def normalise (rs : List (Nat × Nat)) : List (Nat × Nat) := mergeR (sortFst rs)

def ranges (rs : List (HChar × HChar)) : CharSet :=
  ⟨normalise ((rs.filter (fun p => decide (p.1.val ≤ p.2.val))).map (fun p => (p.1.val, p.2.val))), false⟩

def single (c : Char) : CharSet := ⟨normalise [(c.toNat, c.toNat)], false⟩

def CharSet.union (a b : CharSet) : CharSet := ⟨normalise (a.rs ++ b.rs), a.eof || b.eof⟩

def interGo : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | (x1, y1) :: xs, (x2, y2) :: ys =>
    if y1 < x2 then interGo xs ((x2, y2) :: ys)
    else if y2 < x1 then interGo ((x1, y1) :: xs) ys
    else (max x1 x2, min y1 y2) ::
      (if y1 < y2 then interGo xs ((x2, y2) :: ys) else interGo ((x1, y1) :: xs) ys)
  | _, _ => []
termination_by xs ys => xs.length + ys.length

def CharSet.intersect (a b : CharSet) : CharSet := ⟨interGo a.rs b.rs, a.eof && b.eof⟩

def minusGo : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], _ => []
  | xs, [] => xs
  | (x1, y1) :: xs, (x2, y2) :: ys =>
    if y2 < x1 then minusGo ((x1, y1) :: xs) ys
    else if y1 < x2 then (x1, y1) :: minusGo xs ((x2, y2) :: ys)
    else (if x1 < x2 then [(x1, x2 - 1)] else []) ++
      (if y2 < y1 then minusGo ((y2 + 1, y1) :: xs) ys else minusGo xs ((x2, y2) :: ys))
termination_by xs ys => xs.length + ys.length

def CharSet.minus (a b : CharSet) : CharSet := ⟨minusGo a.rs b.rs, a.eof && !b.eof⟩

def CharSet.isEmpty (a : CharSet) : Bool := a.rs.isEmpty && !a.eof

def CharSet.meets (a b : CharSet) : Bool := !(a.intersect b).isEmpty

/-! ## Well-formed sets -/

def Gap (x y : Nat × Nat) : Prop := x.2 + 1 < y.1

def Bounded (x : Nat × Nat) : Prop := x.1 ≤ x.2 ∧ x.2 ≤ maxCode

structure RangesWF (l : List (Nat × Nat)) : Prop where
  pw : l.Pairwise Gap
  each : ∀ x ∈ l, Bounded x

def CharSet.WF (s : CharSet) : Prop := RangesWF s.rs

theorem rangesWF_nil : RangesWF [] := ⟨List.Pairwise.nil, by simp⟩

theorem rangesWF_cons {x : Nat × Nat} {l : List (Nat × Nat)} :
    RangesWF (x :: l) ↔ Bounded x ∧ (∀ y ∈ l, Gap x y) ∧ RangesWF l := by
  constructor
  · intro ⟨pw, each⟩
    rw [List.pairwise_cons] at pw
    exact ⟨each x (by simp), pw.1, pw.2, fun y hy => each y (by simp [hy])⟩
  · intro ⟨hb, hg, hw⟩
    refine ⟨List.pairwise_cons.2 ⟨hg, hw.pw⟩, ?_⟩
    intro y hy
    simp at hy
    rcases hy with rfl | hy
    · exact hb
    · exact hw.each y hy

-- sortFst sorts by the start and keeps the elements.
theorem mem_insertFst {x y : Nat × Nat} {l : List (Nat × Nat)} :
    y ∈ insertFst x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertFst]
  | cons z zs ih =>
    unfold insertFst
    split <;> simp [ih, or_left_comm]

theorem mem_sortFst {y : Nat × Nat} {l : List (Nat × Nat)} : y ∈ sortFst l ↔ y ∈ l := by
  induction l with
  | nil => simp [sortFst]
  | cons z zs ih => simp [sortFst, mem_insertFst, ih]

def StartSorted (l : List (Nat × Nat)) : Prop := l.Pairwise (fun x y => x.1 ≤ y.1)

theorem insertFst_sorted {x : Nat × Nat} {l : List (Nat × Nat)} (h : StartSorted l) :
    StartSorted (insertFst x l) := by
  induction l with
  | nil => simp [insertFst, StartSorted]
  | cons z zs ih =>
    unfold StartSorted at h
    rw [List.pairwise_cons] at h
    unfold insertFst
    split
    · rename_i hxz
      unfold StartSorted
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
      intro w hw
      simp at hw
      rcases hw with rfl | hw
      · exact hxz
      · exact Nat.le_trans hxz (h.1 w hw)
    · rename_i hxz
      unfold StartSorted
      refine List.pairwise_cons.2 ⟨?_, ih h.2⟩
      intro w hw
      rw [mem_insertFst] at hw
      rcases hw with rfl | hw
      · omega
      · exact h.1 w hw

theorem sortFst_sorted (l : List (Nat × Nat)) : StartSorted (sortFst l) := by
  induction l with
  | nil => simp [sortFst, StartSorted]
  | cons z zs ih => exact insertFst_sorted ih

-- The merge of sorted bounded ranges: the first range keeps its start and
-- may grow, and the rest is well formed after it.
theorem mergeR_spec : ∀ (l : List (Nat × Nat)) (a b : Nat) (rest : List (Nat × Nat)),
    l = (a, b) :: rest → StartSorted l → (∀ x ∈ l, Bounded x) →
    ∃ b' out, mergeR l = (a, b') :: out ∧ b ≤ b' ∧ b' ≤ maxCode ∧
      (∀ y ∈ out, b' + 1 < y.1) ∧ RangesWF out := by
  intro l
  induction l using mergeR.induct with
  | case1 a b c d rest hc ih =>
    intro a' b' rest' heq hs hb
    simp only [List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    unfold StartSorted at hs
    rw [List.pairwise_cons, List.pairwise_cons] at hs
    have hsorted : StartSorted ((a, max b d) :: rest) := by
      unfold StartSorted
      exact List.pairwise_cons.2 ⟨fun w hw => hs.1 w (by simp [hw]), hs.2.2⟩
    have hbd : ∀ x ∈ (a, max b d) :: rest, Bounded x := by
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · have h1 := hb (a, b) (by simp)
        have h2 := hb (c, d) (by simp)
        simp [Bounded] at h1 h2 ⊢
        omega
      · exact hb x (by simp [hx])
    obtain ⟨b'', out, h1, h2, h3, h4, h5⟩ := ih a (max b d) rest rfl hsorted hbd
    refine ⟨b'', out, ?_, by omega, h3, h4, h5⟩
    simp only [mergeR, hc, ↓reduceIte, h1]
  | case2 a b c d rest hc ih =>
    intro a' b' rest' heq hs hb
    simp only [List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    unfold StartSorted at hs
    rw [List.pairwise_cons] at hs
    obtain ⟨d', out, h1, h2, h3, h4, h5⟩ :=
      ih c d rest rfl hs.2 (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    have hab := hb (a, b) (by simp)
    have hcd := hb (c, d) (by simp)
    simp [Bounded] at hab hcd
    refine ⟨b, (c, d') :: out, ?_, Nat.le_refl _, hab.2, ?_, ?_⟩
    · simp only [mergeR, hc, ↓reduceIte, h1]
    · intro y hy
      simp at hy
      rcases hy with rfl | hy
      · simp; omega
      · have := h4 y hy; omega
    · refine rangesWF_cons.2 ⟨⟨by omega, h3⟩, fun y hy => h4 y hy, h5⟩
  | case3 rs hne =>
    intro a b rest heq hs hb
    subst heq
    cases rest with
    | nil =>
      have hab := hb (a, b) (by simp)
      exact ⟨b, [], by simp [mergeR], Nat.le_refl _, hab.2, by simp, rangesWF_nil⟩
    | cons y ys => exact absurd rfl (hne a b y.1 y.2 ys)

theorem normalise_wf (l : List (Nat × Nat)) (hb : ∀ x ∈ l, Bounded x) :
    RangesWF (normalise l) := by
  unfold normalise
  cases h : sortFst l with
  | nil => simp [mergeR, rangesWF_nil]
  | cons x rest =>
    have hs := sortFst_sorted l
    rw [h] at hs
    have hb' : ∀ y ∈ x :: rest, Bounded y := by
      intro y hy
      rw [← h, mem_sortFst] at hy
      exact hb y hy
    obtain ⟨b', out, h1, h2, h3, h4, h5⟩ := mergeR_spec (x :: rest) x.1 x.2 rest rfl hs hb'
    rw [h1]
    have hx := hb' x (by simp)
    exact rangesWF_cons.2 ⟨⟨by simp [Bounded] at hx; omega, h3⟩, fun y hy => h4 y hy, h5⟩

/-! ## The operations keep sets well formed -/

theorem everything_wf : everything.WF :=
  rangesWF_cons.2 ⟨⟨by simp, by simp⟩, by simp, rangesWF_nil⟩

theorem anyChar_wf : anyChar.WF :=
  rangesWF_cons.2 ⟨⟨by simp, by simp⟩, by simp, rangesWF_nil⟩

theorem none_wf : CharSet.none.WF := rangesWF_nil

theorem endOfInput_wf : endOfInput.WF := rangesWF_nil

theorem ranges_wf (rs : List (HChar × HChar)) : (ranges rs).WF := by
  apply normalise_wf
  intro x hx
  simp at hx
  obtain ⟨a, b, ⟨_, hab⟩, rfl⟩ := hx
  exact ⟨hab, b.le⟩

theorem single_wf (c : Char) : (single c).WF := by
  apply normalise_wf
  intro x hx
  simp at hx
  subst hx
  refine ⟨Nat.le_refl _, ?_⟩
  have h : c.val.toNat.isValidChar := c.valid
  unfold Nat.isValidChar at h
  change c.val.toNat ≤ 0x10FFFF
  omega

theorem union_wf {a b : CharSet} (ha : a.WF) (hb : b.WF) : (a.union b).WF := by
  apply normalise_wf
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha.each x h
  · exact hb.each x h

theorem interGo_mem : ∀ (xs ys : List (Nat × Nat)) (o : Nat × Nat), o ∈ interGo xs ys →
    ∃ x ∈ xs, ∃ y ∈ ys, o = (max x.1 y.1, min x.2 y.2) := by
  intro xs ys
  induction xs, ys using interGo.induct with
  | case1 x1 y1 xs x2 y2 ys h ih =>
    intro o ho
    simp only [interGo, h, ↓reduceIte] at ho
    obtain ⟨x, hx, y, hy, h1⟩ := ih o ho
    exact ⟨x, List.mem_cons_of_mem _ hx, y, hy, h1⟩
  | case2 x1 y1 xs x2 y2 ys h h' ih =>
    intro o ho
    simp only [interGo, h, h', ↓reduceIte] at ho
    obtain ⟨x, hx, y, hy, h1⟩ := ih o ho
    exact ⟨x, hx, y, List.mem_cons_of_mem _ hy, h1⟩
  | case3 x1 y1 xs x2 y2 ys h h' ih1 ih2 =>
    intro o ho
    simp only [interGo, h, h', ↓reduceIte, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact ⟨(x1, y1), by simp, (x2, y2), by simp, rfl⟩
    · split at ho
      · obtain ⟨x, hx, y, hy, h1⟩ := ih1 o ho
        exact ⟨x, List.mem_cons_of_mem _ hx, y, hy, h1⟩
      · obtain ⟨x, hx, y, hy, h1⟩ := ih2 o ho
        exact ⟨x, hx, y, List.mem_cons_of_mem _ hy, h1⟩
  | case4 xs ys hne =>
    intro o ho
    cases xs with
    | nil => simp [interGo] at ho
    | cons x xs' =>
      cases ys with
      | nil => simp [interGo] at ho
      | cons y ys' => exact absurd rfl (hne x.1 x.2 xs' y.1 y.2 ys' rfl)

theorem interGo_wf : ∀ (xs ys : List (Nat × Nat)), RangesWF xs → RangesWF ys →
    RangesWF (interGo xs ys) := by
  intro xs ys
  induction xs, ys using interGo.induct with
  | case1 x1 y1 xs x2 y2 ys h ih =>
    intro hx hy
    simp only [interGo, h, ↓reduceIte]
    exact ih (rangesWF_cons.1 hx).2.2 hy
  | case2 x1 y1 xs x2 y2 ys h h' ih =>
    intro hx hy
    simp only [interGo, h, h', ↓reduceIte]
    exact ih hx (rangesWF_cons.1 hy).2.2
  | case3 x1 y1 xs x2 y2 ys h h' ih1 ih2 =>
    intro hx hy
    simp only [interGo, h, h', ↓reduceIte]
    have hx' := rangesWF_cons.1 hx
    have hy' := rangesWF_cons.1 hy
    have hb1 := hx'.1
    have hb2 := hy'.1
    simp [Bounded] at hb1 hb2
    split
    · rename_i hlt
      refine rangesWF_cons.2 ⟨⟨by simp; omega, by simp; omega⟩, ?_, ih1 hx'.2.2 hy⟩
      intro o ho
      obtain ⟨x, hxm, y, _, rfl⟩ := interGo_mem _ _ o ho
      have := hx'.2.1 x hxm
      simp [Gap] at this ⊢
      omega
    · rename_i hlt
      refine rangesWF_cons.2 ⟨⟨by simp; omega, by simp; omega⟩, ?_, ih2 hx hy'.2.2⟩
      intro o ho
      obtain ⟨x, _, y, hym, rfl⟩ := interGo_mem _ _ o ho
      have := hy'.2.1 y hym
      simp [Gap] at this ⊢
      omega
  | case4 xs ys hne =>
    intro _ _
    cases xs with
    | nil => simp [interGo, rangesWF_nil]
    | cons x xs' =>
      cases ys with
      | nil => simp [interGo, rangesWF_nil]
      | cons y ys' => exact absurd rfl (hne x.1 x.2 xs' y.1 y.2 ys' rfl)

theorem intersect_wf {a b : CharSet} (ha : a.WF) (hb : b.WF) : (a.intersect b).WF :=
  interGo_wf a.rs b.rs ha hb

theorem minusGo_mem : ∀ (xs ys : List (Nat × Nat)) (o : Nat × Nat), (∀ x ∈ xs, x.1 ≤ x.2) →
    o ∈ minusGo xs ys → o.1 ≤ o.2 ∧ ∃ x ∈ xs, x.1 ≤ o.1 ∧ o.2 ≤ x.2 := by
  intro xs ys
  induction xs, ys using minusGo.induct with
  | case1 ys => intro o _ ho; simp [minusGo] at ho
  | case2 xs hne =>
    intro o hb ho
    cases xs with
    | nil => exact absurd rfl hne
    | cons x xs' =>
      simp only [minusGo] at ho
      exact ⟨hb o ho, o, ho, Nat.le_refl _, Nat.le_refl _⟩
  | case3 x1 y1 xs x2 y2 ys h ih =>
    intro o hb ho
    simp only [minusGo, h, ↓reduceIte] at ho
    exact ih o hb ho
  | case4 x1 y1 xs x2 y2 ys h h' ih =>
    intro o hb ho
    simp only [minusGo, h, h', ↓reduceIte, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact ⟨hb _ (by simp), _, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨h1, x, hx, h2⟩ := ih o (fun x hx => hb x (List.mem_cons_of_mem _ hx)) ho
      exact ⟨h1, x, List.mem_cons_of_mem _ hx, h2⟩
  | case5 x1 y1 xs x2 y2 ys h h' ih1 ih2 =>
    intro o hb ho
    simp only [minusGo, h, h', ↓reduceIte] at ho
    have hx1 := hb (x1, y1) (by simp)
    simp at hx1
    rcases List.mem_append.1 ho with ho | ho
    · split at ho
      · simp at ho
        subst ho
        exact ⟨by simp; omega, (x1, y1), by simp, by simp, by simp; omega⟩
      · simp at ho
    · split at ho
      · have hb' : ∀ x ∈ (y2 + 1, y1) :: xs, x.1 ≤ x.2 := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp; omega
          · exact hb x (List.mem_cons_of_mem _ hx)
        obtain ⟨h1, x, hx, h2⟩ := ih1 o hb' ho
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · refine ⟨h1, (x1, y1), by simp, ?_, ?_⟩ <;> simp at h2 ⊢ <;> omega
        · exact ⟨h1, x, List.mem_cons_of_mem _ hx, h2⟩
      · obtain ⟨h1, x, hx, h2⟩ := ih2 o (fun x hx => hb x (List.mem_cons_of_mem _ hx)) ho
        exact ⟨h1, x, List.mem_cons_of_mem _ hx, h2⟩

theorem minusGo_wf : ∀ (xs ys : List (Nat × Nat)), RangesWF xs → RangesWF ys →
    RangesWF (minusGo xs ys) := by
  intro xs ys
  induction xs, ys using minusGo.induct with
  | case1 ys => intro _ _; simp [minusGo, rangesWF_nil]
  | case2 xs hne =>
    intro hx _
    cases xs with
    | nil => exact absurd rfl hne
    | cons x xs' => simpa [minusGo] using hx
  | case3 x1 y1 xs x2 y2 ys h ih =>
    intro hx hy
    simp only [minusGo, h, ↓reduceIte]
    exact ih hx (rangesWF_cons.1 hy).2.2
  | case4 x1 y1 xs x2 y2 ys h h' ih =>
    intro hx hy
    simp only [minusGo, h, h', ↓reduceIte]
    have hx' := rangesWF_cons.1 hx
    refine rangesWF_cons.2 ⟨hx'.1, ?_, ih hx'.2.2 hy⟩
    intro o ho
    obtain ⟨_, x, hxm, h2, _⟩ := minusGo_mem _ _ o (fun x hx => (hx'.2.2.each x hx).1) ho
    have := hx'.2.1 x hxm
    simp [Gap] at this ⊢
    omega
  | case5 x1 y1 xs x2 y2 ys h h' ih1 ih2 =>
    intro hx hy
    simp only [minusGo, h, h', ↓reduceIte]
    have hx' := rangesWF_cons.1 hx
    have hy' := rangesWF_cons.1 hy
    have hb1 := hx'.1
    have hb2 := hy'.1
    simp [Bounded] at hb1 hb2
    -- the elements after the first part start after x2
    have hrest : RangesWF (if y2 < y1 then minusGo ((y2 + 1, y1) :: xs) ys
        else minusGo xs ((x2, y2) :: ys)) ∧
        ∀ o ∈ (if y2 < y1 then minusGo ((y2 + 1, y1) :: xs) ys
          else minusGo xs ((x2, y2) :: ys)), x2 < o.1 := by
      split
      · rename_i hlt
        have hnew : RangesWF ((y2 + 1, y1) :: xs) := by
          refine rangesWF_cons.2 ⟨⟨by simp; omega, by simp; omega⟩, ?_, hx'.2.2⟩
          intro y hy
          have := hx'.2.1 y hy
          simp [Gap] at this ⊢
          omega
        refine ⟨ih1 hnew hy'.2.2, ?_⟩
        intro o ho
        obtain ⟨_, x, hxm, h2, _⟩ := minusGo_mem _ _ o (fun x hx => (hnew.each x hx).1) ho
        simp only [List.mem_cons] at hxm
        rcases hxm with rfl | hxm
        · simp at h2; omega
        · have := hx'.2.1 x hxm
          simp [Gap] at this; omega
      · refine ⟨ih2 hx'.2.2 hy, ?_⟩
        intro o ho
        obtain ⟨_, x, hxm, h2, _⟩ := minusGo_mem _ _ o (fun x hx => (hx'.2.2.each x hx).1) ho
        have := hx'.2.1 x hxm
        simp [Gap] at this; omega
    split
    · rename_i hlt
      simp only [List.singleton_append]
      refine rangesWF_cons.2 ⟨⟨by simp; omega, by simp; omega⟩, ?_, hrest.1⟩
      intro o ho
      have := hrest.2 o ho
      simp [Gap]; omega
    · simpa using hrest.1

theorem minus_wf {a b : CharSet} (ha : a.WF) (hb : b.WF) : (a.minus b).WF :=
  minusGo_wf a.rs b.rs ha hb

/-! ## Finitely many well-formed sets -/

-- The lists of at most n elements of xs.
def listsUpTo {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap (fun x => (listsUpTo xs n).map (x :: ·))

theorem mem_listsUpTo {α : Type} (xs : List α) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (∀ x ∈ l, x ∈ xs) → l ∈ listsUpTo xs n := by
  intro n
  induction n with
  | zero => intro l hl _; cases l <;> simp_all [listsUpTo]
  | succ n ih =>
    intro l hl hm
    cases l with
    | nil => simp [listsUpTo]
    | cons y ys =>
      simp only [listsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
      right
      exact ⟨y, hm y (by simp), ys, ih ys (by simp at hl; omega) (fun x hx => hm x (by simp [hx])), rfl⟩

theorem rangesWF_length : ∀ (l : List (Nat × Nat)) (m : Nat), RangesWF l → (∀ x ∈ l, m ≤ x.1) →
    m ≤ maxCode + 1 → l.length + m ≤ maxCode + 1 := by
  intro l
  induction l with
  | nil => intro m _ _ h; simpa using h
  | cons x r ih =>
    intro m hw hm hle
    have hw' := rangesWF_cons.1 hw
    have hx := hm x (by simp)
    have hb := hw'.1
    simp [Bounded] at hb
    have := ih (x.1 + 1) hw'.2.2 (fun y hy => by have := hw'.2.1 y hy; simp [Gap] at this; omega)
      (by omega)
    simp
    omega

noncomputable def codePairs : List (Nat × Nat) :=
  (List.range (maxCode + 1)).flatMap (fun a => (List.range (maxCode + 1)).map (fun b => (a, b)))

noncomputable def charSetUniverse : List CharSet :=
  (listsUpTo codePairs (maxCode + 1)).flatMap (fun rs => [⟨rs, false⟩, ⟨rs, true⟩])

theorem wf_mem_universe {s : CharSet} (h : s.WF) : s ∈ charSetUniverse := by
  unfold charSetUniverse
  rw [List.mem_flatMap]
  refine ⟨s.rs, ?_, ?_⟩
  · apply mem_listsUpTo
    · have := rangesWF_length s.rs 0 h (by simp) (by simp)
      omega
    · intro x hx
      have := h.each x hx
      simp [Bounded] at this
      simp only [codePairs, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨x.1, by omega, x.2, by omega, rfl⟩
  · cases s with
    | mk rs eof => cases eof <;> simp

end PegHs.LabelCheck
