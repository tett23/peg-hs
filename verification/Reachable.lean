import Std

namespace PegHs.Reachable

-- Names in a finite Haskell rule list, its references and its roots are
-- enumerated as Fin n. A missing rule has an empty refs list. In the
-- resolveImports caller, duplicates are rejected before reachable runs.
-- The model records visited names in reverse order, while Haskell uses a Set.
private def go {n : Nat} (refs : Fin n → List (Fin n))
    (unseen seen pending : List (Fin n)) : List (Fin n) :=
  match pending with
  | [] => seen
  | name :: rest =>
    if _h : name ∈ unseen then
      go refs (unseen.erase name) (name :: seen) (refs name ++ rest)
    else
      go refs unseen seen rest
termination_by (unseen.length, pending.length)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.left
    rw [List.length_erase_of_mem _h]
    have hpos : 0 < unseen.length := List.length_pos_of_mem _h
    omega
  · apply Prod.Lex.right
    omega

def reachable {n : Nat} (refs : Fin n → List (Fin n))
    (roots : List (Fin n)) : List (Fin n) :=
  go refs (List.finRange n) [] roots

inductive Walk {n : Nat} (refs : Fin n → List (Fin n))
    (roots : List (Fin n)) : Fin n → Prop where
  | root {name} : name ∈ roots → Walk refs roots name
  | edge {src dst} : Walk refs roots src → dst ∈ refs src → Walk refs roots dst

private theorem go_sound {n : Nat} (refs : Fin n → List (Fin n))
    (roots unseen seen pending : List (Fin n))
    (seenSound : ∀ name ∈ seen, Walk refs roots name)
    (pendingSound : ∀ name ∈ pending, Walk refs roots name) :
    ∀ name ∈ go refs unseen seen pending, Walk refs roots name := by
  induction unseen, seen, pending using go.induct (refs := refs) with
  | case1 unseen seen =>
    simpa [go] using seenSound
  | case2 unseen seen name rest h ih =>
    have nameSound : Walk refs roots name := pendingSound name (by simp)
    simp only [go, dite_eq_left h]
    apply ih
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact nameSound
      · exact seenSound x hx
    · intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact Walk.edge nameSound hx
      · exact pendingSound x (by simp [hx])
  | case3 unseen seen name rest h ih =>
    simp only [go, dite_eq_right h]
    apply ih
    · exact seenSound
    · intro x hx
      exact pendingSound x (by simp [hx])

theorem invariant2_reachable_sound {n : Nat} (refs : Fin n → List (Fin n))
    (roots : List (Fin n)) (name : Fin n) :
    name ∈ reachable refs roots → Walk refs roots name := by
  intro h
  exact go_sound refs roots (List.finRange n) [] roots
    (by simp) (by intro x hx; exact Walk.root hx) name h

private theorem seen_iff_not_unseen {n : Nat}
    (seen unseen : List (Fin n))
    (cover : ∀ name, name ∈ seen ∨ name ∈ unseen)
    (disjoint : ∀ name, name ∈ seen → name ∉ unseen)
    (name : Fin n) :
    name ∈ seen ↔ name ∉ unseen := by
  constructor
  · exact disjoint name
  · intro absent
    rcases cover name with h | h
    · exact h
    · exact False.elim (absent h)

private theorem go_complete {n : Nat} (refs : Fin n → List (Fin n))
    (roots unseen seen pending : List (Fin n))
    (seenOrUnseen : ∀ x, x ∈ seen ∨ x ∈ unseen)
    (unseenNodup : unseen.Nodup)
    (disjoint : ∀ x, x ∈ seen → x ∉ unseen)
    (seenClosed : ∀ x ∈ seen, ∀ y ∈ refs x, y ∈ seen ∨ y ∈ pending)
    (rootsCovered : ∀ x ∈ roots, x ∈ seen ∨ x ∈ pending) :
    ∀ name, Walk refs roots name → name ∈ go refs unseen seen pending := by
  induction unseen, seen, pending using go.induct (refs := refs) with
  | case1 unseen seen =>
    have closed : ∀ x ∈ seen, ∀ y ∈ refs x, y ∈ seen := by
      intro x hx y hy
      rcases seenClosed x hx y hy with h | h
      · exact h
      · simp at h
    have covered : ∀ x ∈ roots, x ∈ seen := by
      intro x hx
      rcases rootsCovered x hx with h | h
      · exact h
      · simp at h
    intro x walk
    induction walk with
    | root hx => simpa [go] using covered _ hx
    | edge prev hy ih => simpa [go] using closed _ (by simpa [go] using ih) _ hy
  | case2 unseen seen x rest hx ih =>
    have newClosed : ∀ a ∈ x :: seen, ∀ b ∈ refs a,
        b ∈ x :: seen ∨ b ∈ refs x ++ rest := by
      intro a ha b hb
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inr (List.mem_append.mpr (Or.inl hb))
      · rcases seenClosed a ha b hb with hbSeen | hbPending
        · exact Or.inl (by simp [hbSeen])
        · simp only [List.mem_cons] at hbPending
          rcases hbPending with rfl | hbRest
          · exact Or.inl (by simp)
          · exact Or.inr (List.mem_append.mpr (Or.inr hbRest))
    have newCovered : ∀ a ∈ roots,
        a ∈ x :: seen ∨ a ∈ refs x ++ rest := by
      intro a ha
      rcases rootsCovered a ha with haSeen | haPending
      · exact Or.inl (by simp [haSeen])
      · simp only [List.mem_cons] at haPending
        rcases haPending with rfl | haRest
        · exact Or.inl (by simp)
        · exact Or.inr (List.mem_append.mpr (Or.inr haRest))
    have nextCoverage : ∀ a, a ∈ x :: seen ∨ a ∈ unseen.erase x := by
      intro a
      rcases seenOrUnseen a with haSeen | haUnseen
      · exact Or.inl (by simp [haSeen])
      · by_cases heq : a = x
        · exact Or.inl (by simp [heq])
        · exact Or.inr ((List.mem_erase_of_ne heq).mpr haUnseen)
    have nextDisjoint : ∀ a, a ∈ x :: seen → a ∉ unseen.erase x := by
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact unseenNodup.not_mem_erase
      · intro inErase
        exact disjoint a ha (List.mem_of_mem_erase inErase)
    simpa [go, hx] using ih nextCoverage (unseenNodup.erase x) nextDisjoint newClosed newCovered
  | case3 unseen seen x rest hx ih =>
    have xSeen : x ∈ seen :=
      (seen_iff_not_unseen seen unseen seenOrUnseen disjoint x).mpr hx
    have nextClosed : ∀ a ∈ seen, ∀ b ∈ refs a,
        b ∈ seen ∨ b ∈ rest := by
      intro a ha b hb
      rcases seenClosed a ha b hb with hbSeen | hbPending
      · exact Or.inl hbSeen
      · simp only [List.mem_cons] at hbPending
        rcases hbPending with rfl | hbRest
        · exact Or.inl xSeen
        · exact Or.inr hbRest
    have nextCovered : ∀ a ∈ roots, a ∈ seen ∨ a ∈ rest := by
      intro a ha
      rcases rootsCovered a ha with haSeen | haPending
      · exact Or.inl haSeen
      · simp only [List.mem_cons] at haPending
        rcases haPending with rfl | haRest
        · exact Or.inl xSeen
        · exact Or.inr haRest
    simpa [go, hx] using ih seenOrUnseen unseenNodup disjoint nextClosed nextCovered

theorem invariant2_reachable_complete {n : Nat}
    (refs : Fin n → List (Fin n)) (roots : List (Fin n)) (name : Fin n) :
    Walk refs roots name → name ∈ reachable refs roots := by
  intro h
  apply go_complete refs roots (List.finRange n) [] roots
  · intro x
    exact Or.inr (List.mem_finRange x)
  · exact List.nodup_finRange n
  · intro x hx; simp at hx
  · intro x hx; simp at hx
  · intro x hx; exact Or.inr hx
  · exact h

theorem invariant2_reachable_iff {n : Nat}
    (refs : Fin n → List (Fin n)) (roots : List (Fin n)) (name : Fin n) :
    name ∈ reachable refs roots ↔ Walk refs roots name := by
  exact ⟨invariant2_reachable_sound refs roots name,
    invariant2_reachable_complete refs roots name⟩

-- Invariant 2: empty, singleton, a cycle, and an undefined reference.
example : reachable (n := 0) (fun x => Fin.elim0 x) [] = [] := by
  simp [reachable, go, List.finRange]
example : reachable (n := 1) (fun _ => []) [0] = [0] := by
  simp [reachable, go, List.finRange]
example : reachable (n := 2) (fun x => if x = 0 then [1] else [0]) [0] = [1, 0] := by
  simp [reachable, go, List.finRange]
example : (1 : Fin 3) ∈
    reachable (fun x => if x = 0 then [1] else []) [0] := by
  simp [reachable, go, List.finRange]
example : (2 : Fin 3) ∉
    reachable (fun x => if x = 0 then [1] else []) [0] := by
  simp [reachable, go, List.finRange]

end PegHs.Reachable

#print axioms PegHs.Reachable.invariant2_reachable_iff
