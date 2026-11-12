import AssembleValidation

namespace PegHs.AssembleValidation

private theorem repeatedGo_iff [DecidableEq α] (x : α) (xs seen : List α) :
    x ∈ repeated.go seen xs ↔ 2 ≤ xs.count x + (if x ∈ seen then 1 else 0) ∧ x ∈ xs := by
  induction xs generalizing seen with
  | nil => simp [repeated.go]
  | cons a xs ih =>
    by_cases eq : a = x
    · subst a
      by_cases mem : x ∈ seen <;>
        simp [repeated.go, ih, mem] <;>
        grind [List.count_pos_iff]
    · have rev := Ne.symm eq
      by_cases mem : a ∈ seen <;> by_cases prior : x ∈ seen <;>
        simp_all [repeated.go]

theorem invariant2_repeated_iff [DecidableEq α] (x : α) (xs : List α) :
    x ∈ repeated xs ↔ 2 ≤ xs.count x := by
  simp only [repeated, repeatedGo_iff, List.not_mem_nil, ite_false, Nat.add_zero]
  grind [List.count_pos_iff]

private theorem countSelected (ds : List (String × String)) (names : List String) (name : String)
    (selected : name ∈ names) :
    ((ds.filter (fun d => names.contains d.1)).map (·.1)).count name =
      (ds.filter (fun d => d.1 == name)).length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases same : d.1 = name
    · simpa [same, selected] using ih
    · by_cases keep : d.1 ∈ names <;> simpa [same, keep] using ih

theorem invariant2_duplicate_directive (tops : List Top) (p : Predicates) (name : String)
    (selected : name ∈ ["module", "start", "env", "tabstop", "syntax", "deriving", "library"])
    (twice : 2 ≤ ((directives tops).filter (fun d => d.1 == name)).length) :
    diagnostic ⟨.duplicateDirective, name⟩ ∈ errors tops p := by
  have witness := (invariant2_repeated_iff name _).2
    ((countSelected (directives tops) _ name selected).symm ▸ twice)
  have emitted := (List.mem_map (f := fun n => Violation.mk .duplicateDirective n)).mpr ⟨name, witness, rfl⟩
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

#print axioms invariant2_duplicate_directive
end PegHs.AssembleValidation
