import Pipeline

namespace PegHs.RuleRejection

-- The location is projected to Nat because only list nonemptiness matters.
-- Haskell's full Loc and the order within a nonempty list remain outside scope.
abbrev Diagnostic := Nat × String
abbrev Diagnostics := List String

private def order (a b : Diagnostic) : Bool := decide (a.1 ≤ b.1)

def sortErrors (errors : List Diagnostic) : List Diagnostic :=
  errors.mergeSort order

-- `before` denotes arity, entry, and reachability errors. `after` denotes
-- the remaining checks in the Haskell `errors` list, in their original order.
def allErrors (undefined repetition before after : List Diagnostic) : List Diagnostic :=
  undefined ++ before ++ repetition ++ after

def checkRoot (undefined repetition : List Diagnostic)
    (before after : List Diagnostic := []) : Except Diagnostics Unit :=
  match sortErrors (allErrors undefined repetition before after) with
  | [] => .ok ()
  | ds => .error (ds.map Prod.snd)

def undefinedRef (location : Nat) (name : String) : Diagnostic :=
  (location, "undefined rule " ++ name)

def nullableRepeat (location : Nat) (canMatchEmpty : Bool) : List Diagnostic :=
  if canMatchEmpty then
    [(location, "the repeated expression can match the empty string, which would loop forever")]
  else []

def undefinedFromRefs (refs : List (Nat × String)) (defined : List String) :
    List Diagnostic :=
  refs.flatMap fun (location, name) =>
    if name ∈ defined then [] else [undefinedRef location name]

def repetitionFromNullable (repeats : List (Nat × Bool)) : List Diagnostic :=
  repeats.flatMap fun (location, canMatchEmpty) => nullableRepeat location canMatchEmpty

theorem invariant2_missingRefProducesError
    (refs : List (Nat × String)) (defined : List String)
    (location : Nat) (name : String)
    (present : (location, name) ∈ refs) (missing : name ∉ defined) :
    undefinedRef location name ∈ undefinedFromRefs refs defined := by
  apply List.mem_flatMap.mpr
  exact ⟨(location, name), present, by simp [missing]⟩

theorem invariant2_nullableRepeatProducesError
    (repeats : List (Nat × Bool)) (location : Nat)
    (present : (location, true) ∈ repeats) :
    nullableRepeat location true ⊆ repetitionFromNullable repeats := by
  intro diagnostic hd
  apply List.mem_flatMap.mpr
  exact ⟨(location, true), present, hd⟩

private theorem sorted_has {errors : List Diagnostic} {d : Diagnostic}
    (h : d ∈ errors) : d ∈ sortErrors errors := by
  exact (List.mergeSort_perm errors order).mem_iff.mpr h

private theorem rejects_of_mem (undefined repetition before after : List Diagnostic)
    (d : Diagnostic) (h : d ∈ allErrors undefined repetition before after) :
    ∃ ds, ds ≠ [] ∧ checkRoot undefined repetition before after = .error ds := by
  have hs : d ∈ sortErrors (allErrors undefined repetition before after) := sorted_has h
  unfold checkRoot
  cases sorted : sortErrors (allErrors undefined repetition before after) with
  | nil =>
    rw [sorted] at hs
    simp at hs
  | cons first rest =>
    refine ⟨(first :: rest).map Prod.snd, by simp, ?_⟩
    rfl

theorem invariant2_undefinedRefRejected (undefined repetition before after : List Diagnostic)
    (location : Nat) (name : String)
    (h : undefinedRef location name ∈ undefined) :
    ∃ ds, ds ≠ [] ∧ checkRoot undefined repetition before after = .error ds := by
  apply rejects_of_mem undefined repetition before after (undefinedRef location name)
  simp [allErrors, h]

theorem invariant2_nullableRepeatRejected (undefined repetition before after : List Diagnostic)
    (location : Nat)
    (h : nullableRepeat location true ⊆ repetition) :
    ∃ ds, ds ≠ [] ∧ checkRoot undefined repetition before after = .error ds := by
  apply rejects_of_mem undefined repetition before after
    (location, "the repeated expression can match the empty string, which would loop forever")
  have hm : (location, "the repeated expression can match the empty string, which would loop forever") ∈ repetition :=
    h (by simp [nullableRepeat])
  simp [allErrors, hm]

-- The actual reached grammar supplies the four error groups to `check`.
-- A template note must preserve a nonempty diagnostic list.
theorem invariant2_rejectionReachesVisible {G : Type}
    (parsed g0 g : G)
    (resolve expand : G → Except Diagnostics G)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G))
    (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (undefined repetition before after : List Diagnostic)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hn : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (rejected : (∃ location name, undefinedRef location name ∈ undefined) ∨
      (∃ location, nullableRepeat location true ⊆ repetition)) :
    ∃ ds, ds ≠ [] ∧
      PegHs.Pipeline.visible
        (PegHs.Pipeline.pipeline (.ok parsed) resolve expand
          (fun _ => checkRoot undefined repetition before after)
          notes strip warningFor generate) = .error ds := by
  have outcome : ∃ raw, raw ≠ [] ∧
      checkRoot undefined repetition before after = .error raw := by
    rcases rejected with ⟨location, name, h⟩ | ⟨location, h⟩
    · exact invariant2_undefinedRefRejected undefined repetition before after location name h
    · exact invariant2_nullableRepeatRejected undefined repetition before after location h
  obtain ⟨raw, nonempty, hc⟩ := outcome
  refine ⟨notes g0 raw, hn raw nonempty, ?_⟩
  exact PegHs.Pipeline.invariant2_checkFailure parsed g0 g raw resolve expand
    (fun _ => checkRoot undefined repetition before after) notes strip warningFor generate hr he hc

theorem invariant2_missingRefVisible {G : Type}
    (parsed g0 g : G)
    (resolve expand : G → Except Diagnostics G)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (refs : List (Nat × String)) (defined : List String)
    (repetition before after : List Diagnostic)
    (location : Nat) (name : String)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hn : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (present : (location, name) ∈ refs) (missing : name ∉ defined) :
    ∃ ds, ds ≠ [] ∧
      PegHs.Pipeline.visible
        (PegHs.Pipeline.pipeline (.ok parsed) resolve expand
          (fun _ => checkRoot (undefinedFromRefs refs defined) repetition before after)
          notes strip warningFor generate) = .error ds := by
  apply invariant2_rejectionReachesVisible parsed g0 g resolve expand notes strip warningFor
    generate (undefinedFromRefs refs defined) repetition before after hr he hn
  exact Or.inl ⟨location, name,
    invariant2_missingRefProducesError refs defined location name present missing⟩

theorem invariant2_nullableRepeatVisible {G : Type}
    (parsed g0 g : G)
    (resolve expand : G → Except Diagnostics G)
    (notes : G → Diagnostics → Diagnostics)
    (strip : Option (G → G)) (warningFor : G → G → Diagnostics)
    (generate : G → Except Diagnostics String)
    (undefined before after : List Diagnostic)
    (repeats : List (Nat × Bool)) (location : Nat)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hn : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (present : (location, true) ∈ repeats) :
    ∃ ds, ds ≠ [] ∧
      PegHs.Pipeline.visible
        (PegHs.Pipeline.pipeline (.ok parsed) resolve expand
          (fun _ => checkRoot undefined (repetitionFromNullable repeats) before after)
          notes strip warningFor generate) = .error ds := by
  apply invariant2_rejectionReachesVisible parsed g0 g resolve expand notes strip warningFor
    generate undefined (repetitionFromNullable repeats) before after hr he hn
  exact Or.inr ⟨location, invariant2_nullableRepeatProducesError repeats location present⟩

-- Invariant 2: an undefined reference or nullable repetition cannot succeed.
example : ∃ ds, ds ≠ [] ∧ checkRoot [undefinedRef 3 "Missing"] [] = .error ds := by
  exact invariant2_undefinedRefRejected _ _ _ _ 3 "Missing" (by simp)
example : ∃ ds, ds ≠ [] ∧ checkRoot [] (nullableRepeat 3 true) = .error ds := by
  exact invariant2_nullableRepeatRejected _ _ _ _ 3 (by simp [nullableRepeat])

end PegHs.RuleRejection

#print axioms PegHs.RuleRejection.invariant2_undefinedRefRejected
#print axioms PegHs.RuleRejection.invariant2_nullableRepeatRejected
#print axioms PegHs.RuleRejection.invariant2_rejectionReachesVisible
#print axioms PegHs.RuleRejection.invariant2_missingRefVisible
#print axioms PegHs.RuleRejection.invariant2_nullableRepeatVisible
