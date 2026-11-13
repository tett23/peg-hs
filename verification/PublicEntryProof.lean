import TranslatedEntry

namespace PegHs.PublicParsing

-- The start-rule result and the diagnostic formatter are the two inputs here.
-- The runtime position is measured in UTF-8 bytes, as is ctxLen.
theorem invariant1_translated_entry {T} (bytes : Nat) (r : StartResult T)
    (d : Failure → String) :
    translatedPublic d (translatedRuntime bytes r) = entry bytes r d := by
  cases r with
  | ok j x => by_cases endPos : j = bytes <;> simp [translatedRuntime, translatedPublic, entry, endPos]
  | fail => rfl
  | throwLabel => rfl

theorem invariant1_translated_grammar {T G} (bytes : Nat) (start : StartResult T)
    (d : Failure → String) (assemble : T → Except PegHs.Pipeline.Diagnostics G) (g : G) :
    translatedGrammar bytes start d assemble = .ok g ↔
      ∃ tops, start = .ok bytes tops ∧ assemble tops = .ok g := by
  unfold translatedGrammar
  rw [invariant1_translated_entry]
  cases start with
  | ok pos tops =>
    by_cases full : pos = bytes <;> simp [entry, full, Except.bind]
  | fail => simp [entry, Except.bind]
  | throwLabel => simp [entry, Except.bind]

theorem invariant1_translated_grammar_assembled {T M G} (bytes : Nat) (start : StartResult T)
    (d : Failure → String) (errors : T → List String) (name : T → Option M)
    (build : T → M → G) (missing : String) (sortErrors : List String → List String) (g : G) :
    translatedGrammar bytes start d (fun t =>
      translatedAssemble (errors t) (name t) (build t) missing sortErrors) = .ok g ↔
      ∃ t m, start = .ok bytes t ∧ errors t = [] ∧ name t = some m ∧ build t m = g := by
  rw [invariant1_translated_grammar]
  constructor
  · rintro ⟨t, hs, ha⟩
    cases he : errors t with
    | cons e es => simp [translatedAssemble, he] at ha
    | nil =>
      cases hn : name t with
      | none => simp [translatedAssemble, he, hn] at ha
      | some m => exact ⟨t, m, hs, he, hn, by simpa [translatedAssemble, he, hn] using ha⟩
  · rintro ⟨t, m, hs, he, hn, rfl⟩
    exact ⟨t, hs, by simp [translatedAssemble, he, hn]⟩

theorem invariant2_assembly_diagnostics {T M G} (bytes : Nat) (tops : T) (d : Failure → String)
    (errors : List String) (name : Option M) (build : M → G) (missing : String)
    (sortErrors : List String → List String) (ds : List String) :
    translatedGrammar bytes (.ok bytes tops) d (fun _ =>
      translatedAssemble errors name build missing sortErrors) = .error ds ↔
      (errors = [] ∧ name = none ∧ ds = [missing]) ∨
      (errors ≠ [] ∧ ds = sortErrors errors) := by
  cases errors <;> cases name <;>
    simp [translatedGrammar, translatedRuntime, translatedPublic, translatedAssemble, Except.bind,
      eq_comm]

-- GHC.Internal.Data.OldList.merge takes the right head exactly for GT.
private def mergeRuns {A} (greater : A → A → Bool) : List A → List A → List A
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if greater x y then y :: mergeRuns greater (x :: xs) ys
    else x :: mergeRuns greater xs (y :: ys)
termination_by xs ys => xs.length + ys.length

theorem invariant2_mergeRuns_length {A} (greater : A → A → Bool) (xs ys : List A) :
    (mergeRuns greater xs ys).length = xs.length + ys.length := by
  induction xs, ys using mergeRuns.induct greater with
  | case1 | case2 => simp [mergeRuns]
  | case3 | case4 =>
    rw [mergeRuns]
    split <;> simp_all <;> omega

#print axioms invariant2_mergeRuns_length

private def mergePairs {A} (greater : A → A → Bool) : List (List A) → List (List A)
  | a :: b :: xs => mergeRuns greater a b :: mergePairs greater xs
  | xs => xs

theorem invariant2_mergePairs_length {A} (greater : A → A → Bool) (runs : List (List A)) :
    (mergePairs greater runs).flatten.length = runs.flatten.length := by
  induction runs using mergePairs.induct with
  | case1 => simp_all [mergePairs, invariant2_mergeRuns_length, Nat.add_assoc]
  | case2 xs h => cases xs with
    | nil => rfl
    | cons a tail => cases tail with
      | nil => rfl
      | cons b rest => exact False.elim (h a b rest rfl)

#print axioms invariant2_mergePairs_length

private theorem mergePairs_count_le {A} (gt : A → A → Bool) (runs : List (List A)) :
    (mergePairs gt runs).length ≤ runs.length := by
  induction runs using mergePairs.induct with
  | case1 => simp_all [mergePairs] <;> omega
  | case2 xs h => cases xs with
    | nil => exact Nat.le_refl _
    | cons a tail => cases tail with
      | nil => exact Nat.le_refl _
      | cons b rest => exact False.elim (h a b rest rfl)

private def mergeAllRuns {A} (gt : A → A → Bool) : List (List A) → List A
  | [] => []
  | [run] => run
  | a :: b :: rest => mergeAllRuns gt (mergePairs gt (a :: b :: rest))
termination_by runs => runs.length
decreasing_by
  simp only [mergePairs, List.length_cons]
  have := mergePairs_count_le gt rest
  omega

theorem invariant2_mergeAll_length {A} (gt : A → A → Bool) (runs : List (List A)) :
    (mergeAllRuns gt runs).length = runs.flatten.length := by
  induction runs using mergeAllRuns.induct gt with
  | case1 | case2 => simp [mergeAllRuns]
  | case3 a b rest ih =>
    rw [mergeAllRuns, ih, invariant2_mergePairs_length]

#print axioms invariant2_mergeAll_length

-- Data.List.sortOn decorates each element with its key, sorts the pairs,
-- and projects the original elements. Only the length matters to rejection.
theorem invariant2_sortOn_length {A K} (key : A → K)
    (sortPairs : List (K × A) → List (K × A))
    (perm : ∀ pairs, (sortPairs pairs).Perm pairs) (xs : List A) :
    ((sortPairs (xs.map fun x => (key x, x))).map Prod.snd).length = xs.length := by
  rw [List.length_map, (perm _).length_eq, List.length_map]

theorem invariant2_sortOn_mergeSort_length {A K} (key : A → K) (le : K → K → Bool)
    (xs : List A) :
    (((xs.map fun x => (key x, x)).mergeSort (fun a b => le a.1 b.1)).map Prod.snd).length
      = xs.length :=
  invariant2_sortOn_length key _ (fun _ => List.mergeSort_perm ..) xs

#print axioms invariant2_sortOn_mergeSort_length
#print axioms invariant2_sortOn_length

theorem invariant2_sorted_assembly_error_nonempty {T M G} (bytes : Nat) (tops : T)
    (d : Failure → String) (errors : List String) (name : Option M) (build : M → G)
    (missing : String) (sortErrors : List String → List String)
    (length_sort : ∀ es, (sortErrors es).length = es.length) (ds : List String)
    (rejected : translatedGrammar bytes (.ok bytes tops) d (fun _ =>
      translatedAssemble errors name build missing sortErrors) = .error ds) :
    ds ≠ [] := by
  rcases (invariant2_assembly_diagnostics ..).mp rejected with ⟨_, _, rfl⟩ | ⟨hne, rfl⟩
  · simp
  · intro hempty
    apply hne
    apply List.length_eq_zero_iff.mp
    simpa only [length_sort, List.length_nil] using congrArg List.length hempty

#print axioms invariant2_sorted_assembly_error_nonempty

theorem invariant2_translated_grammar_error_nonempty {T M G} (bytes : Nat)
    (start : StartResult T) (d : Failure → String) (errors : T → List String)
    (name : T → Option M) (build : T → M → G) (missing : String)
    (sortErrors : List String → List String)
    (length_sort : ∀ es, (sortErrors es).length = es.length) (ds : List String)
    (rejected : translatedGrammar bytes start d (fun t =>
      translatedAssemble (errors t) (name t) (build t) missing
        sortErrors) = .error ds) : ds ≠ [] := by
  cases start with
  | ok pos tops =>
    by_cases full : pos = bytes
    · subst pos
      exact invariant2_sorted_assembly_error_nonempty bytes tops d (errors tops) (name tops)
        (build tops) missing sortErrors length_sort ds (by
          simpa [translatedGrammar, translatedRuntime, translatedPublic, Except.bind] using rejected)
    · simp [translatedGrammar, translatedRuntime, translatedPublic, Except.bind, full] at rejected
      subst ds
      simp
  | fail | throwLabel =>
    simp [translatedGrammar, translatedRuntime, translatedPublic, Except.bind] at rejected
    subst ds
    simp

#print axioms invariant2_translated_grammar_error_nonempty

open PegHs.Pipeline in
theorem invariant2_rejected_grammar_visible {T M G} (bytes : Nat) (start : StartResult T)
    (d : Failure → String) (errors : T → List String) (name : T → Option M)
    (build : T → M → G) (missing : String) (sortErrors : List String → List String)
    (length_sort : ∀ es, (sortErrors es).length = es.length)
    (resolve expand : G → Except Diagnostics G) (check : G → Except Diagnostics Unit)
    (notes : G → Diagnostics → Diagnostics) (strip : Option (G → G))
    (warnings : G → G → Diagnostics) (generate : G → Except Diagnostics String)
    (invalid : ¬ ∃ t m, start = .ok bytes t ∧ errors t = [] ∧ name t = some m) :
    let parsed := translatedGrammar bytes start d (fun t =>
      translatedAssemble (errors t) (name t) (build t) missing sortErrors)
    ∃ msg rest, visible (pipeline parsed resolve expand check notes strip warnings generate)
      = .error (msg :: rest) := by
  dsimp only
  cases hp : translatedGrammar bytes start d (fun t =>
      translatedAssemble (errors t) (name t) (build t) missing sortErrors) with
  | ok g =>
    obtain ⟨t, m, hs, he, hn, _⟩ := (invariant1_translated_grammar_assembled ..).mp hp
    exact False.elim (invalid ⟨t, m, hs, he, hn⟩)
  | error ds =>
    have nonempty := invariant2_translated_grammar_error_nonempty bytes start d errors name
      build missing sortErrors length_sort ds hp
    cases ds with
    | nil => exact False.elim (nonempty rfl)
    | cons msg rest => exact ⟨msg, rest, rfl⟩

#print axioms invariant2_rejected_grammar_visible

theorem invariant1_translated_module_selection {T L G} (bytes : Nat) (start : StartResult T)
    (d : Failure → String) (errors : T → List String) (library : T → Option L)
    (single : T → String → Option (L × String)) (build : T → (L × String) → G)
    (missing : String) (sortErrors : List String → List String) (g : G) :
    translatedGrammar bytes start d (fun t => translatedAssemble (errors t)
      (translatedModuleName (library t) (single t)) (build t) missing sortErrors) = .ok g ↔
      ∃ t, start = .ok bytes t ∧ errors t = [] ∧
        ((∃ l, library t = some l ∧ build t (l, "") = g) ∨
         (library t = none ∧ ∃ m, single t "module" = some m ∧ build t m = g)) := by
  rw [invariant1_translated_grammar_assembled]
  constructor
  · rintro ⟨t, m, hs, he, hm, hg⟩
    refine ⟨t, hs, he, ?_⟩
    cases hl : library t with
    | none => exact Or.inr ⟨rfl, m, by simpa [translatedModuleName, hl] using hm, hg⟩
    | some l =>
      have eq : (l, "") = m := by simpa [translatedModuleName, hl] using hm
      exact Or.inl ⟨l, rfl, eq ▸ hg⟩
  · rintro ⟨t, hs, he, lib | mod⟩
    · obtain ⟨l, hl, hg⟩ := lib
      exact ⟨t, _, hs, he, by simp [translatedModuleName, hl], hg⟩
    · obtain ⟨hl, m, hm, hg⟩ := mod
      exact ⟨t, m, hs, he, by simpa [translatedModuleName, hl] using hm, hg⟩

theorem invariant2_missing_module_iff {L} (ds : List (L × String × String)) :
    translatedModuleName (translatedLibraryLoc ds) (translatedSingle ds) = none ↔
      ∀ d ∈ ds, d.2.1 ≠ "library" ∧ d.2.1 ≠ "module" := by
  have absent (name : String) :
      translatedSingle ds name = none ↔ ∀ d ∈ ds, d.2.1 ≠ name := by
    simp [translatedSingle]
  have libraryAbsent :
      translatedLibraryLoc ds = none ↔ ∀ d ∈ ds, d.2.1 ≠ "library" := by
    simp [translatedLibraryLoc]
  cases h : translatedLibraryLoc ds with
  | none =>
    simp only [translatedModuleName, absent]
    exact ⟨fun hm d hd => ⟨libraryAbsent.mp h d hd, hm d hd⟩,
      fun both d hd => (both d hd).2⟩
  | some loc =>
    simp only [translatedModuleName, reduceCtorEq, false_iff]
    intro both
    have hn := libraryAbsent.mpr (fun d hd => (both d hd).1)
    simp [h] at hn

theorem invariant2_missing_module_items {L} (items : List (AssemblyItem L)) :
    let ds := translatedDirectives items
    translatedModuleName (translatedLibraryLoc ds) (translatedSingle ds) = none ↔
      ∀ l n al a, AssemblyItem.directive l n al a ∈ items → n ≠ "library" ∧ n ≠ "module" := by
  dsimp only
  rw [invariant2_missing_module_iff]
  constructor
  · intro h l n al a member
    apply h (l, n, a)
    exact List.mem_filterMap.mpr ⟨_, member, rfl⟩
  · intro h d member
    obtain ⟨item, hi, eq⟩ := List.mem_filterMap.mp member
    cases item with
    | other => contradiction
    | directive l n al a =>
      cases eq
      exact h l n al a hi

#print axioms invariant2_missing_module_items
#print axioms invariant2_missing_module_iff
#print axioms invariant1_translated_module_selection
#print axioms invariant2_assembly_diagnostics
#print axioms invariant1_translated_grammar_assembled
#print axioms invariant1_translated_grammar
#print axioms invariant1_translated_entry
end PegHs.PublicParsing
