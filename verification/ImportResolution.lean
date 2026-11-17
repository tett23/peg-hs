import Std

namespace PegHs.ImportResolution

/-!
A model of `resolveImports` in packages/peg-grammar/src/Peg/Grammar/Import.hs
(ADR 0092), following each step of the Haskell definition:

* the `isJust (grammarLibrary root)` guard (`resolve`, first branch);
* `zipWith library [1 ..] (grammarImports root)` (`readAll`, `readLibrary`);
* `partitionEithers` and `sortOn diagLoc (concat errs)` (`partition`,
  `List.mergeSort`, which is stable like `sortOn`);
* `merge`, `duplicates`, `kept` and `reachable` (`merge`,
  `duplicateDiagnostics`, `kept`, `reachable`).

verification/check-import-resolution.sh pins those source spans and runs
ImportResolutionProbe.hs, which runs `resolveImports` on root and library
texts and compares its result with this model evaluated by
ImportResolutionProbe.lean on the same inputs.

Inputs of the model, not modelled here (premises):

* `Library`: what `library i` reads before relocating, that is the result of
  `lookup p texts`, `parseTops`, the `%library` check on the parsed tops,
  `assemble` and `libraryErrors`. The probe computes it with those Haskell
  functions themselves.
* `name`, `file`, `refs`: `ruleName`, `locFile . ruleLoc` and `ruleRefs`.
* `inFile`, `relocate`, `noSuchFile`, `notALibrary`, `duplicate`,
  `missingModule`: the diagnostics and relocations built by the Haskell code.
* `locationLE`: `(<=)` on `diagLoc`, the derived order of `Loc`.
* `directiveNames`: `directiveRules root`.
* For `invariant2_resolve_error_nonempty`: the diagnostics of a failed
  `parseTops` and a failed `assemble` are nonempty (hypotheses
  `parseNonempty` and `assembleNonempty`).

Termination: every definition here is total; `reachable.go` terminates by
`termination_by` on the rule names not yet seen and the pending names.
-/

-- What `library i (Located l p)` finds before it relocates anything.
inductive Library (D R : Type) where
  -- `lookup p texts = Nothing`
  | noText
  -- `parseTops text = Left ds`
  | parseError (errors : List D)
  -- the parsed tops have no `%library` directive
  | notLibrary
  -- `assemble tops = Left ds`
  | assemblyError (errors : List D)
  -- `assemble tops = Right g`, with `libraryErrors g` and `grammarRules g`
  | assembled (libraryErrors : List D) (rules : List R)

section
variable {D R L : Type}

-- The local `library i (Located l p)` of `resolveImports`.
def readLibrary (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (lookupLibrary : String → Library D R)
    (i : Nat) (imp : L × String) : Except (List D) (List R) :=
  match lookupLibrary imp.2 with
  | .noText => .error [noSuchFile imp.1 imp.2]
  | .parseError ds => .error (ds.map (inFile i))
  | .notLibrary => .error [notALibrary imp.1 imp.2]
  | .assemblyError ds => .error (ds.map (inFile i))
  | .assembled [] rs => .ok (rs.map (relocate i))
  | .assembled ds _ => .error (ds.map (inFile i))

-- `zipWith library [i ..]`.
def readAll (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (lookupLibrary : String → Library D R) :
    Nat → List (L × String) → List (Except (List D) (List R))
  | _, [] => []
  | i, imp :: imps =>
    readLibrary inFile relocate noSuchFile notALibrary lookupLibrary i imp ::
      readAll inFile relocate noSuchFile notALibrary lookupLibrary (i + 1) imps

-- `Data.Either.partitionEithers`.
def partition {E A : Type} : List (Except E A) → List E × List A
  | [] => ([], [])
  | .error e :: xs => (e :: (partition xs).1, (partition xs).2)
  | .ok a :: xs => ((partition xs).1, a :: (partition xs).2)

-- `duplicates`: the `scanl` gives each rule the names of the rules before it.
def duplicateDiagnostics (name : R → String) (report : R → D) :
    List String → List R → List D
  | _, [] => []
  | seen, r :: rs =>
    let tail := duplicateDiagnostics name report (name r :: seen) rs
    if seen.contains (name r) then report r :: tail else tail

-- `M.lookup n byName` with `byName = M.fromList [(ruleName r, r) | r <- rules]`:
-- `fromList` keeps the last rule of a name.
def lookupRule (name : R → String) (rules : List R) (n : String) : Option R :=
  rules.reverse.find? (fun r => name r == n)

-- `maybe [] ruleRefs (M.lookup n byName)`.
def refsOf (name : R → String) (refs : R → List String) (rules : List R)
    (n : String) : List String :=
  match lookupRule name rules n with
  | none => []
  | some r => refs r

def unseenCount (seen : List String) : List String → Nat
  | [] => 0
  | x :: xs => (if x ∈ seen then 0 else 1) + unseenCount seen xs

theorem unseenCount_head_le (seen : List String) (x n : String) :
    (if x ∈ n :: seen then 0 else 1) ≤ (if x ∈ seen then 0 else 1) := by
  split <;> split <;> simp_all

theorem unseenCount_insert_le (names seen : List String) (n : String) :
    unseenCount (n :: seen) names ≤ unseenCount seen names := by
  induction names with
  | nil => simp [unseenCount]
  | cons x xs ih =>
    simp only [unseenCount]
    have := unseenCount_head_le seen x n
    omega

theorem unseenCount_insert_lt (names seen : List String) (n : String)
    (fresh : n ∉ seen) (named : n ∈ names) :
    unseenCount (n :: seen) names < unseenCount seen names := by
  induction names with
  | nil => simp at named
  | cons x xs ih =>
    simp only [unseenCount]
    by_cases hn : x = n
    · subst hn
      have := unseenCount_insert_le xs seen x
      simp [fresh]
      omega
    · have tail : n ∈ xs := by
        rcases List.mem_cons.mp named with h | h
        · exact absurd h.symm hn
        · exact h
      have := ih tail
      have := unseenCount_head_le seen x n
      omega

theorem unseenCount_insert_eq (names seen : List String) (n : String)
    (unnamed : n ∉ names) :
    unseenCount (n :: seen) names = unseenCount seen names := by
  induction names with
  | nil => simp [unseenCount]
  | cons x xs ih =>
    have hn : x ≠ n := fun h => unnamed (h ▸ List.mem_cons_self ..)
    have := ih (fun h => unnamed (List.mem_cons_of_mem _ h))
    simp [unseenCount, hn, this]

-- `go` of `reachable`. `seen` is the `Set` as a list. A name that is not the
-- name of a rule has no rule in `byName`, so its references are `[]`
-- (`refsOf_unnamed`); `go_unseen` is the Haskell equation.
def reachableGo (name : R → String) (refs : R → List String) (rules : List R)
    (seen : List String) : List String → List String
  | [] => seen
  | n :: ns =>
    if n ∈ seen then reachableGo name refs rules seen ns
    else if n ∈ rules.map name then
      reachableGo name refs rules (n :: seen) (refsOf name refs rules n ++ ns)
    else reachableGo name refs rules (n :: seen) ns
termination_by pending => (unseenCount seen (rules.map name), pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (unseenCount_insert_lt _ _ _ ‹_› ‹_›)
  · rw [unseenCount_insert_eq _ _ _ ‹_›]
    exact Prod.Lex.right _ (by simp)

-- `reachable rules`.
def reachable (name : R → String) (refs : R → List String) (rules : List R)
    (roots : List String) : List String :=
  reachableGo name refs rules [] roots

theorem refsOf_unnamed (name : R → String) (refs : R → List String) (rules : List R)
    (n : String) (unnamed : n ∉ rules.map name) : refsOf name refs rules n = [] := by
  unfold refsOf lookupRule
  have : rules.reverse.find? (fun r => name r == n) = none := by
    rw [List.find?_eq_none]
    intro r hr
    have : name r ≠ n := fun h => unnamed (List.mem_map.mpr ⟨r, List.mem_reverse.mp hr, h⟩)
    simpa using this
  simp [this]

theorem go_seen (name : R → String) (refs : R → List String) (rules : List R)
    (seen : List String) (n : String) (ns : List String) (h : n ∈ seen) :
    reachableGo name refs rules seen (n :: ns) = reachableGo name refs rules seen ns := by
  rw [reachableGo]; simp [h]

theorem go_unseen (name : R → String) (refs : R → List String) (rules : List R)
    (seen : List String) (n : String) (ns : List String) (h : n ∉ seen) :
    reachableGo name refs rules seen (n :: ns) =
      reachableGo name refs rules (n :: seen) (refsOf name refs rules n ++ ns) := by
  rw [reachableGo]
  by_cases named : n ∈ rules.map name
  · simp [h, named]
  · simp only [h, named, ite_false, refsOf_unnamed name refs rules n named, List.nil_append]

-- What `go` has seen stays seen.
theorem go_mono (name : R → String) (refs : R → List String) (rules : List R)
    (seen pending : List String) :
    ∀ x ∈ seen, x ∈ reachableGo name refs rules seen pending := by
  induction seen, pending using reachableGo.induct name refs rules with
  | case1 seen => intro x hx; rw [reachableGo]; exact hx
  | case2 seen n ns h ih => intro x hx; rw [go_seen _ _ _ _ _ _ h]; exact ih x hx
  | case3 seen n ns h _ ih =>
    intro x hx; rw [go_unseen _ _ _ _ _ _ h]; exact ih x (List.mem_cons_of_mem _ hx)
  | case4 seen n ns h unnamed ih =>
    intro x hx
    rw [go_unseen _ _ _ _ _ _ h, refsOf_unnamed _ _ _ _ unnamed, List.nil_append]
    exact ih x (List.mem_cons_of_mem _ hx)

-- Every root is reached.
theorem go_pending (name : R → String) (refs : R → List String) (rules : List R)
    (seen pending : List String) :
    ∀ x ∈ pending, x ∈ reachableGo name refs rules seen pending := by
  induction seen, pending using reachableGo.induct name refs rules with
  | case1 seen => simp
  | case2 seen n ns h ih =>
    intro x hx
    rw [go_seen _ _ _ _ _ _ h]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact go_mono _ _ _ _ _ x h
    · exact ih x hx
  | case3 seen n ns h _ ih =>
    intro x hx
    rw [go_unseen _ _ _ _ _ _ h]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact go_mono _ _ _ _ _ x (List.mem_cons_self ..)
    · exact ih x (List.mem_append_right _ hx)
  | case4 seen n ns h unnamed ih =>
    intro x hx
    rw [go_unseen _ _ _ _ _ _ h, refsOf_unnamed _ _ _ _ unnamed, List.nil_append]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact go_mono _ _ _ _ _ x (List.mem_cons_self ..)
    · exact ih x hx

-- `kept rules r`.
def kept (name : R → String) (file : R → Nat) (refs : R → List String)
    (rootRules : List R) (directiveNames : List String) (rules : List R) (r : R) : Bool :=
  file r == 0 || (reachable name refs rules (rootRules.map name ++ directiveNames)).contains (name r)

-- `merge rules`.
def merge (name : R → String) (file : R → Nat) (refs : R → List String) (duplicate : R → D)
    (rootRules : List R) (directiveNames : List String) (rules : List R) :
    Except (List D) (List R) :=
  match duplicateDiagnostics name duplicate [] rules with
  | [] => .ok (rules.filter (kept name file refs rootRules directiveNames rules))
  | ds => .error ds

-- `resolveImports root texts`.
def resolve (isLibrary : Bool) (missingModule : D) (rootRules : List R)
    (directiveNames : List String) (imports : List (L × String))
    (lookupLibrary : String → Library D R) (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (locationLE : D → D → Bool)
    (name : R → String) (file : R → Nat) (refs : R → List String) (duplicate : R → D) :
    Except (List D) (List R) :=
  if isLibrary then .error [missingModule] else
    match partition (readAll inFile relocate noSuchFile notALibrary lookupLibrary 1 imports) with
    | ([], libs) => merge name file refs duplicate rootRules directiveNames (rootRules ++ libs.flatten)
    | (errs, _) => .error (errs.flatten.mergeSort locationLE)

/-! Theorems -/

theorem invariant2_partition_errors_nil {E A : Type} (xs : List (Except E A)) :
    (partition xs).1 = [] ↔ ∀ x ∈ xs, ∃ a, x = .ok a := by
  induction xs with
  | nil => simp [partition]
  | cons x xs ih => cases x <;> simp [partition, ih]

theorem partition_ok {E A : Type} (xs : List (Except E A))
    (h : ∀ x ∈ xs, ∃ a, x = .ok a) :
    xs = (partition xs).2.map Except.ok := by
  induction xs with
  | nil => simp [partition]
  | cons x xs ih =>
    obtain ⟨a, rfl⟩ := h x (by simp)
    simp [partition, ← ih (fun y hy => h y (by simp [hy]))]

theorem partition_map_ok {E A : Type} (xs : List A) :
    partition (xs.map (Except.ok (ε := E))) = ([], xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [partition, ih]

theorem invariant2_duplicate_scan (name : R → String) (report : R → D)
    (seen : List String) (rs : List R) :
    duplicateDiagnostics name report seen rs = [] ↔
      (rs.map name).Nodup ∧ ∀ n ∈ rs.map name, n ∉ seen := by
  induction rs generalizing seen with
  | nil => simp [duplicateDiagnostics]
  | cons r rs ih =>
    by_cases h : name r ∈ seen
    · simp [duplicateDiagnostics, h]
    · simp [duplicateDiagnostics, h, ih, List.nodup_cons]
      grind

-- A failed read has at least one diagnostic.
theorem readLibrary_error_nonempty (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (lookupLibrary : String → Library D R)
    (parseNonempty : ∀ p ds, lookupLibrary p = .parseError ds → ds ≠ [])
    (assembleNonempty : ∀ p ds, lookupLibrary p = .assemblyError ds → ds ≠ [])
    (i : Nat) (imp : L × String) (ds : List D)
    (failed : readLibrary inFile relocate noSuchFile notALibrary lookupLibrary i imp = .error ds) :
    ds ≠ [] := by
  unfold readLibrary at failed
  split at failed <;> cases failed
  · simp
  · rename_i es h; simpa using parseNonempty _ es h
  · simp
  · rename_i es h; simpa using assembleNonempty _ es h
  · rename_i es _ h _; simpa using h

theorem readAll_error_nonempty (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (lookupLibrary : String → Library D R)
    (parseNonempty : ∀ p ds, lookupLibrary p = .parseError ds → ds ≠ [])
    (assembleNonempty : ∀ p ds, lookupLibrary p = .assemblyError ds → ds ≠ [])
    (i : Nat) (imps : List (L × String)) :
    ∀ ds ∈ (partition (readAll inFile relocate noSuchFile notALibrary lookupLibrary i imps)).1,
      ds ≠ [] := by
  induction imps generalizing i with
  | nil => simp [readAll, partition]
  | cons imp imps ih =>
    intro ds hds
    simp only [readAll] at hds
    cases h : readLibrary inFile relocate noSuchFile notALibrary lookupLibrary i imp with
    | error es =>
      rw [h] at hds
      simp only [partition, List.mem_cons] at hds
      rcases hds with rfl | hds
      · exact readLibrary_error_nonempty _ _ _ _ _ parseNonempty assembleNonempty _ _ _ h
      · exact ih (i + 1) ds hds
    | ok rs =>
      rw [h] at hds
      exact ih (i + 1) ds hds

-- Invariant 2: a rejection has at least one diagnostic (and, being `.error`,
-- no grammar).
theorem invariant2_resolve_error_nonempty (isLibrary : Bool) (missingModule : D)
    (rootRules : List R) (directiveNames : List String) (imports : List (L × String))
    (lookupLibrary : String → Library D R) (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (locationLE : D → D → Bool)
    (name : R → String) (file : R → Nat) (refs : R → List String) (duplicate : R → D)
    (parseNonempty : ∀ p ds, lookupLibrary p = .parseError ds → ds ≠ [])
    (assembleNonempty : ∀ p ds, lookupLibrary p = .assemblyError ds → ds ≠ [])
    (ds : List D)
    (failed : resolve isLibrary missingModule rootRules directiveNames imports lookupLibrary
      inFile relocate noSuchFile notALibrary locationLE name file refs duplicate = .error ds) :
    ds ≠ [] := by
  unfold resolve at failed
  split at failed
  · cases failed; simp
  · have each := readAll_error_nonempty inFile relocate noSuchFile notALibrary lookupLibrary
      parseNonempty assembleNonempty 1 imports
    generalize partition (readAll inFile relocate noSuchFile notALibrary lookupLibrary 1
      imports) = p at failed each
    obtain ⟨errs, libs⟩ := p
    cases errs with
    | nil =>
      simp only at failed
      unfold merge at failed
      split at failed
      · cases failed
      · cases failed; assumption
    | cons e es =>
      simp only at failed
      cases failed
      intro hnil
      have perm := List.mergeSort_perm ((e :: es).flatten) locationLE
      rw [hnil] at perm
      have : e = [] := by
        have := perm.length_eq
        simp at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      exact each e (by simp) this

-- Invariant 2: each rejection condition of ADR 0092 rejects.
theorem invariant2_library_root_rejected (missingModule : D)
    (rootRules : List R) (directiveNames : List String) (imports : List (L × String))
    (lookupLibrary : String → Library D R) (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (locationLE : D → D → Bool)
    (name : R → String) (file : R → Nat) (refs : R → List String) (duplicate : R → D) :
    resolve true missingModule rootRules directiveNames imports lookupLibrary
      inFile relocate noSuchFile notALibrary locationLE name file refs duplicate =
      .error [missingModule] := by
  simp [resolve]

theorem invariant2_failed_import_rejected (missingModule : D)
    (rootRules : List R) (directiveNames : List String) (imports : List (L × String))
    (lookupLibrary : String → Library D R) (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (locationLE : D → D → Bool)
    (name : R → String) (file : R → Nat) (refs : R → List String) (duplicate : R → D)
    (failing : ∃ x ∈ readAll inFile relocate noSuchFile notALibrary lookupLibrary 1 imports,
      ∃ es, x = .error es) :
    ∃ ds, resolve false missingModule rootRules directiveNames imports lookupLibrary
      inFile relocate noSuchFile notALibrary locationLE name file refs duplicate = .error ds := by
  have notNil : (partition (readAll inFile relocate noSuchFile notALibrary lookupLibrary 1
      imports)).1 ≠ [] := by
    intro h
    obtain ⟨x, hx, es, rfl⟩ := failing
    obtain ⟨a, ha⟩ := (invariant2_partition_errors_nil _).mp h _ hx
    cases ha
  unfold resolve
  simp only [Bool.false_eq_true, ite_false]
  generalize partition (readAll inFile relocate noSuchFile notALibrary lookupLibrary 1
    imports) = p at notNil ⊢
  obtain ⟨errs, libs⟩ := p
  cases errs with
  | nil => exact absurd rfl notNil
  | cons e es => exact ⟨_, rfl⟩

theorem invariant2_merge_ok_iff (name : R → String) (file : R → Nat) (refs : R → List String)
    (duplicate : R → D) (rootRules : List R) (directiveNames : List String) (rules : List R) :
    (∃ out, merge name file refs duplicate rootRules directiveNames rules = .ok out) ↔
      (rules.map name).Nodup := by
  have scan := invariant2_duplicate_scan name duplicate [] rules
  unfold merge
  split <;> simp_all

-- Invariant 2: acceptance is exactly no library root, every import read, and
-- no name defined twice; the grammar then keeps the rules of `kept`.
theorem invariant2_resolve_ok_iff (isLibrary : Bool) (missingModule : D)
    (rootRules : List R) (directiveNames : List String) (imports : List (L × String))
    (lookupLibrary : String → Library D R) (inFile : Nat → D → D) (relocate : Nat → R → R)
    (noSuchFile notALibrary : L → String → D) (locationLE : D → D → Bool)
    (name : R → String) (file : R → Nat) (refs : R → List String) (duplicate : R → D)
    (out : List R) :
    resolve isLibrary missingModule rootRules directiveNames imports lookupLibrary
      inFile relocate noSuchFile notALibrary locationLE name file refs duplicate = .ok out ↔
      isLibrary = false ∧
      ∃ libs : List (List R), readAll inFile relocate noSuchFile notALibrary lookupLibrary 1 imports =
          libs.map Except.ok ∧
        ((rootRules ++ libs.flatten).map name).Nodup ∧
        out = (rootRules ++ libs.flatten).filter
          (kept name file refs rootRules directiveNames (rootRules ++ libs.flatten)) := by
  cases isLibrary
  · simp only [resolve, Bool.false_eq_true, ite_false, true_and]
    generalize hxs : readAll inFile relocate noSuchFile notALibrary lookupLibrary 1 imports = xs
    constructor
    · intro h
      split at h
      · rename_i libs hp
        have allOk := (invariant2_partition_errors_nil xs).mp (by rw [hp])
        have eq := partition_ok xs allOk
        rw [hp] at eq
        refine ⟨libs, eq, ?_⟩
        have scan := invariant2_duplicate_scan name duplicate [] (rootRules ++ libs.flatten)
        unfold merge at h
        split at h
        · cases h; exact ⟨(scan.mp ‹_›).1, rfl⟩
        · cases h
      · cases h
    · rintro ⟨libs, rfl, nodup, rfl⟩
      rw [partition_map_ok]
      simp only
      have scan := invariant2_duplicate_scan name duplicate [] (rootRules ++ libs.flatten)
      unfold merge
      rw [scan.mpr ⟨nodup, by simp⟩]
  · simp [resolve]

-- Every rule of the root is kept, and a library rule is kept when the root
-- rules or the directive names reach it.
theorem invariant2_kept_root (name : R → String) (file : R → Nat) (refs : R → List String)
    (rootRules : List R) (directiveNames : List String) (rules : List R) (r : R)
    (root : file r = 0) : kept name file refs rootRules directiveNames rules r = true := by
  simp [kept, root]

theorem invariant2_kept_named (name : R → String) (file : R → Nat) (refs : R → List String)
    (rootRules : List R) (directiveNames : List String) (rules : List R) (r : R)
    (named : name r ∈ rootRules.map name ++ directiveNames) :
    kept name file refs rootRules directiveNames rules r = true := by
  have := go_pending name refs rules [] _ _ named
  simp [kept, reachable, this]

end

end PegHs.ImportResolution
