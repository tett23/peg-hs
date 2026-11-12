import Pipeline

namespace PegHs.ImportResolution

-- Positions are abstract; the first lookup wins even when input paths repeat.
abbrev Errors (D : Type) := D × List D
inductive Library (D R : Type) where
  | parseError (errors : Errors D)
  | moduleOnly
  | assemblyError (errors : Errors D)
  | checked (diagnostics : List D) (rules : List R)

def readLibrary {D R : Type} (files : List (String × Library D R))
    (missing notLibrary : String → D) (relocate : Nat → D → D)
    (moveRule : Nat → R → R) (index : Nat) (path : String) :
    Except (Errors D) (List R) :=
  match files.lookup path with
  | none => .error (missing path, [])
  | some .moduleOnly => .error (notLibrary path, [])
  | some (.parseError (d, ds)) | some (.assemblyError (d, ds)) =>
    .error (relocate index d, ds.map (relocate index))
  | some (.checked [] rs) => .ok (rs.map (moveRule index))
  | some (.checked (d :: ds) _) => .error (relocate index d, ds.map (relocate index))

def collect {D R : Type} : List (Except (Errors D) (List R)) → Except (Errors D) (List R)
  | [] => .ok []
  | result :: tail =>
    match result, collect tail with
    | .ok rs, .ok rest => .ok (rs ++ rest)
    | .error e, .ok _ | .ok _, .error e => .error e
    | .error (e, es), .error (d, ds) => .error (e, es ++ d :: ds)

theorem invariant2_import_batch_fails {D R : Type} (xs : List (Except (Errors D) (List R))) :
    (∃ e, collect xs = .error e) ↔ ∃ x ∈ xs, ∃ e, x = .error e := by
  induction xs with
  | nil => simp [collect]
  | cons x xs ih =>
    cases x <;> cases h : collect xs <;> simp_all [collect] <;> grind

-- Scan in file order, recording a diagnostic at each later definition.
def duplicateDiagnostics {R D : Type} (name : R → String) (report : R → D) :
    List String → List R → List D
  | _, [] => []
  | seen, r :: rs =>
    let tail := duplicateDiagnostics name report (name r :: seen) rs
    if seen.contains (name r) then report r :: tail else tail

theorem invariant2_duplicate_scan {R D : Type} (name : R → String) (report : R → D)
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

def resolve {D R : Type} (libraryRoot : Bool) (missingModule : D) (root : List R)
    (imports : List (Except (Errors D) (List R))) (sort : List D → List D)
    (name : R → String) (report : R → D) (keep : List R → List R) : Except (List D) (List R) :=
  if libraryRoot then .error [missingModule] else
    match collect imports with
    | .error (d, ds) => .error (sort (d :: ds))
    | .ok rs =>
      match duplicateDiagnostics name report [] (root ++ rs) with
      | [] => .ok (keep (root ++ rs))
      | d :: ds => .error (d :: ds)

theorem invariant2_resolve_failure_nonempty {D R : Type} (lib : Bool) (missing : D)
    (root : List R) (imports : List (Except (Errors D) (List R))) (sort : List D → List D)
    (ordered : ∀ xs, (sort xs).Perm xs) (name : R → String) (report : R → D)
    (keep : List R → List R) (ds : List D)
    (failure : resolve lib missing root imports sort name report keep = .error ds) : ds ≠ [] := by
  unfold resolve at failure
  split at failure
  · cases failure
    simp
  · split at failure
    · rename_i d rest _
      cases failure
      intro h
      have hp := ordered (d :: rest)
      rw [h] at hp
      simp at hp
    · split at failure <;> cases failure
      simp

theorem invariant2_import_merge_ok_iff {D R : Type} (missing : D) (root rs : List R)
    (imports : List (Except (Errors D) (List R))) (loaded : collect imports = .ok rs)
    (sort : List D → List D) (name : R → String) (report : R → D) (keep : List R → List R) :
    resolve false missing root imports sort name report keep = .ok (keep (root ++ rs)) ↔
      ((root ++ rs).map name).Nodup := by
  have scan := invariant2_duplicate_scan name report [] (root ++ rs)
  cases h : duplicateDiagnostics name report [] (root ++ rs) <;>
    simp_all [resolve]

end PegHs.ImportResolution
