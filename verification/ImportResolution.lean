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

def resolve {D R : Type} (libraryRoot : Bool) (missingModule : D) (root : List R)
    (imports : List (Except (Errors D) (List R))) (sort : List D → List D)
    (duplicates : List R → List D) (keep : List R → List R) : Except (List D) (List R) :=
  if libraryRoot then .error [missingModule] else
    match collect imports with
    | .error (d, ds) => .error (sort (d :: ds))
    | .ok rs =>
      match duplicates (root ++ rs) with
      | [] => .ok (keep (root ++ rs))
      | d :: ds => .error (d :: ds)

theorem invariant2_resolve_failure_nonempty {D R : Type} (lib : Bool) (missing : D)
    (root : List R) (imports : List (Except (Errors D) (List R))) (sort : List D → List D)
    (ordered : ∀ xs, (sort xs).Perm xs) (duplicates : List R → List D)
    (keep : List R → List R) (ds : List D)
    (failure : resolve lib missing root imports sort duplicates keep = .error ds) : ds ≠ [] := by
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

end PegHs.ImportResolution
