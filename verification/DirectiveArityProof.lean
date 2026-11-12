import TranslatedArity
import DirectiveDuplicates

namespace PegHs.TranslatedArity
open AssembleValidation MetaExecution

theorem invariant2_source_missing_argument (tops : List Top) (p : Predicates) (name : String)
    (present : Top.directive name "" ∈ tops) (recognized : known.contains name = true)
    (required : optional.contains name = false) :
    diagnostic ⟨.missingArgument, name⟩ ∈ errors tops p :=
  invariant2_missing_argument tops name p present recognized required

theorem invariant2_source_unexpected_argument (tops : List Top) (p : Predicates) (name arg : String)
    (present : Top.directive name arg ∈ tops) (flag : flags.contains name = true)
    (nonempty : arg.isEmpty = false) :
    diagnostic ⟨.unexpectedArgument, name⟩ ∈ errors tops p :=
  invariant2_unexpected_argument tops name arg p present flag nonempty

theorem duplicateLocation_iff (name : String) (ds : List (α × String × String)) :
    (duplicateLocation name ds).isSome ↔
      2 ≤ (ds.filter (fun d => d.2.1 == name)).length := by
  unfold duplicateLocation
  rw [← List.length_reverse]
  cases (ds.filter (fun d => d.2.1 == name)).reverse with
  | nil => simp
  | cons first rest => cases rest <;> simp

theorem invariant2_source_duplicate (tops : List Top) (p : Predicates) (name : String)
    (ds : List (α × String × String)) (project : ds.map Prod.snd = directives tops)
    (selected : name ∈ uniqueNames) (duplicate : (duplicateLocation name ds).isSome) :
    diagnostic ⟨.duplicateDirective, name⟩ ∈ errors tops p := by
  apply invariant2_duplicate_directive tops p name selected
  rw [← project, List.filter_map]
  simpa [Function.comp_def] using (duplicateLocation_iff name ds).mp duplicate

end PegHs.TranslatedArity
