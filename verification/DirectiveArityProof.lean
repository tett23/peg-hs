import TranslatedArity

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

end PegHs.TranslatedArity
