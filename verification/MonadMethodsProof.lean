import MonadLibraryTranslated
import MonadOverrideTranslated
import MonadLiftTranslated

namespace PegHs.MonadMethodsProof

theorem root_adr0097_i2_default_sequence (a b : Int) :
    MonadLibraryTranslated.defaultStep a b = a + b ∧
    MonadLibraryTranslated.defaultOperatorStep a b = a + b := by
  exact ⟨rfl, rfl⟩

theorem root_adr0097_i2_override_sequence (a b : Int) :
    MonadOverrideTranslated.overrideStep a b = a + b + 10 ∧
    MonadOverrideTranslated.overrideOperatorStep a b = a + b + 10 := by
  exact ⟨rfl, rfl⟩

theorem root_adr0097_i2_traversal_methods :
    MonadLibraryTranslated.mapped = 315 ∧
    MonadLibraryTranslated.mappedBase = 4011 ∧
    MonadLibraryTranslated.mapped_ = 1005 ∧
    MonadLibraryTranslated.emptyMapped_ = 999 ∧
    MonadOverrideTranslated.overridden_ = 136 ∧
    MonadLiftTranslated.mappedLift = 165 ∧
    MonadLibraryTranslated.filtered = 3 := by decide

#print axioms PegHs.MonadMethodsProof.root_adr0097_i2_default_sequence
#print axioms PegHs.MonadMethodsProof.root_adr0097_i2_override_sequence
#print axioms PegHs.MonadMethodsProof.root_adr0097_i2_traversal_methods
end PegHs.MonadMethodsProof
