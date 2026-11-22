import TemplateFreshTranslated
import InfiniteHeadProof

namespace PegHs.TemplateFreshProof
open TemplateExpansion

-- GHC syntax-tree translation of the actual local definition in Templates.hs.
-- All its free lexical variables remain explicit arguments.
theorem root_adr0097_i2_fresh_name_translation (fuel : Nat)
    (original generated : HsSet String) (base : String) (start : Int) :
    TemplateFreshTranslated.expandOnce.freshName_240 fuel original base start generated =
      InfiniteHeadTranslated.firstName fuel base start original generated := by
  rfl

theorem root_adr0097_i2_fresh_name_agrees (base : String)
    (original generated : List String) (start k fuel : Nat)
    (found : boundedSearch base original generated start = some k)
    (enough : k - start + 1 < fuel) :
    TemplateFreshTranslated.expandOnce.freshName_240 fuel ⟨original⟩ base start ⟨generated⟩ =
      decimalName base k := by
  rw [root_adr0097_i2_fresh_name_translation]
  exact InfiniteHeadProof.root_adr0097_i2_first_name_agrees base original generated start k fuel
    found enough

theorem root_adr0097_i2_fresh_name_eventually_fresh (base : String)
    (original generated : List String) (start : Nat) :
    ∃ k, start ≤ k ∧ decimalName base k ∉ original ∧ decimalName base k ∉ generated ∧
      ∀ fuel, original.length + generated.length + 2 ≤ fuel →
        TemplateFreshTranslated.expandOnce.freshName_240 fuel ⟨original⟩ base start ⟨generated⟩ =
          decimalName base k := by
  obtain ⟨k, found⟩ := boundedSearch_succeeds base original generated start
  obtain ⟨lower, upper, freeOriginal, freeGenerated, _⟩ :=
    boundedSearch_first base original generated start k found
  refine ⟨k, lower, freeOriginal, freeGenerated, ?_⟩
  intro fuel enough
  apply root_adr0097_i2_fresh_name_agrees base original generated start k fuel found
  omega

#print axioms PegHs.TemplateFreshProof.root_adr0097_i2_fresh_name_translation
#print axioms PegHs.TemplateFreshProof.root_adr0097_i2_fresh_name_agrees
#print axioms PegHs.TemplateFreshProof.root_adr0097_i2_fresh_name_eventually_fresh
end PegHs.TemplateFreshProof
