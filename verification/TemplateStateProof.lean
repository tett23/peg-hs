import TemplateStateTranslated
import TemplateFreshProof

namespace PegHs.TemplateStateProof
open TemplateStateTranslated

theorem root_adr0097_i2_instance_count_delta (fuel : Nat) (usedNames : HsSet String)
    (l : Loc) (depth : Int) (t : Rule) (args : List Expr)
    (tys : List (Option String)) (captured : List (String × Located String)) (st : St) :
    let after := (Expand.runExpandFn
      (expandOnce.instanceOf_221 fuel usedNames l depth t args tys captured) st).2
    St.stCount after = St.stCount st ∨ St.stCount after = St.stCount st + 1 := by
  simp only [expandOnce.instanceOf_221, gets', modify',
    instMonad_gtgteq_Expand, instApplicative_pure_Expand,
    instApplicative_ltstargt_Expand, instFunctor_fmap_Expand, Expand.runExpandFn]
  split <;> simp [St.stCount, HsInt.add]

theorem root_adr0097_i2_instance_count_nonnegative (fuel : Nat) (usedNames : HsSet String)
    (l : Loc) (depth : Int) (t : Rule) (args : List Expr)
    (tys : List (Option String)) (captured : List (String × Located String)) (st : St)
    (nonnegative : 0 ≤ St.stCount st) :
    0 ≤ St.stCount ((Expand.runExpandFn
      (expandOnce.instanceOf_221 fuel usedNames l depth t args tys captured) st).2) := by
  have delta := root_adr0097_i2_instance_count_delta fuel usedNames l depth t args tys captured st
  dsimp only at delta
  omega

theorem fresh_name_translation (fuel : Nat) (used generated : HsSet String)
    (base : String) (start : Int) :
    TemplateStateTranslated.expandOnce.freshName_240 fuel used base start generated =
      TemplateFreshTranslated.expandOnce.freshName_240 fuel used base start generated := by
  rfl

theorem fresh_name_free (fuel : Nat) (used generated : HsSet String)
    (base : String) (start : Int) (nonnegative : 0 ≤ start)
    (enough : used.elems.length + generated.elems.length + 2 ≤ fuel) :
    let name := TemplateStateTranslated.expandOnce.freshName_240 fuel used base start generated
    name ∉ used.elems ∧ name ∉ generated.elems := by
  obtain ⟨k, _, freeUsed, freeGenerated, stable⟩ :=
    TemplateFreshProof.root_adr0097_i2_fresh_name_eventually_fresh base used.elems
      generated.elems start.toNat
  have count : (start.toNat : Int) = start := by omega
  have same := stable fuel enough
  rw [count] at same
  simpa only [fresh_name_translation, same] using And.intro freeUsed freeGenerated

theorem root_adr0097_i2_new_instance_name_free (fuel : Nat) (usedNames : HsSet String)
    (l : Loc) (depth : Int) (t : Rule) (args : List Expr)
    (tys : List (Option String)) (captured : List (String × Located String)) (st : St)
    (nonnegative : 0 ≤ St.stCount st)
    (enough : usedNames.elems.length + (St.stInstanceNames st).elems.length + 2 ≤ fuel) :
    let result := Expand.runExpandFn
      (expandOnce.instanceOf_221 fuel usedNames l depth t args tys captured) st
    St.stCount st < St.stCount result.2 →
      result.1 ∉ usedNames.elems ∧ result.1 ∉ (St.stInstanceNames st).elems := by
  simp only [expandOnce.instanceOf_221, gets', modify',
    instMonad_gtgteq_Expand, instApplicative_pure_Expand,
    instApplicative_ltstargt_Expand, instFunctor_fmap_Expand, Expand.runExpandFn]
  split
  · intro impossible
    simp only [St.stCount] at impossible
    omega
  · intro _
    exact fresh_name_free fuel usedNames (St.stInstanceNames st) (Rule.ruleName t)
      (St.stCount st) nonnegative enough

#print axioms PegHs.TemplateStateProof.root_adr0097_i2_instance_count_delta
#print axioms PegHs.TemplateStateProof.root_adr0097_i2_instance_count_nonnegative
#print axioms PegHs.TemplateStateProof.root_adr0097_i2_new_instance_name_free
end PegHs.TemplateStateProof
