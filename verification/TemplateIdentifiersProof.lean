import TemplatesTranslated

namespace PegHs.TemplateIdentifiersProof
open TemplatesTranslated

theorem root_adr0097_i2_identifier_split_preserves_text (t : String) :
    HsText.concat (identifierSplit t) = t := by
  refine (measure (fun s : String => s.toList.length)).wf.induction
    (C := fun t => HsText.concat (identifierSplit t) = t) t ?_
  intro t ih
  rw [identifierSplit]
  split
  · rename_i empty
    have emptyText : t = "" := by
      apply String.toList_eq_nil_iff.mp
      simpa [HsText.null] using empty
    simp [emptyText, HsText.concat]
  · rename_i nonempty
    split
    · rename_i first
      rcases pieces : HsText.span identifierSplit.isIdent_294 t with ⟨a, b⟩
      dsimp only
      simp only [HsText.concat, String.join_cons]
      have smaller := HsText.span_shrinks identifierSplit.isIdent_294 t
        (by simpa using nonempty) first
      rw [pieces] at smaller
      change a ++ HsText.concat (identifierSplit b) = t
      rw [ih b smaller]
      simpa [pieces] using HsText.span_append identifierSplit.isIdent_294 t
    · rename_i first
      rcases pieces : HsText.«break» identifierSplit.isIdent_294 t with ⟨a, b⟩
      dsimp only
      simp only [HsText.concat, String.join_cons]
      have smaller := HsText.break_shrinks identifierSplit.isIdent_294 t
        (by simpa using nonempty) (by simpa using first)
      rw [pieces] at smaller
      change a ++ HsText.concat (identifierSplit b) = t
      rw [ih b smaller]
      have append : (HsText.«break» identifierSplit.isIdent_294 t).1 ++
          (HsText.«break» identifierSplit.isIdent_294 t).2 = t :=
        HsText.span_append (fun c => !identifierSplit.isIdent_294 c) t
      simpa [pieces] using append

theorem root_adr0097_i2_instance_type_fields (a b : Rule) (tys : List (Option String))
    (typeCode : a.ruleType.unLoc = b.ruleType.unLoc)
    (parameters : a.ruleTemplateParams = b.ruleTemplateParams) :
    instanceType a tys = instanceType b tys := by
  simp only [instanceType, typeCode, parameters]

#print axioms PegHs.TemplateIdentifiersProof.root_adr0097_i2_identifier_split_preserves_text
end PegHs.TemplateIdentifiersProof
