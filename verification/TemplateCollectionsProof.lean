import HsPrelude
import LabelsBridge

namespace PegHs.TemplateCollectionsProof

theorem set_member_iff {α : Type} [BEq α] [LawfulBEq α] (x : α) (s : HsSet α) :
    HsSet.member x s = true ↔ x ∈ s.elems := by
  simp only [HsSet.member, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨y, member, rfl⟩
    exact member
  · intro member
    exact ⟨x, member, rfl⟩

theorem root_adr0097_i2_set_intersection {α : Type} [BEq α] [LawfulBEq α]
    (x : α) (left right : HsSet α) :
    x ∈ (HsSet.intersection left right).elems ↔ x ∈ left.elems ∧ x ∈ right.elems := by
  simp only [HsSet.intersection, List.mem_filter, set_member_iff]

private theorem map_member_eq_isSome {κ ν : Type} [BEq κ] (k : κ) (m : HsMap κ ν) :
    HsMap.member k m = (HsMap.lookup k m).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [HsMap.member, HsMap.lookup, List.any_eq_true, Option.isSome_map,
    List.find?_isSome]

private theorem union_fold_preserves_left {ν : Type} (k : String) (value : ν)
    (pairs : List (String × ν)) (m : HsMap String ν) (present : HsMap.lookup k m = some value) :
    HsMap.lookup k (pairs.foldl (fun result p =>
      if HsMap.member p.1 result then result else HsMap.insert p.1 p.2 result) m) = some value := by
  induction pairs generalizing m with
  | nil => exact present
  | cons p pairs ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact present
    · rename_i absent
      have different : p.1 ≠ k := by
        intro same
        have occupied : HsMap.member k m = true := by
          rw [map_member_eq_isSome, present]
          rfl
        rw [same] at absent
        exact absent occupied
      rw [LabelsBridge.lookup_insert, ite_eq_right different]
      exact present

theorem root_adr0097_i2_map_union_left_bias {ν : Type} (k : String) (value : ν)
    (left right : HsMap String ν) (present : HsMap.lookup k left = some value) :
    HsMap.lookup k (HsMap.union left right) = some value :=
  union_fold_preserves_left k value right.pairs left present

theorem root_adr0097_i2_map_values {κ α β : Type} [BEq κ]
    (f : α → β) (k : κ) (m : HsMap κ α) :
    HsMap.lookup k (HsMap.map f m) = (HsMap.lookup k m).map f := by
  cases m with
  | mk pairs =>
    induction pairs with
    | nil => rfl
    | cons p pairs ih =>
      cases h : p.1 == k <;>
        simp_all [HsMap.map, HsMap.lookup]

#print axioms PegHs.TemplateCollectionsProof.root_adr0097_i2_set_intersection
#print axioms PegHs.TemplateCollectionsProof.root_adr0097_i2_map_union_left_bias
#print axioms PegHs.TemplateCollectionsProof.root_adr0097_i2_map_values
end PegHs.TemplateCollectionsProof
