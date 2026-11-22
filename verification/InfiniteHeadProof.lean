import InfiniteHeadTranslated
import TemplateExpansionFresh

namespace PegHs.InfiniteHeadProof
open TemplateExpansion

private theorem pack_show_nat (n : Nat) :
    HsText.pack (HsInt.«show» (n : Int)) = Nat.repr n := by
  have convert (c : Char) : HsText.toChar (HsChar.ofChar c) = c := by
    have valid : c.toNat.isValidChar := c.valid
    simp [HsText.toChar, HsChar.ofChar, valid, Char.ofNat_toNat]
  simp [HsInt.«show», HsText.pack, Function.comp_def, convert]
  rfl

private theorem member_eq (name : String) (xs : List String) :
    HsSet.member name ⟨xs⟩ = decide (name ∈ xs) := by
  apply Bool.eq_iff_iff.mpr
  simp only [HsSet.member, List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨x, member, rfl⟩
    exact member
  · intro member
    exact ⟨name, member, rfl⟩

-- The Integer loop of the translated comprehension, not a capped
-- enumeration. The finite model supplies a sufficient evaluation fuel.
theorem root_adr0097_i2_first_name_agrees (base : String)
    (original generated : List String) (start k fuel : Nat)
    (found : boundedSearch base original generated start = some k)
    (enough : k - start + 1 < fuel) :
    InfiniteHeadTranslated.firstName fuel base start ⟨original⟩ ⟨generated⟩ =
      decimalName base k := by
  obtain ⟨lower, _, freeOriginal, freeGenerated, earlier⟩ :=
    boundedSearch_first base original generated start k found
  cases fuel with
  | zero => omega
  | succ fuel =>
    unfold InfiniteHeadTranslated.firstName
    apply HsList.firstFrom_hit (offset := k - start) (value := decimalName base k)
      (tail := [])
    · omega
    · intro i before
      have occupied := earlier (start + i) (by omega) (by omega)
      have cast : (start : Int) + (i : Int) = ((start + i : Nat) : Int) := by omega
      rw [cast, pack_show_nat]
      simp only [HsText.append, ← String.append_assoc, member_eq,
        HsBase.not]
      simp only [decimalName] at occupied
      rcases occupied with occupied | occupied <;> simp [occupied]
    · have cast : (start : Int) + ((k - start : Nat) : Int) = (k : Int) := by omega
      rw [cast, pack_show_nat]
      simp only [HsText.append, ← String.append_assoc, member_eq,
        HsBase.not]
      simp only [decimalName] at freeOriginal freeGenerated ⊢
      simp [freeOriginal, freeGenerated]

#print axioms PegHs.InfiniteHeadProof.root_adr0097_i2_first_name_agrees
end PegHs.InfiniteHeadProof
