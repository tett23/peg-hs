import AssembleTextProof

/-!
The directive predicates of the translation of Peg.Grammar.Assemble
(AssembleTranslated) against the models that AssembleValidation reads:
`isImportPath` and `isExtensionName` against DirectiveNames, `positiveTabstop`
against BoundedDecimal.positive at `intMax`, and `splitExports` (its texts)
against AssembleValidationHelpers.splitExports. Each theorem holds on every
input.
-/

namespace PegHs.AssembleTextProof

/-! ## ASCII classes: the AssembleChars table below 128 and Lean's `Char` predicates -/

theorem alphaNum_ascii_table : ∀ n, n < 128 →
    inRangesNat AssembleChars.alphaNumRanges n =
      decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122)) := by
  decide +kernel

theorem isAlphanum_iff (c : Char) : c.isAlphanum =
    decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
      (97 ≤ c.toNat ∧ c.toNat ≤ 122)) := by
  simp only [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit]
  rw [Bool.eq_iff_iff]
  simp [UInt32.le_iff_toNat_le]
  omega

theorem isUpper_iff (c : Char) : c.isUpper = decide (65 ≤ c.toNat ∧ c.toNat ≤ 90) := by
  simp only [Char.isUpper]
  rw [Bool.eq_iff_iff]
  simp [UInt32.le_iff_toNat_le]

theorem asciiAlphaNum_ofChar (c : Char) :
    (HsChar.isAscii (HsChar.ofChar c) && HsChar.isAlphaNum (HsChar.ofChar c)) = c.isAlphanum := by
  rw [isAlphanum_iff]
  simp only [HsChar.isAscii, HsChar.isAlphaNum, ofChar_val]
  by_cases h : c.toNat < 128
  · rw [alphaNum_ascii_table _ h]; simp [h]
  · simp only [h, decide_false, Bool.false_and]
    symm; simp; omega


/-! ## isExtensionName and isImportPath -/

theorem isExtensionName_eq (t : String) :
    AssembleTranslated.isExtensionName t = DirectiveNames.validExtension t := by
  unfold AssembleTranslated.isExtensionName DirectiveNames.validExtension
  simp only [HsText.uncons]
  cases t.toList with
  | nil => rfl
  | cons c cs =>
    simp only [HsBase.and, HsText.all, String.toList_ofList, asciiAlphaNum_ofChar, isUpper_iff,
      HsChar.isAsciiUpper, ofChar_val]
    rfl

theorem pathChar_ofChar (c : Char) :
    (HsBase.and (HsChar.isAscii (HsChar.ofChar c)) (HsBase.or (HsChar.isAlphaNum (HsChar.ofChar c))
      (HsList.elem (HsChar.ofChar c) [HsChar.ofNat 95, HsChar.ofNat 45, HsChar.ofNat 46]))) =
      DirectiveNames.pathChar c := by
  rw [DirectiveNames.pathChar, ← asciiAlphaNum_ofChar]
  simp only [HsBase.and, HsBase.or, HsList.elem, List.any_cons, List.any_nil, Bool.or_false]
  have e (n : Nat) (h : n.isValidChar) : (HsChar.ofNat n == HsChar.ofChar c) = (c == Char.ofNat n) := by
    rw [← eq_ofChar_lit c n h, HsBase.eq, Bool.beq_comm]
  rw [e 95 (by decide), e 45 (by decide), e 46 (by decide)]
  by_cases h : c.toNat < 128
  · simp [HsChar.isAscii, ofChar_val, h, Bool.or_assoc]
  · have n1 : (c == '_') = false := by simp; intro e; subst e; simp at h
    have n2 : (c == '-') = false := by simp; intro e; subst e; simp at h
    have n3 : (c == '.') = false := by simp; intro e; subst e; simp at h
    simp [HsChar.isAscii, ofChar_val, h, n1, n2, n3]

theorem part_eq (p : String) :
    AssembleTranslated.isImportPath.part_446 p = DirectiveNames.pathPart p := by
  unfold AssembleTranslated.isImportPath.part_446 DirectiveNames.pathPart
  simp only [HsText.all, pathChar_ofChar]
  simp only [HsBase.and, HsBase.not, null_eq, HsList.notElem, List.any_cons, List.any_nil,
    Bool.or_false, Bool.not_or, bne, Bool.beq_comm (a := p), Bool.and_assoc]

theorem isImportPath_eq (t : String) :
    AssembleTranslated.isImportPath t = DirectiveNames.validImportPath t := by
  unfold AssembleTranslated.isImportPath DirectiveNames.validImportPath DirectiveNames.pathParts
  have slash : ("/") = String.singleton '/' := rfl
  rw [slash, splitOn_single_eq]
  simp only [HsBase.and, HsList.all, List.all_map, Function.comp_def, part_eq]
  rfl


/-! ## positiveTabstop -/

theorem isDigit_iff (c : Char) : c.isDigit = decide (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by
  simp only [Char.isDigit]
  rw [Bool.eq_iff_iff]
  simp [UInt32.le_iff_toNat_le]

theorem tabstopStep_eq (acc : Nat) (c : Char) :
    AssembleTranslated.positiveTabstop.step_425 (acc : Int) (HsChar.ofChar c) =
      (BoundedDecimal.checkedChar AssembleValidation.intMax acc c).map (fun n => (n : Int)) := by
  rw [BoundedDecimal.checkedChar_eq _ _ _ (by decide), isDigit_iff]
  have z : '0'.toNat = 48 := rfl
  unfold AssembleTranslated.positiveTabstop.step_425
  by_cases h : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · have hd : HsChar.isDigit (HsChar.ofChar c) = true := by simp [HsChar.isDigit, ofChar_val, h]
    have hv : HsChar.digitToInt (HsChar.ofChar c) = ((c.toNat - 48 : Nat) : Int) := by
      simp only [HsChar.digitToInt, hd, ite_true, ofChar_val, Int.ofNat_eq_natCast]; omega
    simp only [hd, hv, ite_true, z, HsInt.le, HsInt.div, HsInt.sub,
      HsInt.maxBound, HsInt.add, HsInt.mul]
    have small : c.toNat - 48 ≤ 9 := by omega
    generalize c.toNat - 48 = n at small ⊢
    have q : (9223372036854775807 : Int) - (n : Int) = ((AssembleValidation.intMax - n : Nat) : Int) := by
      simp only [AssembleValidation.intMax]; omega
    rw [q, show (10 : Int) = ((10 : Nat) : Int) from rfl, ← Int.ofNat_fdiv]
    by_cases k : acc ≤ (AssembleValidation.intMax - n) / 10
    · simp [k, h]; omega
    · simp [k, h]; omega
  · have hd : HsChar.isDigit (HsChar.ofChar c) = false := by simp [HsChar.isDigit, ofChar_val, h]
    simp [hd, h]

theorem tabstopFold_eq (acc : Nat) (cs : List Char) :
    HsMaybe.foldM AssembleTranslated.positiveTabstop.step_425 (acc : Int) (cs.map HsChar.ofChar) =
      (cs.foldlM (BoundedDecimal.checkedChar AssembleValidation.intMax) acc).map (fun n => (n : Int)) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, HsMaybe.foldM, tabstopStep_eq, List.foldlM_cons]
    cases BoundedDecimal.checkedChar AssembleValidation.intMax acc c with
    | none => rfl
    | some n => simp [ih]

theorem positiveTabstop_eq (t : String) :
    AssembleTranslated.positiveTabstop t =
      (BoundedDecimal.positive AssembleValidation.intMax t).map (fun n => (n : Int)) := by
  rw [← BoundedDecimal.invariant2_streaming_positive]
  unfold AssembleTranslated.positiveTabstop
  rw [unpack_eq]
  have := tabstopFold_eq 0 t.toList
  rw [show ((0 : Nat) : Int) = 0 from rfl] at this
  rw [this]
  cases t.toList.foldlM (BoundedDecimal.checkedChar AssembleValidation.intMax) 0 with
  | none => rfl
  | some n => by_cases h : n > 0 <;> simp [HsMaybe.bind, HsInt.gt, h] <;> omega

theorem positiveTabstop_isNone (t : String) :
    (AssembleTranslated.positiveTabstop t).isNone =
      (BoundedDecimal.positive AssembleValidation.intMax t).isNone := by
  rw [positiveTabstop_eq]; cases BoundedDecimal.positive AssembleValidation.intMax t <;> rfl


/-! ## splitExports: the translation keeps the parts reversed, with locations -/

open AssembleTranslated in
theorem finish_eq (start : Option Loc) (cur : List Char) (acc : List (Located String))
    (inv : start = none ↔ cur = []) :
    ((splitExports.finish_548 start (cur.map HsChar.ofChar).reverse acc).reverse.map Located.unLoc) =
      (acc.reverse.map Located.unLoc) ++ AssembleValidationHelpers.finish cur := by
  unfold splitExports.finish_548 AssembleValidationHelpers.finish
  cases start with
  | none =>
    have : cur = [] := inv.mp rfl
    subst this
    simp [AssembleValidationHelpers.stripSpace]
  | some l =>
    simp only [HsList.reverse, List.reverse_reverse, pack_map_ofChar, strip_eq, null_eq, HsBase.not]
    split <;> simp_all [Located.unLoc]

open AssembleTranslated in
theorem splitGo_eq (cs : List Char) (l : Loc) (d : Int) (start : Option Loc) (cur : List Char)
    (acc : List (Located String)) (inv : start = none ↔ cur = []) :
    (splitExports.go_539 l (cs.map HsChar.ofChar) d start (cur.map HsChar.ofChar).reverse acc).map
        Located.unLoc =
      AssembleValidationHelpers.splitGo cs d cur (acc.reverse.map Located.unLoc) := by
  induction cs generalizing l d start cur acc with
  | nil =>
    simp only [List.map_nil, splitExports.go_539, AssembleValidationHelpers.splitGo]
    rw [← finish_eq start cur acc inv]
    rfl
  | cons c cs ih =>
    have e (n : Nat) (h : n.isValidChar) : (HsChar.ofNat n == HsChar.ofChar c) = (c == Char.ofNat n) := by
      rw [← eq_ofChar_lit c n h, HsBase.eq, Bool.beq_comm]
    simp only [List.map_cons, splitExports.go_539, AssembleValidationHelpers.splitGo]
    rw [eq_ofChar_lit c 44 (by decide), eq_ofChar_lit c 32 (by decide)]
    simp only [HsBase.and, HsBase.eq, HsList.null, List.isEmpty_reverse, List.isEmpty_map, HsList.elem,
      List.any_cons, List.any_nil, Bool.or_false, HsInt.add, HsInt.sub, e 40 (by decide),
      e 91 (by decide), e 41 (by decide), e 93 (by decide)]
    by_cases h1 : (c == ',' && d == 0) = true
    · simp only [h1, ite_true]
      have := ih (splitExports.adv_547 l) d none []
        (splitExports.finish_548 start (cur.map HsChar.ofChar).reverse acc) (by simp)
      rw [finish_eq start cur acc inv] at this
      simpa using this
    · by_cases h2 : (c == ' ' && cur.isEmpty) = true
      · simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
        exact ih _ _ start cur acc inv
      · simp only [h1, h2, ite_false, Bool.false_eq_true]
        have := ih (splitExports.adv_547 l) (if (c == '(' || c == '[') = true then d + 1
          else if (c == ')' || c == ']') = true then d - 1 else d)
          (HsBase.maybe (some l) some start) (cur ++ [c]) acc
          (by cases start <;> simp [HsBase.maybe])
        simpa using this

theorem splitExports_eq (l : AssembleTranslated.Loc) (t : String) :
    (AssembleTranslated.splitExports l t).map AssembleTranslated.Located.unLoc =
      AssembleValidationHelpers.splitExports t := by
  unfold AssembleTranslated.splitExports AssembleValidationHelpers.splitExports
  rw [unpack_eq]
  exact splitGo_eq t.toList l 0 none [] [] (by simp)

end PegHs.AssembleTextProof
