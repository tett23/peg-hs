import AssembleTextProof

/-!
`isExportItem` of the translation of Peg.Grammar.Assemble (AssembleTranslated)
against the model `validExport` of AssemblePredicates, on every input.

The translation splits the text into tokens of code points
(`isExportItem.tokens`) and parses them with `item`, `plain`, `names` and
`member`; the model does the same on tokens that are strings. `codes` maps a
model token to the translation's: each production of the translation applied
to the codes of the model's tokens gives the codes of the model's result.

Theorems: `tokens_eq`, `member_eq`, `names_eq`, `plain_eq`, `item_eq` and
`isExportItem_eq`.
-/

namespace PegHs.AssembleTextProof
open PegHs.AssembleValidation

/-- The code points of a text, as the translation reads a token. -/
def codes (s : String) : List HsChar := s.toList.map HsChar.ofChar

theorem codes_inj {s u : String} : codes s = codes u ↔ s = u := by
  constructor
  · intro h
    have : s.toList = u.toList := (List.map_inj_right (fun _ _ h => ofChar_inj.mp h)).mp h
    exact String.toList_inj.mp this
  · intro h; rw [h]

theorem pack_codes (s : String) : HsText.pack (codes s) = s := by
  simp [codes, pack_map_ofChar, String.ofList_toList]

theorem elem_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    (inj : ∀ a b, f a = f b → a = b) (x : α) (xs : List α) :
    HsList.elem (f x) (xs.map f) = xs.contains x := by
  rw [Bool.eq_iff_iff]
  simp only [HsList.elem, List.any_map, List.any_eq_true, Function.comp_def, beq_iff_eq, List.contains_iff_mem]
  constructor
  · rintro ⟨y, hy, e⟩; rw [← inj _ _ e]; exact hy
  · intro h; exact ⟨x, h, rfl⟩

theorem eq_codes (s u : String) : HsBase.eq (codes s) (codes u) = (s == u) := by
  rw [HsBase.eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, codes_inj]

theorem elem_codes (s : String) (xs : List String) : HsList.elem (codes s) (xs.map codes) = xs.contains s :=
  elem_map_inj codes (fun _ _ h => codes_inj.mp h) s xs

theorem notElem_codes (s : String) (xs : List String) : HsList.notElem (codes s) (xs.map codes) = !xs.contains s := by
  rw [← elem_codes]; rfl

theorem elem_ofChar (c : Char) (xs : List Char) :
    HsList.elem (HsChar.ofChar c) (xs.map HsChar.ofChar) = xs.contains c :=
  elem_map_inj HsChar.ofChar (fun _ _ h => ofChar_inj.mp h) c xs

/-- The delimiters of `tokens`. -/
def delim (c : Char) : Bool := c == ' ' || c == '\t' || "(),".toList.contains c

theorem tokensGo_word (cur cs : List Char) :
    tokensGo cur cs = flush ((cs.takeWhile (fun c => !delim c)).reverse ++ cur) ++
      tokensGo [] (cs.dropWhile (fun c => !delim c)) := by
  induction cs generalizing cur with
  | nil => simp [tokensGo, flush]
  | cons c cs ih =>
    by_cases hs : (c == ' ' || c == '\t') = true
    · have hd : delim c = true := by simp [delim, hs]
      simp [tokensGo, hs, hd, flush]
    · by_cases hp : "(),".toList.contains c = true
      · have hd : delim c = true := by simp only [delim, hp, Bool.or_true]
        simp only [tokensGo, hs, hp, hd, List.takeWhile_cons, List.dropWhile_cons, Bool.not_true,
          Bool.false_eq_true, ite_false, ite_true, List.reverse_nil, List.nil_append]
        simp [flush]
      · have hd : delim c = false := by simp_all [delim]
        simp only [tokensGo, hs, hp, Bool.false_eq_true, ite_false, List.takeWhile_cons,
          List.dropWhile_cons, hd, Bool.not_false, ite_true, ih, List.reverse_cons, List.append_assoc,
          List.singleton_append]

theorem lit_parens : [HsChar.ofNat 40, HsChar.ofNat 41, HsChar.ofNat 44] = "(),".toList.map HsChar.ofChar := by
  decide

theorem lit_delims : [HsChar.ofNat 32, HsChar.ofNat 9, HsChar.ofNat 40, HsChar.ofNat 41, HsChar.ofNat 44] =
    " \t(),".toList.map HsChar.ofChar := by
  decide

theorem delim_eq (c : Char) : " \t(),".toList.contains c = delim c := by
  rw [Bool.eq_iff_iff]
  simp [delim]
  grind

theorem space_tab_eq (c : Char) :
    HsBase.or (HsBase.eq (HsChar.ofChar c) (HsChar.ofNat 32)) (HsBase.eq (HsChar.ofChar c) (HsChar.ofNat 9)) =
      (c == ' ' || c == '\t') := by
  rw [eq_ofChar_lit _ 32 (by decide), eq_ofChar_lit _ 9 (by decide)]
  rfl

theorem break_delims (l : List Char) :
    HsList.break (fun x => HsList.elem x [HsChar.ofNat 32, HsChar.ofNat 9, HsChar.ofNat 40, HsChar.ofNat 41,
      HsChar.ofNat 44]) (l.map HsChar.ofChar) =
      ((l.takeWhile (fun c => !delim c)).map HsChar.ofChar, (l.dropWhile (fun c => !delim c)).map HsChar.ofChar) := by
  have p : ((fun x => !HsList.elem x [HsChar.ofNat 32, HsChar.ofNat 9, HsChar.ofNat 40, HsChar.ofNat 41,
      HsChar.ofNat 44]) ∘ HsChar.ofChar) = fun c => !delim c := by
    funext c
    simp only [Function.comp_def, lit_delims, elem_ofChar, delim_eq]
  simp only [HsList.break, HsList.span, List.takeWhile_map, List.dropWhile_map, p]

theorem E_singleton (c : Char) : codes (String.singleton c) = [HsChar.ofChar c] := by
  simp [codes]

theorem E_ofList (cs : List Char) : codes (String.ofList cs) = cs.map HsChar.ofChar := by
  simp [codes]

theorem tokens_eq (cs : List Char) :
    AssembleTranslated.isExportItem.tokens_525 (cs.map HsChar.ofChar) = (tokens cs).map codes :=
  match cs with
  | [] => by
    rw [AssembleTranslated.isExportItem.tokens_525.eq_def]
    rfl
  | c :: cs => by
    show AssembleTranslated.isExportItem.tokens_525 (HsChar.ofChar c :: cs.map HsChar.ofChar) = _
    rw [AssembleTranslated.isExportItem.tokens_525.eq_def]
    simp only [space_tab_eq]
    by_cases hs : (c == ' ' || c == '\t') = true
    · simp only [hs, ite_true, tokens_eq cs, tokens, tokensGo, flush, List.isEmpty_nil, List.nil_append]
    · have hp : HsList.elem (HsChar.ofChar c) [HsChar.ofNat 40, HsChar.ofNat 41, HsChar.ofNat 44] =
          "(),".toList.contains c := by rw [lit_parens, elem_ofChar]
      simp only [hs, Bool.false_eq_true, ite_false, hp]
      by_cases hq : "(),".toList.contains c = true
      · simp only [hq, ite_true]
        rw [tokens_eq cs]
        simp only [tokens]
        rw [tokensGo]
        simp only [hs, hq, ite_true, Bool.false_eq_true, ite_false, flush, List.isEmpty_nil, List.nil_append,
          List.map_cons, E_singleton]
      · have hd : delim c = false := by simp_all [delim]
        have hb := break_delims (c :: cs)
        rw [List.map_cons] at hb
        have hw : List.dropWhile (fun c => !delim c) (c :: cs) = List.dropWhile (fun c => !delim c) cs := by
          simp [hd]
        have ht : List.takeWhile (fun c => !delim c) (c :: cs) = c :: List.takeWhile (fun c => !delim c) cs := by
          simp [hd]
        have hm : tokens (c :: cs) = flush ((cs.takeWhile (fun c => !delim c)).reverse ++ [c]) ++
            tokens (cs.dropWhile (fun c => !delim c)) := by
          simp only [tokens]
          rw [tokensGo]
          simp only [hs, hq, Bool.false_eq_true, ite_false]
          exact tokensGo_word [c] cs
        simp only [hq, Bool.false_eq_true, ite_false]
        rw [hb, hw, ht, hm, tokens_eq (List.dropWhile (fun c => !delim c) cs)]
        simp [flush, codes]
termination_by cs.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := (List.dropWhile_sublist (l := cs) (fun c => !delim c)).length_le; omega)

/-! ## Names and operators -/

theorem exportIdent_eq (s : String) : AssembleTranslated.isExportItem.exportIdent_508 s = exportIdent s := by
  simp only [AssembleTranslated.isExportItem.exportIdent_508, exportIdent, HsBase.and, HsBase.not,
    isValidIdent_eq, startsWithModifier_eq]

theorem notElem_eq {α : Type} [BEq α] (x : α) (xs : List α) : HsList.notElem x xs = !HsList.elem x xs := rfl

theorem unqualifiedName_eq (options : List String) (s : String) :
    AssembleTranslated.isExportItem.unqualifiedName_509 (recursiveDoEnabled options) (arrowsEnabled options) s =
      unqualifiedName options s := by
  simp only [AssembleTranslated.isExportItem.unqualifiedName_509, unqualifiedName, HsBase.and, HsBase.not,
    exportIdent_eq, extensionKeyword_eq, reservedWords_eq, notElem_eq, elem_eq_contains, Bool.and_assoc]

theorem null_codes (s : String) : HsList.null (codes s) = s.isEmpty := by
  rw [Bool.eq_iff_iff]
  simp [HsList.null, codes, String.isEmpty_iff, String.toList_eq_nil_iff]

theorem lit_symbols : [HsChar.ofNat 33, HsChar.ofNat 35, HsChar.ofNat 36, HsChar.ofNat 37, HsChar.ofNat 38,
    HsChar.ofNat 42, HsChar.ofNat 43, HsChar.ofNat 46, HsChar.ofNat 47, HsChar.ofNat 60, HsChar.ofNat 61,
    HsChar.ofNat 62, HsChar.ofNat 63, HsChar.ofNat 64, HsChar.ofNat 92, HsChar.ofNat 94, HsChar.ofNat 124,
    HsChar.ofNat 45, HsChar.ofNat 126, HsChar.ofNat 58] = symbolChars.map HsChar.ofChar := by
  decide

theorem lit_reservedOps : [[HsChar.ofNat 46, HsChar.ofNat 46], [HsChar.ofNat 58, HsChar.ofNat 58],
    [HsChar.ofNat 61], [HsChar.ofNat 92], [HsChar.ofNat 124], [HsChar.ofNat 60, HsChar.ofNat 45],
    [HsChar.ofNat 45, HsChar.ofNat 62], [HsChar.ofNat 61, HsChar.ofNat 62]] =
    ["..", "::", "=", "\\", "|", "<-", "->", "=>"].map codes := by
  decide

theorem lit_arrowOps : [[HsChar.ofNat 45, HsChar.ofNat 60], [HsChar.ofNat 62, HsChar.ofNat 45],
    [HsChar.ofNat 45, HsChar.ofNat 60, HsChar.ofNat 60], [HsChar.ofNat 62, HsChar.ofNat 62, HsChar.ofNat 45]] =
    ["-<", ">-", "-<<", ">>-"].map codes := by
  decide

theorem isOperator_eq (options : List String) (op : String) :
    AssembleTranslated.isExportItem.isOperator_520 (arrowsEnabled options) (codes op) = isOperator options op := by
  simp only [AssembleTranslated.isExportItem.isOperator_520, isOperator, HsBase.and, HsBase.not, HsBase.or,
    null_codes, lit_reservedOps, lit_arrowOps, notElem_codes, AssembleTranslated.isExportItem.isSymbolChar_523,
    lit_symbols, HsList.all]
  simp only [codes, List.all_map, Function.comp_def, elem_ofChar, Bool.and_assoc]

theorem breakOnEnd_dot (n : List Char) :
    HsText.breakOnEnd "." (String.ofList n) =
      (String.ofList (breakOnEndDot n).1, String.ofList (breakOnEndDot n).2) := by
  have dot : (".").toList = ['.'] := rfl
  simp [HsText.breakOnEnd, dot, breakOnList_single, breakOnEndDot]

theorem isQualifiedName_eq (options : List String) (n : String) :
    AssembleTranslated.isExportItem.isQualifiedName_513 (recursiveDoEnabled options) (arrowsEnabled options) (codes n) =
      isQualifiedName options n := by
  unfold AssembleTranslated.isExportItem.isQualifiedName_513 isQualifiedName
  rw [pack_codes, ← String.ofList_toList (s := n), breakOnEnd_dot, String.toList_ofList]
  cases breakOnEndDot n.toList with
  | mk q nm =>
    cases q with
    | nil => simp [HsBase.eq, unqualifiedName_eq]
    | cons c q =>
      have ne : HsBase.eq (String.ofList (c :: q)) "" = false := by
        simp [HsBase.eq, ← String.toList_inj]
      have drop : HsText.dropEnd 1 (String.ofList (c :: q)) = String.ofList (c :: q).dropLast := by
        simp [HsText.dropEnd, List.dropLast_eq_take]
      simp only [ne, Bool.false_eq_true, ite_false, drop, isModuleName_eq, exportIdent_eq, HsBase.and,
        HsBase.ne, HsBase.or, HsBase.not, Bool.and_assoc]
      rfl

theorem isTypeName_eq (options : List String) (n : String) :
    AssembleTranslated.isExportItem.isTypeName_511 (recursiveDoEnabled options) (arrowsEnabled options) (codes n) =
      isTypeName options n := by
  unfold AssembleTranslated.isExportItem.isTypeName_511 isTypeName
  have dot : (fun c => HsBase.ne (HsChar.ofChar c) (HsChar.ofNat 46)) = (· != '.') := by
    funext c
    have := eq_ofChar_lit c 46 (by decide)
    simp only [HsBase.eq] at this
    simp only [HsBase.ne, this]
    rfl
  have twe : HsText.takeWhileEnd (fun x => HsBase.ne x (HsChar.ofNat 46)) (HsText.pack (codes n)) =
      String.ofList (breakOnEndDot n.toList).2 := by
    rw [pack_codes]
    simp only [HsText.takeWhileEnd, breakOnEndDot, dot]
  rw [twe, isQualifiedName_eq]
  simp only [HsBase.and, HsText.uncons, String.toList_ofList]
  cases (breakOnEndDot n.toList).2 with
  | nil => rfl
  | cons c cs => simp [HsMaybe.fmap, HsBase.maybe, isUpper_ofChar]

/-! ## The productions of an export item -/

theorem lit_open : [HsChar.ofNat 40] = codes "(" := by decide
theorem lit_close : [HsChar.ofNat 41] = codes ")" := by decide
theorem lit_comma : [HsChar.ofNat 44] = codes "," := by decide
theorem lit_dots : [HsChar.ofNat 46, HsChar.ofNat 46] = codes ".." := by decide
theorem lit_module : [HsChar.ofNat 109, HsChar.ofNat 111, HsChar.ofNat 100, HsChar.ofNat 117, HsChar.ofNat 108,
    HsChar.ofNat 101] = codes "module" := by decide
theorem lit_keywords : [[HsChar.ofNat 116, HsChar.ofNat 121, HsChar.ofNat 112, HsChar.ofNat 101],
    [HsChar.ofNat 112, HsChar.ofNat 97, HsChar.ofNat 116, HsChar.ofNat 116, HsChar.ofNat 101, HsChar.ofNat 114,
      HsChar.ofNat 110]] = ["type", "pattern"].map codes := by decide

theorem member_eq (options : List String) (ts : List String) :
    AssembleTranslated.isExportItem.member_504 (recursiveDoEnabled options) (arrowsEnabled options) (ts.map codes) =
      (exportMember options ts).map (List.map codes) := by
  unfold AssembleTranslated.isExportItem.member_504
  unfold exportMember
  match ts with
  | x :: y :: z :: rest =>
    simp only [List.map_cons, lit_open, lit_close, eq_codes, isOperator_eq, pack_codes, unqualifiedName_eq,
      exportMemberName]
    split <;> simp_all
    split <;> (try split) <;> simp_all
  | [] => rfl
  | [x] => simp [pack_codes, unqualifiedName_eq, exportMemberName]
  | [x, y] => simp [pack_codes, unqualifiedName_eq, exportMemberName]

theorem names_eq (options : List String) (ts : List String) :
    AssembleTranslated.isExportItem.names_498 (recursiveDoEnabled options) (arrowsEnabled options) (ts.map codes) =
      (exportNames options ts).map (List.map codes) := by
  rw [AssembleTranslated.isExportItem.names_498.eq_def, exportNames, member_eq]
  split
  · rename_i hm
    rw [hm]
    rfl
  · rename_i rest hm
    simp only [hm, HsMaybe.bind, Option.map_some]
    have := exportMember_shorter options ts _ hm
    cases rest with
    | nil => rfl
    | cons y more =>
      simp only [List.map, lit_comma, lit_close, eq_codes]
      by_cases h1 : y = ","
      · subst h1
        simp only [beq_self_eq_true, ite_true]
        exact names_eq options more
      · by_cases h2 : y = ")"
        · subst h2
          simp
        · simp only [show (y == ",") = false by simpa using h1, show (y == ")") = false by simpa using h2,
            Bool.false_eq_true, ite_false]
          split <;> grind
termination_by ts.length
decreasing_by
  simp only [List.length_cons] at this
  omega

/-! The productions of AssemblePredicates with their string patterns as conditions. -/

theorem exportPlainList_cons (options : List String) (n x : String) (rest : List String) :
    exportPlainList options (n :: x :: rest) =
      if (x == "(" && isTypeName options n) = true then exportNames options rest
      else exportPlainSingle options (n :: x :: rest) := by
  unfold exportPlainList
  by_cases hx : x = "("
  · subst hx; simp
  · simp only [show (x == "(") = false by simpa using hx, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> grind

theorem exportPlainNamed_cons (options : List String) (n x y z : String) (rest : List String) :
    exportPlainNamed options (n :: x :: y :: z :: rest) =
      if (x == "(" && y == ".." && z == ")" && isTypeName options n) = true then some rest
      else exportPlainList options (n :: x :: y :: z :: rest) := by
  unfold exportPlainNamed
  by_cases h : x = "(" ∧ y = ".." ∧ z = ")"
  · obtain ⟨rfl, rfl, rfl⟩ := h; simp
  · have : (x == "(" && y == ".." && z == ")") = false := by simp; grind
    simp only [this, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> grind

theorem exportPlain_cons (options : List String) (x op y : String) (rest : List String) :
    exportPlain options (x :: op :: y :: rest) =
      if (x == "(" && y == ")" && isOperator options op) = true then some rest
      else exportPlainNamed options (x :: op :: y :: rest) := by
  unfold exportPlain
  by_cases h : x = "(" ∧ y = ")"
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have : (x == "(" && y == ")") = false := by simp; grind
    simp only [this, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> grind

theorem exportItem_cons (options : List String) (k m : String) (rest : List String) :
    exportItem options (k :: m :: rest) =
      if (k == "module" && validModule m) = true then some rest
      else if ["type", "pattern"].contains k = true then exportPlain options (m :: rest)
      else exportPlain options (k :: m :: rest) := by
  unfold exportItem
  by_cases hk : k = "module"
  · subst hk; simp
  · simp only [show (k == "module") = false by simpa using hk, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> grind

theorem exportPlainNamed_three (options : List String) (a b c : String) :
    exportPlainNamed options [a, b, c] = exportPlainList options [a, b, c] := by
  unfold exportPlainNamed
  split
  · rename_i h; simp at h
  · rfl

theorem plain_eq (options : List String) (ts : List String) :
    AssembleTranslated.isExportItem.plain_491 (recursiveDoEnabled options) (arrowsEnabled options) (ts.map codes) =
      (exportPlain options ts).map (List.map codes) := by
  unfold AssembleTranslated.isExportItem.plain_491
  rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · rfl
  · simp [isQualifiedName_eq, exportPlain, exportPlainNamed, exportPlainList, exportPlainSingle]
  · have n0 := names_eq options []
    simp only [List.map] at n0
    simp only [List.map, lit_open, eq_codes, isQualifiedName_eq, isTypeName_eq, n0, exportPlainSingle,
      exportPlain, exportPlainNamed, exportPlainList_cons]
    repeat' split
    all_goals simp_all
  · have n1 := names_eq options [c]
    simp only [List.map] at n1
    simp only [List.map, lit_open, lit_close, eq_codes, isOperator_eq, isQualifiedName_eq, isTypeName_eq, n1,
      exportPlainSingle, exportPlain_cons, exportPlainNamed_three, exportPlainList_cons]
    repeat' split
    all_goals simp_all
  · have n2 := names_eq options (c :: d :: rest)
    simp only [List.map] at n2
    simp only [List.map, lit_open, lit_close, lit_dots, eq_codes, isOperator_eq, isQualifiedName_eq,
      isTypeName_eq, n2, exportPlainSingle, exportPlain_cons, exportPlainNamed_cons, exportPlainList_cons]
    repeat' split
    all_goals simp_all

theorem item_eq (options : List String) (ts : List String) :
    AssembleTranslated.isExportItem.item_486 (recursiveDoEnabled options) (arrowsEnabled options) (ts.map codes) =
      (exportItem options ts).map (List.map codes) := by
  unfold AssembleTranslated.isExportItem.item_486
  rcases ts with _ | ⟨k, _ | ⟨m, rest⟩⟩
  · exact plain_eq options []
  · have p1 := plain_eq options []
    have p2 := plain_eq options [k]
    have hk := elem_codes k ["type", "pattern"]
    simp only [List.map] at p1 p2 hk
    simp only [List.map, lit_keywords, hk, p1, p2, exportItem]
    split <;> simp_all
  · have p1 := plain_eq options (m :: rest)
    have p2 := plain_eq options (k :: m :: rest)
    have hk := elem_codes k ["type", "pattern"]
    simp only [List.map] at p1 p2 hk
    simp only [List.map, lit_module, lit_keywords, eq_codes, hk, pack_codes, isModuleName_eq, p1, p2,
      exportItem_cons]
    repeat' split
    all_goals simp_all

theorem isInfixOf_eq (needle hay : List Char) : HsText.isInfixList needle hay = isInfixOf needle hay := by
  induction hay with
  | nil => rfl
  | cons c cs ih => simp only [HsText.isInfixList, isInfixOf, ih]

theorem isExportItem_eq (options : List String) (t : String) :
    AssembleTranslated.isExportItem (recursiveDoEnabled options) (arrowsEnabled options) t =
      validExport options t := by
  unfold AssembleTranslated.isExportItem validExport
  rw [unpack_eq, tokens_eq, item_eq]
  simp only [HsBase.and, HsBase.not, HsList.any, HsText.isInfixOf, isInfixOf_eq]
  cases exportItem options (tokens t.toList) with
  | none => rfl
  | some ts => simp [HsBase.maybe, HsList.null]

end PegHs.AssembleTextProof

#print axioms PegHs.AssembleTextProof.isExportItem_eq
