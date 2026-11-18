import AssembleTextProof

/-!
The string argument of `%expect` and `%message`: the translation of
`Peg.Grammar.Assemble.stringArg` and of the decoder `decodeString` that it calls
(AssembleTranslated) against the model `AssembleValidationHelpers.stringArg`, a
state machine folded over the characters.

- `decode_agree`: the mutual functions `go`, `escape` and `unicode` of the
  translation agree with the model's states `plain`, `escaped` and `brace` on
  every input: both fail, or both succeed with the same decoded characters and
  the same characters after the closing quote. Both map a surrogate code point
  of `\u{...}` to U+FFFD (the translation through `T.pack`).
- `stringArg_eq`: the translated `stringArg` fails exactly when the model does,
  and otherwise returns the model's name. AssembleValidation reads no more of
  it (the diagnostics' wording and locations are erased).
-/

open PegHs PegHs.AssembleTextProof
open AssembleTranslated
open PegHs.AssembleValidationHelpers (decodeStep finishDecode hexValue simpleEscape DecodeState)

namespace PegHs.AssembleTextProof

/-- What the decoded string shows: failure, or the characters and the rest. -/
def tOut : Except Diagnostic (String × List HsChar) → Except Unit (List Char × List Char)
  | .error _ => .error ()
  | .ok (s, r) => .ok (s.toList, r.map HsText.toChar)

/-- The same view of the model's decoding. -/
def mOut : Except String (List Char × List Char) → Except Unit (List Char × List Char)
  | .error _ => .error ()
  | .ok p => .ok p

theorem foldl_failed (cs : List Char) (m : String) :
    cs.foldl decodeStep (.failed m) = .failed m := by
  induction cs <;> simp_all [decodeStep]

theorem foldl_done (cs : List Char) (v t : List Char) :
    cs.foldl decodeStep (.done v t) = .done v (t ++ cs) := by
  induction cs generalizing t <;> simp_all [decodeStep]

def hexDigit (c : Char) : Bool := (hexValue c).isSome

def hexNumber (n : Nat) (hs : List Char) : Nat := hs.foldl (fun m c => m * 16 + (hexValue c).getD 0) n

theorem foldl_hex (hs : List Char) (h : ∀ c ∈ hs, hexDigit c = true) (v : List Char) (d n : Nat) :
    hs.foldl decodeStep (.hex v d n) = .hex v (d + hs.length) (hexNumber n hs) := by
  induction hs generalizing d n with
  | nil => rfl
  | cons c hs ih =>
    have hc := h c (by simp)
    simp only [hexDigit, Option.isSome_iff_exists] at hc
    obtain ⟨k, hk⟩ := hc
    simp only [List.foldl_cons, decodeStep, hk, hexNumber, Option.getD_some]
    rw [ih (fun x hx => h x (by simp [hx]))]
    simp [hexNumber]; omega

theorem isHexDigit_ofChar (c : Char) : HsChar.isHexDigit (HsChar.ofChar c) = hexDigit c := by
  simp only [HsChar.isHexDigit, HsChar.isDigit, ofChar_val, hexDigit, hexValue]
  by_cases a1 : 48 ≤ c.toNat <;> by_cases a2 : c.toNat ≤ 57 <;> by_cases a3 : 65 ≤ c.toNat <;>
    by_cases a4 : c.toNat ≤ 70 <;> by_cases a5 : 97 ≤ c.toNat <;> by_cases a6 : c.toNat ≤ 102 <;>
    simp [a1, a2, a3, a4, a5, a6] <;> omega

theorem digitToInt_ofChar (c : Char) (h : hexDigit c = true) :
    HsChar.digitToInt (HsChar.ofChar c) = ((hexValue c).getD 0 : Nat) := by
  simp only [hexDigit, hexValue] at h
  simp only [HsChar.digitToInt, HsChar.isDigit, ofChar_val, hexValue]
  by_cases a1 : 48 ≤ c.toNat <;> by_cases a2 : c.toNat ≤ 57 <;> by_cases a3 : 65 ≤ c.toNat <;>
    by_cases a4 : c.toNat ≤ 70 <;> by_cases a5 : 97 ≤ c.toNat <;> by_cases a6 : c.toNat ≤ 102 <;>
    simp [a1, a2, a3, a4, a5, a6] at h ⊢ <;> omega

theorem span_hex (cs : List Char) :
    HsList.span HsChar.isHexDigit (cs.map HsChar.ofChar) =
      ((cs.takeWhile hexDigit).map HsChar.ofChar, (cs.dropWhile hexDigit).map HsChar.ofChar) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [HsList.span] at ih ⊢
    simp only [List.map_cons, List.takeWhile_cons, List.dropWhile_cons, isHexDigit_ofChar]
    cases hexDigit c <;> simp_all

theorem number_ofChar (hs : List Char) (h : ∀ c ∈ hs, hexDigit c = true) (n : Nat) :
    HsList.foldl (fun (m : Int) (d : HsChar) => HsInt.add (HsInt.mul m 16) (HsInt.toInteger (HsChar.digitToInt d)))
      (n : Int) (hs.map HsChar.ofChar) = (hexNumber n hs : Int) := by
  induction hs generalizing n with
  | nil => rfl
  | cons c hs ih =>
    simp only [HsList.foldl, List.map_cons, List.foldl_cons] at ih ⊢
    rw [digitToInt_ofChar c (h c (by simp))]
    have := ih (fun x hx => h x (by simp [hx])) (n * 16 + (hexValue c).getD 0)
    simp only [HsInt.add, HsInt.mul, HsInt.toInteger] at this ⊢
    push_cast at this ⊢
    rw [this]; rfl


theorem go_nil (S : List (HsChar × HsChar)) (l : Loc) (acc : List HsChar) :
    tOut (decodeString.go_158 S l acc []) = .error () := by
  rw [decodeString.go_158.eq_def]; rfl

theorem escape_nil (S : List (HsChar × HsChar)) (back l : Loc) (acc : List HsChar) :
    tOut (decodeString.escape_164 S back l acc []) = .error () := by
  rw [decodeString.escape_164.eq_def]; rfl

theorem unicode_nil (S : List (HsChar × HsChar)) (back l : Loc) (acc : List HsChar) :
    tOut (decodeString.unicode_171 S back l acc []) = .error () := by
  rw [decodeString.unicode_171.eq_def]; rfl

theorem go_cons (S : List (HsChar × HsChar)) (l : Loc) (acc : List HsChar) (c : Char) (cs : List Char) :
    decodeString.go_158 S l acc (HsChar.ofChar c :: cs.map HsChar.ofChar) =
      if c = '"' then .ok (HsText.pack acc.reverse, cs.map HsChar.ofChar)
      else if c = '\\' then
        decodeString.escape_164 S l (decodeString.next__157 l (HsChar.ofNat 92)) acc (cs.map HsChar.ofChar)
      else decodeString.go_158 S (decodeString.next__157 l (HsChar.ofChar c)) (HsChar.ofChar c :: acc)
        (cs.map HsChar.ofChar) := by
  rw [decodeString.go_158.eq_def]
  simp only [eq_ofChar_lit _ 34 (by decide), eq_ofChar_lit _ 92 (by decide), HsList.reverse]
  by_cases h1 : c = '"' <;> by_cases h2 : c = '\\' <;> simp_all

theorem escape_cons (S : List (HsChar × HsChar)) (back l : Loc) (acc : List HsChar) (c : Char)
    (cs : List Char) :
    tOut (decodeString.escape_164 S back l acc (HsChar.ofChar c :: cs.map HsChar.ofChar)) =
      if c = 'u' then
        tOut (decodeString.unicode_171 S back (decodeString.next__157 l (HsChar.ofNat 117)) acc
          (cs.map HsChar.ofChar))
      else match HsList.lookup (HsChar.ofChar c) S with
        | some d => tOut (decodeString.go_158 S (decodeString.next__157 l (HsChar.ofChar c)) (d :: acc)
            (cs.map HsChar.ofChar))
        | none => .error () := by
  rw [decodeString.escape_164.eq_def]
  simp only [eq_ofChar_lit _ 117 (by decide)]
  by_cases h1 : c = 'u'
  · simp [h1]
  · have h1' : ¬c = Char.ofNat 117 := h1
    simp only [h1]
    cases HsList.lookup (HsChar.ofChar c) S <;> simp [tOut, h1']

theorem unicode_cons (S : List (HsChar × HsChar)) (back l : Loc) (acc : List HsChar) (c : Char)
    (cs : List Char) :
    tOut (decodeString.unicode_171 S back l acc (HsChar.ofChar c :: cs.map HsChar.ofChar)) =
      if c = '{' then
        match cs.dropWhile hexDigit with
        | [] => .error ()
        | c2 :: more =>
          if c2 = '}' ∧ cs.takeWhile hexDigit ≠ [] ∧ hexNumber 0 (cs.takeWhile hexDigit) ≤ 1114111 then
            tOut (decodeString.go_158 S (decodeString.next__157 (advanceLoc (decodeString.next__157 l
                (HsChar.ofNat 123)) (HsText.pack ((cs.takeWhile hexDigit).map HsChar.ofChar)))
                (HsChar.ofNat 125))
              (HsChar.ofNat (hexNumber 0 (cs.takeWhile hexDigit)) :: acc) (more.map HsChar.ofChar))
          else .error ()
      else .error () := by
  have hn := number_ofChar (cs.takeWhile hexDigit)
    (fun x hx => List.all_eq_true.mp List.all_takeWhile x hx) 0
  simp only [Int.natCast_zero] at hn
  rw [decodeString.unicode_171.eq_def]
  simp only [eq_ofChar_lit _ 123 (by decide), span_hex]
  by_cases hc : c = '{'
  · have hc' : c = Char.ofNat 123 := hc
    simp only [hc', beq_self_eq_true, ite_true]
    split
    · rename_i ν more hsnd
      rw [span_hex] at hsnd
      cases hd : cs.dropWhile hexDigit with
      | nil => simp [hd] at hsnd
      | cons c2 more' =>
        simp only [hd, List.map_cons, List.cons.injEq] at hsnd
        obtain ⟨rfl, rfl⟩ := hsnd
        simp only [eq_ofChar_lit _ 125 (by decide), hn, HsBase.and, HsBase.not, HsInt.le, HsList.null,
          HsInt.fromInteger, HsChar.chr, Int.toNat_natCast, List.isEmpty_map]
        by_cases h2 : c2 = '}'
        · have h2' : c2 = Char.ofNat 125 := h2
          by_cases h3 : (cs.takeWhile hexDigit) ≠ [] ∧ hexNumber 0 (cs.takeWhile hexDigit) ≤ 1114111
          · have hle : ((hexNumber 0 (cs.takeWhile hexDigit) : Nat) : Int) ≤ 1114111 := by
              have := h3.2; omega
            simp_all
          · simp only [h2', h3, beq_self_eq_true, ite_true, ite_false, and_false]
            have : ¬ ((!(List.takeWhile hexDigit cs).isEmpty &&
                decide ((hexNumber 0 (List.takeWhile hexDigit cs) : Int) ≤ 1114111)) = true) := by
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq]
              intro hh
              exact h3 ⟨hh.1, by have := hh.2; omega⟩
            simp [this, tOut]
        · have h2' : ¬c2 = Char.ofNat 125 := h2
          simp [h2', tOut]
    · rename_i hsnd
      rw [span_hex] at hsnd
      cases hd : cs.dropWhile hexDigit with
      | nil => rfl
      | cons c2 more' => exact (hsnd (HsChar.ofChar c2) (more'.map HsChar.ofChar) (by simp [hd])).elim
  · have hc' : ¬c = Char.ofNat 123 := hc
    simp [hc', tOut]

theorem toChar_ofNat (n : Nat) (h : n ≤ 0x10FFFF) : HsText.toChar (HsChar.ofNat n) =
    Char.ofNat (if 0xD800 ≤ n && n ≤ 0xDFFF then 0xFFFD else n) := by
  have lt : n < 0x110000 := by omega
  simp only [HsText.toChar, HsChar.ofNat, lt, dite_true, Nat.isValidChar]
  split <;> split <;> simp_all <;> first | omega | rfl

theorem toList_pack (xs : List HsChar) : (HsText.pack xs).toList = xs.map HsText.toChar := by
  simp [HsText.pack]

/-- The decoding of a string: the translation of go, escape and unicode against the
model's states plain, escaped and brace. -/
theorem decode_agree (S : List (HsChar × HsChar))
    (hS : ∀ c, HsList.lookup (HsChar.ofChar c) S = (simpleEscape c).map HsChar.ofChar) (n : Nat) :
    ∀ cs : List Char, cs.length ≤ n → ∀ (l back : Loc) (acc : List HsChar),
      tOut (decodeString.go_158 S l acc (cs.map HsChar.ofChar)) =
          mOut (finishDecode (cs.foldl decodeStep (.plain (acc.reverse.map HsText.toChar)))) ∧
      tOut (decodeString.escape_164 S back l acc (cs.map HsChar.ofChar)) =
          mOut (finishDecode (cs.foldl decodeStep (.escaped (acc.reverse.map HsText.toChar)))) ∧
      tOut (decodeString.unicode_171 S back l acc (cs.map HsChar.ofChar)) =
          mOut (finishDecode (cs.foldl decodeStep (.brace (acc.reverse.map HsText.toChar)))) := by
  induction n with
  | zero =>
    intro cs hlen l back acc
    have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [go_nil, escape_nil, unicode_nil, finishDecode, mOut]
  | succ n ih =>
    intro cs hlen l back acc
    cases cs with
    | nil => simp [go_nil, escape_nil, unicode_nil, finishDecode, mOut]
    | cons c cs =>
      have hcs : cs.length ≤ n := by simp at hlen; omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.map_cons, go_cons, List.foldl_cons, decodeStep]
        by_cases h1 : c = '"'
        · simp [h1, tOut, foldl_done, finishDecode, mOut, toList_pack, Function.comp_def, toChar_ofChar]
        · by_cases h2 : c = '\\'
          · simp [h2, (ih cs hcs _ l acc).2.1]
          · simp only [h1, h2, ite_false, beq_iff_eq]
            rw [(ih cs hcs _ l _).1]
            simp [toChar_ofChar]
      · rw [List.map_cons, escape_cons, List.foldl_cons]
        by_cases h1 : c = 'u'
        · simp only [h1, ↓reduceIte]
          rw [(ih cs hcs _ back acc).2.2]
          simp [decodeStep]
        · simp only [h1, ite_false, decodeStep, beq_iff_eq, hS]
          cases simpleEscape c with
          | none => simp [foldl_failed, finishDecode, mOut]
          | some d =>
            simp only [Option.map_some]
            rw [(ih cs hcs _ l _).1]
            simp [toChar_ofChar]
      · rw [List.map_cons, unicode_cons, List.foldl_cons]
        by_cases h1 : c = '{'
        · simp only [h1, ite_true, decodeStep, beq_self_eq_true]
          conv => rhs; rw [← List.takeWhile_append_dropWhile (p := hexDigit) (l := cs), List.foldl_append,
            foldl_hex _ (fun x hx => List.all_eq_true.mp List.all_takeWhile x hx)]
          cases hd : cs.dropWhile hexDigit with
          | nil => simp [finishDecode, mOut]
          | cons c2 more =>
            have hc2 : hexDigit c2 = false := by
              have := List.head_dropWhile_not hexDigit (l := cs) (by simp [hd])
              simpa [hd] using this
            have hv : hexValue c2 = none := by simpa [hexDigit] using hc2
            have hmore : more.length ≤ n := by
              have := (List.dropWhile_sublist (l := cs) hexDigit).length_le
              rw [hd] at this; simp at this; omega
            simp only [List.foldl_cons, decodeStep, hv, Nat.zero_add]
            by_cases h2 : c2 = '}'
            · by_cases h3 : cs.takeWhile hexDigit ≠ [] ∧ hexNumber 0 (cs.takeWhile hexDigit) ≤ 1114111
              · have hlen0 : (cs.takeWhile hexDigit).length ≠ 0 := by simpa using h3.1
                simp only [h2, h3, bne_self_eq_false, Bool.false_eq_true, ite_false]
                rw [(ih more hmore _ back _).1]
                have hb : ((cs.takeWhile hexDigit).length == 0 ||
                    decide (hexNumber 0 (cs.takeWhile hexDigit) > 1114111)) = false := by
                  simp; omega
                simp [hb, toChar_ofNat _ h3.2, h3.1]
              · have hb : ((cs.takeWhile hexDigit).length == 0 ||
                    decide (hexNumber 0 (cs.takeWhile hexDigit) > 1114111)) = true := by
                  by_cases he : cs.takeWhile hexDigit = []
                  · simp [he]
                  · have : ¬ hexNumber 0 (cs.takeWhile hexDigit) ≤ 1114111 := fun hle => h3 ⟨he, hle⟩
                    simp [he]; omega
                simp [h2, h3, hb, foldl_failed, finishDecode, mOut]
            · simp [h2, foldl_failed, finishDecode, mOut]
        · simp [h1, decodeStep, foldl_failed, finishDecode, mOut]

theorem ofNat_eq_ofChar (c : Char) (n : Nat) (lt : n < 0x110000) :
    HsChar.ofNat n = HsChar.ofChar c ↔ c.toNat = n := by
  rw [eq_comm]; exact ofChar_eq_ofNat c n lt

theorem decodeString_eq (start : Loc) (cs : List Char) :
    tOut (AssembleTranslated.decodeString start (cs.map HsChar.ofChar)) =
      mOut (AssembleValidationHelpers.decodeString cs) := by
  have hS : ∀ c, HsList.lookup (HsChar.ofChar c) [(HsChar.ofNat 110, HsChar.ofNat 10),
      (HsChar.ofNat 116, HsChar.ofNat 9), (HsChar.ofNat 114, HsChar.ofNat 13), (HsChar.ofNat 92, HsChar.ofNat 92),
      (HsChar.ofNat 39, HsChar.ofNat 39), (HsChar.ofNat 34, HsChar.ofNat 34), (HsChar.ofNat 91, HsChar.ofNat 91),
      (HsChar.ofNat 93, HsChar.ofNat 93), (HsChar.ofNat 45, HsChar.ofNat 45)] =
      (simpleEscape c).map HsChar.ofChar := by
    intro c
    unfold simpleEscape
    split <;> simp_all [HsList.lookup, ofNat_eq_ofChar, ← Char.toNat_inj] <;> decide
  exact (decode_agree _ hS cs.length cs (Nat.le_refl _) _ start []).1

theorem drop_takeWhile_length {α : Type} (p : α → Bool) (l : List α) :
    l.drop (l.takeWhile p).length = l.dropWhile p := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h, ih]

theorem toNat_ofNat_int (k : Nat) : (Int.ofNat k).toNat = k := rfl

/-- What AssembleValidation reads of a string argument: failure, or the name. -/
def stringOutcome : Except AssembleTranslated.Diagnostic
    (AssembleTranslated.Located String × AssembleTranslated.Located String) → Except Unit String
  | .error _ => .error ()
  | .ok (n, _) => .ok (AssembleTranslated.Located.unLoc n)

theorem stringArg_eq (d : String) (l al : AssembleTranslated.Loc) (a : String) :
    stringOutcome (AssembleTranslated.stringArg d l (.Located al a)) =
      (AssembleValidationHelpers.stringArg AssembleValidation.validIdent d a).mapError (fun _ => ()) := by
  unfold AssembleTranslated.stringArg AssembleValidationHelpers.stringArg
  simp only [HsText.«break», HsText.span, HsText.takeWhile, HsText.drop, HsText.length, HsText.uncons,
    String.toList_ofList, isSpace_ofChar, isValidIdent_eq, toNat_ofNat_int, drop_takeWhile_length]
  have hsp : (fun c => PegVerification.ghcIsSpace c) = PegVerification.ghcIsSpace := rfl
  simp only [hsp]
  generalize List.takeWhile (fun c => !PegVerification.ghcIsSpace c) a.toList = N
  generalize List.dropWhile (fun c => !PegVerification.ghcIsSpace c) a.toList = R
  cases hv : AssembleValidation.validIdent (String.ofList N)
  · simp [stringOutcome, Except.mapError]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases List.dropWhile PegVerification.ghcIsSpace R with
    | nil => simp [stringOutcome, Except.mapError]
    | cons q body =>
      simp only [eq_ofChar_lit _ 34 (by decide)]
      by_cases hq : q = '"'
      · have hq' : q = Char.ofNat 34 := hq
        subst hq
        simp only [hq', beq_self_eq_true, ite_true, unpack_eq, String.toList_ofList]
        have hd := decodeString_eq
          (advanceLoc al (HsText.append (String.ofList N)
            (String.ofList (List.takeWhile (fun c => PegVerification.ghcIsSpace c) R)))) body
        revert hd
        cases AssembleTranslated.decodeString _ (body.map HsChar.ofChar) with
        | error e =>
          intro hd
          cases hm : AssembleValidationHelpers.decodeString body with
          | error e' => simp [HsEither.bind, stringOutcome, Except.mapError]
          | ok p => simp [hm, tOut, mOut] at hd
        | ok p =>
          intro hd
          obtain ⟨s, r⟩ := p
          cases hm : AssembleValidationHelpers.decodeString body with
          | error e' => simp [hm, tOut, mOut] at hd
          | ok p' =>
            simp only [hm, tOut, mOut, Except.ok.injEq, Prod.ext_iff] at hd
            obtain ⟨h1, h2⟩ := hd
            obtain ⟨value, after⟩ := p'
            simp only at h1 h2
            subst h1 h2
            simp only [HsEither.bind, strip_eq, toList_pack, null_eq, HsBase.not, stringArg.check_145]
            have he1 : (String.ofList (AssembleValidationHelpers.stripSpace (r.map HsText.toChar))).isEmpty =
                (AssembleValidationHelpers.stripSpace (r.map HsText.toChar)).isEmpty := by
              rw [← null_eq]; simp [HsText.null]
            have he2 : s.isEmpty = s.toList.isEmpty := by rw [← null_eq]; rfl
            have he3 : HsText.any_ (fun c => HsBase.or (c.lt (HsChar.ofNat 32)) (HsBase.eq c (HsChar.ofNat 127))) s =
                s.toList.any (fun c => decide (c.toNat < 32) || c.toNat == 127) := by
              simp only [HsText.any_]
              congr 1
              funext c
              simp only [HsBase.or, eq_ofChar_ofNat c 127 (by decide)]
              cases h : c.toNat == 127 <;> simp_all [HsChar.lt, ofChar_val, HsChar.ofNat]
            rw [he1, he2, he3]
            generalize (AssembleValidationHelpers.stripSpace (r.map HsText.toChar)).isEmpty = b1
            generalize s.toList.isEmpty = b2
            generalize (s.toList.any fun c => decide (c.toNat < 32) || c.toNat == 127) = b3
            cases b1 <;> cases b2 <;> cases b3 <;> simp [stringOutcome, Except.mapError, Located.unLoc]
      · have hq' : ¬q = Char.ofNat 34 := hq
        simp [hq', stringOutcome, Except.mapError]

end PegHs.AssembleTextProof
