namespace Peg.Verification

private def quote : Char := '"'
private def slash : Char := '\\'

def Plain (c : Char) : Prop :=
  32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ quote ∧ c ≠ slash

-- GHC Show spellings for ASCII controls other than tab and newline.
private def controlEscape (c : Char) : Option String :=
  match c.toNat with
  | 0 => some "\\NUL"
  | 1 => some "\\SOH"
  | 2 => some "\\STX"
  | 3 => some "\\ETX"
  | 4 => some "\\EOT"
  | 5 => some "\\ENQ"
  | 6 => some "\\ACK"
  | 7 => some "\\a"
  | 8 => some "\\b"
  | 11 => some "\\v"
  | 12 => some "\\f"
  | 13 => some "\\r"
  | 14 => some "\\SO"
  | 15 => some "\\SI"
  | 16 => some "\\DLE"
  | 17 => some "\\DC1"
  | 18 => some "\\DC2"
  | 19 => some "\\DC3"
  | 20 => some "\\DC4"
  | 21 => some "\\NAK"
  | 22 => some "\\SYN"
  | 23 => some "\\ETB"
  | 24 => some "\\CAN"
  | 25 => some "\\EM"
  | 26 => some "\\SUB"
  | 27 => some "\\ESC"
  | 28 => some "\\FS"
  | 29 => some "\\GS"
  | 30 => some "\\RS"
  | 31 => some "\\US"
  | 127 => some "\\DEL"
  | _ => none

def Allowed (c : Char) : Prop :=
  Plain c ∨ c = quote ∨ c = slash ∨ c = '\n' ∨ c = '\t' ∨ (controlEscape c).isSome = true ∨ 127 < c.toNat

inductive TokenSyntax : Char → String → Prop where
  | plain (c : Char) (h : Plain c) : TokenSyntax c (String.singleton c)
  | quote : TokenSyntax quote "\\\""
  | slash : TokenSyntax slash "\\\\"
  | newline : TokenSyntax '\n' "\\n"
  | tab : TokenSyntax '\t' "\\t"

  | decimal (c : Char) (h : 127 < c.toNat) : TokenSyntax c ("\\" ++ c.toNat.repr)
  | control (c : Char) (text : String) (h : controlEscape c = some text) : TokenSyntax c text

-- A decimal escape consumes following ASCII digits, and SO followed by H
-- would be read as SOH. Require an empty escape at these boundaries.
def needsEscapeTerminator (c : Char) (rest : List Char) : Bool :=
  rest.head?.any fun next =>
    (c.toNat == 14 && next == 'H') || (127 < c.toNat && next.isDigit)

inductive BodySyntax : List Char → String → Prop where
  | nil : BodySyntax [] ""
  | cons (c : Char) (cs : List Char) (token rest : String)
      (hToken : TokenSyntax c token) (hRest : BodySyntax cs rest)
      (boundary : needsEscapeTerminator c cs = false) :
      BodySyntax (c :: cs) (token ++ rest)

  | separated (c : Char) (cs : List Char) (token rest : String)
      (hToken : TokenSyntax c token) (hRest : BodySyntax cs rest)
      (boundary : needsEscapeTerminator c cs = true) :
      BodySyntax (c :: cs) (token ++ "\\&" ++ rest)

inductive LiteralSyntax : String → Prop where
  | string (chars : List Char) (body : String)
      (hBody : BodySyntax chars body) :
      LiteralSyntax ("\"" ++ body ++ "\"")

def encodeChar (c : Char) : String :=
  if c == quote then "\\\""
  else if c == slash then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\t' then "\\t"
  else if 127 < c.toNat then "\\" ++ c.toNat.repr
  else (controlEscape c).getD (String.singleton c)

def encodeBody : List Char → String
  | [] => ""
  | c :: cs =>
    if needsEscapeTerminator c cs then encodeChar c ++ "\\&" ++ encodeBody cs
    else encodeChar c ++ encodeBody cs

-- Classify the next spelling by the only two ASCII prefixes that can
-- extend an escape. All non-ASCII characters start with a backslash.
private def escapePrefix (c : Char) : Bool × Bool := (c == 'H', c.isDigit)

private theorem encoded_prefix (c : Char) (suffix : String) :
    ((encodeChar c ++ suffix).toList.head?.map escapePrefix) = some (escapePrefix c) := by
  by_cases high : 127 < c.toNat
  · have enc : encodeChar c = "\\" ++ c.toNat.repr := by
      simp [encodeChar, high, quote, slash]
      repeat' split
      all_goals first | rfl | (subst c; contradiction)
    have noH : (c == 'H') = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      subst c
      contradiction
    have noDigit : c.isDigit = false := by
      have upper : ¬ c.val ≤ '9'.val := by
        intro h
        have le : c.toNat ≤ 57 := UInt32.le_iff_toNat_le.mp h
        omega
      simp only [Char.isDigit, decide_eq_false upper, Bool.and_false]
    simp [enc, String.toList_append, escapePrefix, noH, noDigit]
  · have finite : ∀ n : Fin 128, (encodeChar (Char.ofNat n.val)).toList.head?.map escapePrefix =
        some (escapePrefix (Char.ofNat n.val)) := by decide
    have eqn := finite ⟨c.toNat, by omega⟩
    simp only [Char.ofNat_toNat] at eqn
    simp only [String.toList_append]
    cases hc : (encodeChar c).toList <;> simp_all

theorem encoded_suffix_prefix (cs : List Char) :
    (encodeBody cs).toList.head?.map escapePrefix = cs.head?.map escapePrefix := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    unfold encodeBody
    split
    · simpa [String.append_assoc] using encoded_prefix c ("\\&" ++ encodeBody cs)
    · exact encoded_prefix c (encodeBody cs)

#print axioms encoded_suffix_prefix

-- Fold from the right, testing the first character of the already
-- rendered suffix as a ShowS-style escape printer does.
def prependEscaped (c : Char) (suffix : String) : String :=
  if needsEscapeTerminator c suffix.toList then encodeChar c ++ "\\&" ++ suffix
  else encodeChar c ++ suffix

theorem fold_escaped_body (chars : List Char) :
    chars.foldr prependEscaped "" = encodeBody chars := by
  induction chars with
  | nil => rfl
  | cons c cs ih =>
    let check (p : Option (Bool × Bool)) :=
      p.any fun flags => (c.toNat == 14 && flags.1) || (127 < c.toNat && flags.2)
    have classify (xs : List Char) :
        check (xs.head?.map escapePrefix) = needsEscapeTerminator c xs := by
      cases xs <;> rfl
    have same := congrArg check (encoded_suffix_prefix cs)
    rw [classify, classify] at same
    simp only [List.foldr_cons, ih, prependEscaped, same, encodeBody]

#print axioms fold_escaped_body

def encodeLiteral (s : String) : String :=
  "\"" ++ encodeBody s.toList ++ "\""

-- Show for String supplies the final double quote as the continuation
-- of showLitString. Its first character cannot extend either escape.
theorem quoted_fold (s : String) :
    "\"" ++ s.toList.foldr prependEscaped "\"" = encodeLiteral s := by
  have aux (cs : List Char) :
      cs.foldr prependEscaped "\"" = encodeBody cs ++ "\"" := by
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      have same : needsEscapeTerminator c (encodeBody cs ++ "\"").toList =
          needsEscapeTerminator c (encodeBody cs).toList := by
        simp only [String.toList_append, needsEscapeTerminator]
        cases (encodeBody cs).toList <;> simp [Char.isDigit]
      rw [← fold_escaped_body (c :: cs), List.foldr_cons, List.foldr_cons, ih,
        fold_escaped_body cs]
      simp only [prependEscaped, same]
      split <;> simp [String.append_assoc]
  simp [aux, encodeLiteral, String.append_assoc]

#print axioms quoted_fold

-- Nonnegative branch of itos' in GHC.Internal.Show (GHC 9.10.3).
private def intDigits (n : Nat) (suffix : List Char) : List Char :=
  if n < 10 then Char.ofNat (48 + n) :: suffix
  else intDigits (n / 10) (Char.ofNat (48 + n % 10) :: suffix)
termination_by n
decreasing_by omega

private theorem decimal_digit (n : Nat) (h : n < 10) :
    Char.ofNat (48 + n) = n.digitChar := by
  have finite : ∀ d : Fin 10, Char.ofNat (48 + d.val) = d.val.digitChar := by decide
  exact finite ⟨n, h⟩

private theorem intDigits_eq (n : Nat) (suffix : List Char) :
    intDigits n suffix = Nat.toDigits 10 n ++ suffix := by
  induction n using Nat.strongRecOn generalizing suffix with
  | ind n ih =>
    rw [intDigits, Nat.toDigits_eq_ite (by decide : 1 < 10)]
    split <;> rename_i h
    · simp [decimal_digit n h]
    · rw [ih (n / 10) (by omega), decimal_digit _ (Nat.mod_lt _ (by decide))]
      simp

-- Character spelling in ghc-9.10.3-release, GHC.Internal.Show:
-- showLitString handles quotes, showLitChar handles the remaining cases.
private def showSpelling (c : Char) : String :=
  if c == '"' then "\\\""
  else if 127 < c.toNat then "\\" ++ String.ofList (intDigits c.toNat [])
  else if c.toNat == 127 then "\\DEL"
  else if c == '\\' then "\\\\"
  else if 32 ≤ c.toNat then String.singleton c
  else
    match c.toNat with
    | 7 => "\\a" | 8 => "\\b" | 9 => "\\t" | 10 => "\\n"
    | 11 => "\\v" | 12 => "\\f" | 13 => "\\r" | 14 => "\\SO"
    | n => "\\" ++ (["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
        "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI", "DLE", "DC1", "DC2",
        "DC3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM", "SUB", "ESC", "FS",
        "GS", "RS", "US", "SP"] : List String)[n]!

theorem showSpelling_eq (c : Char) : showSpelling c = encodeChar c := by
  by_cases high : 127 < c.toNat
  · simp [showSpelling, encodeChar, high, quote, slash, intDigits_eq, Nat.repr]
    repeat' split
    all_goals first | rfl | (subst c; contradiction)
  · have ascii : ∀ n : Fin 128, showSpelling (Char.ofNat n.val) = encodeChar (Char.ofNat n.val) := by
      decide
    simpa using ascii ⟨c.toNat, by omega⟩

#print axioms showSpelling_eq

private def protectEsc (p : Char → Bool) (suffix : String) : String :=
  if suffix.toList.head?.any p then "\\&" ++ suffix else suffix

private def showStringStep (c : Char) (suffix : String) : String :=
  showSpelling c ++
    (if 127 < c.toNat then protectEsc Char.isDigit suffix
     else if c.toNat = 14 then protectEsc (· == 'H') suffix
     else suffix)

private theorem showStringStep_eq (c : Char) (suffix : String) :
    showStringStep c suffix = prependEscaped c suffix := by
  unfold showStringStep prependEscaped needsEscapeTerminator protectEsc
  rw [showSpelling_eq]
  cases h : suffix.toList.head? with
  | none => simp
  | some next =>
    by_cases high : 127 < c.toNat
    · have ne : c.toNat ≠ 14 := by omega
      simp [high, ne, String.append_assoc]
      split <;> rfl
    · by_cases so : c.toNat = 14
      · simp [so, String.append_assoc]
        split <;> rfl
      · simp [high, so]

def showStringModel (s : String) : String :=
  "\"" ++ s.toList.foldr showStringStep "\""

theorem showStringModel_eq (s : String) : showStringModel s = encodeLiteral s := by
  have step : showStringStep = prependEscaped := funext fun c => funext (showStringStep_eq c)
  simpa [showStringModel, step] using quoted_fold s

#print axioms showStringModel_eq

-- The closing apostrophe cannot trigger protectEsc. In a character
-- literal a double quote is plain and the apostrophe itself is escaped.
def encodeEndpoint (c : Char) : String :=
  "'" ++ (if c.toNat = 39 then "\\'" else if c == '"' then "\"" else encodeChar c) ++ "'"

private def showEndpoint (c : Char) : String :=
  if c.toNat = 39 then "'\\''"
  else if c == '"' then "'\"'"
  else "'" ++ showStringStep c "'"

theorem showEndpoint_eq (c : Char) : showEndpoint c = encodeEndpoint c := by
  rw [showEndpoint, encodeEndpoint]
  by_cases apostrophe : c.toNat = 39
  · simp [apostrophe]
  · by_cases doubleQuote : c == '"'
    · simp [apostrophe, doubleQuote]
    · simp [apostrophe, doubleQuote, showStringStep_eq, prependEscaped,
        needsEscapeTerminator, Char.isDigit, String.append_assoc]

#print axioms showEndpoint_eq

private theorem encodeChar_sound (c : Char) (h : Allowed c) :
    TokenSyntax c (encodeChar c) := by
  by_cases hq : c = quote
  · subst c
    simp [encodeChar]
    exact TokenSyntax.quote
  by_cases hs : c = slash
  · subst c
    simp [encodeChar, hq]
    exact TokenSyntax.slash
  by_cases hn : c = '\n'
  · subst c
    simp [encodeChar, hq, hs]
    exact TokenSyntax.newline
  by_cases ht : c = '\t'
  · subst c
    simp [encodeChar, hq, hs]
    exact TokenSyntax.tab
  by_cases high : 127 < c.toNat
  · simpa [encodeChar, hq, hs, hn, ht, high] using TokenSyntax.decimal c high
  cases he : controlEscape c with
  | some text =>
    simpa [encodeChar, hq, hs, hn, ht, high, he] using TokenSyntax.control c text he
  | none =>
    have plain : Plain c := by simpa [Allowed, hq, hs, hn, ht, he, high] using h
    simpa [encodeChar, hq, hs, hn, ht, high, he] using TokenSyntax.plain c plain

private theorem encodeBody_sound (chars : List Char)
    (allowed : ∀ c ∈ chars, Allowed c) :
    BodySyntax chars (encodeBody chars) := by
  induction chars with
  | nil => exact BodySyntax.nil
  | cons c cs ih =>
      have token := encodeChar_sound c (allowed c (by simp))
      have rest := ih (fun x hx => allowed x (by simp [hx]))
      unfold encodeBody
      cases boundary : needsEscapeTerminator c cs with
      | false => exact .cons _ _ _ _ token rest boundary
      | true => exact .separated _ _ _ _ token rest boundary

theorem allCharsAllowed (c : Char) : Allowed c := by
  by_cases high : 127 < c.toNat
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr high)))))
  have ascii : ∀ n : Fin 128, Allowed (Char.ofNat n.val) := by
    unfold Allowed Plain
    decide
  have bound : c.toNat < 128 := by omega
  simpa using ascii ⟨c.toNat, bound⟩

theorem invariant3_literal_sound (s : String) : LiteralSyntax (encodeLiteral s) :=
  .string s.toList (encodeBody s.toList) (encodeBody_sound s.toList (fun c _ => allCharsAllowed c))


inductive PegLitSyntax : String → Prop where
  | application (value source : String)
      (valueSyntax : LiteralSyntax value)
      (sourceSyntax : LiteralSyntax source) :
      PegLitSyntax ("PegRt.lit " ++ value ++ " " ++ source)

def renderPegLit (value source : String) : String :=
  "PegRt.lit " ++ encodeLiteral value ++ " " ++ encodeLiteral source

theorem invariant3_pegLit_sound (value source : String) :
    PegLitSyntax (renderPegLit value source) := by
  exact PegLitSyntax.application (encodeLiteral value) (encodeLiteral source)
    (invariant3_literal_sound value)
    (invariant3_literal_sound source)

#print axioms invariant3_literal_sound
#print axioms invariant3_pegLit_sound

end Peg.Verification
