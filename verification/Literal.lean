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

inductive BodySyntax : List Char → String → Prop where
  | nil : BodySyntax [] ""
  | cons (c : Char) (cs : List Char) (token rest : String)
      (hToken : TokenSyntax c token) (hRest : BodySyntax cs rest) :
      BodySyntax (c :: cs) (token ++ rest)

  | separated (c : Char) (cs : List Char) (token rest : String)
      (hToken : TokenSyntax c token) (hRest : BodySyntax cs rest) :
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
    let separator := cs.head?.any fun next =>
      (c.toNat == 14 && next == 'H') || (127 < c.toNat && next.isDigit)
    if separator then encodeChar c ++ "\\&" ++ encodeBody cs
    else encodeChar c ++ encodeBody cs

def encodeLiteral (s : String) : String :=
  "\"" ++ encodeBody s.toList ++ "\""

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
      dsimp only
      split
      · exact .separated _ _ _ _ token rest
      · exact .cons _ _ _ _ token rest

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
