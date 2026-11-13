namespace Peg.Verification

private def quote : Char := '"'
private def slash : Char := '\\'

def Plain (c : Char) : Prop :=
  32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ quote ∧ c ≠ slash

-- The remaining single-letter control escapes emitted by GHC's Show Char.
private def controlEscape (c : Char) : Option String :=
  match c.toNat with
  | 7 => some "\\a"
  | 8 => some "\\b"
  | 11 => some "\\v"
  | 12 => some "\\f"
  | 13 => some "\\r"
  | _ => none

def Allowed (c : Char) : Prop :=
  Plain c ∨ c = quote ∨ c = slash ∨ c = '\n' ∨ c = '\t' ∨ (controlEscape c).isSome = true

inductive TokenSyntax : Char → String → Prop where
  | plain (c : Char) (h : Plain c) : TokenSyntax c (String.singleton c)
  | quote : TokenSyntax quote "\\\""
  | slash : TokenSyntax slash "\\\\"
  | newline : TokenSyntax '\n' "\\n"
  | tab : TokenSyntax '\t' "\\t"

  | control (c : Char) (text : String) (h : controlEscape c = some text) : TokenSyntax c text

inductive BodySyntax : List Char → String → Prop where
  | nil : BodySyntax [] ""
  | cons (c : Char) (cs : List Char) (token rest : String)
      (hToken : TokenSyntax c token) (hRest : BodySyntax cs rest) :
      BodySyntax (c :: cs) (token ++ rest)

inductive LiteralSyntax : String → Prop where
  | string (chars : List Char) (body : String)
      (hBody : BodySyntax chars body) :
      LiteralSyntax ("\"" ++ body ++ "\"")

def encodeChar (c : Char) : String :=
  if c == quote then "\\\""
  else if c == slash then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\t' then "\\t"
  else (controlEscape c).getD (String.singleton c)

def encodeBody : List Char → String
  | [] => ""
  | c :: cs => encodeChar c ++ encodeBody cs

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
  cases he : controlEscape c with
  | some text =>
    simpa [encodeChar, hq, hs, hn, ht, he] using TokenSyntax.control c text he
  | none =>
    have plain : Plain c := by simpa [Allowed, hq, hs, hn, ht, he] using h
    simpa [encodeChar, hq, hs, hn, ht, he] using TokenSyntax.plain c plain

private theorem encodeBody_sound (chars : List Char)
    (allowed : ∀ c ∈ chars, Allowed c) :
    BodySyntax chars (encodeBody chars) := by
  induction chars with
  | nil => exact BodySyntax.nil
  | cons c cs ih =>
      apply BodySyntax.cons
      · exact encodeChar_sound c (allowed c (by simp))
      · exact ih (by
          intro x hx
          exact allowed x (by simp [hx]))

theorem invariant3_literal_sound
    (s : String) (allowed : ∀ c ∈ s.toList, Allowed c) :
    LiteralSyntax (encodeLiteral s) := by
  exact LiteralSyntax.string s.toList (encodeBody s.toList)
    (encodeBody_sound s.toList allowed)

inductive PegLitSyntax : String → Prop where
  | application (value source : String)
      (valueSyntax : LiteralSyntax value)
      (sourceSyntax : LiteralSyntax source) :
      PegLitSyntax ("PegRt.lit " ++ value ++ " " ++ source)

def renderPegLit (value source : String) : String :=
  "PegRt.lit " ++ encodeLiteral value ++ " " ++ encodeLiteral source

theorem invariant3_pegLit_sound (value source : String)
    (valueAllowed : ∀ c ∈ value.toList, Allowed c)
    (sourceAllowed : ∀ c ∈ source.toList, Allowed c) :
    PegLitSyntax (renderPegLit value source) := by
  exact PegLitSyntax.application (encodeLiteral value) (encodeLiteral source)
    (invariant3_literal_sound value valueAllowed)
    (invariant3_literal_sound source sourceAllowed)

#print axioms invariant3_literal_sound
#print axioms invariant3_pegLit_sound

end Peg.Verification
