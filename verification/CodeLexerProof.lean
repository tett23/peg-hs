import TemplatesTranslated

namespace PegHs.CodeLexerProof
open TemplatesTranslated

theorem root_adr0097_i2_string_remainder {α : Type} [Inhabited α]
    (s : List (α × HsChar)) :
    (Peg_Grammar_codeVariables.string_355 s).length ≤ s.length :=
  string_length s

theorem root_adr0097_i2_comment_remainder (depth : Int) (s : List (Loc × HsChar)) :
    (Peg_Grammar_codeVariables.blockComment_368 depth s).length ≤ s.length :=
  block_length depth s

theorem root_adr0097_i2_qualified_remainder {α : Type} [Inhabited α]
    (s : List (α × HsChar)) :
    (Peg_Grammar_codeVariables.qualified_375 s).length ≤ s.length :=
  qualified_length s

theorem root_adr0097_i2_fields_remainder {α : Type} [Inhabited α]
    (s : List (α × HsChar)) :
    (Peg_Grammar_codeVariables.fields_384 s).length ≤ s.length :=
  fields_length s

theorem root_adr0097_i2_character_remainder {α : Type} [Inhabited α]
    (s out : List (α × HsChar))
    (ok : Peg_Grammar_codeVariables.charLiteral_363 s = some out) : out.length ≤ s.length :=
  charLiteral_length s out ok

theorem root_adr0097_i2_identifier_consumes {α : Type} [Inhabited α]
    (l : α) (c : HsChar) (rest : List (α × HsChar))
    (first : Peg_Grammar_codeVariables.isIdentStart_348 c = true) :
    (Peg_Grammar_codeVariables.identifier_344 ((l, c) :: rest)).2.length ≤ rest.length :=
  identifier_cons_length l c rest first

#print axioms root_adr0097_i2_string_remainder
#print axioms root_adr0097_i2_comment_remainder
#print axioms root_adr0097_i2_qualified_remainder
#print axioms root_adr0097_i2_fields_remainder
#print axioms root_adr0097_i2_character_remainder
#print axioms root_adr0097_i2_identifier_consumes
end PegHs.CodeLexerProof
