import RenderExpression

namespace PegHs.RenderExpressionLexer

-- ASCII restriction of GHC 9.10.3 Lexer.x lines 159-165 and 182-202.
-- Unicode classes and extension-sensitive tokens are deliberately excluded.
def asciiLower (c : Char) : Bool :=
  ('a'.toNat ≤ c.toNat && c.toNat ≤ 'z'.toNat) || c == '_'

def asciiUpper (c : Char) : Bool :=
  'A'.toNat ≤ c.toNat && c.toNat ≤ 'Z'.toNat

def asciiDigit (c : Char) : Bool :=
  '0'.toNat ≤ c.toNat && c.toNat ≤ '9'.toNat

def idTail (c : Char) : Bool :=
  asciiLower c || asciiUpper c || asciiDigit c || c == '\''

def varId (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => asciiLower c && cs.all idTail

def conId (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => asciiUpper c && cs.all idTail

def qualifiedVarId (moduleName name : String) : Bool :=
  conId moduleName && varId name

-- This is the one-component case of Lexer.x's (@conid '.')+ @varid.
def qualifiedVarLexeme (s : String) : Prop :=
  ∃ moduleName name,
    s = moduleName ++ "." ++ name ∧ qualifiedVarId moduleName name = true

theorem fixed_choice_lexeme : qualifiedVarLexeme "PegRt.choice" := by
  exact ⟨"PegRt", "choice", rfl, by decide⟩

theorem fixed_many_lexeme : qualifiedVarLexeme "PegRt.many" := by
  exact ⟨"PegRt", "many", rfl, by decide⟩

theorem fixed_choice_qualified : qualifiedVarId "PegRt" "choice" = true := by decide
theorem fixed_many_qualified : qualifiedVarId "PegRt" "many" = true := by decide
theorem fixed_skipMany_qualified : qualifiedVarId "PegRt" "skipMany" = true := by decide
theorem fixed_anyChar_qualified : qualifiedVarId "PegRt" "anyChar" = true := by decide

theorem rule_name_ascii (name : String)
    (tail_ok : ∀ c ∈ name.toList, idTail c = true) :
    varId (Peg.Verification.RenderExpression.renderRule name) = true := by
  simp only [Peg.Verification.RenderExpression.renderRule, varId,
    String.toList_append]
  simp [asciiLower, asciiUpper, asciiDigit, idTail]
  simpa [asciiLower, asciiUpper, asciiDigit, idTail] using tail_ok

theorem rule_reference_ascii (name : String)
    (valid : Peg.Verification.RenderExpression.RuleTail
      (fun c => idTail c = true) name) :
    Peg.Verification.RenderExpression.ExpressionSyntax
      (fun c => idTail c = true)
      (Peg.Verification.RenderExpression.renderRule name) ∧
    varId (Peg.Verification.RenderExpression.renderRule name) = true := by
  constructor
  · exact Peg.Verification.RenderExpression.invariant3_rule_reference
      (fun c => idTail c = true) name valid
  · exact rule_name_ascii name valid

-- The printer uses intercalate for arbitrary-length choices and statements.
-- This lemma fixes the order of inserted lexical delimiters at character level.
private theorem fold_prefix (separator lead acc : String) (rest : List String) :
    rest.foldl (fun out item => out ++ separator ++ item) (lead ++ acc) =
      lead ++ rest.foldl (fun out item => out ++ separator ++ item) acc := by
  induction rest generalizing acc with
  | nil => rfl
  | cons item more ih =>
    simpa [List.foldl, String.append_assoc] using
      ih (acc ++ separator ++ item)

theorem intercalate_cons (separator first : String) (rest : List String) :
    String.intercalate separator (first :: rest) =
      rest.foldl (fun acc item => acc ++ separator ++ item) first := by
  induction rest generalizing first with
  | nil => simp
  | cons item more ih =>
    rw [String.intercalate_cons_cons, List.foldl_cons]
    rw [ih item]
    simpa [String.append_assoc] using
      (fold_prefix separator (first ++ separator) item more).symm

theorem choice_text_fold (first second : String) (rest : List String) :
    Peg.Verification.RenderExpression.renderChoice (first :: second :: rest) =
      "PegRt.choice [" ++
        rest.foldl (fun acc item => acc ++ ", " ++ item)
          (first ++ ", " ++ second) ++ "]" := by
  simp [Peg.Verification.RenderExpression.renderChoice,
    intercalate_cons, String.append_assoc]

theorem do_text_fold (first : String) (rest : List String) :
    Peg.Verification.RenderExpression.renderDo (first :: rest) =
      "do { " ++
        rest.foldl (fun acc item => acc ++ "\n          ; " ++ item) first ++
        "\n          }" := by
  simp [Peg.Verification.RenderExpression.renderDo,
    intercalate_cons, String.append_assoc]

#print axioms fixed_choice_qualified
#print axioms fixed_choice_lexeme
#print axioms fixed_many_lexeme
#print axioms rule_name_ascii
#print axioms rule_reference_ascii
#print axioms intercalate_cons
#print axioms choice_text_fold
#print axioms do_text_fold

end PegHs.RenderExpressionLexer
