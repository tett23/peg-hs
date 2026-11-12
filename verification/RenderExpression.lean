namespace Peg.Verification.RenderExpression

-- The grammar checker supplies a rule name whose characters may continue a
-- Haskell variable identifier. The lower-case generated prefix supplies its
-- initial character and separates it from the following Haskell token.
def RuleTail (tailChar : Char → Prop) (name : String) : Prop :=
  ∀ c ∈ name.toList, tailChar c

inductive VariableSyntax (tailChar : Char → Prop) : String → Prop where
  | rule (name : String) (valid : RuleTail tailChar name) :
      VariableSyntax tailChar ("peg'rule'" ++ name)
  | qualifiedAny : VariableSyntax tailChar "PegRt.anyChar"
  | qualifiedChoice : VariableSyntax tailChar "PegRt.choice"
  | qualifiedMany : VariableSyntax tailChar "PegRt.many"
  | qualifiedSkipMany : VariableSyntax tailChar "PegRt.skipMany"
  | qualifiedMany1 : VariableSyntax tailChar "PegRt.many1"
  | qualifiedSkipMany1 : VariableSyntax tailChar "PegRt.skipMany1"
  | qualifiedOptional : VariableSyntax tailChar "PegRt.optional"
  | qualifiedSkipOptional : VariableSyntax tailChar "PegRt.skipOptional"
  | qualifiedAnd : VariableSyntax tailChar "PegRt.andP"
  | qualifiedNot : VariableSyntax tailChar "PegRt.notP"
  | qualifiedCapture : VariableSyntax tailChar "PegRt.capture"
  | qualifiedVoid : VariableSyntax tailChar "PegRt.voidP"

inductive ExpressionSyntax (tailChar : Char → Prop) : String → Prop where
  | variable (s : String) (valid : VariableSyntax tailChar s) :
      ExpressionSyntax tailChar s
  | parenthesized (s : String) (valid : ExpressionSyntax tailChar s) :
      ExpressionSyntax tailChar ("(" ++ s ++ ")")
  | application (f arg : String)
      (function : ExpressionSyntax tailChar f)
      (argument : ExpressionSyntax tailChar arg) :
      ExpressionSyntax tailChar (f ++ " " ++ arg)
  | applicationParenthesized (f arg : String)
      (function : ExpressionSyntax tailChar f)
      (argument : ExpressionSyntax tailChar arg) :
      ExpressionSyntax tailChar (f ++ " (" ++ arg ++ ")")
  | choice (items : List String)
      (valid : ∀ item ∈ items, ExpressionSyntax tailChar item) :
      ExpressionSyntax tailChar
        ("PegRt.choice [" ++ String.intercalate ", " items ++ "]")

def renderRule (name : String) : String := "peg'rule'" ++ name

def renderWrap (function inner : String) : String :=
  function ++ " (" ++ inner ++ ")"

def renderChoice (items : List String) : String :=
  "PegRt.choice [" ++ String.intercalate ", " items ++ "]"

inductive DoSyntax (statementSyntax : String → Prop) : String → Prop where
  | block (statements : List String)
      (nonempty : statements ≠ [])
      (valid : ∀ statement ∈ statements, statementSyntax statement) :
      DoSyntax statementSyntax
        ("do { " ++ String.intercalate "\n          ; " statements ++ "\n          }")

def renderDo (statements : List String) : String :=
  "do { " ++ String.intercalate "\n          ; " statements ++ "\n          }"

inductive GroupSyntax (statementSyntax : String → Prop) : String → Prop where
  | choice (alternatives : List (List String))
      (valid : ∀ statements ∈ alternatives,
        statements ≠ [] ∧ ∀ statement ∈ statements, statementSyntax statement) :
      GroupSyntax statementSyntax
        ("PegRt.choice [" ++
          String.intercalate ", " (alternatives.map renderDo) ++ "]")

def renderGroup (alternatives : List (List String)) : String :=
  renderChoice (alternatives.map renderDo)

theorem invariant3_rule_reference (tailChar : Char → Prop) (name : String)
    (valid : RuleTail tailChar name) :
    ExpressionSyntax tailChar (renderRule name) := by
  exact ExpressionSyntax.variable _ (VariableSyntax.rule name valid)

theorem invariant3_application (tailChar : Char → Prop) (function inner : String)
    (validFunction : ExpressionSyntax tailChar function)
    (validInner : ExpressionSyntax tailChar inner) :
    ExpressionSyntax tailChar (renderWrap function inner) := by
  exact ExpressionSyntax.applicationParenthesized function inner validFunction validInner

theorem invariant3_choice (tailChar : Char → Prop) (items : List String)
    (valid : ∀ item ∈ items, ExpressionSyntax tailChar item) :
    ExpressionSyntax tailChar (renderChoice items) := by
  exact ExpressionSyntax.choice items valid

theorem invariant3_any (tailChar : Char → Prop) :
    ExpressionSyntax tailChar "PegRt.anyChar" := by
  exact ExpressionSyntax.variable _ VariableSyntax.qualifiedAny

theorem invariant3_many (tailChar : Char → Prop) (inner : String)
    (valid : ExpressionSyntax tailChar inner) :
    ExpressionSyntax tailChar (renderWrap "PegRt.many" inner) := by
  exact invariant3_application tailChar "PegRt.many" inner
    (ExpressionSyntax.variable _ VariableSyntax.qualifiedMany) valid

theorem invariant3_sequence (statementSyntax : String → Prop)
    (statements : List String) (nonempty : statements ≠ [])
    (valid : ∀ statement ∈ statements, statementSyntax statement) :
    DoSyntax statementSyntax (renderDo statements) := by
  exact DoSyntax.block statements nonempty valid

theorem invariant3_group (statementSyntax : String → Prop)
    (alternatives : List (List String))
    (valid : ∀ statements ∈ alternatives,
      statements ≠ [] ∧ ∀ statement ∈ statements, statementSyntax statement) :
    GroupSyntax statementSyntax (renderGroup alternatives) := by
  exact GroupSyntax.choice alternatives valid

#print axioms invariant3_rule_reference
#print axioms invariant3_application
#print axioms invariant3_choice
#print axioms invariant3_any
#print axioms invariant3_many
#print axioms invariant3_sequence
#print axioms invariant3_group

end Peg.Verification.RenderExpression
