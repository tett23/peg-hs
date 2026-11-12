import GHCGrammar
import RenderExpression

namespace PegHs.RenderExpressionGHC

open CFG GHCGrammar

private theorem trans {g : Grammar} {xs ys zs : List Symbol}
    (first : Derives g xs ys) (second : Derives g ys zs) : Derives g xs zs := by
  induction first with
  | refl _ => exact second
  | production rule next ih => exact .production rule (ih second)

private theorem derives_pre {g : Grammar} (pre : List Symbol) {xs ys : List Symbol}
    (h : Derives g xs ys) : Derives g (pre ++ xs) (pre ++ ys) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs left right result rule next ih =>
    have next' : Derives g ((pre ++ left) ++ rhs ++ right) (pre ++ result) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := pre ++ left) (post := right) rule next')

private theorem derives_post {g : Grammar} (post : List Symbol) {xs ys : List Symbol}
    (h : Derives g xs ys) : Derives g (xs ++ post) (ys ++ post) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs left right result rule next ih =>
    have next' : Derives g (left ++ rhs ++ (right ++ post)) (result ++ post) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := left) (post := right ++ post) rule next')

private theorem one {id lhs rhs : Nat} {g : Grammar} {body : List Symbol}
    (rule : g id = some (lhs, [.nonterminal rhs]))
    (child : Derives g [.nonterminal rhs] body) :
    Derives g [.nonterminal lhs] body := by
  simpa using (Derives.production (pre := []) (post := []) rule child)

private theorem two {id lhs left right : Nat} {g : Grammar}
    {a b : List Symbol}
    (rule : g id = some (lhs, [.nonterminal left, .nonterminal right]))
    (ha : Derives g [.nonterminal left] a)
    (hb : Derives g [.nonterminal right] b) :
    Derives g [.nonterminal lhs] (a ++ b) := by
  have h : Derives g [.nonterminal left, .nonterminal right] (a ++ b) := by
    simpa [List.append_assoc] using
      trans (derives_post [.nonterminal right] ha) (derives_pre a hb)
  simpa using (Derives.production (pre := []) (post := []) rule h)

-- GHC Parser.y production 533: fexp -> fexp aexp.
theorem application {function argument : List Symbol}
    (function_ok : Derives productions [.nonterminal 217] function)
    (argument_ok : Derives productions [.nonterminal 218] argument) :
    Derives productions [.nonterminal 217] (function ++ argument) := by
  exact two (id := 533) (by decide) function_ok argument_ok

-- GHC Parser.y productions 562, 554, 551: aexp2 -> '(' texp ')',
-- aexp1 -> aexp2, aexp -> aexp1.
theorem parenthesized {inner : List Symbol}
    (inner_ok : Derives productions [.nonterminal 229] inner) :
    Derives productions [.nonterminal 218]
      ([.terminal 107] ++ inner ++ [.terminal 108]) := by
  have wrapped : Derives productions [.nonterminal 220]
      ([.terminal 107] ++ inner ++ [.terminal 108]) := by
    have rule : productions 562 = some
        (220, [.terminal 107, .nonterminal 229, .terminal 108]) := by decide
    have h := derives_pre [.terminal 107] (derives_post [.terminal 108] inner_ok)
    simpa [List.append_assoc] using
      (Derives.production (pre := []) (post := [])
        (id := 562) rule h)
  have rule554 : productions 554 = some (219, [.nonterminal 220]) := by decide
  have rule551 : productions 551 = some (218, [.nonterminal 219]) := by decide
  exact one rule551 (one rule554 wrapped)

theorem application_parenthesized {function inner : List Symbol}
    (function_ok : Derives productions [.nonterminal 217] function)
    (inner_ok : Derives productions [.nonterminal 229] inner) :
    Derives productions [.nonterminal 217]
      (function ++ [.terminal 107] ++ inner ++ [.terminal 108]) := by
  simpa [List.append_assoc] using application function_ok (parenthesized inner_ok)

-- GHC Parser.y productions 548 and 649: aexp -> DO stmtlist,
-- stmtlist -> '{' stmts '}'. The semicolons are composed below.
theorem do_block {statements : List Symbol}
    (statements_ok : Derives productions [.nonterminal 254] statements) :
    Derives productions [.nonterminal 218]
      ([.terminal 125, .terminal 101] ++ statements ++ [.terminal 102]) := by
  have braces : Derives productions [.nonterminal 253]
      ([.terminal 101] ++ statements ++ [.terminal 102]) := by
    have rule : productions 649 = some
        (253, [.terminal 101, .nonterminal 254, .terminal 102]) := by decide
    have h := derives_pre [.terminal 101] (derives_post [.terminal 102] statements_ok)
    simpa [List.append_assoc] using
      (Derives.production (pre := []) (post := [])
        (id := 649) rule h)
  have rule : productions 548 = some (218, [.terminal 125, .nonterminal 253]) := by decide
  have h := derives_pre [.terminal 125] braces
  simpa [List.append_assoc] using
    (Derives.production (pre := []) (post := [])
      (id := 548) rule h)

theorem statement_cons {initial statement : List Symbol}
    (initial_ok : Derives productions [.nonterminal 254] initial)
    (statement_ok : Derives productions [.nonterminal 257] statement) :
    Derives productions [.nonterminal 254]
      (initial ++ [.terminal 113] ++ statement) := by
  have rule : productions 651 = some
      (254, [.nonterminal 254, .terminal 113, .nonterminal 257]) := by decide
  have h : Derives productions
      [.nonterminal 254, .terminal 113, .nonterminal 257]
      (initial ++ [.terminal 113] ++ statement) := by
    have first := derives_post ([.terminal 113, .nonterminal 257]) initial_ok
    have second := derives_pre (initial ++ [.terminal 113]) statement_ok
    have first' : Derives productions
        [.nonterminal 254, .terminal 113, .nonterminal 257]
        (initial ++ [.terminal 113] ++ [.nonterminal 257]) := by
      simpa [List.append_assoc] using first
    exact trans first' second
  simpa using (Derives.production (pre := []) (post := []) rule h)

theorem statement_one {statement : List Symbol}
    (statement_ok : Derives productions [.nonterminal 257] statement) :
    Derives productions [.nonterminal 254] statement := by
  have rule : productions 653 = some (254, [.nonterminal 257]) := by decide
  exact one rule statement_ok

def semicolonAppend (acc item : List Symbol) : List Symbol :=
  acc ++ [.terminal 113] ++ item

theorem statement_fold (first : List Symbol) (rest : List (List Symbol))
    (first_ok : Derives productions [.nonterminal 257] first)
    (rest_ok : ∀ item ∈ rest, Derives productions [.nonterminal 257] item) :
    Derives productions [.nonterminal 254]
      (rest.foldl semicolonAppend first) := by
  have general (acc : List Symbol) (tail : List (List Symbol))
      (acc_ok : Derives productions [.nonterminal 254] acc)
      (tail_ok : ∀ item ∈ tail, Derives productions [.nonterminal 257] item) :
      Derives productions [.nonterminal 254]
        (tail.foldl semicolonAppend acc) := by
    induction tail generalizing acc with
    | nil => simpa using acc_ok
    | cons item more ih =>
      have item_ok := tail_ok item (by simp)
      have more_ok : ∀ x ∈ more, Derives productions [.nonterminal 257] x := by
        intro x hx
        exact tail_ok x (by simp [hx])
      simpa [List.foldl, semicolonAppend] using
        ih (semicolonAppend acc item) (statement_cons acc_ok item_ok) more_ok
  exact general first rest (statement_one first_ok) rest_ok

theorem do_many (first : List Symbol) (rest : List (List Symbol))
    (first_ok : Derives productions [.nonterminal 257] first)
    (rest_ok : ∀ item ∈ rest, Derives productions [.nonterminal 257] item) :
    Derives productions [.nonterminal 218]
      ([.terminal 125, .terminal 101] ++
        rest.foldl semicolonAppend first ++ [.terminal 102]) := by
  exact do_block (statement_fold first rest first_ok rest_ok)

-- A qualified rule/function name is a QVARID token. These six rules lift it
-- through qvarid, qvar, aexp2, aexp1, aexp, and fexp.
theorem qualified_function :
    Derives productions [.nonterminal 217] [.terminal 121] := by
  have r774 : productions 774 = some (306, [.terminal 121]) := by decide
  have r769 : productions 769 = some (304, [.nonterminal 306]) := by decide
  have r555 : productions 555 = some (220, [.nonterminal 304]) := by decide
  have r554 : productions 554 = some (219, [.nonterminal 220]) := by decide
  have r551 : productions 551 = some (218, [.nonterminal 219]) := by decide
  have r536 : productions 536 = some (217, [.nonterminal 218]) := by decide
  have terminal : Derives productions [.nonterminal 306] [.terminal 121] := by
    simpa using (Derives.production (pre := []) (post := []) r774 (.refl _))
  exact one r536 (one r551 (one r554 (one r555 (one r769 terminal))))

theorem choice_list {items : List Symbol}
    (items_ok : Derives productions [.nonterminal 233] items) :
    Derives productions [.nonterminal 218]
      ([.terminal 105] ++ items ++ [.terminal 106]) := by
  have r567 : productions 567 = some
      (220, [.terminal 105, .nonterminal 233, .terminal 106]) := by decide
  have r554 : productions 554 = some (219, [.nonterminal 220]) := by decide
  have r551 : productions 551 = some (218, [.nonterminal 219]) := by decide
  have h := derives_pre [.terminal 105] (derives_post [.terminal 106] items_ok)
  have list : Derives productions [.nonterminal 220]
      ([.terminal 105] ++ items ++ [.terminal 106]) := by
    simpa [List.append_assoc] using
      (Derives.production (pre := []) (post := []) r567 h)
  exact one r551 (one r554 list)

-- GHC Parser.y production 533 composes the qualified choice function and
-- a list literal. The list's item derivation is supplied by the caller.
theorem choice {items : List Symbol}
    (items_ok : Derives productions [.nonterminal 233] items) :
    Derives productions [.nonterminal 217]
      ([.terminal 121, .terminal 105] ++ items ++ [.terminal 106]) := by
  simpa [List.append_assoc] using application qualified_function (choice_list items_ok)

theorem choice_singleton {item : List Symbol}
    (item_ok : Derives productions [.nonterminal 229] item) :
    Derives productions [.nonterminal 217]
      ([.terminal 121, .terminal 105] ++ item ++ [.terminal 106]) := by
  have rule : productions 608 = some (233, [.nonterminal 229]) := by decide
  exact choice (one rule item_ok)

theorem choice_pair {left right : List Symbol}
    (left_ok : Derives productions [.nonterminal 229] left)
    (right_ok : Derives productions [.nonterminal 229] right) :
    Derives productions [.nonterminal 217]
      ([.terminal 121, .terminal 105] ++ left ++ [.terminal 114] ++
        right ++ [.terminal 106]) := by
  have r616 : productions 616 = some
      (234, [.nonterminal 229, .terminal 114, .nonterminal 229]) := by decide
  have r609 : productions 609 = some (233, [.nonterminal 234]) := by decide
  have first := derives_post [.terminal 114, .nonterminal 229] left_ok
  have second := derives_pre (left ++ [.terminal 114]) right_ok
  have assembled : Derives productions
      [.nonterminal 229, .terminal 114, .nonterminal 229]
      (left ++ [.terminal 114] ++ right) := by
    have first' : Derives productions
        [.nonterminal 229, .terminal 114, .nonterminal 229]
        (left ++ [.terminal 114] ++ [.nonterminal 229]) := by
      simpa [List.append_assoc] using first
    exact trans first' second
  have list : Derives productions [.nonterminal 233]
      (left ++ [.terminal 114] ++ right) := by
    have lexps : Derives productions [.nonterminal 234]
        (left ++ [.terminal 114] ++ right) := by
      simpa using (Derives.production (pre := []) (post := []) r616 assembled)
    exact one r609 lexps
  simpa [List.append_assoc] using choice list

def commaAppend (acc item : List Symbol) : List Symbol :=
  acc ++ [.terminal 114] ++ item

theorem lexps_extend {initial item : List Symbol}
    (initial_ok : Derives productions [.nonterminal 234] initial)
    (item_ok : Derives productions [.nonterminal 229] item) :
    Derives productions [.nonterminal 234] (commaAppend initial item) := by
  have rule : productions 615 = some
      (234, [.nonterminal 234, .terminal 114, .nonterminal 229]) := by decide
  have first := derives_post [.terminal 114, .nonterminal 229] initial_ok
  have second := derives_pre (initial ++ [.terminal 114]) item_ok
  have assembled : Derives productions
      [.nonterminal 234, .terminal 114, .nonterminal 229]
      (commaAppend initial item) := by
    have first' : Derives productions
        [.nonterminal 234, .terminal 114, .nonterminal 229]
        (initial ++ [.terminal 114] ++ [.nonterminal 229]) := by
      simpa [List.append_assoc] using first
    exact trans first' second
  simpa using (Derives.production (pre := []) (post := []) rule assembled)

theorem choice_many (first second : List Symbol) (rest : List (List Symbol))
    (first_ok : Derives productions [.nonterminal 229] first)
    (second_ok : Derives productions [.nonterminal 229] second)
    (rest_ok : ∀ item ∈ rest, Derives productions [.nonterminal 229] item) :
    Derives productions [.nonterminal 217]
      ([.terminal 121, .terminal 105] ++
        rest.foldl commaAppend (commaAppend first second) ++ [.terminal 106]) := by
  have r616 : productions 616 = some
      (234, [.nonterminal 229, .terminal 114, .nonterminal 229]) := by decide
  have r609 : productions 609 = some (233, [.nonterminal 234]) := by decide
  have pair : Derives productions [.nonterminal 234] (commaAppend first second) := by
    have first' := derives_post [.terminal 114, .nonterminal 229] first_ok
    have second' := derives_pre (first ++ [.terminal 114]) second_ok
    have assembled : Derives productions
        [.nonterminal 229, .terminal 114, .nonterminal 229]
        (commaAppend first second) := by
      have h : Derives productions
          [.nonterminal 229, .terminal 114, .nonterminal 229]
          (first ++ [.terminal 114] ++ [.nonterminal 229]) := by
        simpa [List.append_assoc] using first'
      exact trans h second'
    simpa using (Derives.production (pre := []) (post := []) r616 assembled)
  have general (acc : List Symbol) (tail : List (List Symbol))
      (acc_ok : Derives productions [.nonterminal 234] acc)
      (tail_ok : ∀ item ∈ tail, Derives productions [.nonterminal 229] item) :
      Derives productions [.nonterminal 234] (tail.foldl commaAppend acc) := by
    induction tail generalizing acc with
    | nil => simpa using acc_ok
    | cons item more ih =>
      have item_ok := tail_ok item (by simp)
      have more_ok : ∀ x ∈ more, Derives productions [.nonterminal 229] x := by
        intro x hx
        exact tail_ok x (by simp [hx])
      simpa [List.foldl] using
        ih (commaAppend acc item) (lexps_extend acc_ok item_ok) more_ok
  exact choice (one r609 (general _ rest pair rest_ok))

theorem aexp_to_texp {body : List Symbol}
    (body_ok : Derives productions [.nonterminal 218] body) :
    Derives productions [.nonterminal 229] body := by
  have r536 : productions 536 = some (217, [.nonterminal 218]) := by decide
  have r528 : productions 528 = some (214, [.nonterminal 217]) := by decide
  have r523 : productions 523 = some (212, [.nonterminal 214]) := by decide
  have r520 : productions 520 = some (211, [.nonterminal 212]) := by decide
  have r596 : productions 596 = some (229, [.nonterminal 211]) := by decide
  exact one r596 (one r520 (one r523 (one r528 (one r536 body_ok))))

def blockTokens : List (List Symbol) → List Symbol
  | [] => []
  | head :: tail => [.terminal 125, .terminal 101] ++
      tail.foldl semicolonAppend head ++ [.terminal 102]

theorem group_many (first second : List (List Symbol))
    (rest : List (List (List Symbol)))
    (first_ok : ∃ head tail, first = head :: tail ∧
      Derives productions [.nonterminal 257] head ∧
      ∀ item ∈ tail, Derives productions [.nonterminal 257] item)
    (second_ok : ∃ head tail, second = head :: tail ∧
      Derives productions [.nonterminal 257] head ∧
      ∀ item ∈ tail, Derives productions [.nonterminal 257] item)
    (rest_ok : ∀ block ∈ rest, ∃ head tail, block = head :: tail ∧
      Derives productions [.nonterminal 257] head ∧
      ∀ item ∈ tail, Derives productions [.nonterminal 257] item) :
    Derives productions [.nonterminal 217]
      ([.terminal 121, .terminal 105] ++
        (rest.map blockTokens).foldl commaAppend
          (commaAppend (blockTokens first) (blockTokens second)) ++
        [.terminal 106]) := by
  obtain ⟨head1, tail1, shape1, h1, t1⟩ := first_ok
  obtain ⟨head2, tail2, shape2, h2, t2⟩ := second_ok
  have f1 : Derives productions [.nonterminal 229] (blockTokens first) := by
    rw [shape1]
    exact aexp_to_texp (do_many head1 tail1 h1 t1)
  have f2 : Derives productions [.nonterminal 229] (blockTokens second) := by
    rw [shape2]
    exact aexp_to_texp (do_many head2 tail2 h2 t2)
  have restDerives : ∀ item ∈ rest.map blockTokens,
      Derives productions [.nonterminal 229] item := by
    intro item member
    obtain ⟨block, inRest, eq⟩ := List.mem_map.mp member
    obtain ⟨head, tail, shape, headOk, tailOk⟩ := rest_ok block inRest
    rw [shape] at eq
    subst item
    exact aexp_to_texp (do_many head tail headOk tailOk)
  exact choice_many (blockTokens first) (blockTokens second)
    (rest.map blockTokens) f1 f2 restDerives

-- The syntax predicates describe printer output. The explicit lexer equation
-- is the boundary between character strings and GHC terminal IDs.
theorem bridge_wrap (tailChar : Char → Prop) (lex : String → List Symbol)
    (function inner : String) (functionTokens innerTokens : List Symbol)
    (functionSyntax : Peg.Verification.RenderExpression.ExpressionSyntax tailChar function)
    (innerSyntax : Peg.Verification.RenderExpression.ExpressionSyntax tailChar inner)
    (functionDerives : Derives productions [.nonterminal 217] functionTokens)
    (innerDerives : Derives productions [.nonterminal 229] innerTokens)
    (lexes : lex (Peg.Verification.RenderExpression.renderWrap function inner) =
      functionTokens ++ [.terminal 107] ++ innerTokens ++ [.terminal 108]) :
    Peg.Verification.RenderExpression.ExpressionSyntax tailChar
      (Peg.Verification.RenderExpression.renderWrap function inner) ∧
    Derives productions [.nonterminal 217]
      (lex (Peg.Verification.RenderExpression.renderWrap function inner)) := by
  constructor
  · exact Peg.Verification.RenderExpression.invariant3_application
      tailChar function inner functionSyntax innerSyntax
  · rw [lexes]
    exact application_parenthesized functionDerives innerDerives

theorem bridge_choice (tailChar : Char → Prop) (lex : String → List Symbol)
    (items : List String) (itemTokens : List Symbol)
    (itemSyntax : ∀ item ∈ items,
      Peg.Verification.RenderExpression.ExpressionSyntax tailChar item)
    (itemDerives : Derives productions [.nonterminal 233] itemTokens)
    (lexes : lex (Peg.Verification.RenderExpression.renderChoice items) =
      [.terminal 121, .terminal 105] ++ itemTokens ++ [.terminal 106]) :
    Peg.Verification.RenderExpression.ExpressionSyntax tailChar
      (Peg.Verification.RenderExpression.renderChoice items) ∧
    Derives productions [.nonterminal 217]
      (lex (Peg.Verification.RenderExpression.renderChoice items)) := by
  constructor
  · exact Peg.Verification.RenderExpression.invariant3_choice tailChar items itemSyntax
  · rw [lexes]
    exact choice itemDerives

theorem bridge_do (statementSyntax : String → Prop) (lex : String → List Symbol)
    (statements : List String) (statementTokens : List Symbol)
    (nonempty : statements ≠ [])
    (valid : ∀ statement ∈ statements, statementSyntax statement)
    (statementDerives : Derives productions [.nonterminal 254] statementTokens)
    (lexes : lex (Peg.Verification.RenderExpression.renderDo statements) =
      [.terminal 125, .terminal 101] ++ statementTokens ++ [.terminal 102]) :
    Peg.Verification.RenderExpression.DoSyntax statementSyntax
      (Peg.Verification.RenderExpression.renderDo statements) ∧
    Derives productions [.nonterminal 218]
      (lex (Peg.Verification.RenderExpression.renderDo statements)) := by
  constructor
  · exact Peg.Verification.RenderExpression.invariant3_sequence
      statementSyntax statements nonempty valid
  · rw [lexes]
    exact do_block statementDerives

#print axioms application
#print axioms parenthesized
#print axioms application_parenthesized
#print axioms do_block
#print axioms statement_cons
#print axioms choice
#print axioms choice_singleton
#print axioms choice_pair
#print axioms bridge_wrap
#print axioms bridge_choice
#print axioms bridge_do
#print axioms statement_fold
#print axioms choice_many
#print axioms group_many

end PegHs.RenderExpressionGHC
