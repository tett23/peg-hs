import RenderExpressionGHC
import RenderExpressionLexer
import RenderDeclarationsGHC
import RenderPrimitiveChoice

namespace PegHs.RenderPrimitiveStatement

open PegHs.CFG PegHs.GHCGrammar

private theorem one {id lhs child : Nat} {out : List Symbol}
    (rule : productions id = some (lhs, [.nonterminal child]))
    (valid : Derives productions [.nonterminal child] out) :
    Derives productions [.nonterminal lhs] out := by
  simpa using
    (Derives.production (pre := []) (post := []) rule valid)

private theorem trans {xs ys zs : List Symbol}
    (left : Derives productions xs ys) (right : Derives productions ys zs) :
    Derives productions xs zs := by
  induction left with
  | refl _ => exact right
  | production rule next ih => exact .production rule (ih right)

private theorem before (lead : List Symbol) {xs ys : List Symbol}
    (h : Derives productions xs ys) :
    Derives productions (lead ++ xs) (lead ++ ys) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs pre post result rule next ih =>
    have inner : Derives productions
        ((lead ++ pre) ++ rhs ++ post) (lead ++ result) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := lead ++ pre) (post := post) rule inner)

private theorem after (tail : List Symbol) {xs ys : List Symbol}
    (h : Derives productions xs ys) :
    Derives productions (xs ++ tail) (ys ++ tail) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs pre post result rule next ih =>
    have inner : Derives productions
        (pre ++ rhs ++ (post ++ tail)) (result ++ tail) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := pre) (post := post ++ tail) rule inner)

theorem pure_name_lexeme :
    RenderExpressionLexer.qualifiedVarId "PegPrelude" "pure" = true := by
  decide

theorem pure_value_statement {value : List Symbol}
    (value_ok : Derives productions [.nonterminal 218] value) :
    Derives productions [.nonterminal 257] ([.terminal 121] ++ value) := by
  have r528 : productions 528 = some (214, [.nonterminal 217]) := by decide
  have r523 : productions 523 = some (212, [.nonterminal 214]) := by decide
  have r520 : productions 520 = some (211, [.nonterminal 212]) := by decide
  have r661 : productions 661 = some (258, [.nonterminal 211]) := by decide
  have r658 : productions 658 = some (257, [.nonterminal 258]) := by decide
  have applied := RenderExpressionGHC.application
    RenderExpressionGHC.qualified_function value_ok
  exact one r658 (one r661 (one r520 (one r523 (one r528 applied))))

-- Codegen.altCode emits this exact final statement when a unit rule has no
-- action. The source checker pins that branch, and the GHC lexer probe checks
-- QVARID LPAREN RPAREN independently of this CFG derivation.
theorem pure_unit_statement :
    Derives productions [.nonterminal 257]
      [.terminal 121, .terminal 107, .terminal 108] := by
  have r708 : productions 708 = some
      (280, [.terminal 107, .terminal 108]) := by decide
  have r694 : productions 694 = some (274, [.nonterminal 280]) := by decide
  have r556 : productions 556 = some (220, [.nonterminal 274]) := by decide
  have r554 : productions 554 = some (219, [.nonterminal 220]) := by decide
  have r551 : productions 551 = some (218, [.nonterminal 219]) := by decide
  have r528 : productions 528 = some (214, [.nonterminal 217]) := by decide
  have r523 : productions 523 = some (212, [.nonterminal 214]) := by decide
  have r520 : productions 520 = some (211, [.nonterminal 212]) := by decide
  have r661 : productions 661 = some (258, [.nonterminal 211]) := by decide
  have r658 : productions 658 = some (257, [.nonterminal 258]) := by decide
  have unitCon : Derives productions [.nonterminal 280]
      [.terminal 107, .terminal 108] := by
    simpa using (Derives.production (pre := []) (post := []) r708 (.refl _))
  have unitArg : Derives productions [.nonterminal 218]
      [.terminal 107, .terminal 108] :=
    one r551 (one r554 (one r556 (one r694 unitCon)))
  have applied := RenderExpressionGHC.application
    RenderExpressionGHC.qualified_function unitArg
  exact one r658 (one r661 (one r520 (one r523 (one r528
    (by simpa using applied)))))

-- The two binding forms printed by Codegen.itemStmt share the same grammar
-- production. The right-hand expression is a child derivation, supplied by
-- exprCodeU's remaining proof obligation.
theorem binding_statement {pattern body : List Symbol}
    (pattern_ok : Derives productions [.nonterminal 211] pattern)
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 257]
      (pattern ++ [.terminal 82] ++ body) := by
  have r641 : productions 641 = some (248, [.nonterminal 211]) := by decide
  have r660 : productions 660 = some
      (258, [.nonterminal 248, .terminal 82, .nonterminal 211]) := by decide
  have r658 : productions 658 = some (257, [.nonterminal 258]) := by decide
  have pat := one r641 pattern_ok
  have left := after ([.terminal 82, .nonterminal 211]) pat
  have right := before (pattern ++ [.terminal 82]) body_ok
  have right' : Derives productions
      (pattern ++ [.terminal 82, .nonterminal 211])
      (pattern ++ [.terminal 82] ++ body) := by
    simpa [List.append_assoc] using right
  have children : Derives productions
      [.nonterminal 248, .terminal 82, .nonterminal 211]
      (pattern ++ [.terminal 82] ++ body) := by
    simpa [List.append_assoc] using trans left right'
  have qual : Derives productions [.nonterminal 258]
      (pattern ++ [.terminal 82] ++ body) := by
    simpa using (Derives.production (pre := []) (post := []) r660 children)
  exact one r658 qual

theorem named_binding_statement {body : List Symbol}
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 257]
      ([.terminal 117, .terminal 82] ++ body) := by
  have r520 : productions 520 = some (211, [.nonterminal 212]) := by decide
  have name := one r520 RenderDeclarationsGHC.name_infixexp
  simpa using binding_statement name body_ok

theorem wildcard_binding_statement {body : List Symbol}
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 257]
      ([.terminal 2, .terminal 82] ++ body) := by
  have r536 : productions 536 = some (217, [.nonterminal 218]) := by decide
  have r528 : productions 528 = some (214, [.nonterminal 217]) := by decide
  have r523 : productions 523 = some (212, [.nonterminal 214]) := by decide
  have r520 : productions 520 = some (211, [.nonterminal 212]) := by decide
  have wildcard : Derives productions [.nonterminal 211] [.terminal 2] :=
    one r520 (one r523 (one r528 (one r536
      RenderDeclarationsGHC.wildcard_argument)))
  simpa using binding_statement wildcard body_ok

-- The surrounding lexer bridge checks the bound name token. The caller supplies the
-- expression derivation for exprCodeU's output.
def itemStatement (source : String) (tokens : List Symbol)
    (expression : Derives productions [.nonterminal 211] tokens)
    (hasValue honorBind : Bool) (binding : Option String) : RenderPrimitiveDoGHC.Statement :=
  if hasValue then
    match binding.filter (fun _ => honorBind) with
    | some name => ⟨name ++ " <- " ++ source, [.terminal 117, .terminal 82] ++ tokens,
        named_binding_statement expression⟩
    | none => ⟨"_ <- " ++ source, [.terminal 2, .terminal 82] ++ tokens,
        wildcard_binding_statement expression⟩
  else
    have r661 : productions 661 = some (258, [.nonterminal 211]) := by decide
    have r658 : productions 658 = some (257, [.nonterminal 258]) := by decide
    ⟨source, tokens, one r658 (one r661 expression)⟩

private def returningAlternative (stmts : List RenderPrimitiveDoGHC.Statement)
    (ret : RenderPrimitiveDoGHC.Statement) : RenderPrimitiveChoice.Alternative :=
  match stmts with
  | [] => RenderPrimitiveChoice.doAlternative ret []
  | first :: rest => RenderPrimitiveChoice.doAlternative first (rest ++ [ret])

private theorem returningAlternative_source (stmts : List RenderPrimitiveDoGHC.Statement)
    (ret : RenderPrimitiveDoGHC.Statement) :
    (returningAlternative stmts ret).source =
      RenderPrimitiveDo.printedDo (stmts.map RenderPrimitiveDoGHC.Statement.source ++ [ret.source]) := by
  cases stmts <;> simp [returningAlternative, RenderPrimitiveChoice.doAlternative]

def unitAlternative (stmts : List RenderPrimitiveDoGHC.Statement) : RenderPrimitiveChoice.Alternative :=
  returningAlternative stmts
    ⟨"PegPrelude.pure ()", [.terminal 121, .terminal 107, .terminal 108], pure_unit_statement⟩

theorem unitAlternative_source (stmts : List RenderPrimitiveDoGHC.Statement) :
    (unitAlternative stmts).source =
      RenderPrimitiveDo.printedDo (stmts.map RenderPrimitiveDoGHC.Statement.source ++ ["PegPrelude.pure ()"]) :=
  returningAlternative_source stmts _

def valueAlternative (stmts : List RenderPrimitiveDoGHC.Statement) (source : String)
    (tokens : List Symbol) (value : Derives productions [.nonterminal 218] tokens) :
    RenderPrimitiveChoice.Alternative :=
  returningAlternative stmts ⟨"PegPrelude.pure " ++ source, [.terminal 121] ++ tokens, pure_value_statement value⟩

theorem valueAlternative_source (stmts : List RenderPrimitiveDoGHC.Statement) (source : String)
    (tokens : List Symbol) (value : Derives productions [.nonterminal 218] tokens) :
    (valueAlternative stmts source tokens value).source =
      RenderPrimitiveDo.printedDo (stmts.map RenderPrimitiveDoGHC.Statement.source ++ ["PegPrelude.pure " ++ source]) :=
  returningAlternative_source stmts _

#print axioms valueAlternative_source
#print axioms itemStatement
#print axioms unitAlternative_source
#print axioms pure_name_lexeme
#print axioms pure_value_statement
#print axioms pure_unit_statement
#print axioms binding_statement
#print axioms named_binding_statement
#print axioms wildcard_binding_statement

end PegHs.RenderPrimitiveStatement
