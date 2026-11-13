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

-- The syntax-tree backend returns the semantic value and its children as a pair.
theorem pair_argument {value kids : List Symbol}
    (v : Derives productions [.nonterminal 229] value)
    (k : Derives productions [.nonterminal 229] kids) :
    Derives productions [.nonterminal 218]
      ([.terminal 107] ++ value ++ [.terminal 114] ++ kids ++ [.terminal 108]) := by
  have comma : Derives productions [.nonterminal 322] [.terminal 114] := by
    exact Derives.production (pre := []) (post := []) (id := 839) (rhs := [.terminal 114]) (by decide) (.refl _)
  have tail := one (id := 606) (lhs := 232) (by decide) k
  have suffix : Derives productions [.nonterminal 231] ([.terminal 114] ++ kids) := by
    apply Derives.production (pre := []) (post := []) (id := 604) (rhs := [.nonterminal 322, .nonterminal 232]) (by decide)
    exact trans (after [.nonterminal 232] comma) (before [.terminal 114] tail)
  have pair : Derives productions [.nonterminal 230] (value ++ ([.terminal 114] ++ kids)) := by
    apply Derives.production (pre := []) (post := []) (id := 600) (rhs := [.nonterminal 229, .nonterminal 231]) (by decide)
    exact trans (after [.nonterminal 231] v) (before value suffix)
  have arg : Derives productions [.nonterminal 220]
      ([.terminal 107] ++ (value ++ ([.terminal 114] ++ kids)) ++ [.terminal 108]) := by
    apply Derives.production (pre := []) (post := []) (id := 563) (rhs := [.terminal 107, .nonterminal 230, .terminal 108]) (by decide)
    exact after [.terminal 108] (before [.terminal 107] pair)
  have atom := one (id := 551) (lhs := 218) (by decide)
    (one (id := 554) (lhs := 219) (by decide) arg)
  simpa [List.append_assoc] using atom

theorem pure_pair_statement {value kids : List Symbol}
    (v : Derives productions [.nonterminal 229] value)
    (k : Derives productions [.nonterminal 229] kids) :
    Derives productions [.nonterminal 257]
      ([.terminal 121, .terminal 107] ++ value ++ [.terminal 114] ++ kids ++ [.terminal 108]) := by
  simpa [List.append_assoc] using pure_value_statement (pair_argument v k)


#print axioms pair_argument
#print axioms pure_pair_statement

def kidsTokens : List (List Symbol) → List Symbol
  | [] => [.terminal 105, .terminal 106]
  | [child] => child
  | first :: second :: rest =>
    [.terminal 121, .terminal 105] ++ rest.foldl RenderExpressionGHC.commaAppend
      (RenderExpressionGHC.commaAppend first second) ++ [.terminal 106]

theorem kids_return_statement {value : List Symbol} (children : List (List Symbol))
    (value_ok : Derives productions [.nonterminal 229] value)
    (child_ok : ∀ child ∈ children, Derives productions [.nonterminal 229] child) :
    Derives productions [.nonterminal 257]
      ([.terminal 121, .terminal 107] ++ value ++ [.terminal 114] ++
        kidsTokens children ++ [.terminal 108]) := by
  apply pure_pair_statement value_ok
  match children with
  | [] =>
    have nil : Derives productions [.nonterminal 280] [.terminal 105, .terminal 106] :=
      Derives.production (pre := []) (post := []) (id := 709)
        (rhs := [.terminal 105, .terminal 106]) (by decide) (.refl _)
    exact RenderExpressionGHC.aexp_to_texp
      (one (id := 551) (by decide) (one (id := 554) (lhs := 219) (by decide)
        (one (id := 556) (lhs := 220) (by decide) (one (id := 694) (lhs := 274) (by decide) nil))))
  | [child] => exact child_ok child (by simp)
  | first :: second :: rest =>
    have app := RenderExpressionGHC.choice_many first second rest
      (child_ok first (by simp)) (child_ok second (by simp))
      (fun item mem => child_ok item (by simp [mem]))
    exact one (id := 596) (by decide) (one (id := 520) (lhs := 211) (by decide)
      (one (id := 523) (lhs := 212) (by decide) (one (id := 528) (lhs := 214) (by decide) app)))

theorem doReturn_block (stmts children : List (List Symbol)) (value : List Symbol)
    (stmts_ok : ∀ stmt ∈ stmts, Derives productions [.nonterminal 257] stmt)
    (value_ok : Derives productions [.nonterminal 229] value)
    (child_ok : ∀ child ∈ children, Derives productions [.nonterminal 229] child) :
    Derives productions [.nonterminal 218] (RenderExpressionGHC.blockTokens
      (stmts ++ [[.terminal 121, .terminal 107] ++ value ++ [.terminal 114] ++
        kidsTokens children ++ [.terminal 108]])) := by
  have ret := kids_return_statement children value_ok child_ok
  cases stmts with
  | nil => exact RenderExpressionGHC.do_many _ [] ret (by simp)
  | cons head tail =>
    apply RenderExpressionGHC.do_many
    · exact stmts_ok head (by simp)
    · intro stmt mem
      rcases List.mem_append.mp mem with earlier | last
      · exact stmts_ok stmt (List.mem_cons_of_mem _ earlier)
      · obtain rfl := List.mem_singleton.mp last
        exact ret

#print axioms doReturn_block

theorem concat_name_lexeme :
    RenderExpressionLexer.qualifiedVarId "PegPrelude" "concat" = true := by decide

#print axioms kids_return_statement
#print axioms concat_name_lexeme

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

-- Both the discarded-value pattern in itemStmtS and the pass-through
-- pattern bind the second component to the fresh child-list variable.
theorem syntax_item_pair_binding (discard : Bool) {body : List Symbol}
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 257]
      ([.terminal 107, if discard then .terminal 2 else .terminal 117,
        .terminal 114, .terminal 117, .terminal 108, .terminal 82] ++ body) := by
  have first : Derives productions [.nonterminal 218]
      [if discard then .terminal 2 else .terminal 117] := by
    cases discard
    · exact RenderDeclarationsGHC.varid_argument
    · exact RenderDeclarationsGHC.wildcard_argument
  have pair := pair_argument (RenderExpressionGHC.aexp_to_texp first)
    (RenderExpressionGHC.aexp_to_texp RenderDeclarationsGHC.varid_argument)
  have pattern := one (id := 520) (lhs := 211) (by decide)
    (one (id := 523) (lhs := 212) (by decide) (one (id := 528) (lhs := 214) (by decide)
      (one (id := 536) (lhs := 217) (by decide) pair)))
  exact binding_statement pattern body_ok

#print axioms syntax_item_pair_binding

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

-- altCodeS inserts getOffset, spanFrom and the optional askStore binding.
theorem syntax_action_bindings :
    Derives productions [.nonterminal 257] [.terminal 117, .terminal 82, .terminal 121] ∧
    Derives productions [.nonterminal 257]
      [.terminal 117, .terminal 82, .terminal 121, .terminal 117] := by
  have expr {tokens : List Symbol} (f : Derives productions [.nonterminal 217] tokens) :
      Derives productions [.nonterminal 211] tokens :=
    one (id := 520) (by decide) (one (id := 523) (lhs := 212) (by decide)
      (one (id := 528) (lhs := 214) (by decide) f))
  exact ⟨named_binding_statement (expr RenderExpressionGHC.qualified_function),
    named_binding_statement (expr (RenderExpressionGHC.application
      RenderExpressionGHC.qualified_function RenderDeclarationsGHC.varid_argument))⟩

theorem syntax_action_block (hasEnv : Bool) (items : List (List Symbol × List Symbol))
    (fragment : List Symbol)
    (fragment_ok : Derives productions [.nonterminal 229] fragment)
    (items_ok : ∀ item ∈ items, Derives productions [.nonterminal 257] item.1 ∧
      Derives productions [.nonterminal 229] item.2) :
    let bindCall : List Symbol := [.terminal 117, .terminal 82, .terminal 121, .terminal 117]
    let start : List Symbol := [.terminal 117, .terminal 82, .terminal 121]
    let stmts := (if hasEnv then [bindCall] else []) ++ [start] ++ items.map Prod.fst ++ [bindCall]
    Derives productions [.nonterminal 218] (RenderExpressionGHC.blockTokens
      (stmts ++ [[.terminal 121, .terminal 107] ++ ([.terminal 107] ++ fragment ++ [.terminal 108]) ++
        [.terminal 114] ++ kidsTokens (items.map Prod.snd) ++ [.terminal 108]])) := by
  dsimp only
  apply doReturn_block
  · intro stmt mem
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at mem
    rcases mem with (((env | rfl) | ⟨item, hi, rfl⟩) | rfl)
    · cases hasEnv <;> simp_all [syntax_action_bindings.2]
    · exact syntax_action_bindings.1
    · exact (items_ok item hi).1
    · exact syntax_action_bindings.2
  · exact RenderExpressionGHC.aexp_to_texp (RenderExpressionGHC.parenthesized fragment_ok)
  · intro child mem
    obtain ⟨item, hi, rfl⟩ := List.mem_map.mp mem
    exact (items_ok item hi).2

#print axioms syntax_action_block

theorem syntax_action_names :
    ["peg'start", "_span", "_env", "peg'env"].all RenderExpressionLexer.varId = true ∧
    ["getOffset", "spanFrom", "askStore"].all
      (RenderExpressionLexer.qualifiedVarId "PegRt") = true := by decide

#print axioms syntax_action_bindings
#print axioms syntax_action_names

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

-- passThroughOf binds the chosen item and returns that same name after
-- the remaining statements have run.
def passThroughAlternative (lead rest : List RenderPrimitiveDoGHC.Statement)
    (name source : String) (tokens : List Symbol)
    (body : Derives productions [.nonterminal 211] tokens) : RenderPrimitiveChoice.Alternative :=
  valueAlternative (lead ++ itemStatement source tokens body true true (some name) :: rest)
    name [.terminal 117] RenderDeclarationsGHC.varid_argument

theorem passThroughAlternative_source (lead rest : List RenderPrimitiveDoGHC.Statement)
    (name source : String) (tokens : List Symbol) (body : Derives productions [.nonterminal 211] tokens) :
    (passThroughAlternative lead rest name source tokens body).source =
      RenderPrimitiveDo.printedDo (lead.map RenderPrimitiveDoGHC.Statement.source ++
        (name ++ " <- " ++ source) :: (rest.map RenderPrimitiveDoGHC.Statement.source ++ ["PegPrelude.pure " ++ name])) := by
  rw [passThroughAlternative, valueAlternative_source]
  simp [itemStatement, Option.filter, List.append_assoc]

theorem constructor_value (fields : Nat) :
    Derives productions [.nonterminal 218]
      (if fields = 0 then [.terminal 118] else
        [.terminal 107, .terminal 118] ++ List.replicate fields (.terminal 117) ++ [.terminal 108]) := by
  have con : Derives productions [.nonterminal 218] [.terminal 118] := by
    apply one (child := 219) (id := 551) (by decide)
    apply one (child := 220) (id := 554) (by decide)
    apply one (child := 274) (id := 556) (by decide)
    apply one (child := 275) (id := 693) (by decide)
    apply one (child := 315) (id := 695) (by decide)
    apply one (child := 316) (id := 811) (by decide)
    exact Derives.production (pre := []) (post := []) (rhs := [.terminal 118]) (id := 813) (by decide) (.refl _)
  have args (n : Nat) : Derives productions [.nonterminal 217]
      (.terminal 118 :: List.replicate n (.terminal 117)) := by
    induction n with
    | zero => exact one (child := 218) (id := 536) (by decide) con
    | succ n ih =>
      simpa [List.replicate_succ', List.append_assoc] using
        RenderExpressionGHC.application ih RenderDeclarationsGHC.varid_argument
  split
  · exact con
  · apply RenderExpressionGHC.parenthesized
    exact one (child := 211) (id := 596) (by decide) (one (child := 212) (id := 520) (by decide)
      (one (child := 214) (id := 523) (by decide) (one (child := 217) (id := 528) (by decide) (args fields))))

def printedConstructor (name : String) (fields : List String) : String :=
  let text := String.intercalate " " (name :: fields)
  if ' ' ∈ text.toList then "(" ++ text ++ ")" else text

theorem printedConstructor_shape (name : String) (fields : List String) (clean : ' ' ∉ name.toList) :
    printedConstructor name fields =
      match fields with
      | [] => name
      | f :: fs => "(" ++ String.intercalate " " (name :: f :: fs) ++ ")" := by
  cases fields with
  | nil => simp [printedConstructor, clean]
  | cons f fs => simp [printedConstructor]

theorem constructor_name_no_space (name : String) (valid : RenderExpressionLexer.conId name = true) :
    ' ' ∉ name.toList := by
  cases chars : name.toList with
  | nil => simp
  | cons c cs =>
    simp only [RenderExpressionLexer.conId, chars, Bool.and_eq_true, List.all_eq_true] at valid
    intro mem
    rcases List.mem_cons.mp mem with head | tail
    · subst c
      exact (by decide : RenderExpressionLexer.asciiUpper ' ' ≠ true) valid.1
    · exact (by decide : RenderExpressionLexer.idTail ' ' ≠ true) (valid.2 _ tail)

def constructorAlternative (stmts : List RenderPrimitiveDoGHC.Statement) (name : String)
    (fields : List String) : RenderPrimitiveChoice.Alternative :=
  valueAlternative stmts (printedConstructor name fields) _ (constructor_value fields.length)

theorem fresh_name_varid (n : Nat) :
    RenderExpressionLexer.varId ("peg'v" ++ n.repr) = true ∧
    RenderExpressionLexer.varId ("peg'k" ++ n.repr) = true := by
  have digits : n.repr.toList.all RenderExpressionLexer.idTail = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have mem : c ∈ Nat.toDigits 10 n := by simpa [Nat.repr] using hc
    have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) mem
    have ascii : RenderExpressionLexer.asciiDigit c = true := digit
    simp [RenderExpressionLexer.idTail, ascii]
  simp [RenderExpressionLexer.varId, String.toList_append] at *
  constructor <;> exact ⟨by decide, by decide, by decide, by decide, by decide, digits⟩

#print axioms fresh_name_varid
#print axioms constructor_name_no_space
#print axioms printedConstructor_shape
#print axioms constructor_value
#print axioms passThroughAlternative_source
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
