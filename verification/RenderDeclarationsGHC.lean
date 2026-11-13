import GHCGrammar
import RenderModuleGHC
import RenderExpressionGHC

namespace PegHs.RenderDeclarationsGHC

open CFG GHCGrammar

private theorem trans {g : Grammar} {xs ys zs : List Symbol}
    (a : Derives g xs ys) (b : Derives g ys zs) : Derives g xs zs := by
  induction a with
  | refl _ => exact b
  | production rule next ih => exact .production rule (ih b)

private theorem before {g : Grammar} (lead : List Symbol) {xs ys : List Symbol}
    (h : Derives g xs ys) : Derives g (lead ++ xs) (lead ++ ys) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs pre post result rule next ih =>
    have inner : Derives g ((lead ++ pre) ++ rhs ++ post) (lead ++ result) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := lead ++ pre) (post := post) rule inner)

private theorem after {g : Grammar} (tail : List Symbol) {xs ys : List Symbol}
    (h : Derives g xs ys) : Derives g (xs ++ tail) (ys ++ tail) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs pre post result rule next ih =>
    have inner : Derives g (pre ++ rhs ++ (post ++ tail)) (result ++ tail) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := pre) (post := post ++ tail) rule inner)

private theorem beside {g : Grammar} {xs ys us vs : List Symbol}
    (left : Derives g xs ys) (right : Derives g us vs) :
    Derives g (xs ++ us) (ys ++ vs) := by
  exact trans (after us left) (before ys right)

private theorem applyRule {id lhs : Nat} {rhs out : List Symbol} {g : Grammar}
    (rule : g id = some (lhs, rhs)) (children : Derives g rhs out) :
    Derives g [.nonterminal lhs] out := by
  have framed : Derives g ([] ++ rhs ++ []) out := by simpa using children
  simpa using (Derives.production (pre := []) (post := []) rule framed)

private theorem oneRule {id lhs child : Nat} {g : Grammar} {out : List Symbol}
    (rule : g id = some (lhs, [.nonterminal child]))
    (h : Derives g [.nonterminal child] out) :
    Derives g [.nonterminal lhs] out := by
  exact applyRule rule h

-- Parser.y: topdecl -> decl_no_th -> sigdecl -> infixexp :: sigtype.
theorem signature {lhs ty : List Symbol}
    (lhs_ok : Derives productions [.nonterminal 212] lhs)
    (type_ok : Derives productions [.nonterminal 157] ty) :
    Derives productions [.nonterminal 78]
      (lhs ++ [.terminal 76] ++ ty) := by
  have r496 : productions 496 = some
      (207, [.nonterminal 212, .terminal 76, .nonterminal 157]) := by decide
  have r485 : productions 485 = some (202, [.nonterminal 207]) := by decide
  have r164 : productions 164 = some (78, [.nonterminal 202]) := by decide
  have children := beside lhs_ok
    (beside (.refl [.terminal 76]) type_ok)
  exact oneRule r164 (oneRule r485
    (applyRule r496 (by simpa [List.append_assoc] using children)))

-- Parser.y: topdecl -> decl_no_th -> infixexp opt_sig rhs,
-- with opt_sig empty and rhs -> = exp wherebinds (empty).
theorem binding {lhs body : List Symbol}
    (lhs_ok : Derives productions [.nonterminal 212] lhs)
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 78]
      (lhs ++ [.terminal 77] ++ body) := by
  have r486 : productions 486 = some
      (202, [.nonterminal 212, .nonterminal 154, .nonterminal 204]) := by decide
  have r359 : productions 359 = some (154, []) := by decide
  have r491 : productions 491 = some
      (204, [.terminal 77, .nonterminal 211, .nonterminal 131]) := by decide
  have r300 : productions 300 = some (131, []) := by decide
  have r164 : productions 164 = some (78, [.nonterminal 202]) := by decide
  have rhs := applyRule r491
    (beside (.refl [.terminal 77])
      (beside body_ok (applyRule r300 (.refl _))))
  have children := beside lhs_ok
    (beside (applyRule r359 (.refl _)) rhs)
  exact oneRule r164 (applyRule r486 (by simpa [List.append_assoc] using children))

-- A generated unqualified declaration name is a VARID token. This is a
-- token-level theorem; validation of the concrete characters is separate.
theorem varid_argument :
    Derives productions [.nonterminal 218] [.terminal 117] := by
  have r775 : productions 775 = some (307, [.terminal 117]) := by decide
  have r773 : productions 773 = some (306, [.nonterminal 307]) := by decide
  have r769 : productions 769 = some (304, [.nonterminal 306]) := by decide
  have r555 : productions 555 = some (220, [.nonterminal 304]) := by decide
  have r554 : productions 554 = some (219, [.nonterminal 220]) := by decide
  have r551 : productions 551 = some (218, [.nonterminal 219]) := by decide
  exact oneRule r551 (oneRule r554 (oneRule r555
    (oneRule r769 (oneRule r773 (applyRule r775 (.refl _))))))

theorem name_infixexp :
    Derives productions [.nonterminal 212] [.terminal 117] := by
  have r536 : productions 536 = some (217, [.nonterminal 218]) := by decide
  have r528 : productions 528 = some (214, [.nonterminal 217]) := by decide
  have r523 : productions 523 = some (212, [.nonterminal 214]) := by decide
  exact oneRule r523 (oneRule r528 (oneRule r536 varid_argument))

theorem signature_named {ty : List Symbol}
    (type_ok : Derives productions [.nonterminal 157] ty) :
    Derives productions [.nonterminal 78]
      ([.terminal 117, .terminal 76] ++ ty) := by
  simpa using signature name_infixexp type_ok

theorem signature_named_ctype {ty : List Symbol}
    (type_ok : Derives productions [.nonterminal 163] ty) :
    Derives productions [.nonterminal 78]
      ([.terminal 117, .terminal 76] ++ ty) := by
  have r365 : productions 365 = some (157, [.nonterminal 163]) := by decide
  exact signature_named (oneRule r365 type_ok)

theorem binding_named {body : List Symbol}
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 78]
      ([.terminal 117, .terminal 77] ++ body) := by
  simpa using binding name_infixexp body_ok

theorem binding_named_infixexp {body : List Symbol}
    (body_ok : Derives productions [.nonterminal 212] body) :
    Derives productions [.nonterminal 78]
      ([.terminal 117, .terminal 77] ++ body) := by
  have r520 : productions 520 = some (211, [.nonterminal 212]) := by decide
  exact binding_named (oneRule r520 body_ok)

-- Each printed parameter is a separate aexp and function application
-- attaches it to the declaration left hand side.
theorem apply_argument {function argument : List Symbol}
    (function_ok : Derives productions [.nonterminal 217] function)
    (argument_ok : Derives productions [.nonterminal 218] argument) :
    Derives productions [.nonterminal 217] (function ++ argument) := by
  have r533 : productions 533 = some
      (217, [.nonterminal 217, .nonterminal 218]) := by decide
  exact applyRule r533 (beside function_ok argument_ok)

theorem wildcard_argument :
    Derives productions [.nonterminal 218] [.terminal 2] := by
  have r568 : productions 568 = some (220, [.terminal 2]) := by decide
  have r554 : productions 554 = some (219, [.nonterminal 220]) := by decide
  have r551 : productions 551 = some (218, [.nonterminal 219]) := by decide
  exact oneRule r551 (oneRule r554 (applyRule r568 (.refl _)))

def argumentsWord (args : List (List Symbol)) : List Symbol :=
  args.foldl (· ++ ·) [.terminal 117]

theorem name_with_arguments (args : List (List Symbol))
    (args_ok : ∀ arg ∈ args,
      Derives productions [.nonterminal 218] arg) :
    Derives productions [.nonterminal 212] (argumentsWord args) := by
  have r536 : productions 536 = some (217, [.nonterminal 218]) := by decide
  have r528 : productions 528 = some (214, [.nonterminal 217]) := by decide
  have r523 : productions 523 = some (212, [.nonterminal 214]) := by decide
  have name_ok : Derives productions [.nonterminal 217] [.terminal 117] :=
    oneRule r536 varid_argument
  have fold (acc : List Symbol) (remaining : List (List Symbol))
      (acc_ok : Derives productions [.nonterminal 217] acc)
      (remaining_ok : ∀ arg ∈ remaining,
        Derives productions [.nonterminal 218] arg) :
      Derives productions [.nonterminal 217]
        (remaining.foldl (· ++ ·) acc) := by
    induction remaining generalizing acc with
    | nil => simpa using acc_ok
    | cons arg more ih =>
      have more_ok : ∀ x ∈ more,
          Derives productions [.nonterminal 218] x := by
        intro x hx
        exact remaining_ok x (by simp [hx])
      simpa [List.foldl] using ih (acc ++ arg)
        (apply_argument acc_ok (remaining_ok arg (by simp))) more_ok
  exact oneRule r523 (oneRule r528
    (fold [.terminal 117] args name_ok args_ok))

theorem binding_named_arguments (args : List (List Symbol)) {body : List Symbol}
    (args_ok : ∀ arg ∈ args,
      Derives productions [.nonterminal 218] arg)
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 78]
      (argumentsWord args ++ [.terminal 77] ++ body) := by
  exact binding (name_with_arguments args args_ok) body_ok

-- The module frame consumes any number of these top-level declarations.
theorem declarations_named (items : List (List Symbol))
    (valid : ∀ item ∈ items,
      Derives productions [.nonterminal 78] item) :
    Derives productions [.nonterminal 76]
      (items.foldl RenderModuleGHC.semiAppend []) := by
  exact RenderModuleGHC.declarations_many items valid

def generatedPair (ty : List Symbol) (args : List (List Symbol))
    (body : List Symbol) : List (List Symbol) :=
  [[.terminal 117, .terminal 76] ++ ty,
    argumentsWord args ++ [.terminal 77] ++ body]

theorem generated_pair (ty : List Symbol) (args : List (List Symbol))
    (body : List Symbol)
    (type_ok : Derives productions [.nonterminal 163] ty)
    (args_ok : ∀ arg ∈ args,
      Derives productions [.nonterminal 218] arg)
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 76]
      ((generatedPair ty args body).foldl RenderModuleGHC.semiAppend []) := by
  apply declarations_named
  intro item hi
  simp only [generatedPair, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with h | h
  · rw [h]
    exact signature_named_ctype type_ok
  · rw [h]
    exact binding_named_arguments args args_ok body_ok

theorem generated_pair_varid_arguments (ty body : List Symbol) (arity : Nat)
    (type_ok : Derives productions [.nonterminal 163] ty)
    (body_ok : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 76]
      ((generatedPair ty (List.replicate arity [.terminal 117]) body).foldl
        RenderModuleGHC.semiAppend []) := by
  apply generated_pair _ _ _ type_ok _ body_ok
  intro arg member
  have eq := List.eq_of_mem_replicate member
  exact eq ▸ varid_argument

-- ruleDecl emits "(parameterType) -> " once per value parameter.
def parameterArrows (params : List (List Symbol)) (result : List Symbol) : List Symbol :=
  params.foldr (fun param tail => [.terminal 107] ++ param ++ [.terminal 108, .terminal 83] ++ tail) result

theorem parameter_arrows (params : List (List Symbol)) (result : List Symbol)
    (valid : ∀ p ∈ params, Derives productions [.nonterminal 163] p)
    (result_ok : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 163] (parameterArrows params result) := by
  induction params with
  | nil => exact result_ok
  | cons p ps ih =>
    have kt : productions 374 = some (162, [.nonterminal 163]) := by decide
    have paren : productions 412 = some (172, [.terminal 107, .nonterminal 162, .terminal 108]) := by decide
    have app : productions 390 = some (169, [.nonterminal 172]) := by decide
    have infixTy : productions 387 = some (168, [.nonterminal 169]) := by decide
    have base : productions 386 = some (167, [.nonterminal 168]) := by decide
    have arrow : productions 382 = some (165, [.nonterminal 167, .terminal 83, .nonterminal 163]) := by decide
    have ctype : productions 379 = some (163, [.nonterminal 165]) := by decide
    have inner := oneRule kt (valid p (by simp))
    have lhs := applyRule paren (beside (.refl [.terminal 107]) (beside inner (.refl [.terminal 108])))
    have tail := ih (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    have rhs := beside (oneRule base (oneRule infixTy (oneRule app lhs))) (beside (.refl [.terminal 83]) tail)
    simpa [parameterArrows, List.append_assoc] using oneRule ctype (applyRule arrow rhs)

-- runParser, runParserRecover and runSyntaxRecover take the same initial
-- arguments. runSyntaxRecover additionally receives the rule's syntax kind.
def runtimeCallWord (hasEnv withKind : Bool) (config : List Symbol := [.terminal 117]) : List Symbol :=
  let store := [.terminal 117] ++ (if hasEnv then [.terminal 117] else [])
  [.terminal 121] ++ config ++ [.terminal 107] ++ store ++
    [.terminal 108, .terminal 117] ++
    (if withKind then [.terminal 117] else []) ++ [.terminal 117]

-- fst (PegRt.runParser config (newStore [env]) rule input), optionally
-- wrapped in PegPrelude.fmap PegPrelude.fst for lossless syntax mode.
def entryBodyWord (hasEnv syntaxMode : Bool) : List Symbol :=
  let run := runtimeCallWord hasEnv false
  let project := [.terminal 121, .terminal 107] ++ run ++ [.terminal 108]
  if syntaxMode then [.terminal 121, .terminal 121, .terminal 107] ++ project ++ [.terminal 108]
  else project

open RenderExpressionGHC in
theorem runtime_call (hasEnv withKind : Bool) (config : List Symbol := [.terminal 117])
    (config_ok : Derives productions [.nonterminal 218] config := by exact varid_argument) :
    Derives productions [.nonterminal 217] (runtimeCallWord hasEnv withKind config) := by
  have store : Derives productions [.nonterminal 217]
      ([.terminal 117] ++ (if hasEnv then [.terminal 117] else [])) := by
    have name := oneRule (id := 536) (by rfl) varid_argument
    cases hasEnv
    · exact name
    · exact application name varid_argument
  have nested := parenthesized (oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
    (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) store))))
  have partialCall := application (application (application qualified_function config_ok)
    nested) varid_argument
  cases withKind
  · simpa [runtimeCallWord, List.append_assoc] using application partialCall varid_argument
  · simpa [runtimeCallWord, List.append_assoc] using
      application (application partialCall varid_argument) varid_argument

def tabstopConfigWord : List Symbol :=
  [.terminal 107, .terminal 117, .terminal 107, .terminal 121, .terminal 117,
   .terminal 108, .terminal 117, .terminal 108]

open RenderExpressionGHC in
theorem debug_tabstop_call (hasEnv withKind : Bool) :
    Derives productions [.nonterminal 217] (runtimeCallWord hasEnv withKind tabstopConfigWord) := by
  have parens {w} (f : Derives productions [.nonterminal 217] w) :=
    parenthesized (oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
      (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))))
  have get := parens (application qualified_function varid_argument)
  have set := application (oneRule (id := 536) (by rfl) varid_argument) get
  exact runtime_call hasEnv withKind _ (parens (application set varid_argument))

def recordConfigWord : List Symbol :=
  [.terminal 117, .terminal 101, .terminal 121, .terminal 77,
   .terminal 121, .terminal 117, .terminal 102]

open RenderExpressionGHC in
theorem debug_record_call (hasEnv withKind : Bool) :
    Derives productions [.nonterminal 217] (runtimeCallWord hasEnv withKind recordConfigWord) := by
  have field := oneRule (id := 769) (by rfl)
    (applyRule (g := productions) (id := 774) (by rfl) (.refl _))
  have get := application qualified_function varid_argument
  have value := oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
    (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) get)))
  have binding := applyRule (id := 668) (by rfl)
    (beside field (beside (.refl [.terminal 77]) value))
  have fields := oneRule (id := 663) (by rfl) (oneRule (id := 666) (by rfl) binding)
  have cfg := oneRule (id := 554) (by rfl) (oneRule (id := 555) (by rfl)
    (oneRule (id := 769) (by rfl) (oneRule (id := 773) (by rfl)
      (applyRule (g := productions) (id := 775) (by rfl) (.refl _)))))
  have update := applyRule (id := 552) (by rfl) (beside cfg
    (beside (.refl [.terminal 101]) (beside fields (.refl [.terminal 102]))))
  exact runtime_call hasEnv withKind _ (oneRule (id := 551) (by rfl) update)

def debugCallWord (hasEnv withKind noTraditionalRecordSyntax : Bool) : List Symbol :=
  runtimeCallWord hasEnv withKind
    (if noTraditionalRecordSyntax then tabstopConfigWord else recordConfigWord)

theorem debug_direct_binding (hasEnv withKind noTraditionalRecordSyntax : Bool) :
    Derives productions [.nonterminal 78]
      (argumentsWord (List.replicate (if hasEnv then 3 else 2) [.terminal 117]) ++
        [.terminal 77] ++ debugCallWord hasEnv withKind noTraditionalRecordSyntax) := by
  have call : Derives productions [.nonterminal 217]
      (debugCallWord hasEnv withKind noTraditionalRecordSyntax) := by
    cases noTraditionalRecordSyntax
    · exact debug_record_call hasEnv withKind
    · exact debug_tabstop_call hasEnv withKind
  apply binding_named_arguments
  · intro arg member
    exact List.eq_of_mem_replicate member ▸ varid_argument
  · exact oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl)
      (oneRule (id := 528) (by rfl) call))

#print axioms debug_direct_binding
#print axioms debug_record_call
#print axioms debug_tabstop_call
#print axioms runtime_call

open RenderExpressionGHC in
theorem entry_body (hasEnv syntaxMode : Bool) :
    Derives productions [.nonterminal 211] (entryBodyWord hasEnv syntaxMode) := by
  have expr {w} (f : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have parens {w} (f : Derives productions [.nonterminal 217] w) :=
    parenthesized (oneRule (id := 596) (by rfl) (expr f))
  have run := runtime_call hasEnv false
  have project := application qualified_function (parens run)
  cases syntaxMode
  · simpa [entryBodyWord, List.append_assoc] using expr project
  · have fstArg := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
      (oneRule (id := 555) (by rfl) (oneRule (id := 769) (by rfl)
        (applyRule (g := productions) (id := 774) (by rfl) (.refl _)))))
    simpa [entryBodyWord, List.append_assoc] using
      expr (application (application qualified_function fstArg) (parens project))

#print axioms entry_body

def syntaxMapWord : List Symbol :=
  [.terminal 121, .terminal 107, .terminal 78, .terminal 117, .terminal 83,
   .terminal 121, .terminal 117, .terminal 117, .terminal 107, .terminal 121,
   .terminal 117, .terminal 108, .terminal 108]

def syntaxEntryBodyWord (hasEnv : Bool) : List Symbol :=
  syntaxMapWord ++ [.terminal 107] ++ entryBodyWord hasEnv false ++ [.terminal 108]

open RenderExpressionGHC in
private theorem syntax_map : Derives productions [.nonterminal 217] syntaxMapWord := by
  have expr {w} (f : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have parens {w} (e : Derives productions [.nonterminal 211] w) :=
    parenthesized (oneRule (id := 596) (by rfl) e)
  have children := parens (expr (application qualified_function varid_argument))
  have root := expr (application (application (application qualified_function varid_argument)
    varid_argument) children)
  have pat := oneRule (id := 642) (by rfl) (oneRule (id := 646) (by rfl) varid_argument)
  have pats := applyRule (id := 644) (by rfl) (beside pat
    (applyRule (g := productions) (id := 645) (by rfl) (.refl [])))
  have callback := applyRule (id := 542) (by rfl) (beside (.refl [.terminal 78])
    (beside pats (beside (.refl [.terminal 83]) root)))
  exact application qualified_function (parenthesized (aexp_to_texp callback))

open RenderExpressionGHC in
theorem syntax_entry_body (hasEnv : Bool) :
    Derives productions [.nonterminal 211] (syntaxEntryBodyWord hasEnv) := by
  have arg := parenthesized (oneRule (id := 596) (by rfl) (entry_body hasEnv false))
  have call := application syntax_map arg
  simpa [syntaxEntryBodyWord, List.append_assoc] using oneRule (id := 520) (by rfl)
    (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) call))

#print axioms syntax_entry_body

theorem pair_argument {value errors : List Symbol}
    (v : Derives productions [.nonterminal 229] value)
    (e : Derives productions [.nonterminal 229] errors) :
    Derives productions [.nonterminal 218]
      ([.terminal 107] ++ value ++ [.terminal 114] ++ errors ++ [.terminal 108]) := by
  have comma := applyRule (g := productions) (id := 839) (by rfl) (.refl _)
  have suffix := applyRule (id := 604) (by rfl)
    (beside comma (oneRule (id := 606) (by rfl) e))
  have pair := applyRule (id := 600) (by rfl) (beside v suffix)
  have atom := applyRule (id := 563) (by rfl)
    (beside (.refl [.terminal 107]) (beside pair (.refl [.terminal 108])))
  simpa [List.append_assoc] using
    oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl) atom)

-- Recovery binds the value, error list and either a discarded or named stats value.
def recoverPatternWord (keepStats : Bool) : List Symbol :=
  [.terminal 107, .terminal 117, .terminal 114, .terminal 117, .terminal 114,
    if keepStats then .terminal 117 else .terminal 2, .terminal 108]

private theorem recovery_triple {first lastWord : List Symbol}
    (first_ok : Derives productions [.nonterminal 229] first)
    (last : Derives productions [.nonterminal 218] lastWord) :
    Derives productions [.nonterminal 218] ([.terminal 107] ++ first ++
      [.terminal 114, .terminal 117, .terminal 114] ++ lastWord ++ [.terminal 108]) := by
  have comma := applyRule (g := productions) (id := 839) (by rfl) (.refl _)
  have var := RenderExpressionGHC.aexp_to_texp varid_argument
  have tail := applyRule (id := 604) (by rfl) (beside comma
    (oneRule (id := 606) (by rfl) (RenderExpressionGHC.aexp_to_texp last)))
  have middle := applyRule (id := 605) (by rfl) (beside var tail)
  have triple := applyRule (id := 600) (by rfl)
    (beside first_ok (applyRule (id := 604) (by rfl) (beside comma middle)))
  have atom := applyRule (id := 563) (by rfl)
    (beside (.refl [.terminal 107]) (beside triple (.refl [.terminal 108])))
  simpa [List.append_assoc] using oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl) atom)

theorem recover_pattern (keepStats : Bool) :
    Derives productions [.nonterminal 212] (recoverPatternWord keepStats) := by
  have last : Derives productions [.nonterminal 218]
      [if keepStats then .terminal 117 else .terminal 2] := by
    cases keepStats
    · exact wildcard_argument
    · exact varid_argument
  have atom := recovery_triple (RenderExpressionGHC.aexp_to_texp varid_argument) last
  exact oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) (oneRule (id := 536) (by rfl) atom))

#print axioms recover_pattern

def recoverResultWord (projectValue : Bool) : List Symbol :=
  [.terminal 107] ++ (if projectValue then [.terminal 121, .terminal 121] else []) ++
    [.terminal 117, .terminal 114, .terminal 117, .terminal 108]

open RenderExpressionGHC in
private theorem recover_value (projectValue : Bool) :
    Derives productions [.nonterminal 229]
      ((if projectValue then [.terminal 121, .terminal 121] else []) ++ [.terminal 117]) := by
  have name := aexp_to_texp varid_argument
  cases projectValue
  · exact name
  · have fstArg := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
      (oneRule (id := 555) (by rfl) (oneRule (id := 769) (by rfl)
        (applyRule (g := productions) (id := 774) (by rfl) (.refl _)))))
    have value := application (application qualified_function fstArg) varid_argument
    have term := oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
      (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) value)))
    exact term

theorem recover_result (projectValue : Bool) :
    Derives productions [.nonterminal 218] (recoverResultWord projectValue) := by
  simpa [recoverResultWord, List.append_assoc] using pair_argument
    (recover_value projectValue) (RenderExpressionGHC.aexp_to_texp varid_argument)

-- close is either a virtual closing brace or Happy's parser-directed close.
private theorem layout_let {pattern call result close : List Symbol}
    (pattern_ok : Derives productions [.nonterminal 212] pattern)
    (call_ok : Derives productions [.nonterminal 217] call)
    (result_ok : Derives productions [.nonterminal 218] result)
    (close_ok : Derives productions [.nonterminal 320] close) :
    Derives productions [.nonterminal 218] ([.terminal 18, .terminal 103] ++ pattern ++
      [.terminal 77] ++ call ++ close ++ [.terminal 13] ++ result) := by
  have expression {w} (app : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) app))
  have rhs := applyRule (id := 491) (by rfl) (beside (.refl [.terminal 77])
    (beside (expression call_ok)
      (applyRule (g := productions) (id := 300) (by rfl) (.refl []))))
  have decl := applyRule (id := 486) (by rfl) (beside pattern_ok
    (beside (applyRule (g := productions) (id := 359) (by rfl) (.refl [])) rhs))
  have decls := oneRule (id := 292) (by rfl) (oneRule (id := 489) (by rfl) decl)
  have binds := oneRule (id := 296) (by rfl) (applyRule (id := 295) (by rfl)
    (beside (.refl [.terminal 103]) (beside decls close_ok)))
  have body := expression (oneRule (id := 536) (by rfl) result_ok)
  simpa [List.append_assoc] using applyRule (id := 541) (by rfl)
    (beside (.refl [.terminal 18]) (beside binds (beside (.refl [.terminal 13]) body)))

theorem recover_let (hasEnv withKind projectValue : Bool) {close : List Symbol}
    (close_ok : Derives productions [.nonterminal 320] close) :
    Derives productions [.nonterminal 218]
      ([.terminal 18, .terminal 103] ++ recoverPatternWord false ++ [.terminal 77] ++
        runtimeCallWord hasEnv withKind ++ close ++ [.terminal 13] ++
        recoverResultWord projectValue) := by
  exact layout_let (recover_pattern false) (runtime_call hasEnv withKind)
    (recover_result projectValue) close_ok

def debugValueLetWord (hasEnv noTraditionalRecordSyntax : Bool) (close : List Symbol) : List Symbol :=
  [.terminal 18, .terminal 103] ++ recoverResultWord false ++ [.terminal 77] ++
        debugCallWord hasEnv false noTraditionalRecordSyntax ++ close ++ [.terminal 13] ++
        recoverResultWord true

theorem debug_value_let (hasEnv noTraditionalRecordSyntax : Bool) {close : List Symbol}
    (close_ok : Derives productions [.nonterminal 320] close) :
    Derives productions [.nonterminal 218]
      (debugValueLetWord hasEnv noTraditionalRecordSyntax close) := by
  have pattern := oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl)
    (oneRule (id := 536) (by rfl) (recover_result false)))
  apply layout_let pattern _ (recover_result true) close_ok
  cases noTraditionalRecordSyntax
  · exact debug_record_call hasEnv false
  · exact debug_tabstop_call hasEnv false

def debugSyntaxLetWord (hasEnv noTraditionalRecordSyntax : Bool) (close : List Symbol) : List Symbol :=
  [.terminal 18, .terminal 103] ++ recoverResultWord false ++ [.terminal 77] ++
        debugCallWord hasEnv false noTraditionalRecordSyntax ++ close ++ [.terminal 13,
          .terminal 107] ++ syntaxMapWord ++ [.terminal 117, .terminal 114,
          .terminal 117, .terminal 108]

theorem debug_syntax_let (hasEnv noTraditionalRecordSyntax : Bool) {close : List Symbol}
    (close_ok : Derives productions [.nonterminal 320] close) :
    Derives productions [.nonterminal 218]
      (debugSyntaxLetWord hasEnv noTraditionalRecordSyntax close) := by
  have pattern := oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl)
    (oneRule (id := 536) (by rfl) (recover_result false)))
  have mapped := RenderExpressionGHC.application syntax_map varid_argument
  have tree := oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
    (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) mapped)))
  have pair := pair_argument tree (RenderExpressionGHC.aexp_to_texp varid_argument)
  have call : Derives productions [.nonterminal 217]
      (debugCallWord hasEnv false noTraditionalRecordSyntax) := by
    cases noTraditionalRecordSyntax
    · exact debug_record_call hasEnv false
    · exact debug_tabstop_call hasEnv false
  simpa [debugSyntaxLetWord, List.append_assoc] using layout_let pattern call pair close_ok

def debugRecoverLetWord (hasEnv syntaxMode noTraditionalRecordSyntax : Bool) (close : List Symbol) : List Symbol :=
  [.terminal 18, .terminal 103] ++ recoverPatternWord true ++ [.terminal 77] ++
        debugCallWord hasEnv false noTraditionalRecordSyntax ++ close ++ [.terminal 13, .terminal 107] ++
        (if syntaxMode then [.terminal 121, .terminal 121] else []) ++
        [.terminal 117, .terminal 114, .terminal 117, .terminal 114, .terminal 117, .terminal 108]

theorem debug_recover_let (hasEnv syntaxMode noTraditionalRecordSyntax : Bool) {close : List Symbol}
    (close_ok : Derives productions [.nonterminal 320] close) :
    Derives productions [.nonterminal 218]
      (debugRecoverLetWord hasEnv syntaxMode noTraditionalRecordSyntax close) := by
  have call : Derives productions [.nonterminal 217] (debugCallWord hasEnv false noTraditionalRecordSyntax) := by
    cases noTraditionalRecordSyntax
    · exact debug_record_call hasEnv false
    · exact debug_tabstop_call hasEnv false
  simpa [debugRecoverLetWord, List.append_assoc] using layout_let (recover_pattern true) call
    (recovery_triple (recover_value syntaxMode) varid_argument) close_ok

#print axioms debug_recover_let
#print axioms debug_syntax_let
#print axioms debug_value_let

def recoverBodyWord (hasEnv syntaxMode syntaxTree parserClose : Bool) : List Symbol :=
  [.terminal 18, .terminal 103] ++ recoverPatternWord false ++ [.terminal 77] ++
    runtimeCallWord hasEnv syntaxTree ++ [.terminal (if parserClose then 0 else 104),
      .terminal 13] ++ recoverResultWord (syntaxMode && !syntaxTree)

theorem recover_entry_binding (hasEnv syntaxMode syntaxTree parserClose : Bool) :
    Derives productions [.nonterminal 78]
      (argumentsWord (List.replicate (if hasEnv then 2 else 1) [.terminal 117]) ++
        [.terminal 77] ++ recoverBodyWord hasEnv syntaxMode syntaxTree parserClose) := by
  have close : Derives productions [.nonterminal 320]
      [.terminal (if parserClose then 0 else 104)] := by
    cases parserClose
    · exact applyRule (id := 834) (by rfl) (.refl _)
    · exact applyRule (id := 835) (by rfl) (.refl _)
  have atom := recover_let hasEnv syntaxTree (syntaxMode && !syntaxTree) close
  apply binding_named_arguments
  · intro arg h
    exact List.eq_of_mem_replicate h ▸ varid_argument
  · simpa [recoverBodyWord, List.append_assoc] using
      oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl)
        (oneRule (id := 528) (by rfl) (oneRule (id := 536) (by rfl) atom)))

#print axioms recover_entry_binding
#print axioms recover_let

#print axioms recover_result

-- PegRt.Text -> PegPrelude.Either PegRt.ParseError (resultType)
def entryTypeWord (result : List Symbol) : List Symbol :=
  [.terminal 122, .terminal 83, .terminal 122, .terminal 122, .terminal 107] ++
    result ++ [.terminal 108]

private theorem unqualifiedTypeAtom : Derives productions [.nonterminal 172] [.terminal 118] :=
  oneRule (id := 400) (by rfl) (oneRule (id := 718) (by rfl)
    (oneRule (id := 723) (by rfl) (oneRule (id := 732) (by rfl)
      (applyRule (g := productions) (id := 733) (by rfl) (.refl [.terminal 118])))))

-- dataDecl emits an unqualified constructor followed by typeAtom for each field.
theorem data_constructor (fields : List (List Symbol))
    (field_ok : ∀ field ∈ fields, Derives productions [.nonterminal 172] field) :
    Derives productions [.nonterminal 191] ([.terminal 118] ++ fields.flatten) := by
  have name := unqualifiedTypeAtom
  have appendFields (args : List (List Symbol)) (head : List Symbol)
      (h : Derives productions [.nonterminal 169] head)
      (ok : ∀ x ∈ args, Derives productions [.nonterminal 172] x) :
      Derives productions [.nonterminal 169] (head ++ args.flatten) := by
    induction args generalizing head with
    | nil => simpa using h
    | cons x xs ih =>
      have app := applyRule (id := 392) (by rfl)
        (beside h (oneRule (id := 394) (by rfl) (ok x (by simp))))
      simpa [List.append_assoc] using ih _ app (fun y hy => ok y (by simp [hy]))
  have applied := appendFields fields _ (oneRule (id := 390) (by rfl) name) field_ok
  have stuff := oneRule (id := 466) (by rfl) (oneRule (id := 387) (by rfl) applied)
  simpa using applyRule (id := 463) (by rfl)
    (beside (applyRule (g := productions) (id := 465) (by rfl) (.refl [])) stuff)

structure ConstructorFields where
  fields : List (List Symbol)
  valid : ∀ field ∈ fields, Derives productions [.nonterminal 172] field

-- A parenthesized user type occupies exactly one constructor field, even
-- when its outermost production is application or a function arrow.
def ConstructorFields.ofParenthesized (types : List (List Symbol))
    (valid : ∀ ty ∈ types, Derives productions [.nonterminal 162] ty) :
    ConstructorFields where
  fields := types.map fun ty => [.terminal 107] ++ ty ++ [.terminal 108]
  valid := by
    intro field member
    obtain ⟨ty, hty, rfl⟩ := List.mem_map.mp member
    have inner := beside (.refl [.terminal 107]) (beside (valid ty hty) (.refl [.terminal 108]))
    simpa [List.append_assoc] using applyRule (id := 412) (by rfl) inner

#print axioms ConstructorFields.ofParenthesized

def ConstructorFields.word (c : ConstructorFields) : List Symbol :=
  [.terminal 118] ++ c.fields.flatten

def constructorTail (initial : List Symbol) (rest : List ConstructorFields) :=
  rest.foldl (fun acc c => acc ++ [.terminal 81] ++ c.word) initial

theorem data_constructors (first : ConstructorFields) (rest : List ConstructorFields) :
    Derives productions [.nonterminal 189]
      ([.terminal 77] ++ constructorTail first.word rest) := by
  have extend (cs : List ConstructorFields) (initial : List Symbol)
      (valid : Derives productions [.nonterminal 190] initial) :
      Derives productions [.nonterminal 190] (constructorTail initial cs) := by
    induction cs generalizing initial with
    | nil => exact valid
    | cons c cs ih =>
      apply ih
      have next := beside valid (beside (.refl [.terminal 81]) (data_constructor c.fields c.valid))
      simpa [List.append_assoc, ConstructorFields.word] using
        applyRule (id := 460) (by rfl) next
  have list := extend rest first.word (oneRule (id := 461) (by rfl)
    (data_constructor first.fields first.valid))
  exact applyRule (id := 459) (by rfl) (beside (.refl [.terminal 77]) list)

#print axioms data_constructors
#print axioms data_constructor

private theorem qualifiedTypeAtom : Derives productions [.nonterminal 172] [.terminal 122] :=
  oneRule (id := 400) (by rfl) (oneRule (id := 718) (by rfl)
    (oneRule (id := 723) (by rfl) (applyRule (id := 731) (by rfl) (.refl _))))

-- The two contexts used by typeCode: a complete type inside a list and
-- an atomic argument after Maybe or a data constructor.
structure FieldType where
  word : List Symbol
  atom : List Symbol
  typeValid : Derives productions [.nonterminal 162] word
  atomValid : Derives productions [.nonterminal 172] atom

private theorem field_application_type {w} (h : Derives productions [.nonterminal 169] w) :
    Derives productions [.nonterminal 162] w :=
  oneRule (id := 374) (by rfl) (oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
    (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) h))))

-- peg'config :: PegRt.Config, followed by the default binding when the
-- grammar has no explicit tabstop.
theorem config_signature :
    Derives productions [.nonterminal 78] [.terminal 117, .terminal 76, .terminal 122] :=
  signature_named_ctype (oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
    (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl)
      (oneRule (id := 390) (by rfl) qualifiedTypeAtom)))))

theorem default_config_binding :
    Derives productions [.nonterminal 78] [.terminal 117, .terminal 77, .terminal 121] :=
  binding_named_infixexp (oneRule (id := 523) (by rfl)
    (oneRule (id := 528) (by rfl) RenderExpressionGHC.qualified_function))

-- Explicit %tabstop uses either an update of defaultConfig or the
-- positional helper when traditional record syntax is disabled.
def tabstopBindingWord (positional : Bool) : List Symbol :=
  [.terminal 117, .terminal 77] ++
    (if positional then [.terminal 117, .terminal 131, .terminal 121]
     else [.terminal 121, .terminal 101, .terminal 121, .terminal 77,
           .terminal 131, .terminal 102])

open RenderExpressionGHC in
theorem tabstop_config_binding (positional : Bool) :
    Derives productions [.nonterminal 78] (tabstopBindingWord positional) := by
  have qvar := oneRule (id := 769) (by rfl)
    (applyRule (g := productions) (id := 774) (by rfl) (.refl [.terminal 121]))
  have cfg := oneRule (id := 554) (by rfl) (oneRule (id := 555) (by rfl) qvar)
  have number := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
    (applyRule (g := productions) (id := 560) (by rfl) (.refl [.terminal 131])))
  have infixExpr {w} (f : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f)
  cases positional
  · have rhs := oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
      (infixExpr (oneRule (id := 536) (by rfl) number)))
    have field := applyRule (id := 668) (by rfl) (beside qvar (beside (.refl [.terminal 77]) rhs))
    have fields := oneRule (id := 663) (by rfl) (oneRule (id := 666) (by rfl) field)
    have update := applyRule (id := 552) (by rfl) (beside cfg
      (beside (.refl [.terminal 101]) (beside fields (.refl [.terminal 102]))))
    exact binding_named_infixexp (infixExpr (oneRule (id := 536) (by rfl)
      (oneRule (id := 551) (by rfl) update)))
  · have call := application (application (oneRule (id := 536) (by rfl) varid_argument) number)
      (oneRule (id := 551) (by rfl) cfg)
    exact binding_named_infixexp (infixExpr call)

#print axioms tabstop_config_binding
#print axioms config_signature
#print axioms default_config_binding

def FieldType.atomic {w} (h : Derives productions [.nonterminal 172] w) : FieldType :=
  ⟨w, w, field_application_type (oneRule (id := 390) (by rfl) h), h⟩

-- The two named leaves introduced by classify itself (unit and an
-- unqualified generated constructor identifier) have fixed token shapes.
def FieldType.unit : FieldType :=
  .atomic (applyRule (id := 406) (by rfl) (.refl [.terminal 107, .terminal 108]))

def FieldType.generated : FieldType := .atomic unqualifiedTypeAtom

-- For explicitly grouped annotations only the complete type is a premise.
def FieldType.parenthesized {word} (valid : Derives productions [.nonterminal 162] word) :
    FieldType :=
  ⟨word, _, valid, applyRule (id := 412) (by rfl)
    (beside (.refl [.terminal 107]) (beside valid (.refl [.terminal 108])))⟩

def FieldType.list (t : FieldType) : FieldType :=
  .atomic (applyRule (id := 411) (by rfl)
    (beside (.refl [.terminal 105]) (beside t.typeValid (.refl [.terminal 106]))))

def FieldType.maybe (t : FieldType) : FieldType := by
  have app := applyRule (id := 392) (by rfl)
    (beside (oneRule (id := 390) (by rfl) qualifiedTypeAtom)
      (oneRule (id := 394) (by rfl) t.atomValid))
  have ty := field_application_type app
  exact ⟨_, _, ty, applyRule (id := 412) (by rfl)
    (beside (.refl [.terminal 107]) (beside ty (.refl [.terminal 108])))⟩

def ConstructorFields.ofTypes (types : List FieldType) : ConstructorFields where
  fields := types.map FieldType.atom
  valid := by
    intro field member
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp member
    exact t.atomValid

-- Token-level rendering of Peg.Grammar.Types.ValueType. Named leaves carry
-- the two lexical contexts supplied by the annotation or generated name.
inductive ValueType (name : Type) where
  | text
  | list (inner : ValueType name)
  | maybe (inner : ValueType name)
  | named (n : name)

def ValueType.field (resolve : name → FieldType) : ValueType name → FieldType
  | .text => .atomic qualifiedTypeAtom
  | .list inner => (inner.field resolve).list
  | .maybe inner => (inner.field resolve).maybe
  | .named n => resolve n

theorem value_type_constructor (resolve : name → FieldType) (types : List (ValueType name)) :
    Derives productions [.nonterminal 191]
      ([.terminal 118] ++ (types.map fun t => (t.field resolve).atom).flatten) := by
  let fields := ConstructorFields.ofTypes (types.map (ValueType.field resolve))
  simpa [fields, ConstructorFields.ofTypes, List.map_map, Function.comp_def] using
    data_constructor fields.fields fields.valid

#print axioms value_type_constructor
#print axioms FieldType.unit
#print axioms FieldType.generated
#print axioms FieldType.parenthesized
#print axioms FieldType.list
#print axioms FieldType.maybe
#print axioms ConstructorFields.ofTypes

-- Each class is one CONID or QCONID token after lexing.
def derivingNames (qualified : Bool) : List Bool → List Symbol
  | [] => [.terminal (if qualified then 122 else 118)]
  | q :: qs => [.terminal (if qualified then 122 else 118), .terminal 114] ++ derivingNames q qs

def derivingClause : List Bool → List Symbol
  | [] => []
  | q :: qs => [.terminal 8, .terminal 107] ++ derivingNames q qs ++ [.terminal 108]

theorem data_deriving (classes : List Bool) :
    Derives productions [.nonterminal 198] (derivingClause classes) := by
  have classType (q : Bool) : Derives productions [.nonterminal 156]
      [.terminal (if q then 122 else 118)] := by
    have atom : Derives productions [.nonterminal 172] [.terminal (if q then 122 else 118)] := by
      cases q
      · exact oneRule (id := 400) (by rfl) (oneRule (id := 718) (by rfl)
          (oneRule (id := 723) (by rfl) (oneRule (id := 732) (by rfl)
            (applyRule (id := 733) (by rfl) (.refl _)))))
      · exact qualifiedTypeAtom
    exact oneRule (id := 363) (by rfl) (oneRule (id := 365) (by rfl)
      (oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
        (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) (oneRule (id := 390) (by rfl) atom))))))
  have names (q : Bool) (qs : List Bool) :
      Derives productions [.nonterminal 174] (derivingNames q qs) := by
    induction qs generalizing q with
    | nil => exact oneRule (id := 429) (by rfl) (classType q)
    | cons next rest ih =>
      simpa [derivingNames, List.append_assoc] using applyRule (id := 430) (by rfl) (beside (classType q)
        (beside (.refl [.terminal 114]) (ih next)))
  cases classes with
  | nil => exact applyRule (id := 475) (by rfl) (.refl [])
  | cons q qs =>
    have clause := applyRule (id := 484) (by rfl) (beside (.refl [.terminal 107])
      (beside (names q qs) (.refl [.terminal 108])))
    simpa [derivingClause, List.append_assoc] using oneRule (id := 476) (by rfl)
      (oneRule (id := 478) (by rfl) (applyRule (id := 479) (by rfl) (beside (.refl [.terminal 8]) clause)))

def dataDeclWord (first : ConstructorFields) (rest : List ConstructorFields) (classes : List Bool) :=
  let keyword := if rest.isEmpty && first.fields.length == 1 then 20 else 6
  [.terminal keyword, .terminal 118, .terminal 77] ++ constructorTail first.word rest ++ derivingClause classes

private theorem data_header : Derives productions [.nonterminal 105] [.terminal 118] := by
  have atom := oneRule (id := 400) (by rfl) (oneRule (id := 718) (by rfl)
    (oneRule (id := 723) (by rfl) (oneRule (id := 732) (by rfl)
      (applyRule (g := productions) (id := 733) (by rfl) (.refl _)))))
  exact oneRule (id := 238) (by rfl) (oneRule (id := 381) (by rfl)
    (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) (oneRule (id := 390) (by rfl) atom))))

-- Peg'Store has one type parameter even when it has no fields. In the
-- positional form, data is retained for any number of constructor fields.
private theorem type_with_state_parameter {w} (atom : Derives productions [.nonterminal 172] w) :
    Derives productions [.nonterminal 169] (w ++ [.terminal 117]) := by
  have param := oneRule (id := 401) (by rfl) (oneRule (id := 760) (by rfl)
    (applyRule (g := productions) (id := 762) (by rfl) (.refl [.terminal 117])))
  exact applyRule (id := 392) (by rfl)
    (beside (oneRule (id := 390) (by rfl) atom) (oneRule (id := 394) (by rfl) param))

def groupedKeyParameter (ty : List Symbol) : List Symbol :=
  [.terminal 107] ++ ty ++ [.terminal 108]

def keyParameterTail (first : List Symbol) : List (List Symbol) → List Symbol
  | [] => groupedKeyParameter first
  | next :: rest => groupedKeyParameter first ++ [.terminal 114] ++ keyParameterTail next rest

theorem tuple_key_argument (first second : List Symbol) (rest : List (List Symbol))
    (valid : ∀ ty ∈ first :: second :: rest, Derives productions [.nonterminal 162] ty) :
    Derives productions [.nonterminal 172]
      ([.terminal 107] ++ keyParameterTail first (second :: rest) ++ [.terminal 108]) := by
  have group {ty} (h : Derives productions [.nonterminal 162] ty) :=
    field_application_type (oneRule (id := 390) (by rfl) (applyRule (id := 412) (by rfl)
      (beside (.refl [.terminal 107]) (beside h (.refl [.terminal 108])))))
  have tail (x : List Symbol) (xs : List (List Symbol))
      (ok : ∀ t ∈ x :: xs, Derives productions [.nonterminal 162] t) :
      Derives productions [.nonterminal 176] (keyParameterTail x xs) := by
    induction xs generalizing x with
    | nil => simpa [keyParameterTail, groupedKeyParameter, List.append_assoc] using
        oneRule (id := 433) (by rfl) (group (ok x (by simp)))
    | cons y ys ih =>
      have remain := ih y (fun t ht => ok t (List.mem_cons_of_mem _ ht))
      simpa [keyParameterTail, groupedKeyParameter, List.append_assoc] using
        applyRule (id := 434) (by rfl) (beside (group (ok x (by simp))) (beside (.refl [.terminal 114]) remain))
  have remain := tail second rest (fun t ht => valid t (List.mem_cons_of_mem _ ht))
  simpa [keyParameterTail, groupedKeyParameter, List.append_assoc] using
    applyRule (id := 407) (by rfl) (beside (.refl [.terminal 107]) (beside (group (valid first (by simp)))
      (beside (.refl [.terminal 114]) (beside remain (.refl [.terminal 108])))))

#print axioms tuple_key_argument

def memoTableTypeWord (key : Option (List Symbol)) (result : List Symbol) : List Symbol :=
  [.terminal 122, .terminal 117] ++
    (match key with
     | none => []
     | some ty => [.terminal 107] ++ ty ++ [.terminal 108]) ++ result

theorem memo_table_field_type (key : Option (List Symbol)) {result : List Symbol}
    (validKey : ∀ ty ∈ key.toList, Derives productions [.nonterminal 162] ty)
    (validResult : Derives productions [.nonterminal 172] result) :
    Derives productions [.nonterminal 163] (memoTableTypeWord key result) := by
  have appendArg {w a} (f : Derives productions [.nonterminal 169] w)
      (arg : Derives productions [.nonterminal 172] a) :=
    applyRule (id := 392) (by rfl) (beside f (oneRule (id := 394) (by rfl) arg))
  have liftApp {w} (f : Derives productions [.nonterminal 169] w) :=
    oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
      (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) f)))
  have table := type_with_state_parameter qualifiedTypeAtom
  cases key with
  | none => exact liftApp (appendArg table validResult)
  | some ty =>
    have group := applyRule (id := 412) (by rfl)
      (beside (.refl [.terminal 107]) (beside (validKey ty (by simp)) (.refl [.terminal 108])))
    simpa [memoTableTypeWord, List.append_assoc] using liftApp (appendArg (appendArg table group) validResult)

#print axioms memo_table_field_type

private theorem store_header :
    Derives productions [.nonterminal 105] [.terminal 118, .terminal 117] :=
  oneRule (id := 238) (by rfl) (oneRule (id := 381) (by rfl)
    (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl)
      (type_with_state_parameter unqualifiedTypeAtom))))

def storeAccessorSignatureWord (fieldType : List Symbol) : List Symbol :=
  [.terminal 117, .terminal 76, .terminal 118, .terminal 117, .terminal 83] ++ fieldType

theorem store_accessor_signature {fieldType : List Symbol}
    (result : Derives productions [.nonterminal 163] fieldType) :
    Derives productions [.nonterminal 78] (storeAccessorSignatureWord fieldType) := by
  have store := oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl)
    (type_with_state_parameter unqualifiedTypeAtom))
  have arrow := applyRule (id := 382) (by rfl)
    (beside store (beside (.refl [.terminal 83]) result))
  exact signature_named_ctype (oneRule (id := 379) (by rfl) arrow)

#print axioms store_accessor_signature

def newStoreSignatureWord (env : Option (List Symbol)) : List Symbol :=
  [.terminal 117, .terminal 76] ++ parameterArrows env.toList
    [.terminal 122, .terminal 117, .terminal 107, .terminal 118, .terminal 117, .terminal 108]

theorem new_store_signature (env : Option (List Symbol))
    (valid : ∀ ty ∈ env.toList, Derives productions [.nonterminal 163] ty) :
    Derives productions [.nonterminal 78] (newStoreSignatureWord env) := by
  have store := field_application_type (type_with_state_parameter unqualifiedTypeAtom)
  have grouped := applyRule (id := 412) (by rfl)
    (beside (.refl [.terminal 107]) (beside store (.refl [.terminal 108])))
  have st := applyRule (id := 392) (by rfl) (beside (type_with_state_parameter qualifiedTypeAtom)
    (oneRule (id := 394) (by rfl) grouped))
  apply signature_named_ctype
  apply parameter_arrows _ _ valid
  exact oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
    (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) st)))

#print axioms new_store_signature

theorem positional_store_declaration (fields : ConstructorFields) :
    Derives productions [.nonterminal 78]
      ([.terminal 6, .terminal 118, .terminal 117, .terminal 77] ++ fields.word) := by
  have kw := applyRule (g := productions) (id := 222) (by rfl) (.refl [.terminal 6])
  have capi := applyRule (g := productions) (id := 245) (by rfl) (.refl [])
  have decl := applyRule (id := 169) (by rfl) (beside kw (beside capi (beside store_header
    (beside (data_constructors fields []) (data_deriving [])))))
  simpa [constructorTail, derivingClause] using oneRule (id := 153) (by rfl) decl

def storeRecordFields (first : List Symbol) : List (List Symbol) → List Symbol
  | [] => [.terminal 117, .terminal 76] ++ first
  | next :: rest => [.terminal 117, .terminal 76] ++ first ++ [.terminal 114] ++ storeRecordFields next rest

theorem store_record_fields (first : List Symbol) (rest : List (List Symbol))
    (valid : ∀ ty ∈ first :: rest, Derives productions [.nonterminal 163] ty) :
    Derives productions [.nonterminal 196] (storeRecordFields first rest) := by
  have field {ty} (h : Derives productions [.nonterminal 163] ty) :=
    applyRule (id := 474) (by rfl) (beside
      (oneRule (id := 367) (by rfl) (oneRule (id := 767) (by rfl)
        (applyRule (g := productions) (id := 775) (by rfl) (.refl [.terminal 117]))))
      (beside (.refl [.terminal 76]) h))
  induction rest generalizing first with
  | nil => exact oneRule (id := 473) (by rfl) (field (valid first (by simp)))
  | cons next rest ih =>
    have tail := ih next (fun ty h => valid ty (List.mem_cons_of_mem _ h))
    simpa [storeRecordFields, List.append_assoc] using applyRule (id := 472) (by rfl)
      (beside (field (valid first (by simp))) (beside (.refl [.terminal 114]) tail))

def recordStoreWord (first : List Symbol) (rest : List (List Symbol)) : List Symbol :=
  [.terminal 6, .terminal 118, .terminal 117, .terminal 77, .terminal 118, .terminal 101] ++
    storeRecordFields first rest ++ [.terminal 102]

theorem record_store_declaration (first : List Symbol) (rest : List (List Symbol))
    (valid : ∀ ty ∈ first :: rest, Derives productions [.nonterminal 163] ty) :
    Derives productions [.nonterminal 78] (recordStoreWord first rest) := by
  have contents := oneRule (id := 471) (by rfl) (store_record_fields first rest valid)
  have braces := applyRule (id := 405) (by rfl)
    (beside (.refl [.terminal 101]) (beside contents (.refl [.terminal 102])))
  let fields : ConstructorFields := ⟨[ _ ], fun f hf => List.mem_singleton.mp hf ▸ braces⟩
  simpa [recordStoreWord, fields, ConstructorFields.word, List.append_assoc] using
    positional_store_declaration fields

#print axioms record_store_declaration
#print axioms store_record_fields

def pureStoreBindingWord (hasEnv : Bool) : List Symbol :=
  let env := if hasEnv then [.terminal 117] else []
  [.terminal 117] ++ env ++ [.terminal 77, .terminal 121, .terminal 107, .terminal 118] ++
    env ++ [.terminal 108]

private theorem store_constructor_expr : Derives productions [.nonterminal 217] [.terminal 118] :=
  oneRule (id := 536) (by rfl) (oneRule (id := 551) (by rfl)
    (oneRule (id := 554) (by rfl) (oneRule (id := 556) (by rfl)
      (oneRule (id := 693) (by rfl) (oneRule (id := 695) (by rfl)
        (oneRule (id := 811) (by rfl) (applyRule (g := productions) (id := 813)
          (by rfl) (.refl [.terminal 118]))))))))

def storeAccessorPattern (prior later : Nat) : List Symbol :=
  [.terminal 107, .terminal 118] ++ List.replicate prior (.terminal 2) ++
    [.terminal 117] ++ List.replicate later (.terminal 2) ++ [.terminal 108]

open RenderExpressionGHC in
theorem store_accessor_binding (prior later : Nat) :
    Derives productions [.nonterminal 78]
      (argumentsWord [storeAccessorPattern prior later] ++ [.terminal 77] ++ [.terminal 117]) := by
  have skips (n : Nat) {w} (head : Derives productions [.nonterminal 217] w) :
      Derives productions [.nonterminal 217] (w ++ List.replicate n (.terminal 2)) := by
    induction n generalizing w with
    | zero => simpa using head
    | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using ih (application head wildcard_argument)
  have selected := application (skips prior store_constructor_expr) varid_argument
  have inner := skips later selected
  have pat := parenthesized (oneRule (id := 596) (by rfl) (oneRule (id := 520) (by rfl)
    (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) inner))))
  apply binding_named_arguments
  · intro arg member
    obtain rfl := List.mem_singleton.mp member
    simpa [storeAccessorPattern, List.append_assoc] using pat
  · exact oneRule (id := 520) (by rfl) name_infixexp

-- Each field contributes its signature and binding before the next field.
def storeAccessors (prior : Nat) : List (List Symbol) → List (List Symbol)
  | [] => []
  | ty :: rest =>
    storeAccessorSignatureWord ty ::
      (argumentsWord [storeAccessorPattern prior rest.length] ++ [.terminal 77] ++ [.terminal 117]) ::
      storeAccessors (prior + 1) rest

theorem store_accessors_valid (types : List (List Symbol))
    (valid : ∀ ty ∈ types, Derives productions [.nonterminal 163] ty)
    (prior : Nat) (item : List Symbol) (member : item ∈ storeAccessors prior types) :
    Derives productions [.nonterminal 78] item := by
  induction types generalizing prior with
  | nil => simp [storeAccessors] at member
  | cons ty rest ih =>
    simp only [storeAccessors, List.mem_cons] at member
    rcases member with rfl | rfl | tail
    · exact store_accessor_signature (valid ty (by simp))
    · exact store_accessor_binding prior rest.length
    · exact ih (fun t ht => valid t (by simp [ht])) _ tail

#print axioms store_accessors_valid
#print axioms store_accessor_binding

open RenderExpressionGHC in
theorem new_store_without_tables (hasEnv : Bool) :
    Derives productions [.nonterminal 78] (pureStoreBindingWord hasEnv) := by
  have con := store_constructor_expr
  have expr {ts} (f : Derives productions [.nonterminal 217] ts) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have pureStore {ts} (f : Derives productions [.nonterminal 217] ts) :=
    expr (application qualified_function (parenthesized (oneRule (id := 596) (by rfl) (expr f))))
  cases hasEnv
  · exact binding_named (pureStore con)
  · exact binding_named_arguments [[.terminal 117]]
      (by intro a h; simpa using List.mem_singleton.mp h ▸ varid_argument)
      (pureStore (application con varid_argument))

-- Both qualified operators and both table allocators have the same token
-- classes. The first pair is <$>/newTable (or newArgTable), then <*> pairs.
def tableAllocations (count : Nat) (head : List Symbol) : List Symbol :=
  head ++ (List.replicate count [.terminal 123, .terminal 121]).flatten

private theorem table_allocations_valid (count : Nat) (head : List Symbol)
    (valid : Derives productions [.nonterminal 212] head) :
    Derives productions [.nonterminal 212] (tableAllocations count head) := by
  induction count generalizing head with
  | zero => simpa [tableAllocations] using valid
  | succ n ih =>
    have op := oneRule (id := 749) (by rfl) (oneRule (id := 756) (by rfl)
      (oneRule (id := 783) (by rfl) (applyRule (g := productions) (id := 786)
        (by rfl) (.refl [.terminal 123]))))
    have rhs := oneRule (id := 525) (by rfl) (oneRule (id := 528) (by rfl)
      RenderExpressionGHC.qualified_function)
    have step := applyRule (id := 524) (by rfl) (beside valid (beside op rhs))
    simpa [tableAllocations, List.replicate_succ, List.append_assoc] using ih _ step

def memoStoreBindingWord (hasEnv : Bool) (additional : Nat) : List Symbol :=
  let env := if hasEnv then [.terminal 117] else []
  [.terminal 117] ++ env ++ [.terminal 77] ++
    tableAllocations (additional + 1) ([.terminal 118] ++ env)

open RenderExpressionGHC in
theorem new_store_with_tables (hasEnv : Bool) (additional : Nat) :
    Derives productions [.nonterminal 78] (memoStoreBindingWord hasEnv additional) := by
  have body {ts} (f : Derives productions [.nonterminal 217] ts) :=
    oneRule (id := 520) (by rfl) (table_allocations_valid (additional + 1) _
      (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f)))
  cases hasEnv
  · exact binding_named (body store_constructor_expr)
  · exact binding_named_arguments [[.terminal 117]]
      (by intro a h; simpa using List.mem_singleton.mp h ▸ varid_argument)
      (body (application store_constructor_expr varid_argument))

#print axioms new_store_with_tables
#print axioms new_store_without_tables

#print axioms positional_store_declaration

theorem data_declaration (first : ConstructorFields) (rest : List ConstructorFields)
    (classes : List Bool) : Derives productions [.nonterminal 78] (dataDeclWord first rest classes) := by
  have kw : Derives productions [.nonterminal 99]
      [.terminal (if rest.isEmpty && first.fields.length == 1 then 20 else 6)] := by
    split
    · exact applyRule (id := 223) (by rfl) (.refl _)
    · exact applyRule (id := 222) (by rfl) (.refl _)
  have capi := applyRule (g := productions) (id := 245) (by rfl) (.refl [])
  have decl := applyRule (id := 169) (by rfl) (beside kw (beside capi (beside data_header
    (beside (data_constructors first rest) (data_deriving classes)))))
  simpa [dataDeclWord, List.append_assoc] using oneRule (id := 153) (by rfl) decl

-- Every retained typed node wraps SyntaxNode and derives qualified Eq and Show.
def syntaxNodeNewtypeWord : List Symbol :=
  [.terminal 20, .terminal 118, .terminal 77, .terminal 118, .terminal 122,
   .terminal 8, .terminal 107, .terminal 122, .terminal 114, .terminal 122, .terminal 108]

theorem syntax_node_newtype :
    Derives productions [.nonterminal 78] syntaxNodeNewtypeWord := by
  let node : ConstructorFields := ⟨[[.terminal 122]], fun _ h =>
    List.mem_singleton.mp h ▸ qualifiedTypeAtom⟩
  exact data_declaration node [] [true, true]

-- kindVar n = PegRt.SyntaxKind k, where k is a nonnegative kind number.
theorem syntax_kind_binding :
    Derives productions [.nonterminal 78] [.terminal 117, .terminal 77, .terminal 122, .terminal 131] := by
  have name := applyRule (g := productions) (id := 812) (by rfl) (.refl [.terminal 122])
  have con := oneRule (id := 536) (by rfl) (oneRule (id := 551) (by rfl)
    (oneRule (id := 554) (by rfl) (oneRule (id := 556) (by rfl)
      (oneRule (id := 693) (by rfl) (oneRule (id := 695) (by rfl) name)))))
  have number := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
    (applyRule (g := productions) (id := 560) (by rfl) (.refl [.terminal 131])))
  exact binding_named_infixexp (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl)
    (RenderExpressionGHC.application con number)))

def triviaListWord : Nat → List Symbol
  | 0 => [.terminal 105, .terminal 106]
  | n + 1 => [.terminal 105, .terminal 117] ++
      (List.replicate n [.terminal 114, .terminal 117]).flatten ++ [.terminal 106]

open RenderExpressionGHC in
theorem trivia_binding (count : Nat) :
    Derives productions [.nonterminal 78]
      (argumentsWord [[.terminal 117]] ++ [.terminal 77] ++
        ([.terminal 121, .terminal 117] ++ triviaListWord count)) := by
  have item := aexp_to_texp varid_argument
  have list : Derives productions [.nonterminal 218] (triviaListWord count) := by
    cases count with
    | zero =>
      exact oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
        (oneRule (id := 556) (by rfl) (oneRule (id := 694) (by rfl)
          (applyRule (id := 709) (by rfl) (.refl _)))))
    | succ n =>
      cases n with
      | zero => exact choice_list (oneRule (id := 608) (by rfl) item)
      | succ n =>
        have extend (k : Nat) {w} (h : Derives productions [.nonterminal 234] w) :
            Derives productions [.nonterminal 234]
              (w ++ (List.replicate k [.terminal 114, .terminal 117]).flatten) := by
          induction k generalizing w with
          | zero => simpa using h
          | succ k ih =>
            simpa [List.replicate_succ, commaAppend, List.append_assoc] using
              ih (lexps_extend h item)
        have pair := applyRule (id := 616) (by rfl) (beside item (beside (.refl [.terminal 114]) item))
        simpa [triviaListWord, List.replicate_succ, List.append_assoc] using
          choice_list (oneRule (id := 609) (by rfl) (extend n pair))
  apply binding_named_arguments
  · intro a h
    exact List.mem_singleton.mp h ▸ varid_argument
  · exact oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl)
      (oneRule (id := 528) (by rfl) (application (application qualified_function varid_argument) list)))

#print axioms trivia_binding
inductive SyntaxAccessorKind where
  | oneNode | manyNodes | oneToken | manyTokens | elements

def syntaxAccessorResult : SyntaxAccessorKind → List Symbol
  | .oneNode => [.terminal 122, .terminal 118]
  | .manyNodes => [.terminal 105, .terminal 118, .terminal 106]
  | .oneToken => [.terminal 122, .terminal 122]
  | .manyTokens | .elements => [.terminal 105, .terminal 122, .terminal 106]

theorem syntax_accessor_signature (kind : SyntaxAccessorKind) :
    Derives productions [.nonterminal 78]
      ([.terminal 117, .terminal 76, .terminal 118, .terminal 83] ++ syntaxAccessorResult kind) := by
  have appType {w} (app : Derives productions [.nonterminal 169] w) :=
    oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
      (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) app)))
  have maybeTy {w} (atom : Derives productions [.nonterminal 172] w) :=
    appType (applyRule (id := 392) (by rfl) (beside (oneRule (id := 390) (by rfl) qualifiedTypeAtom)
      (oneRule (id := 394) (by rfl) atom)))
  have listTy {w} (atom : Derives productions [.nonterminal 172] w) :=
    appType (oneRule (id := 390) (by rfl) (FieldType.list (.atomic atom)).atomValid)
  have result : Derives productions [.nonterminal 163] (syntaxAccessorResult kind) := by
    cases kind with
    | oneNode => exact maybeTy unqualifiedTypeAtom
    | manyNodes => exact listTy unqualifiedTypeAtom
    | oneToken => exact maybeTy qualifiedTypeAtom
    | manyTokens | elements => exact listTy qualifiedTypeAtom
  have arg := oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl)
    (oneRule (id := 390) (by rfl) unqualifiedTypeAtom))
  exact signature_named_ctype (oneRule (id := 379) (by rfl) (applyRule (id := 382) (by rfl)
    (beside arg (beside (.refl [.terminal 83]) result))))

def syntaxAccessorBody (kind : SyntaxAccessorKind) : List Symbol :=
  let lookup := [.terminal 121, .terminal 117, .terminal 107, .terminal 121,
                 .terminal 130, .terminal 108, .terminal 117]
  match kind with
  | .oneNode | .manyNodes => [.terminal 121, .terminal 118, .terminal 107] ++ lookup ++ [.terminal 108]
  | .oneToken | .manyTokens | .elements => lookup

open RenderExpressionGHC in
theorem syntax_accessor_binding (kind : SyntaxAccessorKind) :
    Derives productions [.nonterminal 78]
      (argumentsWord [[.terminal 107, .terminal 118, .terminal 117, .terminal 108]] ++
        [.terminal 77] ++ syntaxAccessorBody kind) := by
  have expr {ts} (f : Derives productions [.nonterminal 217] ts) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have paren {ts} (f : Derives productions [.nonterminal 217] ts) :=
    parenthesized (oneRule (id := 596) (by rfl) (expr f))
  have str := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
    (oneRule (id := 559) (by rfl) (applyRule (g := productions) (id := 819) (by rfl) (.refl [.terminal 130]))))
  have label := paren (application qualified_function str)
  have lookup := application (application (application qualified_function varid_argument) label) varid_argument
  have con := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
    (oneRule (id := 556) (by rfl) (oneRule (id := 693) (by rfl)
      (oneRule (id := 695) (by rfl) (oneRule (id := 811) (by rfl)
        (applyRule (g := productions) (id := 813) (by rfl) (.refl [.terminal 118])))))))
  have mapped := application (application qualified_function con) (paren lookup)
  apply binding_named_arguments
  · intro arg member
    obtain rfl := List.mem_singleton.mp member
    exact paren (application store_constructor_expr varid_argument)
  · cases kind <;> first | exact expr mapped | exact expr lookup

#print axioms syntax_accessor_binding
#print axioms syntax_accessor_signature
#print axioms syntax_node_newtype
#print axioms syntax_kind_binding

structure DataDeclaration where
  constructors : List ConstructorFields
  classes : List Bool

def DataDeclaration.word (d : DataDeclaration) : List Symbol :=
  match d.constructors with
  | [] => [.terminal 6, .terminal 118] ++ derivingClause d.classes
  | first :: rest => dataDeclWord first rest d.classes

theorem data_declaration_valid (d : DataDeclaration) :
    Derives productions [.nonterminal 78] d.word := by
  unfold DataDeclaration.word
  cases d.constructors with
  | cons first rest => exact data_declaration first rest d.classes
  | nil =>
    have kw := applyRule (g := productions) (id := 222) (by rfl) (.refl _)
    have capi := applyRule (g := productions) (id := 245) (by rfl) (.refl [])
    have kind := applyRule (g := productions) (id := 227) (by rfl) (.refl [])
    have empty := applyRule (g := productions) (id := 454) (by rfl) (.refl [])
    have decl := applyRule (id := 170) (by rfl) (beside kw (beside capi (beside data_header
      (beside kind (beside empty (data_deriving d.classes))))))
    simpa using oneRule (id := 153) (by rfl) decl

#print axioms data_declaration_valid
#print axioms data_declaration
#print axioms data_deriving

private theorem qualified_type_arrow {tail : List Symbol}
    (valid : Derives productions [.nonterminal 163] tail) :
    Derives productions [.nonterminal 163] ([.terminal 122, .terminal 83] ++ tail) := by
  have arg := oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl)
    (oneRule (id := 390) (by rfl) qualifiedTypeAtom))
  simpa [List.append_assoc] using oneRule (id := 379) (by rfl) (applyRule (id := 382) (by rfl)
    (beside arg (beside (.refl [.terminal 83]) valid)))

-- nameOfSyntaxKind and isTriviaSyntaxKind return qualified runtime or
-- Prelude types. A typed node cast returns Maybe applied to a local type.
def syntaxQuerySignatureWord (cast : Bool) : List Symbol :=
  [.terminal 117, .terminal 76, .terminal 122, .terminal 83, .terminal 122] ++
    (if cast then [.terminal 118] else [])

theorem syntax_query_signature (cast : Bool) :
    Derives productions [.nonterminal 78] (syntaxQuerySignatureWord cast) := by
  have liftApp {w} (a : Derives productions [.nonterminal 169] w) :=
    oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
      (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) a)))
  have head := oneRule (id := 390) (by rfl) qualifiedTypeAtom
  cases cast with
  | false => exact signature_named_ctype (qualified_type_arrow (liftApp head))
  | true =>
    have app := applyRule (id := 392) (by rfl)
      (beside head (oneRule (id := 394) (by rfl) unqualifiedTypeAtom))
    exact signature_named_ctype (qualified_type_arrow (liftApp app))

def syntaxCastBody : List Symbol :=
  [.terminal 11, .terminal 121, .terminal 117, .terminal 123, .terminal 117,
   .terminal 23, .terminal 122, .terminal 107, .terminal 118, .terminal 117,
   .terminal 108, .terminal 9, .terminal 122]

open RenderExpressionGHC in
theorem syntax_cast_binding :
    Derives productions [.nonterminal 78]
      (argumentsWord [[.terminal 117]] ++ [.terminal 77] ++ syntaxCastBody) := by
  have operand {w} (f : Derives productions [.nonterminal 217] w) := oneRule (id := 528) (by rfl) f
  have expr {w} (f : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (operand f))
  have op := oneRule (id := 749) (by rfl) (oneRule (id := 756) (by rfl)
    (oneRule (id := 783) (by rfl) (applyRule (g := productions) (id := 786) (by rfl) (.refl [.terminal 123]))))
  have lhs := oneRule (id := 523) (by rfl) (operand (application qualified_function varid_argument))
  have rhs := oneRule (id := 525) (by rfl) (operand (oneRule (id := 536) (by rfl) varid_argument))
  have cond := oneRule (id := 520) (by rfl) (applyRule (id := 524) (by rfl) (beside lhs (beside op rhs)))
  have name := applyRule (g := productions) (id := 812) (by rfl) (.refl [.terminal 122])
  have con := oneRule (id := 536) (by rfl) (oneRule (id := 551) (by rfl)
    (oneRule (id := 554) (by rfl) (oneRule (id := 556) (by rfl)
      (oneRule (id := 693) (by rfl) (oneRule (id := 695) (by rfl) name)))))
  have wrapped := parenthesized (oneRule (id := 596) (by rfl)
    (expr (application store_constructor_expr varid_argument)))
  have sep := applyRule (g := productions) (id := 530) (by rfl) (.refl [])
  have branch := applyRule (id := 545) (by rfl) (beside (.refl [.terminal 11]) (beside cond
    (beside sep (beside (.refl [.terminal 23]) (beside (expr (application con wrapped))
      (beside sep (beside (.refl [.terminal 9]) (expr con))))))))
  apply binding_named_arguments
  · intro a h
    exact List.mem_singleton.mp h ▸ varid_argument
  · exact expr (oneRule (id := 536) (by rfl) branch)

def kindNameArm (numbered : Bool) : List Symbol :=
  (if numbered then [.terminal 122, .terminal 131] else [.terminal 2]) ++ [.terminal 83, .terminal 130]

open RenderExpressionGHC in
theorem kind_name_arm (numbered : Bool) :
    Derives productions [.nonterminal 334] (kindNameArm numbered) := by
  have expr {w} (f : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have lit := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
    (oneRule (id := 559) (by rfl) (applyRule (g := productions) (id := 819) (by rfl) (.refl [.terminal 130]))))
  have rhs := applyRule (id := 631) (by rfl) (beside
    (applyRule (id := 632) (by rfl) (beside (.refl [.terminal 83]) (expr (oneRule (id := 536) (by rfl) lit))))
    (applyRule (g := productions) (id := 300) (by rfl) (.refl [])))
  have arm {w} (f : Derives productions [.nonterminal 217] w) :=
    applyRule (id := 865) (by rfl) (beside (oneRule (id := 640) (by rfl)
      (oneRule (id := 639) (by rfl) (expr f))) rhs)
  cases numbered with
  | false => exact arm (oneRule (id := 536) (by rfl) wildcard_argument)
  | true =>
    have name := applyRule (g := productions) (id := 812) (by rfl) (.refl [.terminal 122])
    have con := oneRule (id := 536) (by rfl) (oneRule (id := 551) (by rfl)
      (oneRule (id := 554) (by rfl) (oneRule (id := 556) (by rfl)
        (oneRule (id := 693) (by rfl) (oneRule (id := 695) (by rfl) name)))))
    have num := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
      (applyRule (g := productions) (id := 560) (by rfl) (.refl [.terminal 131])))
    exact arm (application con num)

def numberedKindArms : Nat → List Symbol
  | 0 => kindNameArm true
  | n + 1 => numberedKindArms n ++ [.terminal 113] ++ kindNameArm true

def kindNameBody (extra : Nat) : List Symbol :=
  [.terminal 121, .terminal 107, .terminal 4, .terminal 117, .terminal 21, .terminal 101] ++
    numberedKindArms (extra + 1) ++ [.terminal 113] ++ kindNameArm false ++ [.terminal 102, .terminal 108]

open RenderExpressionGHC in
theorem kind_name_binding (extra : Nat) :
    Derives productions [.nonterminal 78]
      (argumentsWord [[.terminal 117]] ++ [.terminal 77] ++ kindNameBody extra) := by
  have extend {w} (h : Derives productions [.nonterminal 332] w) (numbered : Bool) :=
    applyRule (id := 861) (by rfl) (beside h (beside (.refl [.terminal 113]) (kind_name_arm numbered)))
  have numbers (n : Nat) : Derives productions [.nonterminal 332] (numberedKindArms n) := by
    induction n with
    | zero => exact oneRule (id := 863) (by rfl) (kind_name_arm true)
    | succ n ih => simpa [numberedKindArms, List.append_assoc] using extend ih true
  have alts := oneRule (id := 856) (by rfl) (extend (numbers (extra + 1)) false)
  have block := applyRule (id := 848) (by rfl)
    (beside (.refl [.terminal 101]) (beside alts (.refl [.terminal 102])))
  have scrutinee := oneRule (id := 520) (by rfl) name_infixexp
  have casesExpr := applyRule (id := 547) (by rfl)
    (beside (.refl [.terminal 4]) (beside scrutinee (beside (.refl [.terminal 21]) block)))
  have call := application qualified_function (parenthesized (aexp_to_texp casesExpr))
  apply binding_named_arguments
  · intro a h
    exact List.mem_singleton.mp h ▸ varid_argument
  · simpa [kindNameBody, List.append_assoc] using oneRule (id := 520) (by rfl)
      (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) call))

#print axioms kind_name_binding
#print axioms kind_name_arm
#print axioms syntax_cast_binding
#print axioms syntax_query_signature

theorem with_tabstop_signature :
    Derives productions [.nonterminal 78]
      [.terminal 117, .terminal 76, .terminal 122, .terminal 83,
       .terminal 122, .terminal 83, .terminal 122] := by
  apply signature_named_ctype
  apply qualified_type_arrow
  apply qualified_type_arrow
  exact oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
    (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl)
      (oneRule (id := 390) (by rfl) qualifiedTypeAtom))))

def configProjectionWord : List Symbol :=
  [.terminal 107, .terminal 121, .terminal 117, .terminal 108]

def withTabstopBindingWord : List Symbol :=
  [.terminal 117, .terminal 117, .terminal 117, .terminal 77, .terminal 122] ++
    (List.replicate 4 configProjectionWord).flatten ++ [.terminal 117] ++ configProjectionWord

open RenderExpressionGHC in
theorem with_tabstop_binding :
    Derives productions [.nonterminal 78] withTabstopBindingWord := by
  have expr {ts} (f : Derives productions [.nonterminal 217] ts) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have get := parenthesized (oneRule (id := 596) (by rfl)
    (expr (application qualified_function varid_argument)))
  have name := applyRule (g := productions) (id := 812) (by rfl) (.refl [.terminal 122])
  have con := oneRule (id := 536) (by rfl) (oneRule (id := 551) (by rfl)
    (oneRule (id := 554) (by rfl) (oneRule (id := 556) (by rfl)
      (oneRule (id := 693) (by rfl) (oneRule (id := 695) (by rfl) name)))))
  have four := application (application (application (application con get) get) get) get
  apply binding_named_arguments (List.replicate 2 [.terminal 117])
  · intro arg member
    exact List.eq_of_mem_replicate member ▸ varid_argument
  · exact expr (application (application four varid_argument) get)

#print axioms with_tabstop_signature
#print axioms with_tabstop_binding

-- Config comes first, followed by the optional parenthesized environment,
-- then Text. The result is the statistics-bearing tuple of the chosen entry.
def debugTypeWord (envType : Option (List Symbol)) (result : List Symbol) :=
  [.terminal 122, .terminal 83] ++ parameterArrows envType.toList
    ([.terminal 122, .terminal 83] ++ result)

theorem debug_signature (envType : Option { ty : List Symbol //
    Derives productions [.nonterminal 163] ty }) {result : List Symbol}
    (result_ok : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 78] ([.terminal 117, .terminal 76] ++
      debugTypeWord (envType.map Subtype.val) result) := by
  apply signature_named_ctype
  apply qualified_type_arrow
  apply parameter_arrows _ _ _ (qualified_type_arrow result_ok)
  cases envType with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.toList_some, List.mem_singleton]
    intro ty h
    exact h ▸ e.property

#print axioms debug_signature

def recoveryTupleWord (syntaxTree stats : Bool) (result : List Symbol) : List Symbol :=
  let value := if syntaxTree then [.terminal 122]
    else [.terminal 122, .terminal 107] ++ result ++ [.terminal 108]
  [.terminal 107] ++ value ++
    [.terminal 114, .terminal 105, .terminal 122, .terminal 106] ++
    (if stats then [.terminal 114, .terminal 122] else []) ++ [.terminal 108]

private theorem recovery_tuple_type (syntaxTree stats : Bool) {result : List Symbol}
    (result_ok : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 163] (recoveryTupleWord syntaxTree stats result) := by
  have base {w} (app : Derives productions [.nonterminal 169] w) :=
    oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) app)
  have ctype {w} (app : Derives productions [.nonterminal 169] w) :=
    oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl) (base app))
  have con := oneRule (id := 390) (by rfl) qualifiedTypeAtom
  have errorType := oneRule (id := 374) (by rfl) (ctype con)
  have errors := applyRule (id := 411) (by rfl)
    (beside (.refl [.terminal 105]) (beside errorType (.refl [.terminal 106])))
  have errList := oneRule (id := 374) (by rfl) (ctype (oneRule (id := 390) (by rfl) errors))
  have tail : Derives productions [.nonterminal 176] ([.terminal 105, .terminal 122, .terminal 106] ++
      (if stats then [.terminal 114, .terminal 122] else [])) := by
    cases stats
    · exact oneRule (id := 433) (by rfl) errList
    · exact applyRule (id := 434) (by rfl) (beside errList
        (beside (.refl [.terminal 114]) (oneRule (id := 433) (by rfl) errorType)))
  have value : Derives productions [.nonterminal 169]
      (if syntaxTree then [.terminal 122] else
        [.terminal 122, .terminal 107] ++ result ++ [.terminal 108]) := by
    cases syntaxTree
    · have paren := applyRule (id := 412) (by rfl) (beside (.refl [.terminal 107])
        (beside (oneRule (id := 374) (by rfl) result_ok) (.refl [.terminal 108])))
      simpa [List.append_assoc] using applyRule (id := 392) (by rfl)
        (beside con (oneRule (id := 394) (by rfl) paren))
    · exact con
  have pair := applyRule (id := 407) (by rfl) (beside (.refl [.terminal 107])
    (beside (oneRule (id := 374) (by rfl) (ctype value))
      (beside (.refl [.terminal 114]) (beside tail (.refl [.terminal 108])))))
  have rhs := ctype (oneRule (id := 390) (by rfl) pair)
  simpa [recoveryTupleWord, List.append_assoc] using rhs

def recoverTypeWord (syntaxTree : Bool) (result : List Symbol) :=
  [.terminal 122, .terminal 83] ++ recoveryTupleWord syntaxTree false result

theorem recover_entry_type (syntaxTree : Bool) {result : List Symbol}
    (result_ok : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 163] (recoverTypeWord syntaxTree result) :=
  qualified_type_arrow (recovery_tuple_type syntaxTree false result_ok)

theorem debug_recovery_signature (syntaxTree : Bool) (envType : Option { ty : List Symbol //
    Derives productions [.nonterminal 163] ty }) {result : List Symbol}
    (result_ok : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 78] ([.terminal 117, .terminal 76] ++
      debugTypeWord (envType.map Subtype.val) (recoveryTupleWord syntaxTree true result)) :=
  debug_signature envType (recovery_tuple_type syntaxTree true result_ok)

#print axioms debug_recovery_signature
#print axioms recover_entry_type

private theorem either_type {word : List Symbol}
    (arg : Derives productions [.nonterminal 172] word) :
    Derives productions [.nonterminal 163]
      ([.terminal 122, .terminal 122] ++ word) := by
  have head := oneRule (id := 390) (by rfl) qualifiedTypeAtom
  have eitherError := applyRule (id := 392) (by rfl)
    (beside head (oneRule (id := 394) (by rfl) qualifiedTypeAtom))
  have applied := applyRule (id := 392) (by rfl)
    (beside eitherError (oneRule (id := 394) (by rfl) arg))
  have base {xs} (app : Derives productions [.nonterminal 169] xs) :=
    oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) app)
  have rhs := oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl) (base applied))
  simpa [List.append_assoc] using rhs

private theorem entry_arrow {word : List Symbol}
    (arg : Derives productions [.nonterminal 172] word) :
    Derives productions [.nonterminal 163]
      ([.terminal 122, .terminal 83, .terminal 122, .terminal 122] ++ word) :=
  qualified_type_arrow (either_type arg)

def debugResultWord (syntaxTree : Bool) (result : List Symbol) :=
  let value := if syntaxTree then [.terminal 122] else [.terminal 107] ++ result ++ [.terminal 108]
  [.terminal 107, .terminal 122, .terminal 122] ++ value ++ [.terminal 114, .terminal 122, .terminal 108]

theorem debug_value_signature (syntaxTree : Bool) (envType : Option { ty : List Symbol //
    Derives productions [.nonterminal 163] ty }) {result : List Symbol}
    (valid : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 78] ([.terminal 117, .terminal 76] ++
      debugTypeWord (envType.map Subtype.val) (debugResultWord syntaxTree result)) := by
  have value : Derives productions [.nonterminal 172] (if syntaxTree then [.terminal 122]
      else [.terminal 107] ++ result ++ [.terminal 108]) := by
    cases syntaxTree
    · simpa [List.append_assoc] using applyRule (id := 412) (by rfl) (beside (.refl [.terminal 107])
        (beside (oneRule (id := 374) (by rfl) valid) (.refl [.terminal 108])))
    · exact qualifiedTypeAtom
  have ctype {w} (atom : Derives productions [.nonterminal 172] w) :=
    oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl)
      (oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) (oneRule (id := 390) (by rfl) atom))))
  have first := oneRule (id := 374) (by rfl) (either_type value)
  have stats := oneRule (id := 433) (by rfl) (oneRule (id := 374) (by rfl) (ctype qualifiedTypeAtom))
  have pair := applyRule (id := 407) (by rfl) (beside (.refl [.terminal 107])
    (beside first (beside (.refl [.terminal 114]) (beside stats (.refl [.terminal 108])))))
  apply debug_signature
  simpa [debugResultWord, List.append_assoc] using ctype pair

#print axioms debug_value_signature

inductive DebugEntryKind where
  | value | syntaxTree | recoverValue | recoverSyntax

def DebugEntryKind.body (kind : DebugEntryKind) (env syntaxMode noRecord : Bool)
    (close : List Symbol) : List Symbol :=
  match kind with
  | .value => if syntaxMode then debugValueLetWord env noRecord close else debugCallWord env false noRecord
  | .syntaxTree => debugSyntaxLetWord env noRecord close
  | .recoverValue => debugRecoverLetWord env syntaxMode noRecord close
  | .recoverSyntax => debugCallWord env true noRecord

def DebugEntryKind.resultType (kind : DebugEntryKind) (result : List Symbol) :=
  match kind with
  | .value => debugResultWord false result
  | .syntaxTree => debugResultWord true result
  | .recoverValue => recoveryTupleWord false true result
  | .recoverSyntax => recoveryTupleWord true true result

theorem debug_pair_valid (kind : DebugEntryKind) (env : Option { ty : List Symbol //
    Derives productions [.nonterminal 163] ty }) (syntaxMode noRecord : Bool)
    {close result : List Symbol} (hc : Derives productions [.nonterminal 320] close)
    (hr : Derives productions [.nonterminal 163] result) :
    ∀ item ∈ generatedPair (debugTypeWord (env.map Subtype.val) (kind.resultType result))
      (List.replicate (if env.isSome then 3 else 2) [.terminal 117])
      (kind.body env.isSome syntaxMode noRecord close), Derives productions [.nonterminal 78] item := by
  intro item member
  simp only [generatedPair, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · cases kind with
    | value => exact debug_value_signature false env hr
    | syntaxTree => exact debug_value_signature true env hr
    | recoverValue => exact debug_recovery_signature false env hr
    | recoverSyntax => exact debug_recovery_signature true env hr
  · have fromAtom {w} (atom : Derives productions [.nonterminal 218] w) :=
      binding_named_arguments (List.replicate (if env.isSome then 3 else 2) [.terminal 117])
        (fun _ h => List.eq_of_mem_replicate h ▸ varid_argument)
        (oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl)
          (oneRule (id := 528) (by rfl) (oneRule (id := 536) (by rfl) atom))))
    cases kind with
    | value =>
      cases syntaxMode
      · exact debug_direct_binding _ false _
      · exact fromAtom (debug_value_let _ _ hc)
    | syntaxTree => exact fromAtom (debug_syntax_let _ _ hc)
    | recoverValue => exact fromAtom (debug_recover_let _ _ _ hc)
    | recoverSyntax => exact debug_direct_binding _ true _

#print axioms debug_pair_valid

theorem entry_type {result : List Symbol}
    (valid : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 163] (entryTypeWord result) := by
  have paren := applyRule (g := productions) (id := 412) (by rfl)
    (beside (.refl [.terminal 107]) (beside (oneRule (id := 374) (by rfl) valid)
      (.refl [.terminal 108])))
  simpa [entryTypeWord, List.append_assoc] using entry_arrow paren

theorem syntax_entry_signature (envType : Option { ty : List Symbol //
    Derives productions [.nonterminal 163] ty }) :
    Derives productions [.nonterminal 78] ([.terminal 117, .terminal 76] ++
      parameterArrows (envType.toList.map Subtype.val)
        [.terminal 122, .terminal 83, .terminal 122, .terminal 122, .terminal 122]) := by
  apply signature_named_ctype
  apply parameter_arrows _ _ _ (entry_arrow qualifiedTypeAtom)
  intro ty member
  obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
  exact checked.property

#print axioms syntax_entry_signature
#print axioms entry_type

theorem generated_rule_signature (params : List (List Symbol)) (result : List Symbol)
    (valid : ∀ p ∈ params, Derives productions [.nonterminal 163] p)
    (result_ok : Derives productions [.nonterminal 163] result) :
    Derives productions [.nonterminal 78] ([.terminal 117, .terminal 76] ++ parameterArrows params result) :=
  signature_named_ctype (parameter_arrows params result valid result_ok)

structure RuleTokens where
  params : List (List Symbol)
  result : List Symbol
  arguments : List (List Symbol)
  body : List Symbol

def RuleTokens.declarations (r : RuleTokens) :=
  generatedPair (parameterArrows r.params r.result) r.arguments r.body

def RuleTokens.Valid (r : RuleTokens) : Prop :=
  (∀ p ∈ r.params, Derives productions [.nonterminal 163] p) ∧
  Derives productions [.nonterminal 163] r.result ∧
  (∀ a ∈ r.arguments, Derives productions [.nonterminal 218] a) ∧
  Derives productions [.nonterminal 211] r.body

-- ruleDecl reads the type and binding name from the same parameter list.
-- Each boolean records whether the accepted parameter name is a wildcard.
def ruleFromParams (params : List (List Symbol × Bool)) (result body : List Symbol) : RuleTokens :=
  { params := params.map Prod.fst, result := result, body := body
    arguments := params.map fun p => [if p.2 then .terminal 2 else .terminal 117] }

theorem rule_from_params_valid (params : List (List Symbol × Bool)) (result body : List Symbol)
    (types : ∀ p ∈ params, Derives productions [.nonterminal 163] p.1)
    (result_ok : Derives productions [.nonterminal 163] result)
    (body_ok : Derives productions [.nonterminal 211] body) :
    (ruleFromParams params result body).Valid := by
  refine ⟨?_, result_ok, ?_, body_ok⟩
  · intro ty member
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
    exact types p hp
  · intro arg member
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
    cases p.2
    · exact varid_argument
    · exact wildcard_argument

#print axioms rule_from_params_valid

theorem module_with_rules (name : List Symbol) (usesPegPrelude importsPrelude : Bool)
    (selected : List RenderModuleGHC.GeneratedExport) (dataTypes debugEntries : Nat)
    (userExports imports beforeRules afterRules : List (List Symbol)) (rules : List RuleTokens)
    (name_ok : Derives productions [.nonterminal 321] name)
    (user_ok : ∀ item ∈ userExports, Derives productions [.nonterminal 47] item)
    (imports_ok : ∀ item ∈ imports, Derives productions [.nonterminal 59] item)
    (other_ok : ∀ item ∈ beforeRules ++ afterRules, Derives productions [.nonterminal 78] item)
    (rules_ok : ∀ r ∈ rules, r.Valid) :
    let decls := beforeRules ++ rules.flatMap RuleTokens.declarations ++ afterRules
    Derives (layoutGrammar productions) [.nonterminal 32]
      (sourceSymbols ([.terminal 19] ++ name ++ RenderModuleGHC.exportWord
        (RenderModuleGHC.moduleExports selected dataTypes userExports debugEntries) ++
        [.terminal 25, .terminal 103] ++
        (RenderModuleGHC.generatedImports usesPegPrelude importsPrelude ++ imports).foldl
          RenderModuleGHC.semiAppend [] ++ decls.foldl RenderModuleGHC.semiAppend [])) := by
  apply RenderModuleGHC.generated_with_imports _ _ _ _ _ _ name_ok
    (RenderModuleGHC.module_exports_valid selected dataTypes userExports debugEntries user_ok) imports_ok
  intro item member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with first | rule
    · exact other_ok item (List.mem_append_left _ first)
    · obtain ⟨r, hr, hd⟩ := List.mem_flatMap.mp rule
      obtain ⟨params, result, args, body⟩ := rules_ok r hr
      simp only [RuleTokens.declarations, generatedPair, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact generated_rule_signature _ _ params result
      · exact binding_named_arguments _ args body
  · exact other_ok item (List.mem_append_right _ last)

#print axioms module_with_rules
#print axioms generated_rule_signature
#print axioms generated_pair_varid_arguments
#print axioms signature
#print axioms binding
#print axioms name_with_arguments
#print axioms wildcard_argument
#print axioms binding_named_arguments
#print axioms declarations_named
#print axioms generated_pair

end PegHs.RenderDeclarationsGHC
