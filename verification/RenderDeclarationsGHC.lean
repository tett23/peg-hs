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

-- fst (PegRt.runParser config (newStore [env]) rule input), optionally
-- wrapped in PegPrelude.fmap PegPrelude.fst for lossless syntax mode.
def entryBodyWord (hasEnv syntaxMode : Bool) : List Symbol :=
  let store := [.terminal 117] ++ (if hasEnv then [.terminal 117] else [])
  let run := [.terminal 121, .terminal 117, .terminal 107] ++ store ++
    [.terminal 108, .terminal 117, .terminal 117]
  let project := [.terminal 121, .terminal 107] ++ run ++ [.terminal 108]
  if syntaxMode then [.terminal 121, .terminal 121, .terminal 107] ++ project ++ [.terminal 108]
  else project

open RenderExpressionGHC in
theorem entry_body (hasEnv syntaxMode : Bool) :
    Derives productions [.nonterminal 211] (entryBodyWord hasEnv syntaxMode) := by
  have expr {w} (f : Derives productions [.nonterminal 217] w) :=
    oneRule (id := 520) (by rfl) (oneRule (id := 523) (by rfl) (oneRule (id := 528) (by rfl) f))
  have parens {w} (f : Derives productions [.nonterminal 217] w) :=
    parenthesized (oneRule (id := 596) (by rfl) (expr f))
  have store : Derives productions [.nonterminal 217]
      ([.terminal 117] ++ (if hasEnv then [.terminal 117] else [])) := by
    have name := oneRule (id := 536) (by rfl) varid_argument
    cases hasEnv
    · exact name
    · exact application name varid_argument
  have run := application (application (application (application qualified_function varid_argument)
    (parens store)) varid_argument) varid_argument
  have project := application qualified_function (parens run)
  cases syntaxMode
  · simpa [entryBodyWord, List.append_assoc] using expr project
  · have fstArg := oneRule (id := 551) (by rfl) (oneRule (id := 554) (by rfl)
      (oneRule (id := 555) (by rfl) (oneRule (id := 769) (by rfl)
        (applyRule (g := productions) (id := 774) (by rfl) (.refl _)))))
    simpa [entryBodyWord, List.append_assoc] using
      expr (application (application qualified_function fstArg) (parens project))

#print axioms entry_body

-- PegRt.Text -> PegPrelude.Either PegRt.ParseError (resultType)
def entryTypeWord (result : List Symbol) : List Symbol :=
  [.terminal 122, .terminal 83, .terminal 122, .terminal 122, .terminal 107] ++
    result ++ [.terminal 108]

private theorem qualifiedTypeAtom : Derives productions [.nonterminal 172] [.terminal 122] :=
  oneRule (id := 400) (by rfl) (oneRule (id := 718) (by rfl)
    (oneRule (id := 723) (by rfl) (applyRule (id := 731) (by rfl) (.refl _))))

private theorem entry_arrow {word : List Symbol}
    (arg : Derives productions [.nonterminal 172] word) :
    Derives productions [.nonterminal 163]
      ([.terminal 122, .terminal 83, .terminal 122, .terminal 122] ++ word) := by
  have head := oneRule (id := 390) (by rfl) qualifiedTypeAtom
  have eitherError := applyRule (id := 392) (by rfl)
    (beside head (oneRule (id := 394) (by rfl) qualifiedTypeAtom))
  have applied := applyRule (id := 392) (by rfl)
    (beside eitherError (oneRule (id := 394) (by rfl) arg))
  have base {xs} (app : Derives productions [.nonterminal 169] xs) :=
    oneRule (id := 386) (by rfl) (oneRule (id := 387) (by rfl) app)
  have rhs := oneRule (id := 379) (by rfl) (oneRule (id := 381) (by rfl) (base applied))
  simpa [List.append_assoc] using
    oneRule (id := 379) (by rfl) (applyRule (id := 382) (by rfl)
      (beside (base head) (beside (.refl [.terminal 83]) rhs)))

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
