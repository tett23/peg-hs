import GHCGrammar
import RenderModuleGHC

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

#print axioms generated_pair_varid_arguments
#print axioms signature
#print axioms binding
#print axioms name_with_arguments
#print axioms binding_named_arguments
#print axioms declarations_named
#print axioms generated_pair

end PegHs.RenderDeclarationsGHC
