import Header
import RenderExpression
import RenderModuleGHC

namespace PegHs.RenderModuleNames

open Peg.Verification PegHs.CFG PegHs.GHCGrammar PegHs.RenderModuleGHC

-- These parameters are the GHC lexer categories after adjustChar, rather
-- than Lean's ASCII-only Char.isAlpha and Char.isUpper.
def ghcVarId (small tail : Char → Bool) (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: cs => small c && cs.all tail

def ghcConId (large tail : Char → Bool) (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: cs => large c && cs.all tail

-- Peg.Grammar.Types.generatedTypeName capitalizes the first character when
-- its uppercase mapping is uppercase, and otherwise prefixes the entire name.
def generatedTypeName (toUpper : Char → Char) (upper : Char → Bool) (name : List Char) : String :=
  match name with
  | [] => "Rule'"
  | c :: cs =>
    if upper (toUpper c) then String.ofList (toUpper c :: cs)
    else "Rule'" ++ String.ofList (c :: cs)

theorem generated_type_name_conid (toUpper : Char → Char) (upper large tail : Char → Bool)
    (upper_ok : ∀ c, upper c = true → large c = true)
    (fallback : ghcConId large tail "Rule'" = true)
    (name : List Char) (chars : name.all tail = true) :
    ghcConId large tail (generatedTypeName toUpper upper name) = true := by
  cases name with
  | nil => exact fallback
  | cons c cs =>
    simp only [generatedTypeName]
    split
    next h =>
      simp_all [ghcConId, upper_ok _ h]
    next =>
      change (large 'R' && ['u', 'l', 'e', '\''].all tail) = true at fallback
      simpa [ghcConId, String.toList_append, List.all_append, Bool.and_assoc] using
        (show ((large 'R' && ['u', 'l', 'e', '\''].all tail) && (c :: cs).all tail) = true by
          rw [fallback, chars]; decide)

-- Scan the large idchar* pattern from the current cursor.
def scanConId (large tail : Char → Bool) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if large c then some (c :: cs.takeWhile tail, cs.dropWhile tail) else none

theorem scan_conid_boundary (large tail : Char → Bool) (name : String)
    (valid : ghcConId large tail name = true) (sep : Char) (rest : List Char)
    (boundary : tail sep = false) :
    scanConId large tail (name.toList ++ sep :: rest) = some (name.toList, sep :: rest) := by
  unfold ghcConId at valid
  cases h : name.toList with
  | nil => simp [h] at valid
  | cons c cs =>
    simp [h] at valid
    obtain ⟨first, allTail⟩ := valid
    have span (xs : List Char) (ok : ∀ x ∈ xs, tail x = true) :
        (xs ++ sep :: rest).takeWhile tail = xs ∧
        (xs ++ sep :: rest).dropWhile tail = sep :: rest := by
      induction xs with
      | nil => simp [boundary]
      | cons x xs ih =>
        have next := ih (fun y hy => ok y (by simp [hy]))
        simp [ok x (by simp), next.1, next.2]
    obtain ⟨take, drop⟩ := span cs allTail
    simp [scanConId, first, take, drop]

#print axioms scan_conid_boundary
#print axioms generated_type_name_conid

-- Classify an isolated qualified variable, in Lexer.x rule order. The
-- module part is already separated from the final identifier.
inductive QualifiedVariableToken where
  | qvarid | qualifiedDo | qualifiedMdo
  deriving DecidableEq

def qualifiedVariableToken (validModule : String → Bool) (small tail : Char → Bool)
    (recursiveDo : Bool) (qual name : String) : Option QualifiedVariableToken :=
  if validModule qual && ghcVarId small tail name then
    if name == "do" then some .qualifiedDo
    else if recursiveDo && name == "mdo" then some .qualifiedMdo
    else some .qvarid
  else none

theorem invariant3_qualified_export_variable (validModule : String → Bool)
    (small tail : Char → Bool) (recursiveDo : Bool) (qual name : String)
    (module_ok : validModule qual = true) (var_ok : ghcVarId small tail name = true)
    (notDo : name ≠ "do") (notMdo : recursiveDo = true → name ≠ "mdo") :
    qualifiedVariableToken validModule small tail recursiveDo qual name = some .qvarid ∧
      Derives productions [.nonterminal 47] [.terminal 121] := by
  refine ⟨?_, export_qvarid⟩
  cases recursiveDo <;> simp_all [qualifiedVariableToken]

#print axioms invariant3_qualified_export_variable

theorem generated_rule_var (tail : Char → Bool) (name : String)
    (prefixTail : ∀ c ∈ "eg'rule'".toList, tail c = true)
    (nameTail : ∀ c ∈ name.toList, tail c = true) :
    ghcVarId (· == 'p') tail
      (Peg.Verification.RenderExpression.renderRule name) = true := by
  have pref : ("eg'rule'".toList).all tail = true :=
    List.all_eq_true.mpr prefixTail
  have body : name.toList.all tail = true :=
    List.all_eq_true.mpr nameTail
  simp only [Peg.Verification.RenderExpression.renderRule, ghcVarId,
    String.toList_append]
  simp [body]
  simpa using pref

theorem generated_entry_var (tail : Char → Bool) (name : String)
    (prefixTail : ∀ c ∈ "arse".toList, tail c = true)
    (nameTail : ∀ c ∈ name.toList, tail c = true) :
    ghcVarId (· == 'p') tail ("parse" ++ name) = true := by
  have pref : ("arse".toList).all tail = true :=
    List.all_eq_true.mpr prefixTail
  have body : name.toList.all tail = true :=
    List.all_eq_true.mpr nameTail
  simp only [ghcVarId, String.toList_append]
  simp [body]
  simpa using pref

theorem module_parts_transfer
    (haskellUpper haskellAlphaNum ghcLarge ghcTail : Char → Bool)
    (name : String)
    (largeCompatible : ∀ c, haskellUpper c = true → ghcLarge c = true)
    (tailCompatible : ∀ c,
      identTail haskellAlphaNum c = true → ghcTail c = true)
    (valid : NameSyntax haskellUpper haskellAlphaNum name) :
    ∀ part ∈ name.splitOn ".", ghcConId ghcLarge ghcTail part = true := by
  intro part member
  have shape := valid part member
  unfold PartSyntax at shape
  cases h : part.toList with
  | nil => simp [h] at shape
  | cons first rest =>
    simp only [h] at shape
    obtain ⟨upper, tail⟩ := shape
    unfold ghcConId
    rw [h]
    exact Bool.and_eq_true_iff.mpr
      ⟨largeCompatible first upper,
        List.all_eq_true.mpr (fun c inRest => tailCompatible c (tail c inRest))⟩

-- Recognize the isolated GHC conid / qconid lexical forms. The two
-- character classes are supplied by the host Unicode classification.
def moduleNameTokens (large tail : Char → Bool) (name : String) : Option (List Symbol) :=
  let parts := name.splitOn "."
  if parts.all (ghcConId large tail) then
    some [if parts.length = 1 then .terminal 118 else .terminal 122]
  else none

theorem checked_module_name_tokens (upper alphaNum large tail : Char → Bool) (name : String)
    (first_ok : ∀ c, upper c = true → large c = true)
    (tail_ok : ∀ c, Peg.Verification.identTail alphaNum c = true → tail c = true)
    (accepted : Peg.Verification.moduleName upper alphaNum name = true) :
    ∃ word, moduleNameTokens large tail name = some word ∧
      Derives productions [.nonterminal 321] word := by
  have parts := List.all_eq_true.mp accepted
  refine ⟨[if (name.splitOn ".").length = 1 then .terminal 118 else .terminal 122], ?_, ?_⟩
  · unfold moduleNameTokens
    dsimp only
    rw [ite_eq_left ?_]
    exact List.all_eq_true.mpr (module_parts_transfer _ _ _ _ name first_ok tail_ok
      (Peg.Verification.name_sound _ _ _ accepted))
  · split
    · exact module_name_simple
    · exact module_name_qualified

#print axioms checked_module_name_tokens

-- Once the real lexer has produced CONID or QCONID, Parser.y productions
-- 836/837 discharge the modid child of the module-frame theorem.
theorem module_name_from_token (qualified : Bool) :
    Derives productions [.nonterminal 321]
      [Symbol.terminal (if qualified then 122 else 118)] := by
  cases qualified with
  | false => exact module_name_simple
  | true => exact module_name_qualified

#print axioms generated_rule_var
#print axioms generated_entry_var
#print axioms module_parts_transfer
#print axioms module_name_from_token

end PegHs.RenderModuleNames
