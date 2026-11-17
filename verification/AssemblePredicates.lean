import AssembleChars
import AssembleValidationHelpers
import GrammarReservedWords

-- Translations of the predicates that Peg.Grammar.Assemble.assemble applies
-- to directive arguments and binders. Each definition names its Haskell
-- source. check-assemble-predicates.sh pins those Haskell spans and runs
-- AssemblePredicatesProbe, which evaluates both sides on the same inputs.
--
-- Premises recorded here:
-- * Character classes are GHC 9.10.3's Data.Char tables (AssembleChars).
-- * Text operations (T.uncons, T.all, T.words, T.splitOn ".",
--   T.breakOnEnd ".", T.isInfixOf, T.dropEnd 1, T.takeWhileEnd) are
--   modelled on List Char; the probe compares the results.
namespace PegHs.AssembleValidation

open AssembleChars

-- isIdentStart c = isAlpha c || c == '_'
def identStart (c : Char) : Bool := isAlpha c || c == '_'
-- isIdentChar c = isAlphaNum c || c == '_' || c == '\''
def identChar (c : Char) : Bool := isAlphaNum c || c == '_' || c == '\''

-- isValidIdent
def validIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identStart c && cs.all identChar

-- T.words: maximal runs of characters that are not Data.Char.isSpace.
def wordsGo (current : List Char) : List Char → List String
  | [] => if current.isEmpty then [] else [String.ofList current.reverse]
  | c :: cs =>
    if PegVerification.ghcIsSpace c then
      (if current.isEmpty then [] else [String.ofList current.reverse]) ++ wordsGo [] cs
    else wordsGo (c :: current) cs

def words (s : String) : List String := wordsGo [] s.toList

-- T.splitOn with a one-character separator: always at least one part.
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c == sep then [] :: splitOnChar sep cs
    else match splitOnChar sep cs with
      | [] => [[c]]
      | part :: parts => (c :: part) :: parts

-- isClassName; isModuleName = isClassName.
def classPart : List Char → Bool
  | [] => false
  | c :: cs => isUpper c && cs.all identChar

def validClass (s : String) : Bool :=
  !s.isEmpty && (splitOnChar '.' s.toList).all classPart

def validModule (s : String) : Bool := validClass s

-- startsWithModifier
def startsWithModifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => isModifier c

-- extensionEnabled in assemble: LANGUAGE flags in source order.
def extensionFlag (aliases : List String) (option : String) : Option Bool :=
  if option ∈ aliases then some true
  else if option ∈ aliases.map ("No" ++ ·) then some false else none

def extensionEnabled (aliases options : List String) (initial := false) : Bool :=
  options.foldl (fun enabled option => (extensionFlag aliases option).getD enabled) initial

def recursiveDoEnabled (options : List String) : Bool :=
  extensionEnabled ["RecursiveDo", "DoRec"] options

def arrowsEnabled (options : List String) : Bool :=
  extensionEnabled ["Arrows"] options

-- extensionKeyword recursiveDoEnabled arrowsEnabled
def extensionKeyword (options : List String) (name : String) : Bool :=
  (recursiveDoEnabled options && ["mdo", "rec"].contains name) ||
  (arrowsEnabled options && ["proc", "rec"].contains name)

-- binderKeyword in assemble.
def binderKeyword (options : List String) (name : String) : Bool :=
  (name != "_" && grammarReservedWords.contains name) || extensionKeyword options name

-- binderError name is Just _ exactly when this holds.
def binderError (options : List String) (name : String) : Bool :=
  binderKeyword options name || startsWithModifier name

-- isExportItem and its local functions.
def symbolChars : List Char := "!#$%&*+./<=>?@\\^|-~:".toList

def isOperator (options : List String) (op : String) : Bool :=
  !op.isEmpty && op.toList.all symbolChars.contains &&
  !["..", "::", "=", "\\", "|", "<-", "->", "=>"].contains op &&
  (!arrowsEnabled options || !["-<", ">-", "-<<", ">>-"].contains op)

-- tokens: spaces and tabs separate, parentheses and commas are tokens of
-- their own, and every other run is one token.
def flush (current : List Char) : List String :=
  if current.isEmpty then [] else [String.ofList current.reverse]

def tokensGo (current : List Char) : List Char → List String
  | [] => flush current
  | c :: cs =>
    if c == ' ' || c == '\t' then flush current ++ tokensGo [] cs
    else if "(),".toList.contains c then flush current ++ String.singleton c :: tokensGo [] cs
    else tokensGo (c :: current) cs

def tokens (s : List Char) : List String := tokensGo [] s

def exportIdent (name : String) : Bool := validIdent name && !startsWithModifier name

def unqualifiedName (options : List String) (name : String) : Bool :=
  exportIdent name && !grammarReservedWords.contains name && !extensionKeyword options name

-- T.breakOnEnd "." n: everything up to the last dot, and the rest.
def breakOnEndDot (n : List Char) : List Char × List Char :=
  ((n.reverse.dropWhile (· != '.')).reverse, (n.reverse.takeWhile (· != '.')).reverse)

def isQualifiedName (options : List String) (n : String) : Bool :=
  match breakOnEndDot n.toList with
  | ([], name) => unqualifiedName options (String.ofList name)
  | (qual, name) =>
    validModule (String.ofList qual.dropLast) && exportIdent (String.ofList name) &&
      String.ofList name != "do" && (!recursiveDoEnabled options || String.ofList name != "mdo")

def isTypeName (options : List String) (n : String) : Bool :=
  isQualifiedName options n && (match (breakOnEndDot n.toList).2 with
    | [] => false
    | c :: _ => isUpper c)

def exportMemberName (options : List String) : List String → Option (List String)
  | n :: rest => if unqualifiedName options n then some rest else none
  | [] => none

def exportMember (options : List String) (ts : List String) : Option (List String) :=
  match ts with
  | "(" :: op :: ")" :: rest => if isOperator options op then some rest else exportMemberName options ts
  | _ => exportMemberName options ts

theorem exportMemberName_shorter (options ts rest : List String)
    (h : exportMemberName options ts = some rest) : rest.length < ts.length := by
  cases ts with
  | nil => simp [exportMemberName] at h
  | cons n tail =>
    simp only [exportMemberName] at h
    split at h
    · cases h; simp
    · cases h

theorem exportMember_shorter (options ts rest : List String) (h : exportMember options ts = some rest) :
    rest.length < ts.length := by
  unfold exportMember at h
  split at h
  · split at h
    · cases h; simp only [List.length_cons]; omega
    · exact exportMemberName_shorter _ _ _ h
  · exact exportMemberName_shorter _ _ _ h

set_option linter.unusedVariables false in
def exportNames (options : List String) (ts : List String) : Option (List String) :=
  match h : exportMember options ts with
  | none => none
  | some rest =>
    match rest with
    | "," :: more => exportNames options more
    | ")" :: more => some more
    | _ => none
termination_by ts.length
decreasing_by
  have := exportMember_shorter options ts _ h
  simp at this ⊢
  omega

def exportPlainSingle (options : List String) : List String → Option (List String)
  | n :: rest => if isQualifiedName options n then some rest else none
  | [] => none

def exportPlainList (options : List String) (ts : List String) : Option (List String) :=
  match ts with
  | n :: "(" :: rest => if isTypeName options n then exportNames options rest else exportPlainSingle options ts
  | _ => exportPlainSingle options ts

def exportPlainNamed (options : List String) (ts : List String) : Option (List String) :=
  match ts with
  | n :: "(" :: ".." :: ")" :: rest => if isTypeName options n then some rest else exportPlainList options ts
  | _ => exportPlainList options ts

def exportPlain (options : List String) (ts : List String) : Option (List String) :=
  match ts with
  | "(" :: op :: ")" :: rest => if isOperator options op then some rest else exportPlainNamed options ts
  | _ => exportPlainNamed options ts

def exportItem (options : List String) (ts : List String) : Option (List String) :=
  match ts with
  | "module" :: m :: rest => if validModule m then some rest else exportPlain options ts
  | kw :: rest => if ["type", "pattern"].contains kw then exportPlain options rest else exportPlain options ts
  | [] => exportPlain options ts

-- T.isInfixOf on code points.
def isInfixOf (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => needle.isPrefixOf (c :: cs) || isInfixOf needle cs

def validExport (options : List String) (s : String) : Bool :=
  !(["--", "{-", "-}"].any fun bad => isInfixOf bad.toList s.toList) &&
    (exportItem options (tokens s.toList)).any List.isEmpty

-- Flags act from left to right. Reading them from the right gives an
-- independent specification: the last mention of any alias wins.
theorem invariant2_extension_last_setting (aliases options : List String) (initial : Bool) :
    extensionEnabled aliases options initial =
      (options.reverse.findSome? (extensionFlag aliases)).getD initial := by
  induction options generalizing initial with
  | nil => rfl
  | cons option rest ih =>
    change extensionEnabled aliases rest ((extensionFlag aliases option).getD initial) = _
    rw [ih, List.reverse_cons, List.findSome?_append]
    cases rest.reverse.findSome? (extensionFlag aliases) <;>
      cases h : extensionFlag aliases option <;> simp [h]

example : extensionEnabled ["RecursiveDo", "DoRec"] ["DoRec", "NoRecursiveDo"] = false := rfl
example : extensionEnabled ["RecursiveDo", "DoRec"] ["NoDoRec", "Arrows", "RecursiveDo"] = true := rfl

theorem invariant2_forall_reserved (options : List String) :
    binderKeyword options "forall" = true := by
  have member : "forall" ∈ grammarReservedWords := by decide
  simp [binderKeyword, member]

theorem invariant2_wildcard_not_reserved (options : List String) :
    binderKeyword options "_" = false := by
  simp [binderKeyword, extensionKeyword]

theorem invariant3_unqualified_export_iff (options : List String) (name : String) :
    unqualifiedName options name = true ↔
      exportIdent name = true ∧ name ∉ grammarReservedWords ∧
      (name ∈ ["mdo", "rec"] → recursiveDoEnabled options = false) ∧
      (name ∈ ["proc", "rec"] → arrowsEnabled options = false) := by
  simp [unqualifiedName, extensionKeyword]
  grind

#print axioms invariant2_extension_last_setting
#print axioms invariant2_forall_reserved
#print axioms invariant3_unqualified_export_iff

end PegHs.AssembleValidation
