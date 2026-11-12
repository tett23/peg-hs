import Whitespace

namespace PegHs.AssembleValidationHelpers

open PegVerification (ghcIsSpace)

def stripSpace (xs : List Char) : List Char :=
  ((xs.dropWhile ghcIsSpace).reverse.dropWhile ghcIsSpace).reverse

def finish (cur : List Char) : List String :=
  let s := String.ofList (stripSpace cur)
  if s.isEmpty then [] else [s]

-- Haskell's `splitExports` with locations erased. The Int nesting depth in
-- Haskell is represented by mathematical Int; see the proof boundary.
def splitGo : List Char → Int → List Char → List String → List String
  | [], _, cur, acc => acc ++ finish cur
  | c :: cs, depth, cur, acc =>
    if c == ',' && depth == 0 then
      splitGo cs depth [] (acc ++ finish cur)
    else if c == ' ' && cur.isEmpty then
      splitGo cs depth cur acc
    else
      let next := if c == '(' || c == '[' then depth + 1
        else if c == ')' || c == ']' then depth - 1 else depth
      splitGo cs next (cur ++ [c]) acc

def splitExports (s : String) : List String := splitGo s.toList 0 [] []

theorem finish_length_le_one (cur : List Char) : (finish cur).length ≤ 1 := by
  dsimp [finish]
  split <;> simp

theorem splitGo_length_bound (xs : List Char) (depth : Int) (cur : List Char)
    (acc : List String) :
    (splitGo xs depth cur acc).length ≤ acc.length + xs.length + 1 := by
  induction xs generalizing depth cur acc with
  | nil =>
    simp only [splitGo, List.length_nil, List.length_append]
    have h := finish_length_le_one cur
    omega
  | cons c cs ih =>
    unfold splitGo
    split
    · have h := ih depth [] (acc ++ finish cur)
      have hf := finish_length_le_one cur
      simp only [List.length_append, List.length_cons] at h ⊢
      omega
    · split
      · have h := ih depth cur acc
        simp only [List.length_cons] at h ⊢
        omega
      · have h := ih (if c == '(' || c == '[' then depth + 1 else
          if c == ')' || c == ']' then depth - 1 else depth) (cur ++ [c]) acc
        simp only [List.length_cons] at h ⊢
        omega

theorem splitExports_length_bound (s : String) :
    (splitExports s).length ≤ s.toList.length + 1 := by
  simpa [splitExports] using splitGo_length_bound s.toList 0 [] []

theorem splitExports_empty : splitExports "" = [] := by rfl
example : splitExports "A,B" = ["A", "B"] := by rfl
example : splitExports " A , B " = ["A", "B"] := by rfl
example : splitExports "A(B,C), D" = ["A(B,C)", "D"] := by rfl

def hexValue (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else none

def simpleEscape : Char → Option Char
  | 'n' => some '\n'
  | 't' => some '\t'
  | 'r' => some '\r'
  | '\\' => some '\\'
  | '\'' => some '\''
  | '"' => some '"'
  | '[' => some '['
  | ']' => some ']'
  | '-' => some '-'
  | _ => none

inductive DecodeState where
  | plain (value : List Char)
  | escaped (value : List Char)
  | brace (value : List Char)
  | hex (value : List Char) (digits number : Nat)
  | done (value tail : List Char)
  | failed (message : String)

def decodeStep (state : DecodeState) (c : Char) : DecodeState :=
  match state with
  | .plain value =>
    if c == '"' then .done value []
    else if c == '\\' then .escaped value
    else .plain (value ++ [c])
  | .escaped value =>
    if c == 'u' then .brace value
    else match simpleEscape c with
      | some decoded => .plain (value ++ [decoded])
      | none => .failed ("unknown escape \\" ++ String.singleton c)
  | .brace value =>
    if c == '{' then .hex value 0 0 else .failed "expected '{'"
  | .hex value digits number =>
    match hexValue c with
    | some digit => .hex value (digits + 1) (number * 16 + digit)
    | none =>
      if c != '}' then .failed "expected '}'"
      else if digits == 0 || number > 0x10FFFF then .failed "invalid \\u escape"
      else
        let scalar := if 0xD800 ≤ number && number ≤ 0xDFFF then 0xFFFD else number
        .plain (value ++ [Char.ofNat scalar])
  | .done value tail => .done value (tail ++ [c])
  | .failed message => .failed message

def decodeString (input : List Char) : Except String (List Char × List Char) :=
  match input.foldl decodeStep (.plain []) with
  | .done value tail => .ok (value, tail)
  | .failed message => .error message
  | .brace _ => .error "expected '{'"
  | .hex _ _ _ => .error "expected '}'"
  | .plain _ | .escaped _ => .error "unterminated literal"

def formError (directive : String) : String :=
  "%" ++ directive ++ if directive == "expect" then
    " expects a rule name and a string" else " expects a label and a string"

def stringArg (validIdent : String → Bool) (directive arg : String) :
    Except String String :=
  let chars := arg.toList
  let name := chars.takeWhile (fun c => !ghcIsSpace c)
  let rest := chars.drop name.length
  let quoted := rest.dropWhile ghcIsSpace
  if !validIdent (String.ofList name) then .error (formError directive)
  else match quoted with
    | '"' :: body =>
      match decodeString body with
      | .error e => .error e
      | .ok (value, after) =>
        if !(stripSpace after).isEmpty then .error (formError directive)
        else if value.isEmpty then .error
          (if directive == "expect" then "the description is empty" else "the message is empty")
        else if value.any (fun c => c.toNat < 32 || c.toNat == 127) then .error
          (if directive == "expect" then "the description contains a control character"
           else "the message contains a control character")
        else .ok (String.ofList name)
    | _ => .error (formError directive)

theorem decodeString_total (input : List Char) :
    (∃ value tail, decodeString input = .ok (value, tail)) ∨
      (∃ msg, decodeString input = .error msg) := by
  cases h : decodeString input with
  | ok pair => exact .inl ⟨pair.1, pair.2, by cases pair; rfl⟩
  | error msg => exact .inr ⟨msg, rfl⟩

example : stringArg (· == "S") "expect" "S \"hello\"" = .ok "S" := by rfl
example : stringArg (· == "S") "expect" "S \"\"" =
    .error "the description is empty" := by rfl
example : stringArg (· == "S") "expect" "S \"a\\n\"" =
    .error "the description contains a control character" := by rfl
example : stringArg (· == "S") "expect" "S \"\\u{41}\"" = .ok "S" := by rfl

#print axioms PegHs.AssembleValidationHelpers.decodeString_total
#print axioms PegHs.AssembleValidationHelpers.splitExports_length_bound

end PegHs.AssembleValidationHelpers
