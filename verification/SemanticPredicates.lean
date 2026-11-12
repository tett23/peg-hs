import EscapePredicates
import ParameterPredicates

namespace PegHs.SemanticPredicates
open EscapePredicates ParameterPredicates

structure Classes where
  space : Char → Bool
  alpha : Char → Bool
  alnum : Char → Bool

structure Env where
  captured : List Char
  depth : Nat
  deriving Repr

inductive Kind where
  | space | identStart | identChar | hsIdent | typeText | argument
  | paramForm | paramType | depth | unicodeEscape | classItem
  deriving DecidableEq, Repr

private theorem dropWhile_bound (p : Char → Bool) (xs : List Char) :
    (xs.dropWhile p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons c cs ih => by_cases h : p c = true <;> simp [List.dropWhile, h] <;> omega

-- Haskell's tokens uses span isHexDigit, drops the following delimiter, and
-- recovers with U+FFFD for a code point beyond the representable range.
def decodeTokens : List Char → List Token
  | '\\' :: 'u' :: '{' :: rest =>
    let digits := rest.takeWhile (fun c => (digit c).isSome)
    let suffix := (rest.dropWhile (fun c => (digit c).isSome)).drop 1
    let n := (value 0 digits).getD 0
    (if n ≤ 0x10ffff then n else 0xfffd, false) :: decodeTokens suffix
  | '\\' :: c :: rest =>
    let decoded := match c with
      | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | _ => c
    (decoded.toNat, false) :: decodeTokens rest
  | c :: rest => (c.toNat, c == '-') :: decodeTokens rest
  | [] => []
termination_by xs => xs.length
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := dropWhile_bound (fun c => (digit c).isSome) rest; omega

def eval (cls : Classes) (kind : Kind) (env : Env) : Bool :=
  let c := env.captured.headD ' '
  let identChar := cls.alnum c || c == '_' || c == '\''
  match kind with
  | .space => cls.space c
  | .identStart => cls.alpha c || c == '_'
  | .identChar => identChar
  | .hsIdent => identChar && c != '\''
  | .typeText => !(stripEnd cls.space env.captured).isEmpty
  | .argument => !(strip cls.space env.captured).isEmpty
  | .paramForm => classify cls.space cls.alpha cls.alnum env.captured != .formError
  | .paramType => match classify cls.space cls.alpha cls.alnum env.captured with
    | .ok .. => true | _ => false
  | .depth => env.depth < 256
  | .unicodeEscape => validHex env.captured
  | .classItem => nonEmptyRanges (decodeTokens env.captured)

def spelling : Kind → String
  | .space => "isSpace (firstChar c)"
  | .identStart => "isIdentStart (firstChar c)"
  | .identChar => "isIdentChar (firstChar c)"
  | .hsIdent => "isIdentChar (firstChar c) && firstChar c /= '\\''"
  | .typeText => "not (T.null (T.stripEnd ty))"
  | .argument => "not (T.null (T.strip c))"
  | .paramForm => "paramError l c /= Just paramFormMessage"
  | .paramType => "paramError l c == Nothing"
  | .depth => "d < maxDepth"
  | .unicodeEscape => "validHex h"
  | .classItem => "nonEmptyRanges s"

def kinds : List Kind := [.space, .identStart, .identChar, .hsIdent, .typeText, .argument, .paramForm, .paramType, .depth, .unicodeEscape, .classItem]

def kindOf (source : String) := kinds.find? (fun k => spelling k == source)

def Holds (cls : Classes) (env : Env) : Kind → Prop
  | .space => cls.space (env.captured.headD ' ') = true
  | .identStart => cls.alpha (env.captured.headD ' ') = true ∨ env.captured.headD ' ' = '_'
  | .identChar => cls.alnum (env.captured.headD ' ') = true ∨ env.captured.headD ' ' = '_' ∨ env.captured.headD ' ' = '\''
  | .hsIdent => (cls.alnum (env.captured.headD ' ') = true ∨ env.captured.headD ' ' = '_') ∧ env.captured.headD ' ' ≠ '\''
  | .typeText | .argument => ∃ c ∈ env.captured, cls.space c = false
  | .paramForm => ∃ a b, FirstSeparator env.captured a b ∧ identifier cls.alpha cls.alnum (strip cls.space a) = true
  | .paramType => ∃ a b, FirstSeparator env.captured a b ∧ identifier cls.alpha cls.alnum (strip cls.space a) = true ∧ strip cls.space b ≠ []
  | .depth => env.depth < 256
  | .unicodeEscape => env.captured ≠ [] ∧ ∃ n, HexValue env.captured n ∧ n ≤ 0x10ffff
  | .classItem => ∀ r ∈ ranges (decodeTokens env.captured), ∃ c, r.1 ≤ c ∧ c ≤ r.2

theorem invariant1_eval_iff (cls : Classes) (k : Kind) (e : Env) :
    eval cls k e = true ↔ Holds cls e k := by
  cases k with
  | space => rfl
  | identStart => simp [eval, Holds]
  | identChar => simp [eval, Holds, or_assoc]
  | hsIdent => simp [eval, Holds]; grind
  | depth => simp [eval, Holds]
  | typeText => simpa [eval, Holds] using invariant1_typeText cls.space e.captured
  | argument => simpa [eval, Holds] using invariant1_argumentChunk cls.space e.captured
  | classItem => exact invariant1_nonEmptyRanges
  | unicodeEscape => exact invariant1_validHex
  | paramForm => simp [eval, Holds, invariant1_parameter_form_error]
  | paramType =>
    change (match classify cls.space cls.alpha cls.alnum e.captured with
      | .ok .. => true | _ => false) = true ↔ _
    constructor
    · intro h
      split at h
      next n t ht =>
        obtain ⟨a,b,sep,rfl,rfl,valid,nonempty⟩ := invariant1_parameter_accepts.mp ht
        exact ⟨a,b,sep,valid,nonempty⟩
      next => contradiction
    · rintro ⟨a,b,sep,valid,nonempty⟩
      have accepted := (invariant1_parameter_accepts (space := cls.space)
        (alpha := cls.alpha) (alnum := cls.alnum)).mpr ⟨a,b,sep,rfl,rfl,valid,nonempty⟩
      rw [accepted]

example : kindOf "isIdentChar (firstChar c) && firstChar c /= '\\''" = some .hsIdent := by decide
example : kindOf "unrecognizedPredicate x" = none := by decide
example : decodeTokens "\\u{D800}-\\u{10ffff}".toList =
    [(0xd800, false), (45, true), (0x10ffff, false)] := by cbv
example : decodeTokens "\\-".toList = [(45, false)] := by cbv

end PegHs.SemanticPredicates
