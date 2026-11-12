import SimpleEscapeProof
import DirectiveStringDiagnostic

namespace PegHs.TranslatedEscapes
open AssembleValidationHelpers

inductive Mode where | plain | escaped | brace

abbrev Result := Except String (List Char × List Char)
abbrev Continue := List Char → List Char → Result

def branch (next : Mode → Continue) : Mode → Continue
  | .plain => plain (next .plain) (next .escaped)
  | .escaped => escape (next .plain) (next .brace)
  | .brace => unicode (next .plain)

def model (mode : Mode) (acc input : List Char) : Result :=
  let state := match mode with
    | .plain => DecodeState.plain acc.reverse
    | .escaped => DecodeState.escaped acc.reverse
    | .brace => DecodeState.brace acc.reverse
  finishDecode (input.foldl decodeStep state)

theorem branch_model (mode : Mode) (acc input : List Char) :
    branch model mode acc input = model mode acc input := by
  cases mode with
  | plain => exact invariant2_plain_branch acc input
  | escaped => exact invariant2_escape_branch acc input
  | brace => exact invariant2_unicode_branch acc input

private theorem branch_smaller (next other : Mode → Continue) (mode : Mode)
    (acc input : List Char) (agree : ∀ m a xs, xs.length < input.length →
      next m a xs = other m a xs) : branch next mode acc input = branch other mode acc input := by
  cases input with
  | nil => cases mode <;> rfl
  | cons c rest =>
    have tail (m : Mode) (a : List Char) := agree m a rest (by simp)
    cases mode with
    | plain =>
      by_cases quote : c = '"' <;> by_cases slash : c = '\\' <;> simp [branch, plain, quote, slash, tail]
    | escaped =>
      by_cases u : c = 'u'
      · simp [branch, escape, u, tail]
      · cases h : table.lookup c <;> simp [branch, escape, h, tail]
    | brace =>
      by_cases brace : c = '{'
      · subst c
        simp only [branch, unicode]
        cases h : rest.dropWhile (fun d => (hexDigit d).isSome) with
        | nil => rfl
        | cons d ds =>
          by_cases close : d = '}'
          · subst d
            have bound := congrArg List.length (List.takeWhile_append_dropWhile (p := fun x => (hexDigit x).isSome) (l := rest))
            rw [h] at bound
            have shorter : ds.length < ('{' :: rest).length := by simp_all; omega
            simp [agree _ _ ds shorter]
          · simp [close]
      · simp [branch, unicode, brace]

def run : Nat → Mode → Continue
  | 0 => fun _ _ _ => .error "decoder fuel exhausted"
  | fuel + 1 => branch (run fuel)

theorem invariant2_decode_run (fuel : Nat) (mode : Mode) (acc input : List Char)
    (enough : input.length < fuel) : run fuel mode acc input = model mode acc input := by
  induction fuel generalizing mode acc input with
  | zero => omega
  | succ fuel ih =>
    rw [run, ← branch_model]
    apply branch_smaller
    intro m a xs smaller
    exact ih m a xs (by omega)

theorem invariant2_decode_string (input : List Char) :
    run (input.length + 1) .plain [] input = decodeString input :=
  invariant2_decode_run _ _ _ _ (by omega)

open AssembleValidation

theorem invariant2_decoder_public_rejection (tops : List Top) (p : Predicates)
    (directive : String) (name gap body : List Char) (msg : String)
    (supported : directive = "expect" ∨ directive = "message")
    (member : Top.directive directive (String.ofList (name ++ gap ++ '"' :: body)) ∈ tops)
    (valid : p.validIdent (String.ofList name) = true)
    (noSpace : ∀ c ∈ name, PegVerification.ghcIsSpace c = false)
    (separator : gap ≠ []) (spaces : ∀ c ∈ gap, PegVerification.ghcIsSpace c = true)
    (failed : run (body.length + 1) .plain [] body = .error msg)
    (resolve expand check : Unit → Except (List String) Unit)
    (notes : Unit → List String → List String)
    (strip : Option (Unit → Unit)) (warningFor : Unit → Unit → List String)
    (generate : Unit → Except (List String) String) :
    ∃ ds, Pipeline.visible (Pipeline.pipeline (parseGrammar (.ok tops) p)
        resolve expand check notes strip warningFor generate) = .error ds ∧
      diagnostic ⟨.invalidString, msg⟩ ∈ ds := by
  rw [invariant2_decode_string] at failed
  have reported := invariant2_directive_decoder_diagnostic tops p directive name gap body msg
    supported member valid noSpace separator spaces failed
  cases he : errors tops p with
  | nil => simp [he] at reported
  | cons d ds =>
    have rejected := public_assemble_failure tops p (d :: ds) (by simp only [assemble, he])
      resolve expand check notes strip warningFor generate
    exact ⟨_, rejected.1, he ▸ reported⟩

#print axioms invariant2_decoder_public_rejection
#print axioms invariant2_decode_string
end PegHs.TranslatedEscapes
