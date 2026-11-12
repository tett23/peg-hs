import SimpleEscapeProof
import DirectiveStringDiagnostic
import DirectiveDuplicates

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

private theorem drop_name (p : Char → Bool) (xs : List Char) :
    xs.drop (xs.takeWhile p).length = xs.dropWhile p := by
  have eq := List.drop_left (l₁ := xs.takeWhile p) (l₂ := xs.dropWhile p)
  rwa [List.takeWhile_append_dropWhile] at eq

theorem invariant2_source_string_argument (valid : String → Bool) (directive arg : String) :
    (argument valid (fun body => run (body.length + 1) .plain [] body) directive arg).map Prod.fst =
      stringArg valid directive arg := by
  simp only [argument, stringArg, invariant2_decode_string, drop_name]
  generalize String.ofList _ = name
  generalize (arg.toList.dropWhile _).dropWhile _ = quoted
  cases valid name <;> cases quoted with
  | nil => simp [Except.map]
  | cons c body =>
    by_cases q : c = '"'
    · subst c
      cases decoded : decodeString body with
      | error e => simp [decoded, Except.map, Bind.bind, Except.bind]
      | ok pair =>
        rcases pair with ⟨value, tail⟩
        cases directive == "expect" <;>
          by_cases extra : stripSpace tail = [] <;> by_cases empty : value = [] <;>
          by_cases control : ∃ c ∈ value, c.toNat < 32 ∨ c.toNat = 127 <;>
          simp [decoded, Except.map, Bind.bind, Except.bind, extra, empty, control]
    · simp [q, Except.map]


open AssembleValidation

theorem invariant2_source_string_results (items : List (α × Top)) (p : Predicates) (d : String) :
    (collect (argument p.validIdent (fun body => run (body.length + 1) .plain [] body)) d items).map
        (fun result => result.2.map Prod.fst) = stringResults p (directives (items.map Prod.snd)) d := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨loc, top⟩ := item
    cases top with
    | directive name arg =>
      cases same : name == d <;> cases empty : arg.isEmpty <;>
        simpa only [collect, directives, stringResults, args, List.map_cons, List.filterMap_cons,
          List.filter_cons, same, empty, Bool.not_true, Bool.not_false, Bool.and_false,
          Bool.and_true, Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false,
          ite_true, invariant2_source_string_argument, List.cons.injEq, true_and] using ih
    | _ => exact ih

theorem invariant2_duplicate_string_result (items : List (α × Top)) (p : Predicates)
    (directive target : String) (supported : directive = "expect" ∨ directive = "message")
    (before after : List (Except String String))
    (results :
      (collect (argument p.validIdent (fun body => run (body.length + 1) .plain [] body))
        directive items).map (fun result => result.2.map Prod.fst) =
        before ++ .ok target :: after)
    (earlier : target ∈ parsedNames before) :
    diagnostic ⟨.duplicateString, target⟩ ∈ errors (items.map Prod.snd) p := by
  rw [invariant2_source_string_results] at results
  have twice : 2 ≤ ((parsedNames (stringResults p (directives (items.map Prod.snd)) directive)).count target) := by
    rw [results]
    have positive := List.count_pos_iff.mpr earlier
    simp only [parsedNames, List.filterMap_append, List.filterMap_cons, List.count_append,
      List.count_cons_self] at positive ⊢
    omega
  have witness := (invariant2_repeated_iff target _).2 twice
  have combined : target ∈ repeated (parsedNames (stringResults p (directives (items.map Prod.snd)) "expect")) ++
      repeated (parsedNames (stringResults p (directives (items.map Prod.snd)) "message")) := by
    rcases supported with rfl | rfl
    · exact List.mem_append_left _ witness
    · exact List.mem_append_right _ witness
  have emitted : Violation.mk .duplicateString target ∈ emit .duplicateString _ :=
    List.mem_map.mpr ⟨_, combined, rfl⟩
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

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
