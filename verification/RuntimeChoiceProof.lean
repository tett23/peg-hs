import TranslatedRuntimeChoice
import EnvironmentDerivation
import MetaExecution

namespace PegHs.EnvironmentEval

theorem invariant1_runtime_choice_two (ctx : Inputs) (fuel n : Nat) (env : Env) (a b : Body) :
    translatedChoice [runFuel ctx fuel a n env, runFuel ctx fuel b n env] =
      runFuel ctx (fuel + 1) (.alt a b) n env := by
  simp only [runFuel, translatedChoice]
  cases runFuel ctx fuel a n env with
  | none => rfl
  | some r =>
    cases r <;> try rfl
    cases runFuel ctx fuel b n env with
    | none => rfl
    | some s => cases s <;> rfl

-- The empty runtime choice fails at its input position, as does !epsilon.
def choiceBody (branches : List Body) : Body :=
  branches.foldr .alt (.notAhead .eps)

theorem invariant1_runtime_choice_list {ctx : Inputs} {n : Nat} {env : Env}
    (branches : List (Body × Reply))
    (children : ∀ x ∈ branches, Derives ctx x.1 n env x.2) :
    ∃ r, translatedChoice (branches.map (fun x => some x.2)) = some r ∧
      Derives ctx (choiceBody (branches.map Prod.fst)) n env r := by
  induction branches with
  | nil => exact ⟨.fail, rfl, .notAhead .eps⟩
  | cons first branches ih =>
    obtain ⟨branch, reply⟩ := first
    have head := children (branch, reply) (by simp)
    obtain ⟨r, observed, tail⟩ := ih (fun x h => children x (List.mem_cons_of_mem _ h))
    cases reply with
    | ok pos next => exact ⟨_, rfl, .altLeft head (by simp)⟩
    | throwLabel pos name message => exact ⟨_, rfl, .altLeft head (by simp)⟩
    | fail => exact ⟨r, observed, .altRetry head tail⟩

theorem invariant1_runtime_lookahead {ctx : Inputs} {a : Body} {n : Nat} {env : Env} {r : Reply}
    (child : Derives ctx a n env r) :
    Derives ctx (.ahead a) n env (translatedAhead n env r) ∧
    Derives ctx (.notAhead a) n env (translatedNotAhead n env r) := by
  cases r <;> exact ⟨.ahead child, .notAhead child⟩

theorem invariant1_runtime_sequence (ctx : Inputs) (fuel n : Nat) (env : Env) (a b : Body) :
    translatedBind n (runFuel ctx fuel a n env) (runFuel ctx fuel b) =
      runFuel ctx (fuel + 1) (.seq a b) n env := by
  cases h : runFuel ctx fuel a n env with
  | none => simp [runFuel, translatedBind, h]
  | some r => cases r <;> simp [runFuel, translatedBind, h]

theorem invariant1_runtime_optional {ctx : Inputs} {a : Body} {n : Nat} {env : Env} {r : Reply}
    (child : Derives ctx a n env r) :
    Derives ctx (.alt a .eps) n env (translatedOptional n {env with resultDepth := 0} r) := by
  cases r with
  | ok => exact .altLeft child (by simp [translatedOptional])
  | fail => exact .altRetry child .eps
  | throwLabel => exact .altLeft child (by simp [translatedOptional])

private theorem prefix_bytes_lt (input : List Char) (i j : Nat) (hi : i ≤ input.length)
    (hj : j ≤ input.length) :
    (input.take i).utf8Encode.size < (input.take j).utf8Encode.size ↔ i < j := by
  induction input generalizing i j with
  | nil => simp_all
  | cons c cs ih =>
    have bytes (xs : List Char) : (c :: xs).utf8Encode.size = c.utf8Size + xs.utf8Encode.size := by
      rw [List.utf8Encode_cons, ByteArray.size_append]
      simp [List.utf8Encode_singleton]
    cases i <;> cases j <;> simp_all
    all_goals have positive := c.utf8Size_pos; omega

theorem invariant1_runtime_repeat_progress (input : List Char) (before after : Nat)
    (beginBound : before ≤ input.length) (endBound : after ≤ input.length) :
    Utf8Terminals.byteOffset input (input.length - before) <
      Utf8Terminals.byteOffset input (input.length - after) ↔ after < before := by
  unfold Utf8Terminals.byteOffset
  rw [prefix_bytes_lt input _ _ (Nat.sub_le ..) (Nat.sub_le ..)]
  omega

theorem invariant1_both_repeat_guards (input : List Char) (before after : Nat)
    (beginBound : before ≤ input.length) (endBound : after ≤ input.length) :
    let j := Utf8Terminals.byteOffset input (input.length - before)
    let k := Utf8Terminals.byteOffset input (input.length - after)
    (translatedManyProgress j k ↔ after < before) ∧
      (translatedSkipManyProgress j k ↔ after < before) := by
  have h := invariant1_runtime_repeat_progress input before after beginBound endBound
  exact ⟨h, h⟩

-- Each invocation evaluates the child once. Only a byte-advancing success recurs.
noncomputable def runtimeRepeat {ctx : Inputs} {a : Body}
    (step : ∀ n env, {r // Derives ctx a n env r})
    (n : Nat) (env : Env) (bound : n ≤ ctx.input.length) :
    {r // Derives ctx (.starLoop a) n env r} := by
  classical
  obtain ⟨child, derivation⟩ := step n env
  cases child with
  | fail => exact ⟨_, .loopStop derivation⟩
  | throwLabel => exact ⟨_, .loopThrow derivation⟩
  | ok rest next =>
    have le := invariant1_success_remaining_le derivation rest next rfl
    have endBound := Nat.le_trans le bound
    have guards := invariant1_both_repeat_guards ctx.input n rest bound endBound
    if advance : translatedManyProgress (Utf8Terminals.byteOffset ctx.input (ctx.input.length - n))
        (Utf8Terminals.byteOffset ctx.input (ctx.input.length - rest)) then
      have lt := guards.1.mp advance
      obtain ⟨r, tail⟩ := runtimeRepeat step rest
        {next with resultDepth := max env.resultDepth next.resultDepth} endBound
      exact ⟨r, .loopMore derivation lt tail⟩
    else
      have stop : ¬ rest < n := fun lt => advance (guards.1.mpr lt)
      have same : rest = n := by omega
      subst rest
      exact ⟨_, .loopZero derivation⟩
termination_by n

theorem invariant1_runtime_repeat {ctx : Inputs} {a : Body}
    (step : ∀ n env, {r // Derives ctx a n env r})
    (n : Nat) (env : Env) (bound : n ≤ ctx.input.length) :
    Derives ctx (.star a) n env (runtimeRepeat step n {env with resultDepth := 0} bound).val :=
  .star (runtimeRepeat step n _ bound).property

theorem invariant1_runtime_label {ctx : Inputs} {a : Body} {n : Nat} {env : Env} {r : Reply}
    (name : String) (message : Option String) (child : Derives ctx a n env r) :
    Derives ctx (.label name message a) n env (translatedLabel n name message r) := by
  cases r <;> exact .label child

theorem invariant1_runtime_capture_bytes (before captured after : List Char) :
    translatedCaptureBytes (before ++ captured ++ after).utf8Encode before.utf8Encode.size
      (before.utf8Encode.size + captured.utf8Encode.size) = captured.utf8Encode := by
  have bound : before.utf8Encode.size + captured.utf8Encode.size ≤
      (before ++ captured ++ after).utf8Encode.size := by simp [List.utf8Encode_append]
  simpa [translatedCaptureBytes, ByteArray.extract_extract, Nat.min_eq_left bound] using
    Utf8Terminals.invariant1_capture_bytes before captured after

theorem invariant1_runtime_capture_binding (mode : Bool) (before captured after : List Char)
    (site : Nat) (name : String) (inner : Env) :
    let input := before ++ captured ++ after
    ∃ bound, bindResult (MetaExecution.context mode input) site name (captured.length + after.length)
        (.ok after.length inner) = .ok after.length bound ∧
      (bound.lookup name).utf8Encode = translatedCaptureBytes input.utf8Encode
        before.utf8Encode.size (before.utf8Encode.size + captured.utf8Encode.size) := by
  dsimp only
  rw [invariant1_runtime_capture_bytes]
  have text : matchedText (before ++ captured ++ after) (captured.length + after.length)
      after.length = captured := by
    simp [matchedText, List.append_assoc]
  cases mode <;>
    refine ⟨(inner.put name captured).putDepth name inner.resultDepth, ?_, ?_⟩
  all_goals first
    | change Reply.ok _ ((inner.put name (matchedText (before ++ captured ++ after)
        (captured.length + after.length) after.length)).putDepth name inner.resultDepth) = _
      rw [text]
    | simp [Env.lookup, Env.putDepth, Env.put]

theorem invariant1_runtime_predicate (ctx : Inputs) (site n column : Nat) (env : Env)
    (test : Nat → Bool) (value : predicateTest ctx site env = some (test column)) :
    Derives ctx (.predicate site) n env (translatedPredicate test column n {env with resultDepth := 0}) := by
  cases h : test column with
  | false =>
    simpa [translatedPredicate, h] using Derives.predicateFail (n := n) (Or.inr (value.trans (congrArg some h)))
  | true =>
    simpa [translatedPredicate, h] using Derives.predicateOk (n := n) (value.trans (congrArg some h))

theorem invariant1_runtime_site_predicate (mode : Bool) (input : List Char)
    (site n column : Nat) (env : Env) {kind polarity}
    (found : (MetaExecution.context mode input).sites site = some (kind, polarity)) :
    let ctx := MetaExecution.context mode input
    let test := fun _ : Nat => SemanticPredicates.eval ctx.classes kind (ctx.predicateEnv site env) == polarity
    Derives ctx (.predicate site) n env (translatedPredicate test column n {env with resultDepth := 0}) := by
  apply invariant1_runtime_predicate
  simp [predicateTest, found]

theorem invariant1_runtime_anyChar (before : List Char) (c : Char) (after : List Char) :
    translatedAnyChar (before ++ c :: after).utf8Encode.size before.utf8Encode.size c.utf8Size =
      some (before ++ [c]).utf8Encode.size := by
  have width : (c :: after).utf8Encode.size = c.utf8Size + after.utf8Encode.size := by
    rw [List.utf8Encode_cons, ByteArray.size_append]
    simp [List.utf8Encode_singleton]
  have pos := c.utf8Size_pos
  simp [translatedAnyChar, List.utf8Encode_append, List.utf8Encode_singleton, width, Nat.ne_of_gt pos]

theorem invariant1_runtime_anyChar_eof (input : List Char) (width : Nat) :
    translatedAnyChar input.utf8Encode.size input.utf8Encode.size width = none := by
  simp [translatedAnyChar]

end PegHs.EnvironmentEval
