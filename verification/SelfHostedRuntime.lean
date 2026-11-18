import RuntimeCoreProof
import TotalFile
import FileTops

/-!
The strict metagrammar parser run on the translated runtime (premise R7 of
verification/README.md).

`exec` is the parser that the extracted rule bodies (ExtractSelfHostedFile.hs,
`invariant1_strict_rule_table` of SelfHostedFileProof.lean) denote on the
runtime that ExtractRuntimeCore.hs translates from
packages/peg-runtime/src/Peg/Runtime/Internal.hs. Each body constructor runs
the combinator that the extractor reads for it in the generated
SelfHosted.hs: `bindP` for a `do` sequence, `choice` for alternatives,
`lit`, `cls` and `anyChar` for terminals, `andP` and `notP` for lookahead,
`labeled` and `labeledMessage` for `^label`, `predicate` for a semantic
predicate, and `nomemo` for a rule call. A repetition is the loop of
`manyGo` and `skipManyGo`, with the environment of the model carried from one
iteration to the next. The value of a parser is the model's remaining input
and environment, which stand for the Haskell values (premise M2 and the
hooks of MetaExecution.lean).

`predicate` is not in the translation; it is restated here from the source
(check-runtime-core.sh compares the source lines). The generated predicates
ignore the column (`\_col ->`), which ExtractSelfHostedFile.hs checks.

Theorems:
- `invariant1_exec_agrees`: for every fuel, `exec` returns, from every
  world, the result that `runFuel` of the model returns: the same
  remaining input and environment at the byte offset of that position,
  the same label and message, or no result.
- `invariant1_runtime_file`: the File program, run from the context and
  world that `runParser defaultConfig` builds, returns a result that agrees
  with `FileResult`.
- `invariant1_runtimeStart_eq`: the start result of that run is the
  `startTops` of the recognizer's reply, so `PublicGeneration.parse` can be
  defined on the runtime run.

Premises, besides R1 to R6 of RuntimeCore.lean and RuntimeCoreProof.lean:
- Strict mode (`Strict`): recovery and counting are off, as in
  `defaultConfig`.
- The literal terminals of the context are not empty
  (`invariant1_meta_literals_nonempty` shows it for the metagrammar).

What ties `exec` to the generated SelfHosted.hs:
- A call in the generated code is `memo` or `memoArg`, and `exec` calls
  `nomemo`. SelfHostedMemo.lean runs the same bodies with the tables and
  proves that the result is the same (the cache invariant over the whole
  store, with ScopedEnv.lean for the key of a call without arguments).
- `getOffset`, `spanFrom`, `withCol`, `capture`, `optional` (here an
  alternative with the empty parser), the one-alternative `choice` around a
  rule body and a `choice` of three or more alternatives (here nested
  two-way choices): RuntimeForms.lean proves that they do not change the
  result.
- Premise R7 of verification/README.md, not proved here: the generated code
  computes Haskell values; `exec` computes the model's remaining input and
  environment. In a repetition, `many` drops the bindings of an iteration and
  `exec` passes the environment on.
-/

set_option linter.unusedSimpArgs false
namespace PegHs.SelfHostedRuntime
open RuntimeCore EnvironmentEval ConcreteTerminal MetaExecution

attribute [local simp] st_bind st_pure st_map

section Runs
variable {ρ σ α β : Type}

/-- From every world, the parser returns `o` (`none`: it does not return). -/
def Runs (p : P ρ σ α) (c : Ctx ρ) (i : Nat) (o : Option (Res α)) : Prop :=
  ∀ w : World σ, (p c i w).map Prod.fst = o

theorem runs_pure (x : α) (c : Ctx ρ) (i : Nat) : Runs (pureP x : P ρ σ α) c i (some (Ok i x)) :=
  fun _ => rfl

theorem runs_fail (c : Ctx ρ) (i : Nat) : Runs (fun _ _ => pure Fail : P ρ σ α) c i (some Fail) :=
  fun _ => rfl

def Res.map (f : α → β) : Res α → Res β
  | Ok j x => Ok j (f x)
  | Fail => Fail
  | Throw t l m => Throw t l m

/-- What `bindP p k` returns when `p` returns `o`. -/
def thenRes (o : Option (Res α)) (next : Nat → α → Option (Res β)) : Option (Res β) :=
  match o with
  | none => none
  | some (Ok j x) => next j x
  | some Fail => some Fail
  | some (Throw t l m) => some (Throw t l m)

theorem runs_bind {p : P ρ σ α} {k : α → P ρ σ β} {c : Ctx ρ} {i : Nat} {o : Option (Res α)}
    (hp : Runs p c i o) (next : Nat → α → Option (Res β))
    (hk : ∀ j x, o = some (Ok j x) → Runs (k x) c j (next j x)) :
    Runs (bindP p k) c i (thenRes o next) := by
  intro w
  have h := hp w
  cases hr : p c i w with
  | none => rw [hr] at h; subst h; simp [bindP, st_bind, hr, thenRes]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    rw [hr] at h; simp only [Option.map_some] at h; subst h
    cases r with
    | Ok j x => simpa [bindP, st_bind, hr, thenRes, unP] using hk j x rfl w1
    | Fail => simp [bindP, st_bind, hr, thenRes, st_pure, failed]
    | Throw t l m => simp [bindP, st_bind, hr, thenRes, st_pure, failed]

theorem runs_bind_ok {p : P ρ σ α} {k : α → P ρ σ β} {c : Ctx ρ} {i j : Nat} {x : α}
    {o : Option (Res β)} (hp : Runs p c i (some (Ok j x))) (hk : Runs (k x) c j o) :
    Runs (bindP p k) c i o :=
  runs_bind hp (fun _ _ => o) (fun j' x' h => by cases h; exact hk)

theorem runs_bind_bad {p : P ρ σ α} {k : α → P ρ σ β} {c : Ctx ρ} {i : Nat} {r : Res α}
    (hp : Runs p c i (some r)) (bad : ∀ j x, r ≠ Ok j x) :
    Runs (bindP p k) c i (some (failed r)) := by
  cases r with
  | Ok j x => exact absurd rfl (bad j x)
  | Fail => exact runs_bind (k := k) hp (fun _ _ => none) (fun j x e => by cases e)
  | Throw t l m => exact runs_bind (k := k) hp (fun _ _ => none) (fun j x e => by cases e)

theorem runs_bind_none {p : P ρ σ α} {k : α → P ρ σ β} {c : Ctx ρ} {i : Nat}
    (hp : Runs p c i none) : Runs (bindP p k) c i none :=
  runs_bind hp (fun _ _ => none) (fun j x e => by cases e)

theorem runs_predicate (b : Bool) (c : Ctx ρ) (i : Nat) :
    Runs (fun _ i => pure (if b then Ok i () else Fail) : P ρ σ Unit) c i
      (some (if b then Ok i () else Fail)) := fun _ => rfl

theorem runs_fmap {p : P ρ σ α} {c : Ctx ρ} {i : Nat} {o : Option (Res α)} (f : α → β)
    (hp : Runs p c i o) : Runs (fmapP f p) c i (o.map (Res.map f)) := by
  intro w
  have h := hp w
  cases hr : p c i w with
  | none => rw [hr] at h; subst h; simp [fmapP, st_bind, hr]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    rw [hr] at h; simp only [Option.map_some] at h; subst h
    cases r <;> simp [fmapP, st_bind, hr, st_pure, failed, Res.map]

/-- What `choice [p, q]` returns. -/
def orRes (o : Option (Res α)) (alternative : Option (Res α)) : Option (Res α) :=
  match o with
  | some Fail => alternative
  | other => other

theorem runs_choice {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) {p q : P ρ σ α} {i : Nat} {o o2 : Option (Res α)}
    (hp : Runs p c i o) (hq : o = some Fail → Runs q c i o2) :
    Runs (choice [p, q]) c i (orRes o o2) := by
  intro w
  have h := hp w
  cases hr : p c i w with
  | none =>
    rw [hr] at h; subst h
    simp [choice, choice.go, st_bind, saveErrors_strict strict, hr, unP, orRes]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    rw [hr] at h; simp only [Option.map_some] at h; subst h
    cases r with
    | Ok j x => simp [choice, choice.go, st_bind, saveErrors_strict strict, hr, unP, st_pure, orRes]
    | Throw t l m =>
      simp [choice, choice.go, st_bind, saveErrors_strict strict, hr, unP, st_pure, orRes]
    | Fail =>
      have h2 := hq rfl w1
      cases hq2 : q c i w1 with
      | none =>
        rw [hq2] at h2; subst h2
        simp [choice, choice.go, st_bind, saveErrors_strict strict, hr, hq2, unP, orRes]
      | some qr =>
        obtain ⟨r2, w2⟩ := qr
        rw [hq2] at h2; simp only [Option.map_some] at h2; subst h2
        cases r2 <;> simp [choice, choice.go, st_bind, saveErrors_strict strict, hr, hq2, unP,
          st_pure, orRes]

/-- What `andP p` (`positive`) and `notP p` return at `i`. -/
def lookRes (positive : Bool) (i : Nat) (o : Option (Res α)) : Option (Res Unit) :=
  o.map fun
    | Ok _ _ => if positive then Ok i () else Fail
    | _ => if positive then Fail else Ok i ()

theorem runs_andP {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) {p : P ρ σ α} {i : Nat} {o : Option (Res α)} (hp : Runs p c i o) :
    Runs (andP p) c i (lookRes true i o) := by
  intro w
  have h := hp w
  cases hr : p c i w with
  | none => rw [hr] at h; subst h; simp [andP, st_bind, saveErrors_strict strict, hr, unP, lookRes]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    rw [hr] at h; simp only [Option.map_some] at h; subst h
    cases r <;> simp [andP, st_bind, saveErrors_strict strict, hr, unP, st_pure, lookRes]

theorem runs_notP {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) {p : P ρ σ α} {i : Nat} {o : Option (Res α)} (hp : Runs p c i o) :
    Runs (notP p) c i (lookRes false i o) := by
  intro w
  have h := hp { w with fail := w.fail }
  cases hr : p c i w with
  | none =>
    simp only [hr] at h; subst h
    simp [notP, st_bind, saveErrors_strict strict, hr, unP, lookRes, readSTRef, ctxFail, failRef]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    simp only [hr, Option.map_some] at h; subst h
    cases r <;> simp [notP, st_bind, saveErrors_strict strict, hr, unP, st_pure, lookRes, readSTRef,
      writeSTRef, ctxFail, failRef]

/-- What `labeledWith` without recovery returns at `i`. -/
def labelRes (i : Nat) (name : String) (msg : Option Text) (o : Option (Res α)) : Option (Res α) :=
  o.map fun
    | Fail => Throw i name msg
    | other => other

theorem runs_label {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) {p : P ρ σ α} {i : Nat} {o : Option (Res α)}
    (name : String) (msg : Option Text) (hp : Runs p c i o) :
    Runs (labeledWith plainRecovery name msg none p) c i (labelRes i name msg o) := by
  intro w
  have h := hp { w with fail := NoFailure }
  cases hr : p c i { w with fail := NoFailure } with
  | none =>
    rw [hr] at h; subst h
    simp [labeledWith, st_bind, saveErrors_strict strict, hr, unP, labelRes, readSTRef, writeSTRef,
      ctxFail, failRef]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    rw [hr] at h; simp only [Option.map_some] at h; subst h
    cases r <;> simp [labeledWith, st_bind, saveErrors_strict strict, hr, unP, st_pure, labelRes,
      readSTRef, writeSTRef, ctxFail, failRef, labeledWith.l, T.pack]

theorem runs_nomemo {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false) {body : P ρ σ α} {i : Nat} {o : Option (Res α)}
    (count : cfgCount (ctxConfig c) = false) (name : String) (hp : Runs body c i o) :
    Runs (nomemo name body) c i o := by
  intro w
  have h := hp { w with fail := NoFailure, deps := IS.empty }
  cases hr : body c i { w with fail := NoFailure, deps := IS.empty } with
  | none =>
    rw [hr] at h; subst h
    simp [nomemo, evalBody, countEval, count, when, st_bind, st_map, saveErrors_strict strict, hr,
      unP, readSTRef, writeSTRef, ctxFail, failRef, ctxDeps, depsRef, st_pure]
  | some pr =>
    obtain ⟨r, w1⟩ := pr
    rw [hr] at h; simp only [Option.map_some] at h; subst h
    cases r <;> simp [nomemo, evalBody, countEval, count, when, st_bind, st_map,
      saveErrors_strict strict, hr, unP, readSTRef, writeSTRef, ctxFail, failRef, ctxDeps, depsRef,
      st_pure, newErrors, restoreErrors, maybe]

end Runs

/-! ## Positions -/

/-- The byte offset of the position with `rem` characters left. -/
noncomputable def off (input : List Char) (rem : Nat) : Nat :=
  Utf8Terminals.byteOffset input (input.length - rem)

theorem byteOffset_succ (x : Char) (xs : List Char) (a : Nat) :
    Utf8Terminals.byteOffset (x :: xs) (a + 1) = x.utf8Size + Utf8Terminals.byteOffset xs a := by
  unfold Utf8Terminals.byteOffset
  rw [List.take_succ_cons, List.utf8Encode_cons, ByteArray.size_append]
  simp [List.utf8Encode_singleton]

theorem byteOffset_zero (xs : List Char) : Utf8Terminals.byteOffset xs 0 = 0 := by
  simp [Utf8Terminals.byteOffset]

theorem byteOffset_strict : ∀ (input : List Char) (a b : Nat), a < b → b ≤ input.length →
    Utf8Terminals.byteOffset input a < Utf8Terminals.byteOffset input b
  | [], _, _, lt, le => by simp at le; omega
  | x :: xs, a, b, lt, le => by
    cases b with
    | zero => omega
    | succ b =>
      rw [byteOffset_succ]
      cases a with
      | zero => rw [byteOffset_zero]; have := x.utf8Size_pos; omega
      | succ a =>
        rw [byteOffset_succ]
        have := byteOffset_strict xs a b (by omega) (by simp at le; omega)
        omega

theorem off_lt_iff {input : List Char} {rest rem : Nat} (hrest : rest ≤ rem) (hrem : rem ≤ input.length) :
    off input rem < off input rest ↔ rest < rem := by
  unfold off
  constructor
  · intro h
    apply Nat.lt_of_le_of_ne hrest
    intro eq; subst eq; omega
  · intro h
    exact byteOffset_strict input _ _ (by omega) (by omega)

/-! ## Terminals -/

section Terminals
variable {ρ σ : Type}

def termP : Terminal → P ρ σ Unit
  | .lit chars => lit (String.ofList chars) (String.ofList chars)
  | .cls ranges => cls ranges ""
  | .any => anyChar

def termWidth : Terminal → Nat
  | .lit chars => chars.length
  | _ => 1

theorem matchLiteral_some : ∀ {chars xs tail : List Char},
    matchLiteral chars xs = some tail → xs = chars ++ tail
  | [], xs, tail, h => by simp [matchLiteral] at h; simp [h]
  | _ :: _, [], _, h => by simp [matchLiteral] at h
  | c :: cs, x :: xs, tail, h => by
    simp only [matchLiteral] at h
    split at h
    · rename_i eq
      have := matchLiteral_some h
      simp at eq
      simp [eq, this]
    · cases h

theorem matchLiteral_append : ∀ (chars tail : List Char), matchLiteral chars (chars ++ tail) = some tail
  | [], tail => rfl
  | c :: cs, tail => by simp [matchLiteral, matchLiteral_append cs tail]

theorem split_input (input : List Char) {rem : Nat} (hrem : rem ≤ input.length) :
    (input.drop (input.length - rem)).length = rem ∧
      input = input.take (input.length - rem) ++ input.drop (input.length - rem) ∧
      off input rem = (input.take (input.length - rem)).utf8Encode.size := by
  refine ⟨by simp; omega, (List.take_append_drop _ _).symm, rfl⟩

theorem oracle_eq (t : Terminal) (input : List Char) {rem : Nat} (hrem : rem ≤ input.length) :
    terminalOracle t input rem =
      (matchTerm t (input.drop (input.length - rem))).map List.length := by
  have tailLe : ∀ tail, matchTerm t (input.drop (input.length - rem)) = some tail →
      tail.length ≤ input.length := by
    intro tail h
    cases t with
    | lit chars =>
      have := matchLiteral_some h
      have := congrArg List.length this
      simp at this; omega
    | cls ranges =>
      cases hd : input.drop (input.length - rem) with
      | nil => rw [hd] at h; simp [matchTerm] at h
      | cons x xs =>
        rw [hd] at h; simp only [matchTerm] at h
        split at h
        · cases h
          have := congrArg List.length hd
          simp at this; omega
        · cases h
    | any =>
      cases hd : input.drop (input.length - rem) with
      | nil => rw [hd] at h; simp [matchTerm] at h
      | cons x xs =>
        rw [hd] at h; simp only [matchTerm] at h
        cases h
        have := congrArg List.length hd
        simp at this; omega
  unfold terminalOracle matchAt
  simp only [hrem, ↓reduceIte, Nat.sub_le]
  cases h : matchTerm t (input.drop (input.length - rem)) with
  | none => simp
  | some tail => simp; have := tailLe tail h; omega

theorem cls_eof (ranges : List (Char × Char)) (orig : String) {c : Ctx ρ} {input : List Char}
    (h : OnInput c input) (w : World σ) :
    ∃ w', cls ranges orig c input.utf8Encode.size w = some (Fail, w') := by
  have eq : ctxLen c = input.utf8Encode.size := by rw [h.2, h.1, length_ofList]
  simp only [cls, eq, Nat.lt_irrefl, ↓reduceIte]
  obtain ⟨f, run, -⟩ := failAt_run c _ (ExpectedClass (T.pack orig)) w
  exact ⟨_, run⟩

/-- The runtime terminal agrees with the model's terminal oracle. -/
theorem invariant1_terminal_runs (t : Terminal) (nonempty : t ≠ .lit []) {c : Ctx ρ}
    {input : List Char} (on : OnInput c input) {rem : Nat} (hrem : rem ≤ input.length) :
    (terminalOracle t input rem = none → Runs (termP t : P ρ σ Unit) c (off input rem) (some Fail)) ∧
    (∀ rest, terminalOracle t input rem = some rest →
      rest < rem ∧ rest = rem - termWidth t ∧
        Runs (termP t : P ρ σ Unit) c (off input rem) (some (Ok (off input rest) ()))) := by
  obtain ⟨len, split, at_⟩ := split_input input hrem
  rw [oracle_eq t input hrem, at_]
  generalize hpre : input.take (input.length - rem) = pre at split
  generalize hsuf : input.drop (input.length - rem) = suf at split len
  have on' : OnInput c (pre ++ suf) := split ▸ on
  have offRest : ∀ chars tail, suf = chars ++ tail →
      off input tail.length = pre.utf8Encode.size + chars.utf8Encode.size := by
    intro chars tail hs
    have whole : input = pre ++ chars ++ tail := by rw [split, hs, List.append_assoc]
    have lenEq : input.length - tail.length = pre.length + chars.length := by
      rw [whole]; simp; omega
    unfold off; rw [lenEq, whole]
    exact Utf8Terminals.invariant1_byte_offset pre chars tail
  cases t with
  | lit chars =>
    have ne : chars ≠ [] := fun e => nonempty (by rw [e])
    have charsPos : 0 < chars.length := List.length_pos_iff.mpr ne
    have lemma := invariant1_translated_lit (σ := σ) (String.ofList chars) (String.ofList chars) on'
    simp only [String.toList_ofList] at lemma
    constructor
    · intro none'
      simp only [Option.map_eq_none_iff] at none'
      intro w
      obtain ⟨f, run, -⟩ := (lemma w).2 none'
      simp [termP, run]
    · intro rest some'
      obtain ⟨tail, m, rfl⟩ := Option.map_eq_some_iff.mp some'
      have hs := matchLiteral_some m
      have lens : suf.length = chars.length + tail.length := by rw [hs]; simp
      refine ⟨by omega, by simp [termWidth]; omega, fun w => ?_⟩
      simp only [termP]
      rw [(lemma w).1 ⟨tail, m⟩, offRest chars tail hs]
      rfl
  | cls ranges =>
    cases suf with
    | nil =>
      have whole : input = pre := by simpa using split
      refine ⟨fun _ w => ?_, fun rest h => by simp [matchTerm] at h⟩
      have on2 : OnInput c pre := by simpa using on'
      obtain ⟨w', run⟩ := cls_eof (σ := σ) ranges "" on2 w
      simp [termP, run]
    | cons ch after =>
      have lemma := invariant1_translated_cls (σ := σ) ranges "" on'
      constructor
      · intro none' w
        simp only [Option.map_eq_none_iff] at none'
        obtain ⟨f, run, -⟩ := (lemma w).2 none'
        simp [termP, run]
      · intro rest some'
        obtain ⟨tail, m, rfl⟩ := Option.map_eq_some_iff.mp some'
        have m' := m
        simp only [matchTerm] at m'
        split at m'
        · cases m'
          simp at len
          refine ⟨by omega, by simp [termWidth]; omega, fun w => ?_⟩
          simp only [termP]
          rw [(lemma w).1 m, offRest [ch] after (by simp)]
          simp [List.utf8Encode_append]
        · cases m'
  | any =>
    cases suf with
    | nil =>
      refine ⟨fun _ w => ?_, fun rest h => by simp [matchTerm] at h⟩
      have on2 : OnInput c pre := by simpa using on'
      obtain ⟨f, run, -⟩ := invariant1_translated_anyChar_eof (σ := σ) on2 w
      simp [termP, run]
    | cons ch after =>
      refine ⟨fun h => by simp [matchTerm] at h, fun rest some' => ?_⟩
      obtain ⟨tail, m, rfl⟩ := Option.map_eq_some_iff.mp some'
      simp only [matchTerm] at m
      cases m
      simp at len
      refine ⟨by omega, by simp [termWidth]; omega, fun w => ?_⟩
      simp only [termP]
      rw [invariant1_translated_anyChar on' w, offRest [ch] after (by simp)]
      simp [List.utf8Encode_append]

end Terminals

/-! ## The runtime parser of a body -/

section Exec
variable {ρ σ : Type}

/-- `predicate` of Peg.Runtime.Internal for a predicate that ignores the
column: `predicate f = P $ \c i -> pure (if f (colAt c i) then Ok i () else Fail)`. -/
def predicate (b : Bool) : P ρ σ Unit := fun _ i => pure (if b then Ok i () else Fail)

/-- `labeled` and `labeledMessage` without a recovery parser. -/
def labelP {α : Type} (name : String) : Option String → P ρ σ α → P ρ σ α
  | some msg => labeledMessage name msg none
  | none => labeled name none

theorem labelP_eq {α : Type} (name : String) (msg : Option String) (p : P ρ σ α) :
    labelP name msg p = labeledWith plainRecovery name (msg.map T.pack) none p := by
  cases msg <;> rfl

/-- The runtime parser of a body. The value is the remaining input and the
environment of the model. -/
noncomputable def exec (I : Inputs) : Nat → Body → Nat → Env → P ρ σ (Nat × Env)
  | 0, _, _, _ => fun _ _ _ => none
  | fuel + 1, body, rem, env =>
    match body with
    | .eps => pureP (rem, { env with resultDepth := 0 })
    | .terminal site =>
      match I.terms site with
      | none => fun _ _ => pure Fail
      | some t => bindP (termP t) fun _ => pureP (rem - termWidth t, { env with resultDepth := 0 })
    | .predicate site =>
      match I.sites site with
      | none => fun _ _ => pure Fail
      | some (kind, polarity) =>
        bindP (predicate (SemanticPredicates.eval I.classes kind (I.predicateEnv site env) == polarity))
          fun _ => pureP (rem, { env with resultDepth := 0 })
    | .call site rule =>
      match I.hooks.enterCall site env with
      | none => fun _ _ => pure Fail
      | some callee =>
        fmapP (fun r => (r.1, I.hooks.leaveCall site env r.2))
          (nomemo "rule" (exec I fuel (I.rules rule) rem callee))
    | .seq a b => bindP (exec I fuel a rem env) fun r => exec I fuel b r.1 r.2
    | .alt a b => choice [exec I fuel a rem env, exec I fuel b rem env]
    | .ahead a => fmapP (fun _ => (rem, env)) (andP (exec I fuel a rem env))
    | .notAhead a => fmapP (fun _ => (rem, env)) (notP (exec I fuel a rem env))
    | .star a => exec I fuel (.starLoop a) rem { env with resultDepth := 0 }
    | .starLoop a => fun c i => do
        let saved ← saveErrors c
        unP (exec I fuel a rem env) c i >>= fun
          | Ok k r =>
            if k > i then exec I fuel (.starLoop a) r.1
                { r.2 with resultDepth := max env.resultDepth r.2.resultDepth } c k
            else restoreErrors c saved >>= fun _ => pure (Ok i (rem, env))
          | Throw t l m => restoreErrors c saved >>= fun _ => pure (Throw t l m)
          | Fail => restoreErrors c saved >>= fun _ => pure (Ok i (rem, env))
    | .label name msg a => labelP name msg (exec I fuel a rem env)
    | .capture a => exec I fuel a rem env
    | .bind site name a => bindP (exec I fuel a rem env) fun r =>
        match I.hooks.bindValue site name (matchedText I.input rem r.1) r.2 with
        | some bound => pureP (r.1, bound)
        | none => fun _ _ => pure Fail
    | .action site a => bindP (exec I fuel a rem env) fun r =>
        match I.actions site >>= DepthAction.eval r.2 with
        | some depth => pureP (r.1, { r.2 with resultDepth := depth })
        | none => fun _ _ => pure Fail

/-- A runtime result agrees with a reply of the model. -/
def Agrees (input : List Char) : Option (Res (Nat × Env)) → Option Reply → Prop
  | none, none => True
  | some (Ok j (rest, env)), some (.ok rest' env') => rest = rest' ∧ env = env' ∧ j = off input rest
  | some Fail, some .fail => True
  | some (Throw t l m), some (.throwLabel pos name msg) => t = off input pos ∧ l = name ∧ m = msg
  | _, _ => False

theorem agrees_ok {input : List Char} {o : Option (Res (Nat × Env))} {rest : Nat} {env : Env}
    (h : Agrees input o (some (.ok rest env))) : o = some (Ok (off input rest) (rest, env)) := by
  match o, h with
  | some (Ok j (r, e)), ⟨h1, h2, h3⟩ => subst h1 h2 h3; rfl

theorem agrees_fail {input : List Char} {o : Option (Res (Nat × Env))}
    (h : Agrees input o (some .fail)) : o = some Fail := by
  match o, h with
  | some Fail, _ => rfl

theorem agrees_throw {input : List Char} {o : Option (Res (Nat × Env))} {pos : Nat} {name : String}
    {msg : Option String} (h : Agrees input o (some (.throwLabel pos name msg))) :
    o = some (Throw (off input pos) name msg) := by
  match o, h with
  | some (Throw t l m), ⟨h1, h2, h3⟩ => subst h1 h2 h3; rfl

theorem agrees_none {input : List Char} {o : Option (Res (Nat × Env))}
    (h : Agrees input o none) : o = none := by
  match o, h with
  | none, _ => rfl

theorem rest_le {I : Inputs} {fuel : Nat} {body : Body} {rem : Nat} {env : Env} {rest : Nat} {next : Env}
    (h : runFuel I fuel body rem env = some (.ok rest next)) : rest ≤ rem :=
  invariant1_success_remaining_le (invariant1_runFuel_sound h) rest next rfl

theorem pack_map (msg : Option String) : msg.map T.pack = msg := by cases msg <;> rfl

theorem runs_predicateP (b : Bool) (c : Ctx ρ) (i : Nat) :
    Runs (predicate b : P ρ σ Unit) c i (some (if b then Ok i () else Fail)) := fun _ => rfl

/-- Invariant 1 on the runtime: for every fuel, the runtime parser of a body
returns, from every world, the result that the model returns. -/
theorem invariant1_exec_agrees (I : Inputs) {c : Ctx ρ} (on : OnInput c I.input) (strict : Strict c)
    (literals : ∀ site, I.terms site ≠ some (.lit [])) :
    ∀ fuel body rem env, rem ≤ I.input.length →
      ∃ o, Runs (exec I fuel body rem env : P ρ σ (Nat × Env)) c (off I.input rem) o ∧
        Agrees I.input o (runFuel I fuel body rem env) := by
  intro fuel
  induction fuel with
  | zero => intro body rem env _; exact ⟨none, fun _ => rfl, trivial⟩
  | succ fuel ih =>
    intro body rem env hrem
    cases body with
    | eps =>
      exact ⟨_, runs_pure _ c _, by simp only [runFuel]; exact ⟨rfl, rfl, rfl⟩⟩
    | terminal site =>
      cases ht : I.terms site with
      | none =>
        refine ⟨some Fail, ?_, ?_⟩
        · simp only [exec, ht]; exact runs_fail c _
        · simp only [runFuel, ht]; exact True.intro
      | some t =>
        have T := invariant1_terminal_runs (ρ := ρ) (σ := σ) t (fun e => literals site (e ▸ ht)) on hrem
        cases ho : terminalOracle t I.input rem with
        | none =>
          refine ⟨some Fail, ?_, ?_⟩
          · simp only [exec, ht]
            exact runs_bind_bad (T.1 ho) (fun j x e => by cases e)
          · simp only [runFuel, ht, ho]; exact True.intro
        | some rest =>
          obtain ⟨lt, width, run⟩ := T.2 rest ho
          refine ⟨some (Ok (off I.input rest) (rem - termWidth t, { env with resultDepth := 0 })), ?_, ?_⟩
          · simp only [exec, ht]
            exact runs_bind_ok run (runs_pure _ c _)
          · simp only [runFuel, ht, ho, lt, ↓reduceIte]
            exact ⟨width.symm, rfl, by rw [width]⟩
    | predicate site =>
      cases hs : I.sites site with
      | none =>
        refine ⟨some Fail, ?_, ?_⟩
        · simp only [exec, hs]; exact runs_fail c _
        · simp only [runFuel, hs]; exact True.intro
      | some pair =>
        obtain ⟨kind, polarity⟩ := pair
        have hp := runs_predicateP (ρ := ρ) (σ := σ)
          (SemanticPredicates.eval I.classes kind (I.predicateEnv site env) == polarity) c (off I.input rem)
        cases hb : (SemanticPredicates.eval I.classes kind (I.predicateEnv site env) == polarity) with
        | true =>
          rw [hb] at hp
          refine ⟨some (Ok (off I.input rem) (rem, { env with resultDepth := 0 })), ?_, ?_⟩
          · simp only [exec, hs, hb]
            exact runs_bind_ok hp (runs_pure _ c _)
          · simp only [runFuel, hs, hb, ↓reduceIte]; exact ⟨rfl, rfl, rfl⟩
        | false =>
          rw [hb] at hp
          refine ⟨some Fail, ?_, ?_⟩
          · simp only [exec, hs, hb]
            exact runs_bind_bad hp (fun j x e => by cases e)
          · simp only [runFuel, hs, hb]; exact True.intro
    | call site rule =>
      cases he : I.hooks.enterCall site env with
      | none =>
        refine ⟨some Fail, ?_, ?_⟩
        · simp only [exec, he]; exact runs_fail c _
        · simp only [runFuel, he]; exact True.intro
      | some callee =>
        obtain ⟨o, run, agree⟩ := ih (I.rules rule) rem callee hrem
        have run' := runs_fmap (fun r => (r.1, I.hooks.leaveCall site env r.2))
          (runs_nomemo strict.recover strict.count "rule" run)
        refine ⟨_, by simp only [exec, he]; exact run', ?_⟩
        simp only [runFuel, he]
        cases hr : runFuel I fuel (I.rules rule) rem callee with
        | none => rw [hr] at agree; rw [agrees_none agree]; exact True.intro
        | some reply =>
          rw [hr] at agree
          cases reply with
          | ok rest inner => rw [agrees_ok agree]; exact ⟨rfl, rfl, rfl⟩
          | fail => rw [agrees_fail agree]; exact True.intro
          | throwLabel pos name msg => rw [agrees_throw agree]; exact ⟨rfl, rfl, rfl⟩
    | seq a b =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      cases hr : runFuel I fuel a rem env with
      | none =>
        rw [hr] at agree1; rw [agrees_none agree1] at run1
        refine ⟨none, ?_, ?_⟩
        · simp only [exec]; exact runs_bind_none run1
        · simp only [runFuel, hr]; exact True.intro
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest next =>
          rw [agrees_ok agree1] at run1
          have le := rest_le hr
          obtain ⟨o2, run2, agree2⟩ := ih b rest next (by omega)
          refine ⟨o2, ?_, ?_⟩
          · simp only [exec]; exact runs_bind_ok run1 run2
          · simp only [runFuel, hr]; exact agree2
        | fail =>
          rw [agrees_fail agree1] at run1
          refine ⟨some Fail, ?_, ?_⟩
          · simp only [exec]; exact runs_bind_bad run1 (fun j x e => by cases e)
          · simp only [runFuel, hr]; exact True.intro
        | throwLabel pos name msg =>
          rw [agrees_throw agree1] at run1
          refine ⟨some (Throw (off I.input pos) name msg), ?_, ?_⟩
          · simp only [exec]; exact runs_bind_bad run1 (fun j x e => by cases e)
          · simp only [runFuel, hr]; exact ⟨rfl, rfl, rfl⟩
    | alt a b =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      obtain ⟨o2, run2, agree2⟩ := ih b rem env hrem
      refine ⟨orRes o1 o2, ?_, ?_⟩
      · simp only [exec]; exact runs_choice strict.recover run1 (fun _ => run2)
      · simp only [runFuel]
        cases hr : runFuel I fuel a rem env with
        | none => rw [hr] at agree1; rw [agrees_none agree1]; exact True.intro
        | some reply =>
          rw [hr] at agree1
          cases reply with
          | ok rest next => rw [agrees_ok agree1]; exact ⟨rfl, rfl, rfl⟩
          | fail => rw [agrees_fail agree1]; exact agree2
          | throwLabel pos name msg => rw [agrees_throw agree1]; exact ⟨rfl, rfl, rfl⟩
    | ahead a =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      refine ⟨_, by simp only [exec]; exact runs_fmap _ (runs_andP strict.recover run1), ?_⟩
      simp only [runFuel]
      cases hr : runFuel I fuel a rem env with
      | none => rw [hr] at agree1; rw [agrees_none agree1]; exact True.intro
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest next => rw [agrees_ok agree1]; exact ⟨rfl, rfl, rfl⟩
        | fail => rw [agrees_fail agree1]; exact True.intro
        | throwLabel pos name msg => rw [agrees_throw agree1]; exact True.intro
    | notAhead a =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      refine ⟨_, by simp only [exec]; exact runs_fmap _ (runs_notP strict.recover run1), ?_⟩
      simp only [runFuel]
      cases hr : runFuel I fuel a rem env with
      | none => rw [hr] at agree1; rw [agrees_none agree1]; exact True.intro
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest next => rw [agrees_ok agree1]; exact True.intro
        | fail => rw [agrees_fail agree1]; exact ⟨rfl, rfl, rfl⟩
        | throwLabel pos name msg => rw [agrees_throw agree1]; exact ⟨rfl, rfl, rfl⟩
    | star a =>
      obtain ⟨o, run, agree⟩ := ih (.starLoop a) rem { env with resultDepth := 0 } hrem
      exact ⟨o, by simp only [exec]; exact run, by simp only [runFuel]; exact agree⟩
    | starLoop a =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      cases hr : runFuel I fuel a rem env with
      | none =>
        rw [hr] at agree1; rw [agrees_none agree1] at run1
        refine ⟨none, fun w => ?_, by simp only [runFuel, hr]; exact True.intro⟩
        have h := run1 w
        cases hx : exec I fuel a rem env c (off I.input rem) w with
        | none => simp [exec, saveErrors_strict strict.recover, unP, hx]
        | some _ => rw [hx] at h; cases h
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest next =>
          rw [agrees_ok agree1] at run1
          have le := rest_le hr
          by_cases lt : rest < rem
          · obtain ⟨o2, run2, agree2⟩ := ih (.starLoop a) rest
              { next with resultDepth := max env.resultDepth next.resultDepth } (by omega)
            have gt := (off_lt_iff le hrem).mpr lt
            refine ⟨o2, fun w => ?_, by simp only [runFuel, hr, lt, ↓reduceIte]; exact agree2⟩
            have h := run1 w
            cases hx : exec I fuel a rem env c (off I.input rem) w with
            | none => rw [hx] at h; cases h
            | some pr =>
              obtain ⟨r, w1⟩ := pr
              rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
              simpa [exec, saveErrors_strict strict.recover, unP, hx, gt] using run2 w1
          · have ngt : ¬ off I.input rem < off I.input rest := fun g => lt ((off_lt_iff le hrem).mp g)
            refine ⟨some (Ok (off I.input rem) (rem, env)), fun w => ?_,
              by simp only [runFuel, hr, lt, ↓reduceIte]; exact ⟨rfl, rfl, rfl⟩⟩
            have h := run1 w
            cases hx : exec I fuel a rem env c (off I.input rem) w with
            | none => rw [hx] at h; cases h
            | some pr =>
              obtain ⟨r, w1⟩ := pr
              rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
              simp [exec, saveErrors_strict strict.recover, unP, hx, ngt]
        | fail =>
          rw [agrees_fail agree1] at run1
          refine ⟨some (Ok (off I.input rem) (rem, env)), fun w => ?_,
            by simp only [runFuel, hr]; exact ⟨rfl, rfl, rfl⟩⟩
          have h := run1 w
          cases hx : exec I fuel a rem env c (off I.input rem) w with
          | none => rw [hx] at h; cases h
          | some pr =>
            obtain ⟨r, w1⟩ := pr
            rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            simp [exec, saveErrors_strict strict.recover, unP, hx]
        | throwLabel pos name msg =>
          rw [agrees_throw agree1] at run1
          refine ⟨some (Throw (off I.input pos) name msg), fun w => ?_,
            by simp only [runFuel, hr]; exact ⟨rfl, rfl, rfl⟩⟩
          have h := run1 w
          cases hx : exec I fuel a rem env c (off I.input rem) w with
          | none => rw [hx] at h; cases h
          | some pr =>
            obtain ⟨r, w1⟩ := pr
            rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            simp [exec, saveErrors_strict strict.recover, unP, hx]
    | label name msg a =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      have run := runs_label strict.recover name (msg.map T.pack) run1
      rw [pack_map] at run
      refine ⟨_, by simp only [exec]; rw [labelP_eq, pack_map]; exact run, ?_⟩
      simp only [runFuel]
      cases hr : runFuel I fuel a rem env with
      | none => rw [hr] at agree1; rw [agrees_none agree1]; exact True.intro
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest next => rw [agrees_ok agree1]; exact ⟨rfl, rfl, rfl⟩
        | fail => rw [agrees_fail agree1]; exact ⟨rfl, rfl, rfl⟩
        | throwLabel pos name msg => rw [agrees_throw agree1]; exact ⟨rfl, rfl, rfl⟩
    | capture a =>
      obtain ⟨o, run, agree⟩ := ih a rem env hrem
      exact ⟨o, by simp only [exec]; exact run, by simp only [runFuel]; exact agree⟩
    | bind site name a =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      cases hr : runFuel I fuel a rem env with
      | none =>
        rw [hr] at agree1; rw [agrees_none agree1] at run1
        refine ⟨none, ?_, ?_⟩
        · simp only [exec]; exact runs_bind_none run1
        · simp only [runFuel, hr]; exact True.intro
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest inner =>
          rw [agrees_ok agree1] at run1
          cases hv : I.hooks.bindValue site name (matchedText I.input rem rest) inner with
          | none =>
            refine ⟨some Fail, ?_, ?_⟩
            · simp only [exec]; exact runs_bind_ok run1 (by simp only [hv]; exact runs_fail c _)
            · simp only [runFuel, hr, hv]; exact True.intro
          | some bound =>
            refine ⟨some (Ok (off I.input rest) (rest, bound)), ?_, ?_⟩
            · simp only [exec]; exact runs_bind_ok run1 (by simp only [hv]; exact runs_pure _ c _)
            · simp only [runFuel, hr, hv]; exact ⟨rfl, rfl, rfl⟩
        | fail =>
          rw [agrees_fail agree1] at run1
          refine ⟨some Fail, ?_, ?_⟩
          · simp only [exec]; exact runs_bind_bad run1 (fun j x e => by cases e)
          · simp only [runFuel, hr]; exact True.intro
        | throwLabel pos name msg =>
          rw [agrees_throw agree1] at run1
          refine ⟨some (Throw (off I.input pos) name msg), ?_, ?_⟩
          · simp only [exec]; exact runs_bind_bad run1 (fun j x e => by cases e)
          · simp only [runFuel, hr]; exact ⟨rfl, rfl, rfl⟩
    | action site a =>
      obtain ⟨o1, run1, agree1⟩ := ih a rem env hrem
      cases hr : runFuel I fuel a rem env with
      | none =>
        rw [hr] at agree1; rw [agrees_none agree1] at run1
        refine ⟨none, ?_, ?_⟩
        · simp only [exec]; exact runs_bind_none run1
        · simp only [runFuel, hr]; exact True.intro
      | some reply =>
        rw [hr] at agree1
        cases reply with
        | ok rest inner =>
          rw [agrees_ok agree1] at run1
          cases hv : I.actions site >>= DepthAction.eval inner with
          | none =>
            refine ⟨some Fail, ?_, ?_⟩
            · simp only [exec]; exact runs_bind_ok run1 (by simp only [hv]; exact runs_fail c _)
            · simp only [runFuel, hr, hv]; exact True.intro
          | some depth =>
            refine ⟨some (Ok (off I.input rest) (rest, { inner with resultDepth := depth })), ?_, ?_⟩
            · simp only [exec]; exact runs_bind_ok run1 (by simp only [hv]; exact runs_pure _ c _)
            · simp only [runFuel, hr, hv]; exact ⟨rfl, rfl, rfl⟩
        | fail =>
          rw [agrees_fail agree1] at run1
          refine ⟨some Fail, ?_, ?_⟩
          · simp only [exec]; exact runs_bind_bad run1 (fun j x e => by cases e)
          · simp only [runFuel, hr]; exact True.intro
        | throwLabel pos name msg =>
          rw [agrees_throw agree1] at run1
          refine ⟨some (Throw (off I.input pos) name msg), ?_, ?_⟩
          · simp only [exec]; exact runs_bind_bad run1 (fun j x e => by cases e)
          · simp only [runFuel, hr]; exact ⟨rfl, rfl, rfl⟩

end Exec
/-! ## The File rule from the context of `runParser` -/

section File

set_option maxRecDepth 65536 in
/-- The literal terminals of the metagrammar are not empty. -/
theorem invariant1_meta_literals_nonempty (input : List Char) (site : Nat) :
    (context false input).terms site ≠ some (.lit []) := by
  have all : (MetaTerminal1.table.toList.all fun p => p.2 != .lit []) = true := by rfl
  show (MetaTerminal1.table[site]?).map Prod.snd ≠ some (.lit [])
  intro h
  obtain ⟨p, hp, eq⟩ := Option.map_eq_some_iff.mp h
  have mem : p ∈ MetaTerminal1.table.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp)
  have := List.all_eq_true.mp all p mem
  simp [eq] at this

/-- The world before `newCtx`. Every field that `runParser` reads is reset by
`newCtx` (`startWorld`); the store is the empty store of a parser whose
calls do not memoise. -/
def heap0 : World Unit :=
  { fail := NoFailure, errors := ErrLog.ErrLog 0 [], deps := IS.empty, depth := 0, logs := [],
    stats := emptyStats, store := () }

/-- The context that `runParser defaultConfig` builds for the input. -/
def fileCtx (input : List Char) : Ctx Unit := startCtx defaultConfig () (String.ofList input)

/-- The File rule of the strict metagrammar, run on the translated runtime
for `fuel` steps from the context and world of `runParser defaultConfig`. -/
noncomputable def fileRun (input : List Char) (fuel : Nat) : Option (Res (Nat × Env)) :=
  let I := context false input
  ((exec I fuel (I.rules (startRule false)) input.length {} : P Unit Unit (Nat × Env))
    (fileCtx input) 0 (startWorld heap0)).map Prod.fst

theorem off_start (input : List Char) : off input input.length = 0 := by
  simp [off, Utf8Terminals.byteOffset]

/-- Invariant 1 for the File rule: for every fuel, the runtime run agrees with
the model's run. -/
theorem invariant1_runtime_file (input : List Char) (fuel : Nat) :
    Agrees input (fileRun input fuel)
      (runFuel (context false input) fuel ((context false input).rules (startRule false)) input.length {}) := by
  have strict : Strict (fileCtx input) := ⟨rfl, rfl⟩
  have on : OnInput (fileCtx input) (context false input).input := ⟨rfl, rfl⟩
  obtain ⟨o, run, agree⟩ := invariant1_exec_agrees (ρ := Unit) (σ := Unit) (context false input) on strict
    (invariant1_meta_literals_nonempty input) fuel ((context false input).rules (startRule false))
    input.length {} (Nat.le_refl _)
  have at0 := run (startWorld heap0)
  have offEq : off (context false input).input input.length = 0 := off_start input
  rw [offEq] at at0
  unfold fileRun
  rw [at0]
  exact agree

theorem fileRun_eventually (input : List Char) : ∃ k, (fileRun input k).isSome := by
  obtain ⟨r, hr, _⟩ := invariant1_file_result false input
  obtain ⟨k, ok⟩ := invariant1_derivation_has_fuel hr
  refine ⟨k, ?_⟩
  have agree := invariant1_runtime_file input k
  have ok' : runFuel (context false input) k ((context false input).rules (startRule false)) input.length {} =
      some r := ok
  rw [ok'] at agree
  cases h : fileRun input k with
  | none => rw [h] at agree; cases r <;> exact agree.elim
  | some _ => rfl

/-- The result of the runtime run of File, with enough fuel. -/
noncomputable def runtimeResult (input : List Char) : Res (Nat × Env) :=
  (fileRun input (Classical.choose (fileRun_eventually input))).get
    (Classical.choose_spec (fileRun_eventually input))

/-- The runtime result agrees with the reply of the derivation `FileResult`. -/
theorem invariant1_runtimeResult (input : List Char) :
    ∃ reply, FileResult false input reply ∧ Agrees input (some (runtimeResult input)) (some reply) := by
  have spec := Classical.choose_spec (fileRun_eventually input)
  generalize hk : Classical.choose (fileRun_eventually input) = k at spec
  have agree := invariant1_runtime_file input k
  have eq : some (runtimeResult input) = fileRun input k := by
    unfold runtimeResult; simp only [hk, Option.some_get]
  cases hr : runFuel (context false input) k ((context false input).rules (startRule false)) input.length {} with
  | none =>
    rw [hr] at agree
    have := agrees_none agree
    rw [this] at spec; cases spec
  | some reply =>
    rw [hr] at agree
    refine ⟨reply, invariant1_runFuel_sound hr, ?_⟩
    rw [eq]; exact agree

theorem invariant1_runtimeResult_reply (input : List Char) :
    Agrees input (some (runtimeResult input)) (some (recognizeFile false input).val) := by
  obtain ⟨reply, result, agree⟩ := invariant1_runtimeResult input
  obtain ⟨_, _, unique⟩ := invariant1_file_result false input
  have same := (unique _ result).trans (unique _ (recognizeFile false input).property).symm
  rw [← same]; exact agree

/-- The start result of `runParser` with the value of File, read from the
runtime run. The value list is that of FileTops, as in `startTops`. -/
noncomputable def runtimeStart {T : Type} (value : FileTops.Kind → Nat → T) (input : List Char) :
    PublicParsing.StartResult (List T) :=
  open Classical in
  match runtimeResult input with
  | Ok j _ => .ok j (if h : ∃ tops, FileTops.ParsesTo value input tops then h.choose else [])
  | Fail => .fail
  | Throw t l m => .throwLabel t l m

/-- The runtime start result is the `startTops` of the derivation's reply. -/
theorem invariant1_runtimeStart_eq {T : Type} (value : FileTops.Kind → Nat → T) (input : List Char) :
    runtimeStart value input = FileTops.startTops value input (recognizeFile false input).val := by
  have agree := invariant1_runtimeResult_reply input
  unfold runtimeStart
  cases hr : (recognizeFile false input).val with
  | ok rest env =>
    rw [hr] at agree; rw [Option.some_inj.mp (agrees_ok agree)]
    rfl
  | fail =>
    rw [hr] at agree; rw [Option.some_inj.mp (agrees_fail agree)]
    rfl
  | throwLabel pos name msg =>
    rw [hr] at agree; rw [Option.some_inj.mp (agrees_throw agree)]
    rfl

/-- The public strict entry: `runParser defaultConfig` of the File program
returns a value exactly when PublicParsing's entry of the runtime start
result does. -/
theorem invariant1_runtime_runParser (input : List Char) (fuel : Nat) (r : Res (Nat × Env))
    (run : fileRun input fuel = some r) (d : PublicParsing.Failure → String) :
    let I := context false input
    ∃ res s, runParser defaultConfig (pure () : RuntimeCore.ST Unit Unit)
        (exec I fuel (I.rules (startRule false)) input.length {}) (String.ofList input) heap0 = some (res, s) ∧
      ∀ x, res = .ok x ↔ PublicParsing.entry (TU.lengthWord8 (String.ofList input)) (toStart r) d = .ok x := by
  intro I
  unfold fileRun at run
  obtain ⟨pr, hpr, eq⟩ := Option.map_eq_some_iff.mp run
  obtain ⟨r', w1⟩ := pr
  simp only at eq; subst eq
  exact invariant1_translated_runParser_entry defaultConfig (pure ()) _ (String.ofList input) heap0 ()
    heap0 rfl r' w1 hpr d

end File

#print axioms invariant1_exec_agrees
#print axioms invariant1_terminal_runs
#print axioms invariant1_meta_literals_nonempty
#print axioms invariant1_runtime_file
#print axioms invariant1_runtimeResult
#print axioms invariant1_runtimeStart_eq
#print axioms invariant1_runtime_runParser

end PegHs.SelfHostedRuntime
