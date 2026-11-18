import SelfHostedRuntime
import ScopedEnv
import LoopBindings

/-!
The memo tables of the generated parser (premise R7 of
verification/README.md, the first difference).

The generated SelfHosted.hs wraps every rule call in `memo` (a rule without
parameters, keyed by the byte offset) or `memoArg` (a rule with the depth
parameter, keyed by the offset and the argument), and `defaultConfig` turns
memoisation on. `SelfHostedRuntime.exec` calls `nomemo` instead. This module
runs the same bodies with the tables (`execM`) and shows that the tables do
not change the result.

The store is `Tables`: one `IntMap` per rule for calls without arguments and
one `IntMap` of `Map Nat` per rule for calls with an argument. They are refs
into the store, as premise R1 has them, and their lens laws hold by
construction. `Coherent` is the cache invariant over the whole store: an entry
at a key holds a result that agrees with every reply the model gives at that
key in everything a caller keeps (the position, the label, the result depth).
For a call without arguments the key leaves out the caller's environment;
`ScopedEnv.invariant1_plain_call_independent` shows that it does not matter.
For a call with an argument the callee starts from `{ depth := d }` and the key
holds `d`.

Theorems:
- `invariant1_memo_runs`: from every world whose tables are coherent and whose
  growth-loop logs are empty, `execM` returns, at every fuel at which the model
  returns a reply, the result that corresponds to that reply, and leaves a
  world with coherent tables and empty logs.
- `invariant1_memo_exec_same`: at that fuel, `execM` returns what
  `SelfHostedRuntime.exec` returns.
- `invariant1_memo_file`: the File rule run with the tables, from the context
  and the world (with empty tables) of `runParser defaultConfig`, returns the
  same result as `SelfHostedRuntime.fileRun`; in particular it returns
  `runtimeResult`.

Premises: those of SelfHostedRuntime.lean, except that calls use `memo` and
`memoArg` as in the generated code. Each table holds `Nat × Env`, the value of
the model; the type of the Haskell value of each rule is premise R7's second
difference.
-/

set_option linter.unusedSimpArgs false
namespace PegHs.SelfHostedMemo
open RuntimeCore EnvironmentEval ConcreteTerminal MetaExecution SelfHostedRuntime ScopedEnv

attribute [local simp] st_bind st_pure st_map

abbrev Value := Nat × Env

structure Tables where
  plain : Nat → IntMap (Entry Value)
  arg : Nat → IntMap (Map Nat (Entry Value))

def Tables.empty : Tables := ⟨fun _ => IM.empty, fun _ => IM.empty⟩

/-- `f` with the value at `k` replaced. -/
def upd {β : Type} (f : Nat → β) (k : Nat) (v : β) : Nat → β := fun q => if q = k then v else f q

def plainRef (rule : Nat) : Table Tables Value :=
  storeRef (fun st => st.plain rule) (fun m st => { st with plain := upd st.plain rule m })

def argRef (rule : Nat) : ArgTable Tables Nat Value :=
  storeRef (fun st => st.arg rule) (fun m st => { st with arg := upd st.arg rule m })

abbrev PM := P Unit Tables Value

/-- The call of the generated code: `memo` without an argument, `memoArg`
keyed by the depth argument otherwise. -/
noncomputable def callP (calls : Nat → Option EnvironmentDepth.CallSite) (site rule : Nat) (callee : Env)
    (body : PM) : PM :=
  match calls site with
  | some (_, _, []) => memo (fun _ => plainRef rule) "rule" body
  | _ => memoArg (fun _ => argRef rule) "rule" callee.depth body

/-- `SelfHostedRuntime.exec` with the calls of the generated code. -/
noncomputable def execM (I : Inputs) : Nat → Body → Nat → Env → PM
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
          (callP metaCalls site rule callee (execM I fuel (I.rules rule) rem callee))
    | .seq a b => bindP (execM I fuel a rem env) fun r => execM I fuel b r.1 r.2
    | .alt a b => choice [execM I fuel a rem env, execM I fuel b rem env]
    | .ahead a => fmapP (fun _ => (rem, env)) (andP (execM I fuel a rem env))
    | .notAhead a => fmapP (fun _ => (rem, env)) (notP (execM I fuel a rem env))
    | .star a => execM I fuel (.starLoop a) rem { env with resultDepth := 0 }
    | .starLoop a => fun c i => do
        let saved ← saveErrors c
        unP (execM I fuel a rem env) c i >>= fun
          | Ok k r =>
            if k > i then execM I fuel (.starLoop a) r.1
                { env with resultDepth := max env.resultDepth r.2.resultDepth } c k
            else restoreErrors c saved >>= fun _ => pure (Ok i (rem, env))
          | Throw t l m => restoreErrors c saved >>= fun _ => pure (Throw t l m)
          | Fail => restoreErrors c saved >>= fun _ => pure (Ok i (rem, env))
    | .label name msg a => labelP name msg (execM I fuel a rem env)
    | .capture a => execM I fuel a rem env
    | .bind site name a => bindP (execM I fuel a rem env) fun r =>
        match I.hooks.bindValue site name (matchedText I.input rem r.1) r.2 with
        | some bound => pureP (r.1, bound)
        | none => fun _ _ => pure Fail
    | .action site a => bindP (execM I fuel a rem env) fun r =>
        match I.actions site >>= DepthAction.eval r.2 with
        | some depth => pureP (r.1, { r.2 with resultDepth := depth })
        | none => fun _ _ => pure Fail

/-! ## Results and the cache invariant -/

section Invariant
variable (input : List Char)

/-- The runtime result that a reply of the model stands for. -/
noncomputable def resOf : Reply → Res Value
  | .ok rest env => Ok (off input rest) (rest, env)
  | .fail => Fail
  | .throwLabel pos name msg => Throw (off input pos) name msg

/-- A runtime result agrees with a reply in everything a caller keeps. -/
def SameRes : Res Value → Reply → Prop
  | Ok j (rest, e), .ok rest' e' => j = off input rest' ∧ rest = rest' ∧ e.resultDepth = e'.resultDepth
  | Fail, .fail => True
  | Throw t l m, .throwLabel p l' m' => t = off input p ∧ l = l' ∧ m = m'
  | _, _ => False

def entryRes : Entry Value → Res Value
  | .Entry r _ _ _ => r

/-- The cache invariant of the whole store. -/
def Coherent (st : Tables) : Prop :=
  (∀ rule i e, st.plain rule i = some e → ∃ rem, rem ≤ input.length ∧ i = off input rem ∧
    ∀ fuel env reply, runFuel (context false input) fuel ((context false input).rules rule) rem env =
      some reply → SameRes input (entryRes e) reply) ∧
  (∀ rule i m d e, st.arg rule i = some m → m d = some e → ∃ rem, rem ≤ input.length ∧
    i = off input rem ∧
    ∀ fuel reply, runFuel (context false input) fuel ((context false input).rules rule) rem
      { depth := d } = some reply → SameRes input (entryRes e) reply)

def Inv (w : World Tables) : Prop := Coherent input w.store ∧ w.logs = []

theorem inv_of {w w' : World Tables} (h : Inv input w) (hs : w'.store = w.store)
    (hl : w'.logs = w.logs) : Inv input w' := by
  unfold Inv; rw [hs, hl]; exact h

theorem coherent_empty : Coherent input Tables.empty :=
  ⟨fun _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩

/-- From every world with the invariant, `p` returns `r` and keeps the invariant. -/
def RunsM (p : P Unit Tables α) (c : Ctx Unit) (i : Nat) (r : Res α) : Prop :=
  ∀ w, Inv input w → ∃ w', p c i w = some (r, w') ∧ Inv input w'

/-- From every world with the invariant, `p` returns a result with `good`. -/
def RunsSome (p : P Unit Tables α) (c : Ctx Unit) (i : Nat) (good : Res α → Prop) : Prop :=
  ∀ w, Inv input w → ∃ r w', p c i w = some (r, w') ∧ good r ∧ Inv input w'

end Invariant

/-! ## The combinators keep the invariant -/

section Combinators
variable {input : List Char} {α β : Type} {c : Ctx Unit} {i : Nat}

theorem runsM_pure (x : α) : RunsM input (pureP x) c i (Ok i x) :=
  fun w h => ⟨w, rfl, h⟩

theorem runsM_fail : RunsM input (fun _ _ => pure Fail : P Unit Tables α) c i Fail :=
  fun w h => ⟨w, rfl, h⟩

theorem runsM_bind_ok {p : P Unit Tables α} {k : α → P Unit Tables β} {j : Nat} {x : α} {r : Res β}
    (hp : RunsM input p c i (Ok j x)) (hk : RunsM input (k x) c j r) : RunsM input (bindP p k) c i r := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp w hw
  obtain ⟨w2, e2, i2⟩ := hk w1 i1
  exact ⟨w2, by simp [bindP, e1, unP, e2], i2⟩

theorem runsM_bind_bad {p : P Unit Tables α} {k : α → P Unit Tables β} {r : Res α}
    (hp : RunsM input p c i r) (bad : ∀ j x, r ≠ Ok j x) : RunsM input (bindP p k) c i (failed r) := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp w hw
  refine ⟨w1, ?_, i1⟩
  cases r with
  | Ok j x => exact absurd rfl (bad j x)
  | Fail => simp [bindP, e1, failed]
  | Throw t l m => simp [bindP, e1, failed]

theorem runsM_fmap {p : P Unit Tables α} {r : Res α} (f : α → β) (hp : RunsM input p c i r) :
    RunsM input (fmapP f p) c i (Res.map f r) := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp w hw
  refine ⟨w1, ?_, i1⟩
  cases r <;> simp [fmapP, e1, Res.map, failed]

theorem runsSome_fmap {p : P Unit Tables α} {good : Res α → Prop} (f : α → β) {target : Res β}
    (hp : RunsSome input p c i good) (to : ∀ r, good r → Res.map f r = target) :
    RunsM input (fmapP f p) c i target := by
  intro w hw
  obtain ⟨r, w1, e1, g, i1⟩ := hp w hw
  refine ⟨w1, ?_, i1⟩
  rw [← to r g]
  cases r <;> simp [fmapP, e1, Res.map, failed]

/-- What `choice [p, q]` returns. -/
def orRes' : Res α → Res α → Res α
  | Fail, r2 => r2
  | r1, _ => r1

theorem runsM_choice (strict : cfgRecover (ctxConfig c) = false) {p q : P Unit Tables α} {r1 r2 : Res α}
    (hp : RunsM input p c i r1) (hq : r1 = Fail → RunsM input q c i r2) :
    RunsM input (choice [p, q]) c i (orRes' r1 r2) := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp w hw
  cases r1 with
  | Ok j x => exact ⟨w1, by simp [choice, choice.go, saveErrors_strict strict, e1, unP, orRes'], i1⟩
  | Throw t l m => exact ⟨w1, by simp [choice, choice.go, saveErrors_strict strict, e1, unP, orRes'], i1⟩
  | Fail =>
    obtain ⟨w2, e2, i2⟩ := hq rfl w1 i1
    refine ⟨w2, ?_, i2⟩
    cases r2 <;> simp [choice, choice.go, saveErrors_strict strict, e1, e2, unP, orRes']

def lookRes' (positive : Bool) (i : Nat) : Res α → Res Unit
  | Ok _ _ => if positive then Ok i () else Fail
  | _ => if positive then Fail else Ok i ()

theorem runsM_andP (strict : cfgRecover (ctxConfig c) = false) {p : P Unit Tables α} {r : Res α}
    (hp : RunsM input p c i r) : RunsM input (andP p) c i (lookRes' true i r) := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp w hw
  exact ⟨w1, by cases r <;> simp [andP, saveErrors_strict strict, e1, unP, lookRes'], i1⟩

theorem runsM_notP (strict : cfgRecover (ctxConfig c) = false) {p : P Unit Tables α} {r : Res α}
    (hp : RunsM input p c i r) : RunsM input (notP p) c i (lookRes' false i r) := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp w hw
  refine ⟨{ w1 with fail := w.fail }, ?_, inv_of input i1 rfl rfl⟩
  cases r <;> simp [notP, saveErrors_strict strict, e1, unP, lookRes', readSTRef, writeSTRef, ctxFail,
    failRef]

def labelRes' (i : Nat) (name : String) (msg : Option Text) : Res α → Res α
  | Fail => Throw i name msg
  | other => other

theorem runsM_label (strict : cfgRecover (ctxConfig c) = false) {p : P Unit Tables α} {r : Res α}
    (name : String) (msg : Option String) (hp : RunsM input p c i r) :
    RunsM input (labelP name msg p) c i (labelRes' i name msg r) := by
  intro w hw
  obtain ⟨w1, e1, i1⟩ := hp { w with fail := NoFailure } (inv_of input hw rfl rfl)
  refine ⟨{ w1 with fail := mergeFailure w.fail w1.fail }, ?_, inv_of input i1 rfl rfl⟩
  rw [labelP_eq]
  cases r <;> simp [labeledWith, saveErrors_strict strict, e1, unP, labelRes', readSTRef, writeSTRef,
    ctxFail, failRef, labeledWith.l, T.pack, pack_map]

/-- `evalBody` runs the body on a world with the invariant and keeps it. -/
theorem evalBody_runsM {body : P Unit Tables α} {r : Res α} (strict : Strict c) (name : Text)
    (hb : RunsM input body c i r) (w : World Tables) (hw : Inv input w) :
    ∃ f errs d w', evalBody c name i body w = some ((r, f, errs, d), w') ∧ Inv input w' := by
  obtain ⟨w1, e1, i1⟩ := hb { w with fail := NoFailure, deps := IS.empty } (inv_of input hw rfl rfl)
  let w2 : World Tables := { w1 with fail := mergeFailure w.fail w1.fail, deps := IS.union w.deps w1.deps }
  refine ⟨w1.fail, noErrors, w1.deps, w2, ?_, inv_of input i1 rfl rfl⟩
  simp only [evalBody, countEval, saveErrors, strict.count, strict.recover, when, st_bind, st_pure,
    st_map, readSTRef, writeSTRef, ctxFail, ctxDeps, failRef, depsRef, unP, Bool.false_eq_true,
    ↓reduceIte, Option.bind_some]
  rw [e1]
  cases r <;> simp [newErrors, restoreErrors, maybe, st_map, st_pure] <;> rfl

end Combinators

/-! ## The memo tables -/

section Tables
variable {input : List Char} {c : Ctx Unit}

theorem off_inj {a b : Nat} (ha : a ≤ input.length) (hb : b ≤ input.length)
    (h : off input a = off input b) : a = b := by
  rcases Nat.lt_trichotomy a b with lt | eq | gt
  · have := (off_lt_iff (Nat.le_of_lt lt) hb).mpr lt; omega
  · exact eq
  · have := (off_lt_iff (Nat.le_of_lt gt) ha).mpr gt; omega

theorem sameRes_resOf (reply : Reply) : SameRes input (resOf input reply) reply := by
  cases reply with
  | ok rest env => exact ⟨rfl, rfl, rfl⟩
  | fail => trivial
  | throwLabel p l m => exact ⟨rfl, rfl, rfl⟩

theorem replay_keeps (e : Entry Value) (w : World Tables) :
    ∃ w', replay c e w = some (entryRes e, w') ∧ w'.store = w.store ∧ w'.logs = w.logs := by
  obtain ⟨r, f, errs, d⟩ := e
  by_cases h : IS.null d = true <;>
  cases r <;> cases errs <;> rename_i k xs <;> cases k <;>
    simp [replay, mergeFail, when, modifySTRef', ctxFail, failRef, ctxDeps, depsRef, appendSlice,
      ctxErrors, errorsRef, entryRes, h]

theorem logUndo_nil (d : IntSet) (u : RuntimeCore.ST Tables Unit) (w : World Tables) (h : w.logs = []) :
    logUndo c d u w = some ((), w) := by
  simp only [logUndo, when]
  split
  · simp [readSTRef, ctxLogs, logsRef, h]
  · rfl

theorem bumpEntries_off (strict : Strict c) (name : Text) (k : Int) (w : World Tables) :
    bumpEntries c name k w = some ((), w) := by
  simp [bumpEntries, when, strict.count]

/-- A call without arguments through `memo`. The table answers with a result
that agrees with the reply of the body in everything a caller keeps. -/
theorem runsSome_memo_plain (strict : Strict c) {rule rem : Nat} {body : PM} {inner : Reply}
    (hrem : rem ≤ input.length) (hb : RunsM input body c (off input rem) (resOf input inner))
    (hinner : ∃ fuel env, runFuel (context false input) fuel ((context false input).rules rule) rem env =
      some inner)
    (indep : ∀ fuel env reply, runFuel (context false input) fuel ((context false input).rules rule) rem env =
      some reply → SameRes input (resOf input inner) reply) :
    RunsSome input (memo (fun _ => plainRef rule) "rule" body) c (off input rem)
      (fun r => SameRes input r inner) := by
  intro w hw
  cases hm : cfgMemo (ctxConfig c)
  · obtain ⟨f, errs, d, w1, e1, i1⟩ := evalBody_runsM strict (memo.name "rule") hb w hw
    exact ⟨_, w1, by simp [memo, hm, e1], sameRes_resOf inner, i1⟩
  · cases hl : w.store.plain rule (off input rem) with
    | some e =>
      obtain ⟨w1, e1, hs, hlg⟩ := replay_keeps (c := c) e w
      refine ⟨entryRes e, w1, ?_, ?_, inv_of input hw hs hlg⟩
      · simp [memo, hm, plainRef, storeRef, readSTRef, IM.lookup, hl, e1]
      · obtain ⟨rem', hrem', hoff, same⟩ := hw.1.1 rule _ e hl
        have := off_inj hrem hrem' hoff
        subst this
        obtain ⟨fuel, env, run⟩ := hinner
        exact same fuel env inner run
    | none =>
      obtain ⟨f, errs, d, w1, e1, i1⟩ := evalBody_runsM strict (memo.name "rule") hb w hw
      let E : Entry Value := Entry.Entry (resOf input inner) f errs d
      let w2 : World Tables := { w1 with store := { w1.store with
        plain := upd w1.store.plain rule (IM.insert (off input rem) E (w1.store.plain rule)) } }
      refine ⟨resOf input inner, w2, ?_, sameRes_resOf inner, ?_, i1.2⟩
      · simp only [memo, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
          readSTRef, plainRef, storeRef, IM.lookup, hl, Option.map_some, Option.bind_some, e1]
        simp [modifySTRef', bumpEntries_off strict, logUndo_nil, i1.2, w2, E]
      · refine ⟨?_, fun rule' i m k e' h1 h2 => i1.1.2 rule' i m k e' h1 h2⟩
        intro rule' i e' h
        simp only [w2, upd] at h
        by_cases hr : rule' = rule
        · subst hr
          simp only [↓reduceIte, IM.insert] at h
          by_cases hi : i = off input rem
          · subst hi
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            exact ⟨rem, hrem, rfl, indep⟩
          · simp only [hi, ↓reduceIte] at h
            exact i1.1.1 rule' i e' h
        · simp only [hr, ↓reduceIte] at h
          exact i1.1.1 rule' i e' h

/-- A call with an argument through `memoArg`, keyed by the depth argument. -/
theorem runsSome_memo_arg (strict : Strict c) {rule rem k : Nat} {body : PM} {inner : Reply}
    (hrem : rem ≤ input.length) (hb : RunsM input body c (off input rem) (resOf input inner))
    (hinner : ∃ fuel, runFuel (context false input) fuel ((context false input).rules rule) rem
      { depth := k } = some inner) :
    RunsSome input (memoArg (fun _ => argRef rule) "rule" k body) c (off input rem)
      (fun r => SameRes input r inner) := by
  intro w hw
  obtain ⟨fuel0, run0⟩ := hinner
  cases hm : cfgMemo (ctxConfig c)
  · obtain ⟨f, errs, d, w1, e1, i1⟩ := evalBody_runsM strict (memoArg.name "rule") hb w hw
    exact ⟨_, w1, by simp [memoArg, hm, e1], sameRes_resOf inner, i1⟩
  · cases hl : (w.store.arg rule (off input rem)) >>= M.lookup k with
    | some e =>
      obtain ⟨m, hm1, hm2⟩ := Option.bind_eq_some_iff.mp hl
      obtain ⟨w1, e1, hs, hlg⟩ := replay_keeps (c := c) e w
      refine ⟨entryRes e, w1, ?_, ?_, inv_of input hw hs hlg⟩
      · simp only [memoArg, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
          readSTRef, argRef, storeRef, IM.lookup, Option.map_some, Option.bind_some]
        rw [hl]; exact e1
      · obtain ⟨rem', hrem', hoff, same⟩ := hw.1.2 rule _ m k e hm1 hm2
        have := off_inj hrem hrem' hoff
        subst this
        exact same fuel0 inner run0
    | none =>
      obtain ⟨f, errs, d, w1, e1, i1⟩ := evalBody_runsM strict (memoArg.name "rule") hb w hw
      let E : Entry Value := Entry.Entry (resOf input inner) f errs d
      let w2 : World Tables := { w1 with store := { w1.store with
        arg := upd w1.store.arg rule
          (IM.insertWith M.union (off input rem) (M.singleton k E) (w1.store.arg rule)) } }
      refine ⟨resOf input inner, w2, ?_, sameRes_resOf inner, ?_, i1.2⟩
      · simp only [memoArg, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
          readSTRef, argRef, storeRef, IM.lookup, Option.map_some, Option.bind_some]
        rw [hl]
        simp only [st_bind, Option.bind_some, e1]
        simp [modifySTRef', bumpEntries_off strict, logUndo_nil, i1.2, w2, E]
      · refine ⟨fun rule' i e' h => i1.1.1 rule' i e' h, ?_⟩
        intro rule' i m k' e' h1 h2
        simp only [w2, upd] at h1
        by_cases hr : rule' = rule
        · subst hr
          simp only [↓reduceIte, IM.insertWith] at h1
          by_cases hi : i = off input rem
          · subst hi
            simp only [↓reduceIte, Option.some.injEq] at h1
            subst h1
            by_cases hk : k' = k
            · subst hk
              have e2 : e' = E := by
                revert h2
                cases w1.store.arg rule' (off input rem) <;> simp [M.union, M.singleton]
                all_goals intro h; exact h.symm
              subst e2
              refine ⟨rem, hrem, rfl, fun fuel reply run => ?_⟩
              have := invariant1_result_unique _ run run0
              subst this
              exact sameRes_resOf reply
            · have old : ∃ m0, w1.store.arg rule' (off input rem) = some m0 ∧ m0 k' = some e' := by
                revert h2
                cases w1.store.arg rule' (off input rem) <;>
                  simp [M.union, M.singleton, hk]
              obtain ⟨m0, hm0, hk0⟩ := old
              exact i1.1.2 rule' _ m0 k' e' hm0 hk0
          · simp only [hi, ↓reduceIte] at h1
            exact i1.1.2 rule' i m k' e' h1 h2
        · simp only [hr, ↓reduceIte] at h1
          exact i1.1.2 rule' i m k' e' h1 h2

end Tables

/-! ## The run with the tables -/

/-- Every call without arguments in a body targets a rule that no call site
passes an argument to, and no repetition body binds a name
(LoopBindings.lean: then `execM`, which drops the bindings of an iteration as
`many` does, starts each iteration from the environment the model passes). -/
def plainCalls (calls : Nat → Option EnvironmentDepth.CallSite) : Body → Bool
  | .call site rule => match calls site with
    | some (_, _, []) => metaPlain rule
    | _ => true
  | .seq a b | .alt a b => plainCalls calls a && plainCalls calls b
  | .star a | .starLoop a => (binders a).isEmpty && plainCalls calls a
  | .ahead a | .notAhead a | .label _ _ a | .capture a | .bind _ _ a
  | .action _ a => plainCalls calls a
  | _ => true

section PlainCalls
variable (calls : Nat → Option EnvironmentDepth.CallSite)
theorem plainCalls_seq (a b : Body) :
    plainCalls calls (.seq a b) = (plainCalls calls a && plainCalls calls b) := rfl
theorem plainCalls_alt (a b : Body) :
    plainCalls calls (.alt a b) = (plainCalls calls a && plainCalls calls b) := rfl
theorem plainCalls_one (a : Body) :
    (plainCalls calls (.ahead a) = plainCalls calls a) ∧ (plainCalls calls (.notAhead a) = plainCalls calls a) ∧
    (plainCalls calls (.star a) = plainCalls calls (.starLoop a)) ∧
    (plainCalls calls (.starLoop a) = ((binders a).isEmpty && plainCalls calls a)) ∧
    (∀ n m, plainCalls calls (.label n m a) = plainCalls calls a) ∧
    (plainCalls calls (.capture a) = plainCalls calls a) ∧
    (∀ s n, plainCalls calls (.bind s n a) = plainCalls calls a) ∧
    (∀ s, plainCalls calls (.action s a) = plainCalls calls a) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
theorem plainCalls_loops : ∀ body : Body, plainCalls calls body = true →
    LoopBindings.loopsBindNothing body = true
  | .eps, _ | .terminal _, _ | .predicate _, _ | .call _ _, _ => rfl
  | .seq a b, h | .alt a b, h => by
    simp only [plainCalls, Bool.and_eq_true] at h
    simp only [LoopBindings.loopsBindNothing, Bool.and_eq_true]
    exact ⟨plainCalls_loops a h.1, plainCalls_loops b h.2⟩
  | .star a, h | .starLoop a, h => by
    simp only [plainCalls, Bool.and_eq_true] at h
    simp only [LoopBindings.loopsBindNothing, Bool.and_eq_true]
    exact ⟨h.1, plainCalls_loops a h.2⟩
  | .ahead a, h | .notAhead a, h | .label _ _ a, h | .capture a, h | .bind _ _ a, h
  | .action _ a, h => plainCalls_loops a h
theorem plainCalls_call_plain {site rule : Nat} {a b : String} (hs : calls site = some (a, b, []))
    (p : plainCalls calls (.call site rule) = true) : metaPlain rule = true := by
  simpa [plainCalls, hs] using p
end PlainCalls

/-- The rules that `callP` calls through `memoArg` are the rules that the
generated code defines with the parameter `d` and `PegRt.memoArg`:
ExtractSelfHostedFile.hs reads `depthHeader` for Item (24), PrefixE (27),
Labeled (28), LabelPart (29), SuffixE (30), PostOps (31), PostOp (32),
Primary (33), TemplateArgs (34), TemplateArg (35), GroupAlts (37) and
MoreGroup (38), numbered by its `call` table, and `header` (`PegRt.memo`) for
every other rule. -/
theorem invariant1_memoArg_rules :
    (List.range MetaTerminal1.environmentBodyTable.size).filter (fun r => !metaPlain r) =
      [24, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38] := by decide +kernel

def metaPlainCalls : Bool :=
  (List.range MetaTerminal1.environmentBodyTable.size).all fun r =>
    plainCalls metaCalls (MetaTerminal1.environmentBody r)

theorem metaPlainCalls_eq : metaPlainCalls = true := by decide +kernel

theorem rules_plainCalls (input : List Char) (r : Nat) :
    plainCalls metaCalls ((context false input).rules r) = true := by
  show plainCalls metaCalls (MetaTerminal1.environmentBody r) = true
  by_cases lt : r < MetaTerminal1.environmentBodyTable.size
  · have all := metaPlainCalls_eq
    simp only [metaPlainCalls, List.all_eq_true, List.mem_range] at all
    exact all r lt
  · have past : MetaTerminal1.environmentBody r = .terminal 0 := by
      simp [MetaTerminal1.environmentBody, Array.getElem?_eq_none (Nat.le_of_not_lt lt)]
    rw [past]; rfl

section Run
variable {input : List Char} {c : Ctx Unit}

theorem runsM_of_runs {α : Type} {p : P Unit Tables α} {i : Nat} {r : Res α} (h : Runs p c i (some r))
    (frame : ∀ w r' w', p c i w = some (r', w') → w'.store = w.store ∧ w'.logs = w.logs) :
    RunsM input p c i r := by
  intro w hw
  have hr := h w
  cases e : p c i w with
  | none => rw [e] at hr; cases hr
  | some pr =>
    obtain ⟨r', w'⟩ := pr
    rw [e] at hr; simp only [Option.map_some, Option.some.injEq] at hr; subst hr
    obtain ⟨hs, hl⟩ := frame w r' w' e
    exact ⟨w', rfl, inv_of input hw hs hl⟩

theorem termP_frame (t : Terminal) (i : Nat) (w : World Tables) :
    ∀ r w', (termP t : P Unit Tables Unit) c i w = some (r, w') → w'.store = w.store ∧ w'.logs = w.logs := by
  intro r w' h
  cases t with
  | lit chars =>
    simp only [termP, lit] at h
    split at h
    · simp only [st_pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · obtain ⟨f, hf, -⟩ := failAt_run (α := Unit) c i (ExpectedLiteral (T.pack (String.ofList chars))) w
      rw [lit.expected] at h
      rw [hf] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | cls ranges =>
    simp only [termP, cls] at h
    split at h
    · split at h
      · simp only [st_pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
      · obtain ⟨f, hf, -⟩ := failAt_run (α := Unit) c i (ExpectedClass (T.pack "")) w
        rw [cls.expected] at h
        rw [hf] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · obtain ⟨f, hf, -⟩ := failAt_run (α := Unit) c i (ExpectedClass (T.pack "")) w
      rw [cls.expected] at h
      rw [hf] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | any =>
    simp only [termP, anyChar] at h
    split at h
    · simp only [st_pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · obtain ⟨f, hf, -⟩ := failAt_run (α := Unit) c i ExpectedAny w
      rw [hf] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem sameRes_of_sameCall {x y : Reply} (h : SameCall x y) : SameRes input (resOf input x) y := by
  match x, y, h with
  | .ok _ _, .ok _ _, ⟨e, d⟩ => exact ⟨by rw [e], e, d⟩
  | .fail, .fail, _ => trivial
  | .throwLabel _ _ _, .throwLabel _ _ _, ⟨e1, e2, e3⟩ => exact ⟨by rw [e1], e2, e3⟩

theorem enter_arg {site : Nat} {env callee : Env} {a b src : String}
    (hs : metaCalls site = some (a, b, [src]))
    (he : (context false input).hooks.enterCall site env = some callee) :
    callee = { depth := callee.depth } := by
  have unfold : (context false input).hooks.enterCall site env =
      EnvironmentDepth.enterCall metaCalls site env := rfl
  rw [unfold] at he
  simp only [EnvironmentDepth.enterCall, hs] at he
  cases ha : EnvironmentDepth.depthArgOf src with
  | none => simp [ha] at he
  | some arg =>
    cases hv : EnvironmentDepth.evalDepthArg env arg with
    | none => simp [ha, hv] at he
    | some d => simp [ha, hv] at he; subst he; rfl

theorem enter_plain {site : Nat} {env callee : Env} {a b : String}
    (hs : metaCalls site = some (a, b, []))
    (he : (context false input).hooks.enterCall site env = some callee) : callee = env := by
  have unfold : (context false input).hooks.enterCall site env =
      EnvironmentDepth.enterCall metaCalls site env := rfl
  rw [unfold] at he
  simp [EnvironmentDepth.enterCall, hs] at he
  exact he.symm

theorem enter_none {site : Nat} {env callee : Env}
    (hs : metaCalls site = none ∨ ∃ a b x y rest, metaCalls site = some (a, b, x :: y :: rest))
    (he : (context false input).hooks.enterCall site env = some callee) : False := by
  have unfold : (context false input).hooks.enterCall site env =
      EnvironmentDepth.enterCall metaCalls site env := rfl
  rw [unfold] at he
  rcases hs with hs | ⟨a, b, x, y, rest, hs⟩ <;> simp [EnvironmentDepth.enterCall, hs] at he

/-- The tables do not change the result: at every fuel at which the model
returns a reply, the run with the tables returns the corresponding result,
from every world whose tables are coherent, and keeps them coherent. -/
theorem invariant1_memo_runs (on : OnInput c input) (strict : Strict c) :
    ∀ fuel body rem env reply, plainCalls metaCalls body = true → rem ≤ input.length →
      runFuel (context false input) fuel body rem env = some reply →
      RunsM input (execM (context false input) fuel body rem env) c (off input rem) (resOf input reply) := by
  have literals := invariant1_meta_literals_nonempty input
  have on' : OnInput c (context false input).input := on
  intro fuel
  induction fuel with
  | zero => intro body rem env reply _ _ h; cases h
  | succ fuel ih =>
    intro body rem env reply plain hrem hr
    cases body with
    | eps =>
      simp only [runFuel, Option.some.injEq] at hr; subst hr
      exact runsM_pure _
    | terminal site =>
      simp only [runFuel] at hr
      cases ht : (context false input).terms site with
      | none =>
        rw [ht] at hr; simp only [Option.some.injEq] at hr; subst hr
        simp only [execM, ht]; exact runsM_fail
      | some t =>
        simp only [ht] at hr
        have T := invariant1_terminal_runs (ρ := Unit) (σ := Tables) t (fun e => literals site (e ▸ ht)) on' hrem
        cases ho : terminalOracle t (context false input).input rem with
        | none =>
          simp only [ho, Option.some.injEq] at hr; subst hr
          simp only [execM, ht]
          exact runsM_bind_bad (runsM_of_runs (T.1 ho) (termP_frame t _)) (fun j x e => by cases e)
        | some rest =>
          obtain ⟨lt, width, run⟩ := T.2 rest ho
          simp only [ho, lt, ↓reduceIte, Option.some.injEq] at hr; subst hr
          simp only [execM, ht]
          have key := runsM_bind_ok (input := input)
            (k := fun _ => pureP (rem - termWidth t, { env with resultDepth := 0 }))
            (runsM_of_runs run (termP_frame t _)) (runsM_pure _)
          have e2 : ((rest, { env with resultDepth := 0 }) : Value) =
              (rem - termWidth t, { env with resultDepth := 0 }) := by rw [width]
          show RunsM input _ c _ (Ok (off input rest) (rest, { env with resultDepth := 0 }))
          rw [e2]
          exact key
    | predicate site =>
      simp only [runFuel] at hr
      cases hs : (context false input).sites site with
      | none =>
        rw [hs] at hr; simp only [Option.some.injEq] at hr; subst hr
        simp only [execM, hs]; exact runsM_fail
      | some pair =>
        obtain ⟨kind, pol⟩ := pair
        rw [hs] at hr
        simp only [execM, hs]
        have hp : ∀ b, RunsM input (predicate b : P Unit Tables Unit) c (off input rem)
            (if b then Ok (off input rem) () else Fail) := fun b w hw => ⟨w, rfl, hw⟩
        cases hb : (SemanticPredicates.eval (context false input).classes kind
            ((context false input).predicateEnv site env) == pol) with
        | true =>
          simp only [hb, ↓reduceIte, Option.some.injEq] at hr; subst hr
          have := hp true
          simp only [↓reduceIte] at this
          exact runsM_bind_ok this (runsM_pure _)
        | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hr; subst hr
          have := hp false
          simp only [Bool.false_eq_true, ↓reduceIte] at this
          exact runsM_bind_bad this (fun j x e => by cases e)
    | call site rule =>
      simp only [runFuel] at hr
      cases he : (context false input).hooks.enterCall site env with
      | none =>
        simp only [he, Option.some.injEq] at hr; subst hr
        simp only [execM, he]; exact runsM_fail
      | some callee =>
        simp only [he] at hr
        cases hi : runFuel (context false input) fuel ((context false input).rules rule) rem callee with
        | none => simp only [hi] at hr; cases hr
        | some inner =>
          simp only [hi] at hr
          have body := ih _ rem callee inner (rules_plainCalls input rule) hrem hi
          have good : RunsSome input (callP metaCalls site rule callee
              (execM (context false input) fuel ((context false input).rules rule) rem callee)) c
              (off input rem) (fun r => SameRes input r inner) := by
            cases hs : metaCalls site with
            | none => exact (enter_none (Or.inl hs) he).elim
            | some cs =>
              obtain ⟨a, b, args⟩ := cs
              cases args with
              | nil =>
                have isPlain : metaPlain rule = true := plainCalls_call_plain metaCalls hs plain
                have same := enter_plain hs he
                subst same
                unfold callP; rw [hs]
                exact runsSome_memo_plain strict hrem body ⟨fuel, callee, hi⟩
                  (fun fuel' env' reply' run' => sameRes_of_sameCall
                    (invariant1_plain_call_independent input isPlain hi run'))
              | cons src more =>
                cases more with
                | nil =>
                  have shape := enter_arg hs he
                  unfold callP; rw [hs]
                  exact runsSome_memo_arg strict hrem body ⟨fuel, by rw [← shape]; exact hi⟩
                | cons y rest => exact (enter_none (Or.inr ⟨a, b, src, y, rest, hs⟩) he).elim
          simp only [execM, he]
          refine runsSome_fmap _ good ?_
          intro r hsame
          have leave : ∀ e : Env, (context false input).hooks.leaveCall site env e =
              { env with resultDepth := e.resultDepth } := fun _ => rfl
          cases inner with
          | ok rest ienv =>
            simp only [Option.some.injEq] at hr; subst hr
            match r, hsame with
            | Ok j (rest', e), ⟨hj, hrest, hd⟩ =>
              subst hj hrest
              simp [Res.map, leave, resOf, hd]
          | fail =>
            simp only [Option.some.injEq] at hr; subst hr
            match r, hsame with
            | Fail, _ => rfl
          | throwLabel p l m =>
            simp only [Option.some.injEq] at hr; subst hr
            match r, hsame with
            | Throw t l' m', ⟨h1, h2, h3⟩ => subst h1 h2 h3; rfl
    | seq a b =>
      rw [plainCalls_seq metaCalls, Bool.and_eq_true] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := ih a rem env ra plain.1 hrem ha
        simp only [execM]
        cases ra with
        | ok rest next =>
          have le := rest_le ha
          exact runsM_bind_ok IA (ih b rest next reply plain.2 (by omega) hr)
        | fail =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_bind_bad IA (fun j x e => by cases e)
        | throwLabel p l m =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_bind_bad IA (fun j x e => by cases e)
    | alt a b =>
      rw [plainCalls_alt metaCalls, Bool.and_eq_true] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := ih a rem env ra plain.1 hrem ha
        simp only [execM]
        cases ra with
        | fail =>
          exact runsM_choice strict.recover IA (fun _ => ih b rem env reply plain.2 hrem hr)
        | ok rest next =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_choice (r2 := Fail) strict.recover IA (fun h => by cases h)
        | throwLabel p l m =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_choice (r2 := Fail) strict.recover IA (fun h => by cases h)
    | ahead a =>
      rw [(plainCalls_one metaCalls a).1] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := runsM_fmap (fun _ => (rem, env)) (runsM_andP strict.recover (ih a rem env ra plain hrem ha))
        simp only [execM]
        cases ra <;> simp only [Option.some.injEq] at hr <;> subst hr <;> exact IA
    | notAhead a =>
      rw [(plainCalls_one metaCalls a).2.1] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := runsM_fmap (fun _ => (rem, env)) (runsM_notP strict.recover (ih a rem env ra plain hrem ha))
        simp only [execM]
        cases ra <;> simp only [Option.some.injEq] at hr <;> subst hr <;> exact IA
    | star a =>
      simp only [runFuel] at hr
      simp only [execM]
      exact ih (.starLoop a) rem _ reply (by rw [← (plainCalls_one metaCalls a).2.2.1]; exact plain) hrem hr
    | starLoop a =>
      have loopA : (binders a).isEmpty = true ∧ plainCalls metaCalls a = true := by
        have p := plain
        rw [(plainCalls_one metaCalls a).2.2.2.1, Bool.and_eq_true] at p; exact p
      have plainA := loopA.2
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := ih a rem env ra plainA hrem ha
        cases ra with
        | ok rest next =>
          have le := rest_le ha
          by_cases lt : rest < rem
          · simp only [lt, ↓reduceIte] at hr
            rw [LoopBindings.invariant1_loop_env_same _ (fun _ _ _ => rfl) loopA.1 ha] at hr
            have IL := ih (.starLoop a) rest _ reply plain (by omega) hr
            have gt := (off_lt_iff le hrem).mpr lt
            intro w hw
            obtain ⟨w1, e1, i1⟩ := IA w hw
            obtain ⟨w2, e2, i2⟩ := IL w1 i1
            exact ⟨w2, by simp [execM, saveErrors_strict strict.recover, unP, e1, gt, e2, resOf], i2⟩
          · simp only [lt, ↓reduceIte, Option.some.injEq] at hr; subst hr
            have ngt : ¬ off input rem < off input rest := fun g => lt ((off_lt_iff le hrem).mp g)
            intro w hw
            obtain ⟨w1, e1, i1⟩ := IA w hw
            exact ⟨w1, by simp [execM, saveErrors_strict strict.recover, unP, e1, ngt, resOf], i1⟩
        | fail =>
          simp only [Option.some.injEq] at hr; subst hr
          intro w hw
          obtain ⟨w1, e1, i1⟩ := IA w hw
          exact ⟨w1, by simp [execM, saveErrors_strict strict.recover, unP, e1, resOf], i1⟩
        | throwLabel p l m =>
          simp only [Option.some.injEq] at hr; subst hr
          intro w hw
          obtain ⟨w1, e1, i1⟩ := IA w hw
          exact ⟨w1, by simp [execM, saveErrors_strict strict.recover, unP, e1, resOf], i1⟩
    | label name msg a =>
      rw [(plainCalls_one metaCalls a).2.2.2.2.1 name msg] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := runsM_label strict.recover name msg (ih a rem env ra plain hrem ha)
        simp only [execM]
        cases ra <;> simp only [Option.some.injEq] at hr <;> subst hr <;> exact IA
    | capture a =>
      rw [(plainCalls_one metaCalls a).2.2.2.2.2.1] at plain
      simp only [runFuel] at hr
      simp only [execM]
      exact ih a rem env reply plain hrem hr
    | bind site name a =>
      rw [(plainCalls_one metaCalls a).2.2.2.2.2.2.1 site name] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := ih a rem env ra plain hrem ha
        simp only [execM]
        cases ra with
        | ok rest inner =>
          cases hv : (context false input).hooks.bindValue site name
              (matchedText (context false input).input rem rest) inner with
          | none =>
            simp only [hv, Option.some.injEq] at hr; subst hr
            exact runsM_bind_ok IA (by simp only [hv]; exact runsM_fail)
          | some bound =>
            simp only [hv, Option.some.injEq] at hr; subst hr
            exact runsM_bind_ok IA (by simp only [hv]; exact runsM_pure _)
        | fail =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_bind_bad IA (fun j x e => by cases e)
        | throwLabel p l m =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_bind_bad IA (fun j x e => by cases e)
    | action site a =>
      rw [(plainCalls_one metaCalls a).2.2.2.2.2.2.2 site] at plain
      simp only [runFuel] at hr
      cases ha : runFuel (context false input) fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        have IA := ih a rem env ra plain hrem ha
        simp only [execM]
        cases ra with
        | ok rest inner =>
          cases hv : (context false input).actions site >>= DepthAction.eval inner with
          | none =>
            simp only [hv, Option.some.injEq] at hr; subst hr
            exact runsM_bind_ok IA (by simp only [hv]; exact runsM_fail)
          | some depth =>
            simp only [hv, Option.some.injEq] at hr; subst hr
            exact runsM_bind_ok IA (by simp only [hv]; exact runsM_pure _)
        | fail =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_bind_bad IA (fun j x e => by cases e)
        | throwLabel p l m =>
          simp only [Option.some.injEq] at hr; subst hr
          exact runsM_bind_bad IA (fun j x e => by cases e)

end Run

/-! ## The same result as `exec` -/

theorem agrees_resOf {input : List Char} {r : Res Value} {reply : Reply}
    (h : Agrees input (some r) (some reply)) : r = resOf input reply := by
  cases reply with
  | ok rest env => exact Option.some.inj (agrees_ok h)
  | fail => exact Option.some.inj (agrees_fail h)
  | throwLabel p l m => exact Option.some.inj (agrees_throw h)

/-- At every fuel at which `exec` (with `nomemo`) returns a result from some
world, `execM` (with `memo` and `memoArg`) returns the same result from every
world whose tables are coherent. -/
theorem invariant1_memo_exec_same {input : List Char} {c : Ctx Unit} (on : OnInput c input)
    (strict : Strict c) (fuel : Nat) (body : Body) (plain : plainCalls metaCalls body = true)
    (rem : Nat) (env : Env) (hrem : rem ≤ input.length) (r : Res Value) (w0 : World Unit) (w0' : World Unit)
    (run : (exec (context false input) fuel body rem env : P Unit Unit Value) c (off input rem) w0 =
      some (r, w0')) :
    RunsM input (execM (context false input) fuel body rem env) c (off input rem) r := by
  obtain ⟨o, runs, agree⟩ := invariant1_exec_agrees (ρ := Unit) (σ := Unit) (context false input) on strict
    (invariant1_meta_literals_nonempty input) (LoopBindings.invariant1_meta_loops_bind_nothing input)
    fuel body rem env (plainCalls_loops metaCalls body plain) hrem
  have ho : ((exec (context false input) fuel body rem env : P Unit Unit Value) c (off input rem) w0).map
      Prod.fst = o := runs w0
  rw [run] at ho
  simp only [Option.map_some] at ho
  subst ho
  cases hr : runFuel (context false input) fuel body rem env with
  | none => rw [hr] at agree; exact absurd agree (by simp [Agrees])
  | some reply =>
    rw [hr] at agree
    rw [agrees_resOf agree]
    exact invariant1_memo_runs on strict fuel body rem env reply plain hrem hr

/-! ## The File rule with the tables -/

/-- The world before `newCtx`, with empty tables. -/
def heapM : World Tables :=
  { fail := NoFailure, errors := ErrLog.ErrLog 0 [], deps := IS.empty, depth := 0, logs := [],
    stats := emptyStats, store := Tables.empty }

/-- The File rule run with the tables of the generated code from the context
and world of `runParser defaultConfig`. -/
noncomputable def fileRunM (input : List Char) (fuel : Nat) : Option (Res Value) :=
  let I := context false input
  ((execM I fuel (I.rules (startRule false)) input.length {}) (fileCtx input) 0 (startWorld heapM)).map
    Prod.fst

theorem inv_start (input : List Char) : Inv input (startWorld heapM) :=
  ⟨coherent_empty input, rfl⟩

/-- The run with the tables returns what the run without them returns. -/
theorem invariant1_memo_file (input : List Char) (fuel : Nat) (r : Res Value)
    (run : fileRun input fuel = some r) : fileRunM input fuel = some r := by
  have strict : Strict (fileCtx input) := ⟨rfl, rfl⟩
  have on : OnInput (fileCtx input) input := ⟨rfl, rfl⟩
  have agree := invariant1_runtime_file input fuel
  rw [run] at agree
  cases hr : runFuel (context false input) fuel ((context false input).rules (startRule false))
      input.length {} with
  | none => rw [hr] at agree; exact absurd agree (by simp [Agrees])
  | some reply =>
    rw [hr] at agree
    have M := invariant1_memo_runs on strict fuel _ input.length {} reply
      (rules_plainCalls input (startRule false)) (Nat.le_refl _) hr
    obtain ⟨w', e, -⟩ := M (startWorld heapM) (inv_start input)
    rw [off_start] at e
    show ((execM (context false input) fuel ((context false input).rules (startRule false)) input.length {})
      (fileCtx input) 0 (startWorld heapM)).map Prod.fst = some r
    rw [e, agrees_resOf agree]
    rfl

theorem invariant1_memo_runtimeResult (input : List Char) :
    fileRunM input (Classical.choose (fileRun_eventually input)) = some (runtimeResult input) := by
  apply invariant1_memo_file
  unfold runtimeResult
  simp only [Option.some_get]

/-- The public strict entry with the tables: `runParser defaultConfig` of the
File program with the tables of the generated code returns a value exactly
when PublicParsing's entry of the runtime start result does. -/
theorem invariant1_memo_runParser (input : List Char) (d : PublicParsing.Failure → String) :
    let I := context false input
    let k := Classical.choose (fileRun_eventually input)
    ∃ res s, runParser defaultConfig (pure () : RuntimeCore.ST Tables Unit)
        (execM I k (I.rules (startRule false)) input.length {}) (String.ofList input) heapM = some (res, s) ∧
      ∀ x, res = .ok x ↔
        PublicParsing.entry (TU.lengthWord8 (String.ofList input)) (toStart (runtimeResult input)) d = .ok x := by
  intro I k
  have h : ((execM I k (I.rules (startRule false)) input.length {}) (fileCtx input) 0
      (startWorld heapM)).map Prod.fst = some (runtimeResult input) := invariant1_memo_runtimeResult input
  obtain ⟨pr, hpr, eq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', w1⟩ := pr
  simp only at eq
  rw [← eq]
  exact invariant1_translated_runParser_entry defaultConfig (pure ()) _ (String.ofList input) heapM ()
    heapM rfl r' w1 hpr d

#print axioms invariant1_memo_runs
#print axioms invariant1_memo_exec_same
#print axioms invariant1_memo_file
#print axioms invariant1_memo_runtimeResult
#print axioms invariant1_memo_runParser

end PegHs.SelfHostedMemo
