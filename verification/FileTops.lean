import TotalFile

/-!
ADR 0097 invariant 1: the list of `Top` that `parseTops` returns.

FileEntry.lean and TotalFile.lean prove that `parseTops` succeeds exactly when
the start rule `File` of Peg.hpeg derives the whole input, but they erase the
value: their start result carries `()`. This module puts the value back.

The generated parser (packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs)
computes the value of `File <- Ws TopItem* (!.) ^top` as the list that
`PegRt.many peg'rule'TopItem` returns, `TopItem <- TopOne Ws` returns the value
of `TopOne`, and `TopOne <- Verbatim / Directive / Declaration` returns the
value of the first alternative that succeeds. `Peg.Runtime.Internal.many`
adds the value of each call that succeeds with progress, in order, and stops
at the first call that fails or succeeds without progress (a label thrown by
the call propagates). `Chain` is that loop over the derivations of the
recognizer (EnvironmentDerivation.lean), and `Tops` is the whole `File` rule
with it. The value of an item is the value of the chosen alternative's rule
at the start of the item, `value kind start`; these three rules take no
parameters, so their value is a function of the position.

Theorems:
- `invariant1_tops_iff`: some item list derives the input exactly when the
  recognizer accepts the whole input (the existing invariant 1).
- `invariant1_tops_unique`: the item list, and with it the value, is unique.
- `invariant1_tops_linked`: the items follow the leading `Ws` one after
  another, each consumes input, and the last one ends at the end of input.
- `invariant1_parseTops_value`: the public entry, with the value carried
  through `runParser`'s end check and `parseTops`, returns `ts` exactly when
  `ts` is the value list of the derivation.
- `invariant1_parseTops_shape`: that list has one value per item, in order,
  and the i-th value is `value kind start` of the i-th item.
- `runTops_sound`: the executable `runTops`, which the probe runs, returns
  only the item lists of `Tops`.

Ties to the implementation (check-file-tops.sh): the generated `File`,
`TopItem` and `TopOne` rules, `parse` and the runtime `many` are pinned by
`git hash-object`, and FileTopsProbe compares the kinds, the order, the number
and the locations of the items with the `Top` values that the real
`parseTops` returns for every .hpeg file of the repository and for edge cases.

Premises: the rule bodies are those that ExtractConcreteTerminals.hs and
ExtractSelfHostedFile.hs translate (checked elsewhere); the value of
`Verbatim`, `Directive` and `Declaration` at a position is the abstract
`value`, so the contents of each `Top` (the verbatim text, the directive
argument, the alternatives of a rule) are not characterized here.
-/

namespace PegHs.FileTops
open PegHs.EnvironmentEval PegHs.MetaExecution

/-- The alternative of `TopOne` that produced an item. -/
inductive Kind where
  | verbatim
  | directive
  | declaration
  deriving DecidableEq, Repr

theorem file_shape (input : List Char) :
    (context false input).rules (startRule false) =
      .seq (.call 0 4) (.seq (.star (.call 1 1))
        (.label "top" (some "expected a rule, a directive or %{ ... }%")
          (.notAhead (.terminal 0)))) := rfl

theorem topItem_shape (input : List Char) :
    (context false input).rules 1 = .seq (.call 2 2) (.call 3 4) := rfl

theorem topOne_shape (input : List Char) :
    (context false input).rules 2 = .alt (.call 4 11) (.alt (.call 5 12) (.call 6 13)) := rfl

/-- The alternative whose value `TopOne` returns: it succeeded and every
earlier alternative failed. -/
inductive Chosen (ctx : Inputs) (n : Nat) (env : Env) : Kind → Prop where
  | verbatim {rest out} : Derives ctx (.call 4 11) n env (.ok rest out) → Chosen ctx n env .verbatim
  | directive {rest out} : Derives ctx (.call 4 11) n env .fail →
      Derives ctx (.call 5 12) n env (.ok rest out) → Chosen ctx n env .directive
  | declaration {rest out} : Derives ctx (.call 4 11) n env .fail →
      Derives ctx (.call 5 12) n env .fail →
      Derives ctx (.call 6 13) n env (.ok rest out) → Chosen ctx n env .declaration

/-- The call of `TopItem` at `n` with `env` went through the alternative `k`
of `TopOne`. -/
def ItemKind (ctx : Inputs) (n : Nat) (env : Env) (k : Kind) : Prop :=
  ∃ c1 c2, ctx.hooks.enterCall 1 env = some c1 ∧ ctx.hooks.enterCall 2 c1 = some c2 ∧
    Chosen ctx n c2 k

/-- An item: the remaining length at its start, its kind, and the remaining
length after it (and after the `Ws` that `TopItem` reads after `TopOne`). -/
structure Item where
  start : Nat
  kind : Kind
  stop : Nat
  deriving DecidableEq, Repr

/-- The iterations of `many TopItem`, as `Peg.Runtime.Internal.many` runs
them: a call that succeeds with progress adds its item and the loop goes on
from where it stopped; a call that fails or succeeds without progress ends it. -/
inductive Chain (ctx : Inputs) : Nat → Env → List Item → Nat → Env → Prop where
  | stop {n env} : Derives ctx (.call 1 1) n env .fail → Chain ctx n env [] n env
  | still {n env inner} : Derives ctx (.call 1 1) n env (.ok n inner) → Chain ctx n env [] n env
  | next {n env mid inner k items rest final} :
      Derives ctx (.call 1 1) n env (.ok mid inner) → mid < n → ItemKind ctx n env k →
      Chain ctx mid { inner with resultDepth := max env.resultDepth inner.resultDepth }
        items rest final →
      Chain ctx n env (⟨n, k, mid⟩ :: items) rest final

/-- `File <- Ws TopItem* (!.) ^top` on the whole input, with the items of the
repetition. -/
def Tops (input : List Char) (items : List Item) : Prop :=
  ∃ afterWs wsEnv final,
    Derives (context false input) (.call 0 4) input.length {} (.ok afterWs wsEnv) ∧
    Chain (context false input) afterWs { wsEnv with resultDepth := 0 } items 0 final ∧
    Derives (context false input) (.terminal 0) 0 final .fail

/-- The value of `File`: the value of each item's alternative at its start. -/
def fileValue {T : Type} (value : Kind → Nat → T) (items : List Item) : List T :=
  items.map fun item => value item.kind item.start

/-- The derivation of the input has the item list `items` and the value `tops`. -/
def ParsesTo {T : Type} (value : Kind → Nat → T) (input : List Char) (tops : List T) : Prop :=
  ∃ items, Tops input items ∧ tops = fileValue value items

theorem derives_det {ctx : Inputs} {body : Body} {n : Nat} {env : Env} {r1 r2 : Reply}
    (h1 : Derives ctx body n env r1) (h2 : Derives ctx body n env r2) : r1 = r2 := by
  obtain ⟨a, ha⟩ := invariant1_derivation_has_fuel h1
  obtain ⟨b, hb⟩ := invariant1_derivation_has_fuel h2
  exact invariant1_result_unique ctx ha hb

theorem call_ok_inv {ctx : Inputs} {site rule n : Nat} {env : Env} {mid : Nat} {inner : Env}
    (h : Derives ctx (.call site rule) n env (.ok mid inner)) :
    ∃ callee out, ctx.hooks.enterCall site env = some callee ∧
      Derives ctx (ctx.rules rule) n callee (.ok mid out) := by
  generalize hr : Reply.ok mid inner = r at h
  cases h with
  | callMissing _ => cases hr
  | call entered d =>
    rename_i callee r0
    cases r0 with
    | ok rest out =>
      simp only [callResult, Reply.ok.injEq] at hr
      obtain ⟨rfl, _⟩ := hr
      exact ⟨callee, out, entered, d⟩
    | fail => simp [callResult] at hr
    | throwLabel => simp [callResult] at hr

theorem kind_of_item {input : List Char} {n mid : Nat} {env inner : Env}
    (h : Derives (context false input) (.call 1 1) n env (.ok mid inner)) :
    ∃ k, ItemKind (context false input) n env k := by
  obtain ⟨c1, out1, e1, body⟩ := call_ok_inv h
  rw [topItem_shape] at body
  cases body with
  | seqOk first _ =>
    obtain ⟨c2, _, e2, choice⟩ := call_ok_inv first
    rw [topOne_shape] at choice
    cases choice with
    | altLeft verb _ => exact ⟨.verbatim, c1, c2, e1, e2, .verbatim verb⟩
    | altRetry verbFail rest =>
      cases rest with
      | altLeft dir _ => exact ⟨.directive, c1, c2, e1, e2, .directive verbFail dir⟩
      | altRetry dirFail decl => exact ⟨.declaration, c1, c2, e1, e2, .declaration verbFail dirFail decl⟩

theorem chosen_det {ctx : Inputs} {n : Nat} {env : Env} {k1 k2 : Kind}
    (a : Chosen ctx n env k1) (b : Chosen ctx n env k2) : k1 = k2 := by
  cases a with
  | verbatim v =>
    cases b with
    | verbatim => rfl
    | directive vf _ => cases derives_det v vf
    | declaration vf _ _ => cases derives_det v vf
  | directive vf d =>
    cases b with
    | verbatim v => cases derives_det v vf
    | directive => rfl
    | declaration _ df _ => cases derives_det d df
  | declaration vf df _ =>
    cases b with
    | verbatim v => cases derives_det v vf
    | directive _ d => cases derives_det d df
    | declaration => rfl

/-- An item has one kind: the alternatives of `TopOne` are tried in order. -/
theorem kind_det {ctx : Inputs} {n : Nat} {env : Env} {k1 k2 : Kind}
    (a : ItemKind ctx n env k1) (b : ItemKind ctx n env k2) : k1 = k2 := by
  obtain ⟨c1, c2, e1, e2, ch⟩ := a
  obtain ⟨d1, d2, f1, f2, ch'⟩ := b
  obtain rfl := Option.some.inj (e1.symm.trans f1)
  obtain rfl := Option.some.inj (e2.symm.trans f2)
  exact chosen_det ch ch'

theorem chain_loop {ctx : Inputs} {n : Nat} {env : Env} {items : List Item} {rest : Nat}
    {final : Env} (c : Chain ctx n env items rest final) :
    Derives ctx (.starLoop (.call 1 1)) n env (.ok rest final) := by
  induction c with
  | stop failed => exact .loopStop failed
  | still d => exact .loopZero d
  | next d progress _ _ ih => exact .loopMore d progress ih

theorem chain_of_loop (input : List Char) {b : Body} {n : Nat} {env : Env} {r : Reply}
    (h : Derives (context false input) b n env r) :
    b = .starLoop (.call 1 1) → ∀ rest final, r = .ok rest final →
      ∃ items, Chain (context false input) n env items rest final := by
  induction h with
  | loopStop failed =>
    intro hb rest final hr
    cases hb; cases hr
    exact ⟨[], .stop failed⟩
  | loopThrow _ _ => intro _ _ _ hr; cases hr
  | loopZero d _ =>
    intro hb rest final hr
    cases hb; cases hr
    exact ⟨[], .still d⟩
  | loopMore d progress _ _ ih =>
    intro hb rest final hr
    cases hb
    obtain ⟨items, chain⟩ := ih rfl rest final hr
    obtain ⟨k, kind⟩ := kind_of_item d
    exact ⟨_ :: items, .next d progress kind chain⟩
  | _ => intro hb; cases hb

theorem chain_det {ctx : Inputs} {n : Nat} {env : Env} {a b : List Item} {ra rb : Nat}
    {fa fb : Env} (x : Chain ctx n env a ra fa) (y : Chain ctx n env b rb fb) :
    a = b ∧ ra = rb ∧ fa = fb := by
  induction x generalizing b rb fb with
  | stop failed =>
    cases y with
    | stop => exact ⟨rfl, rfl, rfl⟩
    | still d => cases derives_det failed d
    | next d => cases derives_det failed d
  | still d =>
    cases y with
    | stop failed => cases derives_det failed d
    | still => exact ⟨rfl, rfl, rfl⟩
    | next d' progress =>
      have e := (Reply.ok.inj (derives_det d d')).1
      omega
  | next d progress kind _ ih =>
    cases y with
    | stop failed => cases derives_det failed d
    | still d' =>
      have e := (Reply.ok.inj (derives_det d d')).1
      omega
    | next d' _ kind' rest' =>
      obtain ⟨rfl, rfl⟩ := Reply.ok.inj (derives_det d d')
      obtain ⟨rfl, rfl, rfl⟩ := ih rest'
      rw [kind_det kind kind']
      exact ⟨rfl, rfl, rfl⟩

/-- The items follow each other from `n` to `rest`, and each consumes input. -/
def Linked : Nat → List Item → Nat → Prop
  | n, [], rest => n = rest
  | n, item :: items, rest => item.start = n ∧ item.stop < item.start ∧ Linked item.stop items rest

theorem chain_linked {ctx : Inputs} {n : Nat} {env : Env} {items : List Item} {rest : Nat}
    {final : Env} (c : Chain ctx n env items rest final) : Linked n items rest := by
  induction c with
  | stop _ => rfl
  | still _ => rfl
  | next _ progress _ _ ih => exact ⟨rfl, progress, ih⟩

/-- Each item is a successful call of `TopItem` from its start to its stop
that went through the alternative of its kind. -/
theorem chain_items {ctx : Inputs} {n : Nat} {env : Env} {items : List Item} {rest : Nat}
    {final : Env} (c : Chain ctx n env items rest final) :
    ∀ item ∈ items, ∃ e inner, ItemKind ctx item.start e item.kind ∧
      Derives ctx (.call 1 1) item.start e (.ok item.stop inner) := by
  induction c with
  | stop _ => intro _ h; cases h
  | still _ => intro _ h; cases h
  | next d _ kind _ ih =>
    intro item h
    cases h with
    | head => exact ⟨_, _, kind, d⟩
    | tail _ h => exact ih item h

theorem tops_of_file {input : List Char} {env : Env}
    (result : FileResult false input (.ok 0 env)) : ∃ items, Tops input items := by
  have h : Derives (context false input) ((context false input).rules (startRule false))
      input.length {} (.ok 0 env) := result
  rw [file_shape] at h
  cases h with
  | seqOk ws more =>
    cases more with
    | seqOk star tail =>
      generalize hr : Reply.ok 0 env = r at tail
      cases tail with
      | label inner =>
        cases inner with
        | notAhead t =>
          cases t with
          | terminalOk _ _ _ => simp [labelResult, notAheadResult] at hr
          | terminalFail missing =>
            simp only [notAheadResult, labelResult, Reply.ok.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            cases star with
            | star loop =>
              obtain ⟨items, chain⟩ := chain_of_loop input loop rfl _ _ rfl
              exact ⟨items, _, _, _, ws, chain, .terminalFail missing⟩

/-- Invariant 1 with the item list: some item list derives the input exactly
when the recognizer accepts the whole input. -/
theorem invariant1_tops_iff (input : List Char) :
    (∃ items, Tops input items) ↔ ∃ env, FileResult false input (.ok 0 env) := by
  constructor
  · rintro ⟨items, afterWs, wsEnv, final, ws, chain, eof⟩
    refine ⟨final, ?_⟩
    show Derives (context false input) ((context false input).rules (startRule false))
      input.length {} (.ok 0 final)
    rw [file_shape]
    exact .seqOk ws (.seqOk (.star (chain_loop chain)) (.label (.notAhead eof)))
  · rintro ⟨env, result⟩
    exact tops_of_file result

theorem invariant1_tops_unique {input : List Char} {a b : List Item}
    (x : Tops input a) (y : Tops input b) : a = b := by
  obtain ⟨w1, e1, f1, ws1, c1, _⟩ := x
  obtain ⟨w2, e2, f2, ws2, c2, _⟩ := y
  obtain ⟨rfl, rfl⟩ := Reply.ok.inj (derives_det ws1 ws2)
  exact (chain_det c1 c2).1

/-- After the leading `Ws`, the items follow one another and the last one
ends at the end of the input; each is a call of `TopItem` through the
alternative of its kind. -/
theorem invariant1_tops_linked {input : List Char} {items : List Item} (t : Tops input items) :
    ∃ afterWs wsEnv,
      Derives (context false input) (.call 0 4) input.length {} (.ok afterWs wsEnv) ∧
      Linked afterWs items 0 ∧
      ∀ item ∈ items, ∃ e inner, ItemKind (context false input) item.start e item.kind ∧
        Derives (context false input) (.call 1 1) item.start e (.ok item.stop inner) := by
  obtain ⟨afterWs, wsEnv, _, ws, chain, _⟩ := t
  exact ⟨afterWs, wsEnv, ws, chain_linked chain, chain_items chain⟩

theorem invariant1_parsesTo_iff {T : Type} (value : Kind → Nat → T) (input : List Char) :
    (∃ tops, ParsesTo value input tops) ↔ ∃ env, FileResult false input (.ok 0 env) := by
  rw [← invariant1_tops_iff]
  constructor
  · rintro ⟨_, items, h, _⟩
    exact ⟨items, h⟩
  · rintro ⟨items, h⟩
    exact ⟨_, items, h, rfl⟩

theorem invariant1_parsesTo_unique {T : Type} {value : Kind → Nat → T} {input : List Char}
    {a b : List T} (x : ParsesTo value input a) (y : ParsesTo value input b) : a = b := by
  obtain ⟨i1, t1, rfl⟩ := x
  obtain ⟨i2, t2, rfl⟩ := y
  rw [invariant1_tops_unique t1 t2]

/-- The value list has one value per item, in the order of the items, and the
i-th value is the value of the i-th item's alternative at its start. -/
theorem invariant1_parseTops_shape {T : Type} {value : Kind → Nat → T} {input : List Char}
    {tops : List T} (h : ParsesTo value input tops) :
    ∃ items, Tops input items ∧ tops.length = items.length ∧
      ∀ (i : Nat) (hi : i < items.length),
        tops[i]? = some (value items[i].kind items[i].start) := by
  obtain ⟨items, t, rfl⟩ := h
  refine ⟨items, t, by simp [fileValue], fun i hi => ?_⟩
  simp [fileValue, hi]

open Classical in
/-- The start result of `runParser` with the value of `File`. FileEntry.start
is this result with the value erased to `()`. -/
noncomputable def startTops {T : Type} (value : Kind → Nat → T) (input : List Char) :
    Reply → PublicParsing.StartResult (List T)
  | .ok rest _ => .ok (Utf8Terminals.byteOffset input (input.length - rest))
      (if h : ∃ tops, ParsesTo value input tops then h.choose else [])
  | .fail => .fail
  | .throwLabel remaining label message =>
    .throwLabel (Utf8Terminals.byteOffset input (input.length - remaining)) label message

/-- Invariant 1 with the value: the public entry returns `ts` exactly when
`ts` is the value list of the derivation of the whole input. -/
theorem invariant1_parseTops_value {T : Type} (value : Kind → Nat → T) {input : List Char}
    {reply : Reply} (result : FileResult false input reply)
    (diagnostic : PublicParsing.Failure → String) (ts : List T) :
    PublicParsing.entry input.utf8Encode.size (startTops value input reply) diagnostic = .ok ts ↔
      ParsesTo value input ts := by
  rw [PublicParsing.invariant1_parseTops_iff]
  constructor
  · intro h
    cases reply with
    | ok rest env =>
      simp only [startTops, PublicParsing.StartResult.ok.injEq] at h
      obtain ⟨bytes, hts⟩ := h
      obtain rfl := (invariant1_file_end_bytes result).mp bytes
      have ex : ∃ tops, ParsesTo value input tops :=
        (invariant1_parsesTo_iff value input).mpr ⟨env, result⟩
      rw [dite_eq_left_of_eq_true (eq_true ex)] at hts
      rw [← hts]
      exact ex.choose_spec
    | fail => simp [startTops] at h
    | throwLabel => simp [startTops] at h
  · intro h
    obtain ⟨env, accepted⟩ := (invariant1_parsesTo_iff value input).mp ⟨ts, h⟩
    obtain ⟨_, _, unique⟩ := invariant1_file_result false input
    have same := (unique _ result).trans (unique _ accepted).symm
    subst same
    have ex : ∃ tops, ParsesTo value input tops := ⟨ts, h⟩
    simp only [startTops, PublicParsing.StartResult.ok.injEq]
    rw [dite_eq_left_of_eq_true (eq_true ex)]
    exact ⟨by simp [Utf8Terminals.byteOffset], invariant1_parsesTo_unique ex.choose_spec h⟩

/-! The executable form that FileTopsProbe runs. -/

def runChoice (ctx : Inputs) (fuel n : Nat) (env : Env) : Option Kind :=
  match runFuel ctx fuel (.call 4 11) n env with
  | some (.ok _ _) => some .verbatim
  | some .fail =>
    match runFuel ctx fuel (.call 5 12) n env with
    | some (.ok _ _) => some .directive
    | some .fail =>
      match runFuel ctx fuel (.call 6 13) n env with
      | some (.ok _ _) => some .declaration
      | _ => none
    | _ => none
  | _ => none

def runKind (ctx : Inputs) (fuel n : Nat) (env : Env) : Option Kind :=
  match ctx.hooks.enterCall 1 env with
  | none => none
  | some c1 =>
    match ctx.hooks.enterCall 2 c1 with
    | none => none
    | some c2 => runChoice ctx fuel n c2

def runItems (ctx : Inputs) (fuel : Nat) : Nat → Nat → Env → Option (List Item × Nat × Env)
  | 0, _, _ => none
  | steps + 1, n, env =>
    match runFuel ctx fuel (.call 1 1) n env with
    | some .fail => some ([], n, env)
    | some (.ok mid inner) =>
      if mid < n then
        match runKind ctx fuel n env,
          runItems ctx fuel steps mid { inner with resultDepth := max env.resultDepth inner.resultDepth } with
        | some k, some (items, rest, final) => some (⟨n, k, mid⟩ :: items, rest, final)
        | _, _ => none
      else if mid = n then some ([], n, env) else none
    | _ => none

def runTops (input : List Char) (fuel : Nat) : Option (List Item) :=
  match runFuel (context false input) fuel (.call 0 4) input.length {} with
  | some (.ok afterWs wsEnv) =>
    match runItems (context false input) fuel (afterWs + 1) afterWs
        { wsEnv with resultDepth := 0 } with
    | some (items, 0, final) =>
      match runFuel (context false input) fuel (.terminal 0) 0 final with
      | some .fail => some items
      | _ => none
    | _ => none
  | _ => none

theorem runChoice_sound {ctx : Inputs} {fuel n : Nat} {env : Env} {k : Kind}
    (h : runChoice ctx fuel n env = some k) : Chosen ctx n env k := by
  unfold runChoice at h
  cases hv : runFuel ctx fuel (.call 4 11) n env with
  | none => simp [hv] at h
  | some rv =>
    cases rv with
    | ok _ _ =>
      simp only [hv, Option.some.injEq] at h
      subst h
      exact .verbatim (invariant1_runFuel_sound hv)
    | throwLabel => simp [hv] at h
    | fail =>
      cases hd : runFuel ctx fuel (.call 5 12) n env with
      | none => simp [hv, hd] at h
      | some rd =>
        cases rd with
        | ok _ _ =>
          simp only [hv, hd, Option.some.injEq] at h
          subst h
          exact .directive (invariant1_runFuel_sound hv) (invariant1_runFuel_sound hd)
        | throwLabel => simp [hv, hd] at h
        | fail =>
          cases hc : runFuel ctx fuel (.call 6 13) n env with
          | none => simp [hv, hd, hc] at h
          | some rc =>
            cases rc with
            | ok _ _ =>
              simp only [hv, hd, hc, Option.some.injEq] at h
              subst h
              exact .declaration (invariant1_runFuel_sound hv) (invariant1_runFuel_sound hd)
                (invariant1_runFuel_sound hc)
            | fail => simp [hv, hd, hc] at h
            | throwLabel => simp [hv, hd, hc] at h

theorem runKind_sound {ctx : Inputs} {fuel n : Nat} {env : Env} {k : Kind}
    (h : runKind ctx fuel n env = some k) : ItemKind ctx n env k := by
  unfold runKind at h
  cases e1 : ctx.hooks.enterCall 1 env with
  | none => simp [e1] at h
  | some c1 =>
    cases e2 : ctx.hooks.enterCall 2 c1 with
    | none => simp [e1, e2] at h
    | some c2 =>
      simp only [e1, e2] at h
      exact ⟨c1, c2, e1, e2, runChoice_sound h⟩

theorem runItems_sound {ctx : Inputs} {fuel : Nat} :
    ∀ (steps n : Nat) (env : Env) (items : List Item) (rest : Nat) (final : Env),
      runItems ctx fuel steps n env = some (items, rest, final) →
        Chain ctx n env items rest final
  | 0, _, _, _, _, _, h => by simp [runItems] at h
  | steps + 1, n, env, items, rest, final, h => by
    unfold runItems at h
    cases hc : runFuel ctx fuel (.call 1 1) n env with
    | none => simp [hc] at h
    | some r =>
      cases r with
      | fail =>
        simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .stop (invariant1_runFuel_sound hc)
      | throwLabel => simp [hc] at h
      | ok mid inner =>
        simp only [hc] at h
        by_cases lt : mid < n
        · rw [ite_eq_left_of_eq_true _ _ (eq_true lt)] at h
          cases hk : runKind ctx fuel n env with
          | none => simp [hk] at h
          | some k =>
            cases hi : runItems ctx fuel steps mid
                { inner with resultDepth := max env.resultDepth inner.resultDepth } with
            | none => simp [hk, hi] at h
            | some t =>
              obtain ⟨items', rest', final'⟩ := t
              simp only [hk, hi, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact .next (invariant1_runFuel_sound hc) lt (runKind_sound hk)
                (runItems_sound steps _ _ _ _ _ hi)
        · rw [ite_eq_right_of_eq_false _ _ (eq_false lt)] at h
          by_cases eq : mid = n
          · rw [ite_eq_left_of_eq_true _ _ (eq_true eq)] at h
            subst eq
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .still (invariant1_runFuel_sound hc)
          · rw [ite_eq_right_of_eq_false _ _ (eq_false eq)] at h
            cases h

/-- The probe's items are those of the derivation (and, by
`invariant1_tops_unique`, the only ones). -/
theorem runTops_sound {input : List Char} {fuel : Nat} {items : List Item}
    (h : runTops input fuel = some items) : Tops input items := by
  unfold runTops at h
  cases hw : runFuel (context false input) fuel (.call 0 4) input.length {} with
  | none => simp [hw] at h
  | some rw =>
    cases rw with
    | fail => simp [hw] at h
    | throwLabel => simp [hw] at h
    | ok afterWs wsEnv =>
      simp only [hw] at h
      cases hi : runItems (context false input) fuel (afterWs + 1) afterWs
          { wsEnv with resultDepth := 0 } with
      | none => simp [hi] at h
      | some t =>
        obtain ⟨items', rest, final⟩ := t
        cases rest with
        | succ _ => simp [hi] at h
        | zero =>
          simp only [hi] at h
          cases he : runFuel (context false input) fuel (.terminal 0) 0 final with
          | none => simp [he] at h
          | some re =>
            cases re with
            | fail =>
              simp only [he, Option.some.injEq] at h
              subst h
              exact ⟨afterWs, wsEnv, final, invariant1_runFuel_sound hw,
                runItems_sound _ _ _ _ _ _ hi, invariant1_runFuel_sound he⟩
            | ok _ _ => simp [he] at h
            | throwLabel => simp [he] at h

#print axioms invariant1_tops_iff
#print axioms invariant1_tops_unique
#print axioms invariant1_tops_linked
#print axioms invariant1_parseTops_value
#print axioms invariant1_parseTops_shape
#print axioms runTops_sound

end PegHs.FileTops
