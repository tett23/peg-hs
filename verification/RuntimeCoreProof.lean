import TranslatedRuntimeCore
import MemoRecognition
import LabelPropagation
import Utf8Terminals

-- Theorems about TranslatedRuntimeCore, which ExtractRuntimeCore.hs
-- produces from packages/peg-runtime/src/Peg/Runtime/Internal.hs. They tie
-- the runtime that generated parsers call to the models of invariant 1:
-- memo and memoArg satisfy MemoRecognition.memoStep, the strict control
-- combinators follow LabelPropagation's frames and lookahead, lit, cls and
-- anyChar agree with ConcreteTerminal.matchTerm, and runParser succeeds
-- exactly when the start rule ends at the byte length of the input.
--
-- Premises, besides R1-R5 of RuntimeCore.lean:
-- * Strict mode: cfgRecover and cfgCount are off, as in runParser with
--   defaultConfig (the extractor translates both).
-- * BodySpec: started with an empty failure record and no seed
--   dependencies, a rule body returns the same result, failure and
--   dependencies, and leaves the error log, logs and counters alone.
-- * Cache invariant: a table entry at the key is the entry the body
--   evaluates to (MemoRecognition.CacheInvariant).
-- * No growth loop is running (ctxLogs is empty); memoLR and endIteration
--   are not translated, and the metagrammar parsers do not use memoLR
--   (check-memo-meta.sh).
-- * A memo table is a ref into the generated store; reading a table back
--   after a miss needs its lens law.
set_option linter.unusedSimpArgs false
namespace PegHs.RuntimeCore

section Monad
variable {σ α β : Type}

theorem st_bind (x : ST σ α) (f : α → ST σ β) (w : World σ) :
    (x >>= f) w = (x w).bind (fun p => f p.1 p.2) := by
  show (do let (a, s) ← x w; f a s) = _
  cases x w <;> rfl

theorem st_pure (a : α) (w : World σ) : (pure a : ST σ α) w = some (a, w) := rfl

theorem st_map (f : α → β) (x : ST σ α) (w : World σ) :
    (f <$> x) w = (x w).map (fun p => (f p.1, p.2)) := by
  show (do let (a, s) ← x w; pure (f a, s)) = _
  cases x w <;> rfl

end Monad

section Memo
variable {ρ σ α : Type}

structure Strict (c : Ctx ρ) : Prop where
  recover : cfgRecover (ctxConfig c) = false
  count : cfgCount (ctxConfig c) = false

-- What a rule body does when evalBody starts it with an empty failure
-- record and no seed dependencies. Strict bodies leave the error log, the
-- growth-loop logs and the counters alone.
def BodySpec (c : Ctx ρ) (i : Nat) (body : P ρ σ α) (r : Res α) (f : Failure) (d : IntSet) : Prop :=
  ∀ w : World σ, w.fail = NoFailure → w.deps = IS.empty →
    ∃ w', body c i w = some (r, w') ∧ w'.fail = f ∧ w'.deps = d ∧
      w'.errors = w.errors ∧ w'.logs = w.logs ∧ w'.stats = w.stats

theorem evalBody_spec {c : Ctx ρ} {i : Nat} {body : P ρ σ α} {r : Res α} {f : Failure} {d : IntSet}
    (name : Text) (strict : Strict c) (spec : BodySpec c i body r f d) (w : World σ) :
    ∃ w', evalBody c name i body w = some ((r, f, noErrors, d), w') ∧
      w'.fail = mergeFailure w.fail f ∧ w'.deps = IS.union w.deps d ∧
      w'.errors = w.errors ∧ w'.logs = w.logs ∧ w'.stats = w.stats := by
  obtain ⟨w1, run, hf, hd, he, hl, hs⟩ := spec { w with fail := NoFailure, deps := IS.empty } rfl rfl
  refine ⟨{ w1 with fail := mergeFailure w.fail f, deps := IS.union w.deps d }, ?_, rfl, rfl, he, hl, hs⟩
  simp only [evalBody, countEval, saveErrors, strict.count, strict.recover, when, st_bind, st_pure,
    st_map, readSTRef, writeSTRef, ctxFail, ctxDeps, failRef, depsRef, unP, Bool.false_eq_true,
    ↓reduceIte, Option.bind_some]
  rw [run]
  cases r <;> simp [newErrors, restoreErrors, maybe, st_map, st_pure, hf, hd]
  all_goals done

-- The observable outcome of a rule call: the result, and the failure record,
-- seed dependencies, error log, growth-loop logs and counters it leaves.
def Outcome (start : World σ) (r : Res α) (f : Failure) (d : IntSet)
    (run : Option (Res α × World σ)) : Prop :=
  ∃ w', run = some (r, w') ∧ w'.fail = mergeFailure start.fail f ∧
    w'.deps = IS.union start.deps d ∧ w'.errors = start.errors ∧
    w'.logs = start.logs ∧ w'.stats = start.stats

-- R1: a memo table is a ref into the generated store only.
def StoreOnly {τ : Type} (t : Ref σ τ) : Prop := ∃ getter setter, t = storeRef getter setter

theorem union_comm_deps (a b : IntSet) : IS.union a b = IS.union b a := by
  funext x; simp [IS.union, Bool.or_comm]

theorem replay_deps (cur d : IntSet) :
    (if (!IS.null d) = true then IS.union d cur else cur) = IS.union cur d := by
  by_cases h : IS.null d = true
  · have all : ∀ x, d x = false := by
      simpa [IS.null] using h
    simp [h]
    funext x; simp [IS.union, all x]
  · simp at h
    simp [h, union_comm_deps]

theorem replay_outcome (c : Ctx ρ) (w : World σ) (r : Res α) (f : Failure) (d : IntSet) :
    Outcome w r f d (replay c (Entry.Entry r f noErrors d) w) := by
  let deps' := if (!IS.null d) = true then IS.union d w.deps else w.deps
  refine ⟨{ w with fail := mergeFailure w.fail f, deps := deps' }, ?_, rfl, replay_deps _ _, rfl, rfl, rfl⟩
  by_cases h : IS.null d = true <;>
  cases r <;> simp [deps', replay, mergeFail, when, st_bind, st_pure, st_map, modifySTRef', ctxFail, failRef,
    ctxDeps, depsRef, appendSlice, noErrors, h]

theorem memo_outcome (sel : ρ → Table σ α) (rawName : String) (body : P ρ σ α)
    {c : Ctx ρ} {i : Nat} {r : Res α} {f : Failure} {d : IntSet}
    (strict : Strict c) (spec : BodySpec c i body r f d)
    (store : StoreOnly (sel (ctxStore c))) (w : World σ) (noLoop : w.logs = [])
    (cached : IM.lookup i ((sel (ctxStore c)).get w) = none ∨
      IM.lookup i ((sel (ctxStore c)).get w) = some (Entry.Entry r f noErrors d)) :
    Outcome w r f d (memo sel rawName body c i w) := by
  obtain ⟨getter, setter, ht⟩ := store
  cases hm : cfgMemo (ctxConfig c)
  · obtain ⟨w', run, hf, hd, he, hl, hs⟩ := evalBody_spec (memo.name rawName) strict spec w
    refine ⟨w', ?_, hf, hd, he, hl, hs⟩
    simp [memo, hm, st_map, run]
  · rcases cached with miss | hit
    · obtain ⟨w', run, hf, hd, he, hl, hs⟩ := evalBody_spec (memo.name rawName) strict spec w
      refine ⟨{ w' with store := setter (IM.insert i (Entry.Entry r f noErrors d) (getter w'.store)) w'.store },
        ?_, hf, hd, he, hl, hs⟩
      rw [ht] at miss; simp only [storeRef] at miss
      simp only [memo, hm, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
        readSTRef, storeRef, miss, Option.map_some, Option.bind_some, run]
      simp [modifySTRef', storeRef, bumpEntries, strict.count, when, logUndo, readSTRef, ctxLogs,
        logsRef, hl, noLoop, st_bind, st_pure]
      split <;> simp [st_bind, st_pure, readSTRef]
    · rw [ht] at hit; simp only [storeRef] at hit
      simp only [memo, hm, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
        readSTRef, storeRef, hit, Option.map_some, Option.bind_some]
      exact replay_outcome c w r f d

-- A miss stores the entry it evaluated, so the cache invariant holds at the
-- key afterwards (given the lens law of the table's ref).
theorem memo_miss_stores (sel : ρ → Table σ α) (rawName : String) (body : P ρ σ α)
    {c : Ctx ρ} {i : Nat} {r : Res α} {f : Failure} {d : IntSet}
    (strict : Strict c) (spec : BodySpec c i body r f d) (enabled : cfgMemo (ctxConfig c) = true)
    (getter : σ → IntMap (Entry α)) (setter : IntMap (Entry α) → σ → σ)
    (ht : sel (ctxStore c) = storeRef getter setter) (lens : ∀ m s, getter (setter m s) = m)
    (w : World σ) (noLoop : w.logs = []) (miss : IM.lookup i ((sel (ctxStore c)).get w) = none) :
    ∃ w', memo sel rawName body c i w = some (r, w') ∧
      IM.lookup i ((sel (ctxStore c)).get w') = some (Entry.Entry r f noErrors d) := by
  obtain ⟨w', run, -, -, -, hl, -⟩ := evalBody_spec (memo.name rawName) strict spec w
  refine ⟨{ w' with store := setter (IM.insert i (Entry.Entry r f noErrors d) (getter w'.store)) w'.store },
    ?_, by simp [ht, storeRef, lens, IM.lookup, IM.insert]⟩
  rw [ht] at miss; simp only [storeRef] at miss
  simp only [memo, enabled, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
    readSTRef, storeRef, miss, Option.map_some, Option.bind_some, run]
  simp [modifySTRef', storeRef, bumpEntries, strict.count, when, logUndo, readSTRef, ctxLogs,
    logsRef, hl, noLoop, st_bind, st_pure]
  split <;> simp [st_bind, st_pure, readSTRef]

theorem memoArg_outcome {κ : Type} [DecidableEq κ] (sel : ρ → ArgTable σ κ α) (rawName : String)
    (k : κ) (body : P ρ σ α) {c : Ctx ρ} {i : Nat} {r : Res α} {f : Failure} {d : IntSet}
    (strict : Strict c) (spec : BodySpec c i body r f d)
    (store : StoreOnly (sel (ctxStore c))) (w : World σ) (noLoop : w.logs = [])
    (cached : (IM.lookup i ((sel (ctxStore c)).get w) >>= M.lookup k) = none ∨
      (IM.lookup i ((sel (ctxStore c)).get w) >>= M.lookup k) = some (Entry.Entry r f noErrors d)) :
    Outcome w r f d (memoArg sel rawName k body c i w) := by
  obtain ⟨getter, setter, ht⟩ := store
  cases hm : cfgMemo (ctxConfig c)
  · obtain ⟨w', run, hf, hd, he, hl, hs⟩ := evalBody_spec (memoArg.name rawName) strict spec w
    refine ⟨w', ?_, hf, hd, he, hl, hs⟩
    simp [memoArg, hm, st_map, run]
  · rcases cached with miss | hit
    · obtain ⟨w', run, hf, hd, he, hl, hs⟩ := evalBody_spec (memoArg.name rawName) strict spec w
      refine ⟨{ w' with store := setter (IM.insertWith M.union i (M.singleton k (Entry.Entry r f noErrors d))
          (getter w'.store)) w'.store }, ?_, hf, hd, he, hl, hs⟩
      rw [ht] at miss; simp only [storeRef] at miss
      simp only [memoArg, hm, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
        readSTRef, storeRef, miss, Option.map_some, Option.bind_some, run]
      simp [modifySTRef', storeRef, bumpEntries, strict.count, when, logUndo, readSTRef, ctxLogs,
        logsRef, hl, noLoop, st_bind, st_pure]
      split <;> simp [st_bind, st_pure, readSTRef]
    · rw [ht] at hit; simp only [storeRef] at hit
      simp only [memoArg, hm, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, st_bind, st_map,
        readSTRef, storeRef, hit, Option.map_some, Option.bind_some]
      exact replay_outcome c w r f d

-- The projection used by MemoRecognition: the farthest failure offset, the
-- seed dependencies, and the result with its label reduced to a code.
def posOf : Failure → Nat
  | NoFailure => 0
  | Failure.Failure i _ => i

theorem posOf_merge (a b : Failure) : posOf (mergeFailure a b) = max (posOf a) (posOf b) := by
  cases a <;> cases b <;> simp [mergeFailure, posOf]
  rename_i i _ j _
  by_cases h1 : i > j
  · simp [h1, posOf]; omega
  · by_cases h2 : i < j
    · simp [h1, h2, posOf]; omega
    · simp [h1, h2, posOf]; omega

def resultOf (code : Text → Option Text → Nat) : Res α → MemoRecognition.Result α
  | Ok j x => .ok j x
  | Fail => .fail
  | Throw i l m => .throw i (code l m)

def stateOf (w : World σ) : MemoRecognition.State := { failure := posOf w.fail, deps := w.deps }

def entryOf (code : Text → Option Text → Nat) (r : Res α) (f : Failure) (d : IntSet) :
    MemoRecognition.Entry α :=
  { result := resultOf code r, failure := posOf f, deps := d, errors := [] }

theorem outcome_memoStep {κ : Type} [DecidableEq κ] (code : Text → Option Text → Nat)
    {w : World σ} {r : Res α} {f : Failure} {d : IntSet} {run : Option (Res α × World σ)}
    (out : Outcome w r f d run) (enabled : Bool) (evalP : κ → MemoRecognition.Entry α) (key : κ)
    (hev : evalP key = entryOf code r f d) (table : List (κ × MemoRecognition.Entry α))
    (inv : MemoRecognition.CacheInvariant evalP table) :
    ∃ w', run = some (r, w') ∧
      resultOf code r = (MemoRecognition.memoStep enabled evalP table key (stateOf w)).result ∧
      stateOf w' = (MemoRecognition.memoStep enabled evalP table key (stateOf w)).state := by
  obtain ⟨w', hrun, hf, hd, -⟩ := out
  obtain ⟨hr, hs⟩ := MemoRecognition.hit_miss_same_recognition enabled evalP table key (stateOf w) inv
  refine ⟨w', hrun, by rw [hr, hev]; rfl, ?_⟩
  rw [hs, hev]
  simp [stateOf, MemoRecognition.replay, entryOf, hf, hd, posOf_merge]
  rfl

-- The translated memo and memoArg satisfy MemoRecognition's memo step: the
-- memoised result and state equal those of evaluating the body, hit or miss.
theorem invariant1_translated_memo_step (code : Text → Option Text → Nat)
    (sel : ρ → Table σ α) (rawName : String) (body : P ρ σ α)
    {c : Ctx ρ} {i : Nat} {r : Res α} {f : Failure} {d : IntSet}
    (strict : Strict c) (spec : BodySpec c i body r f d)
    (store : StoreOnly (sel (ctxStore c))) (w : World σ) (noLoop : w.logs = [])
    (cached : IM.lookup i ((sel (ctxStore c)).get w) = none ∨
      IM.lookup i ((sel (ctxStore c)).get w) = some (Entry.Entry r f noErrors d))
    (enabled : Bool) (evalP : Nat → MemoRecognition.Entry α) (hev : evalP i = entryOf code r f d)
    (table : List (Nat × MemoRecognition.Entry α)) (inv : MemoRecognition.CacheInvariant evalP table) :
    ∃ w', memo sel rawName body c i w = some (r, w') ∧
      resultOf code r = (MemoRecognition.memoStep enabled evalP table i (stateOf w)).result ∧
      stateOf w' = (MemoRecognition.memoStep enabled evalP table i (stateOf w)).state :=
  outcome_memoStep code (memo_outcome sel rawName body strict spec store w noLoop cached)
    enabled evalP i hev table inv

theorem invariant1_translated_memoArg_step {κ : Type} [DecidableEq κ] (code : Text → Option Text → Nat)
    (sel : ρ → ArgTable σ κ α) (rawName : String) (k : κ) (body : P ρ σ α)
    {c : Ctx ρ} {i : Nat} {r : Res α} {f : Failure} {d : IntSet}
    (strict : Strict c) (spec : BodySpec c i body r f d)
    (store : StoreOnly (sel (ctxStore c))) (w : World σ) (noLoop : w.logs = [])
    (cached : (IM.lookup i ((sel (ctxStore c)).get w) >>= M.lookup k) = none ∨
      (IM.lookup i ((sel (ctxStore c)).get w) >>= M.lookup k) = some (Entry.Entry r f noErrors d))
    (enabled : Bool) (evalP : Nat × κ → MemoRecognition.Entry α) (hev : evalP (i, k) = entryOf code r f d)
    (table : List ((Nat × κ) × MemoRecognition.Entry α)) (inv : MemoRecognition.CacheInvariant evalP table) :
    ∃ w', memoArg sel rawName k body c i w = some (r, w') ∧
      resultOf code r = (MemoRecognition.memoStep enabled evalP table (i, k) (stateOf w)).result ∧
      stateOf w' = (MemoRecognition.memoStep enabled evalP table (i, k) (stateOf w)).state :=
  outcome_memoStep code (memoArg_outcome sel rawName k body strict spec store w noLoop cached)
    enabled evalP (i, k) hev table inv

-- Turning memoisation off does not change the outcome of a call: with the
-- table in either cache state, memo with cfgMemo on, memo with cfgMemo off
-- (in a context whose body behaves the same) and nomemo agree.
theorem invariant1_translated_memo_off_same {c : Ctx ρ} {i : Nat} {body : P ρ σ α}
    {r : Res α} {f : Failure} {d : IntSet} (sel : ρ → Table σ α) (rawName : String)
    (strict : Strict c) (spec : BodySpec c i body r f d) (store : StoreOnly (sel (ctxStore c)))
    (w : World σ) (noLoop : w.logs = [])
    (cached : IM.lookup i ((sel (ctxStore c)).get w) = none ∨
      IM.lookup i ((sel (ctxStore c)).get w) = some (Entry.Entry r f noErrors d))
    (spec' : BodySpec { c with ctxConfig := { ctxConfig c with cfgMemo := false } } i body r f d) :
    Outcome w r f d (memo sel rawName body c i w) ∧
      Outcome w r f d (memo sel rawName body { c with ctxConfig := { ctxConfig c with cfgMemo := false } } i w) ∧
      Outcome w r f d (nomemo rawName body c i w) := by
  have strict' : Strict ({ c with ctxConfig := { ctxConfig c with cfgMemo := false } } : Ctx ρ) :=
    ⟨strict.recover, strict.count⟩
  refine ⟨memo_outcome sel rawName body strict spec store w noLoop cached, ?_, ?_⟩
  · obtain ⟨w', run, hf, hd, he, hl, hs⟩ := evalBody_spec (memo.name rawName) strict' spec' w
    exact ⟨w', by simp [memo, st_map, run], hf, hd, he, hl, hs⟩
  · obtain ⟨w', run, hf, hd, he, hl, hs⟩ := evalBody_spec (nomemo.name rawName) strict spec w
    exact ⟨w', by simp [nomemo, st_map, run], hf, hd, he, hl, hs⟩

end Memo

-- Strict label propagation: in a non-recovering parse, the translated
-- control combinators turn the reply of their child into the reply that
-- LabelPropagation's frames and lookahead give, whatever the state.
section Control
variable {ρ σ α β : Type}
open PegHs.LabelPropagation

attribute [local simp] st_bind st_pure st_map

def toReply : Res α → LabelPropagation.Reply
  | Ok j _ => .ok j ()
  | Fail => .fail
  | Throw i l m => .throwLabel i l m

theorem saveErrors_strict {c : Ctx ρ} (h : cfgRecover (ctxConfig c) = false) (w : World σ) :
    saveErrors c w = some (none, w) := by
  simp [saveErrors, h, st_pure]

@[simp] theorem restoreErrors_none (c : Ctx ρ) (w : World σ) :
    restoreErrors c none w = some ((), w) := rfl

theorem invariant1_translated_bind (p : P ρ σ α) (k : α → P ρ σ β) (c : Ctx ρ) (i : Nat)
    (w w1 : World σ) (r : Res α) (run : p c i w = some (r, w1)) :
    (∀ j x, r = Ok j x → bindP p k c i w = k x c j w1) ∧
    ((∀ j x, r ≠ Ok j x) → bindP p k c i w = some (failed r, w1) ∧
      ∀ next, toReply (failed r : Res β) = unwind (toReply r) (.bind next)) := by
  refine ⟨fun j x h => ?_, fun h => ⟨?_, fun next => ?_⟩⟩
  · subst h; simp [bindP, st_bind, run, unP]
  · cases r with
    | Ok j x => exact absurd rfl (h j x)
    | _ => simp [bindP, st_bind, run, st_pure]
  · cases r with
    | Ok j x => exact absurd rfl (h j x)
    | _ => rfl

theorem invariant1_translated_choice {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false)
    (p q : P ρ σ α) (i : Nat) (w w1 w2 : World σ) (r r2 : Res α)
    (runP : p c i w = some (r, w1)) (runQ : q c i w1 = some (r2, w2)) :
    ∃ r' w', choice [p, q] c i w = some (r', w') ∧
      toReply r' = unwind (toReply r) (.choice (toReply r2)) := by
  cases r with
  | Fail =>
    refine ⟨r2, w2, ?_, rfl⟩
    cases r2 <;> simp [choice, choice.go, st_bind, saveErrors_strict strict, runP, runQ, unP,
      restoreErrors_none, st_pure, st_map]
  | Ok j x =>
    refine ⟨Ok j x, w1, ?_, rfl⟩
    simp [choice, choice.go, st_bind, saveErrors_strict strict, runP, unP, st_pure]
  | Throw t l m =>
    refine ⟨Throw t l m, w1, ?_, rfl⟩
    simp [choice, choice.go, st_bind, saveErrors_strict strict, runP, unP, restoreErrors_none, st_pure]

theorem invariant1_translated_optional {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false)
    (p : P ρ σ α) (i : Nat) (w w1 : World σ) (r : Res α) (runP : p c i w = some (r, w1)) :
    ∃ r', optional p c i w = some (r', w1) ∧ toReply r' = unwind (toReply r) (.optional i) := by
  cases r with
  | Ok j x =>
    exact ⟨Ok j (some x), by simp [optional, st_bind, saveErrors_strict strict, runP, unP, st_pure], rfl⟩
  | Fail =>
    exact ⟨Ok i none, by simp [optional, st_bind, saveErrors_strict strict, runP, unP,
      restoreErrors_none, st_pure], rfl⟩
  | Throw t l m =>
    exact ⟨Throw t l m, by simp [optional, st_bind, saveErrors_strict strict, runP, unP,
      restoreErrors_none, st_pure, failed], rfl⟩

theorem invariant1_translated_label {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false)
    (wrap : Nat → Nat → α → α) (name : String) (msg : Option Text) (recovery : Option (P ρ σ α))
    (p : P ρ σ α) (i : Nat) (w w1 : World σ) (r : Res α)
    (runP : p c i { w with fail := NoFailure } = some (r, w1)) :
    ∃ r', labeledWith wrap name msg recovery p c i w =
        some (r', { w1 with fail := mergeFailure w.fail w1.fail }) ∧
      toReply r' = unwind (toReply r) (.label i name msg) := by
  have run' : p c i { fail := NoFailure, errors := w.errors, deps := w.deps, depth := w.depth, logs := w.logs, stats := w.stats, store := w.store } = some (r, w1) := runP
  cases r with
  | Fail =>
    refine ⟨Throw i name msg, ?_, rfl⟩
    cases recovery <;> simp [labeledWith, st_bind, saveErrors_strict strict, run', unP, readSTRef,
      writeSTRef, ctxFail, failRef, restoreErrors_none, st_pure, strict, labeledWith.l, T.pack]
  | Ok j x =>
    exact ⟨Ok j x, by simp [labeledWith, st_bind, saveErrors_strict strict, run', unP, readSTRef,
      writeSTRef, ctxFail, failRef, st_pure], rfl⟩
  | Throw t l m =>
    exact ⟨Throw t l m, by simp [labeledWith, st_bind, saveErrors_strict strict, run', unP, readSTRef,
      writeSTRef, ctxFail, failRef, st_pure], rfl⟩

theorem invariant1_translated_lookahead {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false)
    (p : P ρ σ α) (i : Nat) (w w1 : World σ) (r : Res α) (runP : p c i w = some (r, w1)) :
    (∃ r', andP p c i w = some (r', w1) ∧ toReply r' = look true i (toReply r)) ∧
    (∃ r', notP p c i w = some (r', { w1 with fail := w.fail }) ∧
      toReply r' = look false i (toReply r)) := by
  cases r with
  | Ok j x =>
    exact ⟨⟨Ok i (), by simp [andP, st_bind, saveErrors_strict strict, runP, unP, restoreErrors_none,
      st_pure], rfl⟩, ⟨Fail, by simp [notP, st_bind, saveErrors_strict strict, runP, unP, readSTRef,
      writeSTRef, ctxFail, failRef, restoreErrors_none, st_pure], rfl⟩⟩
  | Fail =>
    exact ⟨⟨Fail, by simp [andP, st_bind, saveErrors_strict strict, runP, unP, restoreErrors_none,
      st_pure], rfl⟩, ⟨Ok i (), by simp [notP, st_bind, saveErrors_strict strict, runP, unP, readSTRef,
      writeSTRef, ctxFail, failRef, restoreErrors_none, st_pure], rfl⟩⟩
  | Throw t l m =>
    exact ⟨⟨Fail, by simp [andP, st_bind, saveErrors_strict strict, runP, unP, restoreErrors_none,
      st_pure], rfl⟩, ⟨Ok i (), by simp [notP, st_bind, saveErrors_strict strict, runP, unP, readSTRef,
      writeSTRef, ctxFail, failRef, restoreErrors_none, st_pure], rfl⟩⟩


-- One step of the repetition loop shared by many: a label thrown by the
-- child stops the loop, a success that consumes input continues it, and
-- anything else ends it with the values collected so far, in order.
theorem invariant1_translated_many_step {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false)
    (p : P ρ σ α) (j : Nat) (acc : List α) (w w1 : World σ) (r : Res α)
    (runP : p c j w = some (r, w1)) :
    manyGo p c j acc w =
      match r with
      | Ok k x => if k > j then manyGo p c k (x :: acc) w1 else some (Ok j acc.reverse, w1)
      | Throw t l m => some (Throw t l m, w1)
      | Fail => some (Ok j acc.reverse, w1) := by
  rw [manyGo]
  cases r with
  | Ok k x =>
    by_cases h : k > j <;> simp [st_bind, saveErrors_strict strict, runP, unP, h,
      restoreErrors_none, st_pure]
  | _ => simp [st_bind, saveErrors_strict strict, runP, unP, restoreErrors_none, st_pure]

theorem invariant1_translated_skipMany_step {c : Ctx ρ} (strict : cfgRecover (ctxConfig c) = false)
    (p : P ρ σ α) (j : Nat) (w w1 : World σ) (r : Res α)
    (runP : p c j w = some (r, w1)) :
    skipManyGo p c j w =
      match r with
      | Ok k _ => if k > j then skipManyGo p c k w1 else some (Ok j (), w1)
      | Throw t l m => some (Throw t l m, w1)
      | Fail => some (Ok j (), w1) := by
  rw [skipManyGo]
  cases r with
  | Ok k x =>
    by_cases h : k > j <;> simp [st_bind, saveErrors_strict strict, runP, unP, h,
      restoreErrors_none, st_pure]
  | _ => simp [st_bind, saveErrors_strict strict, runP, unP, restoreErrors_none, st_pure]

end Control

-- The public strict entry: runParser runs the start rule at offset 0 in the
-- context newCtx builds, with recovery off, and succeeds exactly when the
-- start rule's match ends at the byte length of the input. A thrown label
-- reaches the ParseError with its message; other failures carry no label.
section Entry
variable {ρ σ α : Type}

def startCtx (cfg : Config) (st : ρ) (input : Text) : Ctx ρ :=
  { ctxInput := input, ctxLen := TU.lengthWord8 input, ctxStore := st, ctxConfig := { cfg with cfgRecover := false } }

def startWorld (w : World σ) : World σ :=
  { w with fail := NoFailure, errors := ErrLog.ErrLog 0 [], logs := [], deps := IS.empty, depth := 0, stats := emptyStats }

-- The ParseError that currentError builds from a failure record.
def errorOf (f : Failure) (label msg : Option Text) : ParseError :=
  match f with
  | NoFailure => ParseError.mk 0 S.empty label msg
  | Failure.Failure i xs => ParseError.mk i xs label msg

theorem currentError_run (ctx : Ctx ρ) (w : World σ) (label msg : Option Text) :
    currentError ctx label msg w = some (errorOf w.fail label msg, w) := by
  cases h : w.fail <;> simp [currentError, st_bind, readSTRef, ctxFail, failRef, h, errorOf, posAt, st_pure]

theorem runParser_run (cfg : Config) (mkStore : ST σ ρ) (start : P ρ σ α)
    (input : Text) (heap : World σ) (st : ρ) (w0 : World σ) (alloc : mkStore heap = some (st, w0))
    (r : Res α) (w1 : World σ) (run : start (startCtx cfg st input) 0 (startWorld w0) = some (r, w1)) :
    runParser cfg mkStore start input heap =
      some (match r with
        | Ok j x => if j = TU.lengthWord8 input then .ok x
          else .error (errorOf (mergeFailure w1.fail (Failure.Failure j (S.singleton ExpectedEnd))) none none)
        | Throw _ l m => .error (errorOf w1.fail (some l) m)
        | Fail => .error (errorOf w1.fail none none), w1.stats) := by
  have run' : start (startCtx cfg st input) 0 { fail := NoFailure, errors := ErrLog.ErrLog 0 [], deps := IS.empty, depth := 0, logs := [], stats := emptyStats, store := w0.store } = some (r, w1) := run
  have ctx : ({ ctxInput := input, ctxLen := TU.lengthWord8 input, ctxStore := st, ctxConfig := { cfg with cfgRecover := false } } : Ctx ρ) = startCtx cfg st input := rfl
  simp only [runParser, runST, newCtx, newFailRef, newErrorsRef, newLogsRef, newDepsRef, newDepthRef,
    newStatsRef, writeSTRef, failRef, errorsRef, logsRef, depsRef, depthRef, statsRef, alloc,
    st_bind, st_pure, st_map, unP, Option.bind_some, ctx, run', StateT.run]
  cases r with
  | Ok j x =>
    by_cases h : j = TU.lengthWord8 input
    · subst h; simp [readSTRef, ctxStats, statsRef, startCtx, st_map, st_bind, st_pure]
    · simp [h, startCtx, mergeFail, modifySTRef', ctxFail, failRef, currentError_run, readSTRef,
        ctxStats, statsRef, st_map, st_bind, st_pure]
  | Throw t l m => simp [currentError_run, readSTRef, ctxStats, statsRef, st_map, st_bind, st_pure]
  | Fail => simp [currentError_run, readSTRef, ctxStats, statsRef, st_map, st_bind, st_pure]

theorem invariant1_translated_runParser (cfg : Config) (mkStore : ST σ ρ) (start : P ρ σ α)
    (input : Text) (heap : World σ) (st : ρ) (w0 : World σ) (alloc : mkStore heap = some (st, w0))
    (r : Res α) (w1 : World σ) (run : start (startCtx cfg st input) 0 (startWorld w0) = some (r, w1)) :
    ∃ res s, runParser cfg mkStore start input heap = some (res, s) ∧
      (∀ x, res = .ok x ↔ r = Ok (TU.lengthWord8 input) x) ∧
      (∀ t l m, r = Throw t l m →
        ∃ e : ParseError, res = .error e ∧ e.parseErrorLabel = some l ∧ e.parseErrorMessage = m) ∧
      ((r = Fail ∨ ∃ j x, r = Ok j x ∧ j ≠ TU.lengthWord8 input) →
        ∃ e : ParseError, res = .error e ∧ e.parseErrorLabel = none) := by
  rw [runParser_run cfg mkStore start input heap st w0 alloc r w1 run]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  · intro y
    cases r with
    | Ok j x =>
      by_cases h : j = TU.lengthWord8 input
      · subst h; simp
      · simp [h]
    | Throw => simp
    | Fail => simp
  · intro t l m h; subst h
    exact ⟨_, rfl, by cases w1.fail <;> rfl, by cases w1.fail <;> rfl⟩
  · rintro (h | ⟨j, x, h, ne⟩)
    · subst h; exact ⟨_, rfl, by cases w1.fail <;> rfl⟩
    · subst h
      refine ⟨errorOf (mergeFailure w1.fail (Failure.Failure j (S.singleton ExpectedEnd))) none none, by simp [ne], ?_⟩
      cases mergeFailure w1.fail (Failure.Failure j (S.singleton ExpectedEnd)) <;> rfl

end Entry

-- Terminals over an input of scalar values, at a scalar boundary. The
-- translated byte-level tests agree with ConcreteTerminal.matchTerm, which
-- Utf8Terminals.ByteStep and the recognition proofs of invariant 1 use.
section Terminals
variable {ρ σ : Type}
open PegHs.ConcreteTerminal

def OnInput (c : Ctx ρ) (input : List Char) : Prop :=
  ctxInput c = String.ofList input ∧ ctxLen c = TU.lengthWord8 (ctxInput c)

theorem bytes_ofList (xs : List Char) : (String.ofList xs).toUTF8 = xs.utf8Encode := by
  simp

theorem length_ofList (xs : List Char) : TU.lengthWord8 (String.ofList xs) = xs.utf8Encode.size := by
  simp [TU.lengthWord8, ← String.size_toByteArray]

theorem size_cons_split (before : List Char) (ch : Char) (after : List Char) :
    (before ++ ch :: after).utf8Encode.size =
      before.utf8Encode.size + ch.utf8Size + after.utf8Encode.size := by
  rw [List.utf8Encode_append, ByteArray.size_append, List.utf8Encode_cons, ByteArray.size_append]
  simp [List.utf8Encode_singleton]
  omega

theorem decode_at (before : List Char) (ch : Char) (after : List Char) :
    (before ++ ch :: after).utf8Encode.utf8DecodeChar? before.utf8Encode.size = some ch := by
  rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract, List.utf8Encode_append,
    ByteArray.size_append, ByteArray.extract_append_eq_right rfl rfl]
  simp

theorem iter_at {c : Ctx ρ} {before : List Char} {ch : Char} {after : List Char}
    (h : OnInput c (before ++ ch :: after)) :
    TU.iter (ctxInput c) before.utf8Encode.size = ⟨ch, ch.utf8Size⟩ := by
  rw [h.1]
  simp only [TU.iter, bytes_ofList, decode_at]

theorem before_lt_len {c : Ctx ρ} {before : List Char} {ch : Char} {after : List Char}
    (h : OnInput c (before ++ ch :: after)) : before.utf8Encode.size < ctxLen c := by
  rw [h.2, h.1, length_ofList, size_cons_split]
  have := ch.utf8Size_pos
  omega

theorem next_offset (before : List Char) (ch : Char) :
    before.utf8Encode.size + ch.utf8Size = (before ++ [ch]).utf8Encode.size := by
  rw [List.utf8Encode_append, ByteArray.size_append]
  simp [List.utf8Encode_singleton]

-- failAt fails and moves the farthest failure to at least i.
theorem failAt_run {α : Type} (ctx : Ctx ρ) (i : Nat) (e : Expected) (w : World σ) :
    ∃ f, failAt (α := α) ctx i e w = some (Fail, { w with fail := f }) ∧ posOf f = max (posOf w.fail) i := by
  cases h : w.fail with
  | NoFailure =>
    refine ⟨mergeFailure NoFailure (Failure.Failure i (S.singleton e)), ?_, by rw [posOf_merge]; simp [posOf]⟩
    simp [failAt, st_bind, readSTRef, ctxFail, failRef, h, writeSTRef, st_pure, st_map]
  | Failure j xs =>
    by_cases far : j > i
    · refine ⟨Failure.Failure j xs, ?_, by simp [posOf]; omega⟩
      have hw : w = { w with fail := Failure.Failure j xs } := by cases w; simp_all
      conv => rhs; rw [← hw]
      simp [failAt, st_bind, readSTRef, ctxFail, failRef, h, far, st_pure]
    · refine ⟨mergeFailure (Failure.Failure j xs) (Failure.Failure i (S.singleton e)), ?_,
        by rw [posOf_merge]; simp [posOf]⟩
      simp [failAt, st_bind, readSTRef, ctxFail, failRef, h, far, writeSTRef, st_pure, st_map]

theorem invariant1_translated_anyChar {c : Ctx ρ} {before : List Char} {ch : Char} {after : List Char}
    (h : OnInput c (before ++ ch :: after)) (w : World σ) :
    anyChar c before.utf8Encode.size w = some (Ok (before ++ [ch]).utf8Encode.size (), w) := by
  simp [anyChar, before_lt_len h, iter_at h, next_offset, st_pure]

theorem invariant1_translated_anyChar_eof {c : Ctx ρ} {input : List Char}
    (h : OnInput c input) (w : World σ) :
    ∃ f, anyChar c input.utf8Encode.size w = some (Fail, { w with fail := f }) ∧
      posOf f = max (posOf w.fail) input.utf8Encode.size := by
  have eq : ctxLen c = input.utf8Encode.size := by rw [h.2, h.1, length_ofList]
  simp only [anyChar, eq, Nat.lt_irrefl, ↓reduceIte]
  exact failAt_run c _ _ w

theorem char_le (a b : Char) : decide (a ≤ b) = decide (a.toNat ≤ b.toNat) :=
  decide_eq_decide.mpr (Char.le_def.trans UInt32.le_iff_toNat_le)

theorem class_test (ranges : List (Char × Char)) (ch : Char) :
    ranges.any (fun (a, b) => decide (a ≤ ch) && decide (ch ≤ b)) = classHas ranges ch := by
  unfold classHas
  congr 1

theorem invariant1_translated_cls (ranges : List (Char × Char)) (orig : String) {c : Ctx ρ}
    {before : List Char} {ch : Char} {after : List Char}
    (h : OnInput c (before ++ ch :: after)) (w : World σ) :
    (matchTerm (.cls ranges) (ch :: after) = some after →
      cls ranges orig c before.utf8Encode.size w = some (Ok (before ++ [ch]).utf8Encode.size (), w)) ∧
    (matchTerm (.cls ranges) (ch :: after) = none →
      ∃ f, cls ranges orig c before.utf8Encode.size w = some (Fail, { w with fail := f }) ∧
        posOf f = max (posOf w.fail) before.utf8Encode.size) := by
  constructor
  · intro m
    have test : classHas ranges ch = true := by
      by_cases t : classHas ranges ch = true
      · exact t
      · simp [matchTerm, t] at m
    simp [cls, before_lt_len h, iter_at h, class_test, test, next_offset, st_pure]
  · intro m
    have test : classHas ranges ch = false := by
      by_cases t : classHas ranges ch = true
      · simp [matchTerm, t] at m
      · simpa using t
    simp only [cls, before_lt_len h, ↓reduceIte, iter_at h, class_test, test, Bool.false_eq_true]
    exact failAt_run c _ _ w

theorem get_in (a : ByteArray) (k : Nat) (h : k < a.size) : TA.unsafeIndex a k = a[k] := by
  rcases a with ⟨bs⟩
  show bs[k]! = bs[k]'h
  exact getElem!_pos bs k h

-- The byte loop of lit compares every byte from k to the literal's length.
theorem lit_go_iff (s : String) (arr : ByteArray) (off i k : Nat) (hk : k ≤ lit.n s) :
    lit.go s arr off i k = true ↔
      ∀ m, k ≤ m → m < lit.n s →
        TA.unsafeIndex arr (off + i + m) = TA.unsafeIndex (lit.tarr s) (lit.toff + m) := by
  induction k using lit.go.induct s arr off i with
  | case1 k eq =>
    have : k = lit.n s := by simpa using eq
    rw [lit.go]; simp only [eq, ↓reduceIte, true_iff]
    intro m km mn; omega
  | case2 k ne lt same ih =>
    rw [lit.go]; simp only [ne, lt, same, ↓reduceIte, Bool.false_eq_true, dite_true]
    rw [ih (by omega)]
    constructor
    · intro rest m km mn
      by_cases e : m = k
      · subst e; simpa using same
      · exact rest m (by omega) mn
    · intro all m km mn; exact all m (by omega) mn
  | case3 k ne lt diff =>
    rw [lit.go]; simp only [ne, lt, diff, ↓reduceIte, Bool.false_eq_true, dite_true, false_iff]
    intro all
    exact diff (by simpa using all k (Nat.le_refl k) lt)
  | case4 k ne nlt =>
    exfalso; have : k ≠ lit.n s := by simpa using ne
    omega

theorem prefix_of_bytes (S U : ByteArray) (hn : S.size ≤ U.size)
    (same : ∀ m (h : m < S.size), U[m]'(by omega) = S[m]) : S ++ U.extract S.size U.size = U := by
  apply ByteArray.ext
  apply Array.ext
  · simp [ByteArray.data_append, ByteArray.data_extract]; omega
  · intro idx h1 h2
    have h1' : idx < (S ++ U.extract S.size U.size).size := h1
    show (S ++ U.extract S.size U.size)[idx]'h1' = U[idx]'h2
    by_cases lt : idx < S.size
    · rw [ByteArray.getElem_append_left lt, same idx lt]
    · rw [ByteArray.getElem_append_right (by omega), ByteArray.getElem_extract]
      congr 1; omega

-- lit succeeds at a scalar boundary exactly when ConcreteTerminal's literal
-- matcher accepts the rest of the input.
theorem invariant1_translated_lit_match (s : String) {c : Ctx ρ} {pre suffix : List Char}
    (h : OnInput c (pre ++ suffix)) :
    lit.matchesAt s (ctxInput c) pre.utf8Encode.size = true ↔
      ∃ tail, matchTerm (.lit s.toList) suffix = some tail := by
  rw [← Utf8Terminals.invariant1_byte_literal_prefix, String.utf8Encode_toList, h.1]
  have nS : lit.n s = s.toByteArray.size := by
    simp [lit.n, TU.lengthWord8, T.pack, String.size_toByteArray]
  have tS : lit.tarr s = s.toByteArray := by simp [lit.tarr, T.pack]
  have input : (String.ofList (pre ++ suffix)).toUTF8 = pre.utf8Encode ++ suffix.utf8Encode := by
    simp [List.utf8Encode_append]
  simp only [lit.matchesAt, length_ofList, Bool.and_eq_true, decide_eq_true_eq]
  rw [input, lit_go_iff _ _ _ _ _ (Nat.zero_le _), tS, nS]
  simp only [List.utf8Encode_append, ByteArray.size_append, Nat.zero_add, Nat.zero_le, true_imp_iff,
    lit.toff]
  constructor
  · rintro ⟨room, same⟩
    refine ⟨_, prefix_of_bytes _ _ (by omega) fun m hm => ?_⟩
    have := same m hm
    rw [get_in _ _ (by rw [ByteArray.size_append]; omega), get_in _ _ hm,
      ByteArray.getElem_append_right (by omega)] at this
    simpa using this
  · rintro ⟨tail, eq⟩
    have room : s.toByteArray.size ≤ suffix.utf8Encode.size := by
      rw [← eq, ByteArray.size_append]; omega
    refine ⟨by omega, fun m hm => ?_⟩
    rw [get_in _ _ (by rw [ByteArray.size_append]; omega), get_in _ _ hm,
      ByteArray.getElem_append_right (by omega)]
    have get := congrArg (fun b : ByteArray => b[m]!) eq
    rw [getElem!_pos _ m (by rw [ByteArray.size_append]; omega), getElem!_pos _ m (by omega),
      ByteArray.getElem_append_left hm] at get
    simpa using get.symm

theorem invariant1_translated_lit (s orig : String) {c : Ctx ρ} {pre suffix : List Char}
    (h : OnInput c (pre ++ suffix)) (w : World σ) :
    ((∃ tail, matchTerm (.lit s.toList) suffix = some tail) →
      lit s orig c pre.utf8Encode.size w =
        some (Ok (pre.utf8Encode.size + s.toList.utf8Encode.size) (), w)) ∧
    (matchTerm (.lit s.toList) suffix = none →
      ∃ f, lit s orig c pre.utf8Encode.size w = some (Fail, { w with fail := f }) ∧
        posOf f = max (posOf w.fail) pre.utf8Encode.size) := by
  constructor
  · intro m
    have yes := (invariant1_translated_lit_match s h).mpr m
    simp [lit, yes, st_pure, lit.n, TU.lengthWord8, T.pack, String.size_toByteArray,
      String.utf8Encode_toList]
  · intro none'
    have no : lit.matchesAt s (ctxInput c) pre.utf8Encode.size = false := by
      by_cases t : lit.matchesAt s (ctxInput c) pre.utf8Encode.size = true
      · obtain ⟨tail, m⟩ := (invariant1_translated_lit_match s h).mp t
        rw [none'] at m; cases m
      · simpa using t
    simp only [lit, no, Bool.false_eq_true, ↓reduceIte]
    exact failAt_run c _ _ w

end Terminals

section Entry
variable {ρ σ α : Type}

def toStart : Res α → PublicParsing.StartResult α
  | Ok j x => .ok j x
  | Fail => .fail
  | Throw i l m => .throwLabel i l m

-- The translated strict entry succeeds with a value exactly when the
-- PublicParsing projection of its start rule does.
theorem invariant1_translated_runParser_entry (cfg : Config) (mkStore : ST σ ρ) (start : P ρ σ α)
    (input : Text) (heap : World σ) (st : ρ) (w0 : World σ) (alloc : mkStore heap = some (st, w0))
    (r : Res α) (w1 : World σ) (run : start (startCtx cfg st input) 0 (startWorld w0) = some (r, w1))
    (d : PublicParsing.Failure → String) :
    ∃ res s, runParser cfg mkStore start input heap = some (res, s) ∧
      ∀ x, res = .ok x ↔ PublicParsing.entry (TU.lengthWord8 input) (toStart r) d = .ok x := by
  obtain ⟨res, s, eq, ok, -⟩ := invariant1_translated_runParser cfg mkStore start input heap st w0 alloc r w1 run
  refine ⟨res, s, eq, fun x => (ok x).trans ?_⟩
  rw [PublicParsing.invariant1_parseTops_iff]
  cases r <;> simp [toStart]

end Entry

#print axioms invariant1_translated_memo_step
#print axioms invariant1_translated_memoArg_step
#print axioms invariant1_translated_memo_off_same
#print axioms memo_miss_stores
#print axioms invariant1_translated_bind
#print axioms invariant1_translated_choice
#print axioms invariant1_translated_optional
#print axioms invariant1_translated_label
#print axioms invariant1_translated_lookahead
#print axioms invariant1_translated_many_step
#print axioms invariant1_translated_skipMany_step
#print axioms invariant1_translated_runParser
#print axioms invariant1_translated_runParser_entry
#print axioms invariant1_translated_anyChar
#print axioms invariant1_translated_anyChar_eof
#print axioms invariant1_translated_cls
#print axioms invariant1_translated_lit

end PegHs.RuntimeCore
