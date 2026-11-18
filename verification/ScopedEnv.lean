import MetaExecution
import EnvProjection
import EnvironmentFuel

/-!
Rule bodies read only what they bind (premise R7 of verification/README.md,
the memo key and the bindings of a repetition).

The model passes one environment through a body: a call without arguments
hands the caller's environment to the callee. The generated Haskell does
not: a rule sees only its parameter and the variables it binds. This module
shows that the difference is not observable in the metagrammar. (The other
difference, that `many` and `skipMany` drop the variables of an iteration
while the model hands them to the next iteration, is LoopBindings.lean.)

`check` is a static analysis of a body. A `Know` lists what two environments
are known to agree on: the depth parameter, the result depth, and the
captures and value depths of some names. `check` follows the body, adds the
names it binds, and fails when a predicate, an action or a call argument
reads something that is not known. A rule called without arguments must
check from `Know.bottom`, where nothing is known; a rule called with an
argument starts from an environment that is the same for every caller.

Theorems:
- `invariant1_scope_sound`: if a body checks from `k`, two runs from
  environments that agree on `k` return replies of the same shape at the same
  positions, with environments that agree on the `Know` that `check`
  returns.
- `invariant1_meta_scoped`: every rule of the strict metagrammar checks, and
  ends with its result depth known.
- `invariant1_plain_call_independent`: a rule of the strict metagrammar
  called without arguments returns, from any two environments, replies with
  the same positions, labels and result depth.

Premises: none besides those of MetaExecution.lean. The analysis is checked
by `decide` on the extracted rule table.
-/

set_option linter.unusedSimpArgs false
namespace PegHs.ScopedEnv
open PegHs.EnvironmentEval PegHs.EnvProjection PegHs.MetaExecution PegHs.ConcreteTerminal

/-- What two environments are known to agree on. -/
structure Know where
  depth : Bool
  result : Bool
  caps : List String
  vals : List String
  deriving DecidableEq, Repr

def Know.bottom : Know := ⟨false, false, [], []⟩

def Know.meet (a b : Know) : Know :=
  ⟨a.depth && b.depth, a.result && b.result, a.caps.filter b.caps.contains,
    a.vals.filter b.vals.contains⟩

/-- `b` knows at least what `a` knows. -/
def Know.le (a b : Know) : Bool :=
  (!a.depth || b.depth) && (!a.result || b.result) && a.caps.all b.caps.contains &&
    a.vals.all b.vals.contains

def predReads (k : Know) : SemanticPredicates.Kind → Bool
  | .depth => k.depth
  | kind => (PredicateBindings.captureName kind).all k.caps.contains

def actionReads (k : Know) : DepthAction → Bool
  | .zero => true
  | .copy n | .successor n => k.vals.contains n
  | .add a b | .maximum a b => k.vals.contains a && k.vals.contains b
  | .plusIfBound v p => k.vals.contains v && k.caps.contains p

def argReads (k : Know) : EnvironmentDepth.DepthArg → Bool
  | .zero => true
  | .current | .successor => k.depth
  | .plusValue n => k.depth && k.vals.contains n

section Check
variable (sites : Nat → Option (SemanticPredicates.Kind × Bool))
  (actions : Nat → Option DepthAction) (calls : Nat → Option EnvironmentDepth.CallSite)
  (plain : Nat → Bool)

/-- The analysis. `plain rule` marks the rules that start from `Know.bottom`:
a call without arguments may only target them. -/
def check : Body → Know → Option Know
  | .eps, k => some { k with result := true }
  | .terminal _, k => some { k with result := true }
  | .predicate site, k => match sites site with
      | none => some { k with result := true }
      | some (kind, _) => if predReads k kind then some { k with result := true } else none
  | .call site rule, k => match calls site with
      | some (_, _, []) => if plain rule then some { k with result := true } else none
      | some (_, _, [src]) => match EnvironmentDepth.depthArgOf src with
          | some a => if argReads k a then some { k with result := true } else none
          | none => some { k with result := true }
      | _ => some { k with result := true }
  | .seq a b, k => do check b (← check a k)
  | .alt a b, k => do
      let x ← check a k
      let y ← check b k
      pure (x.meet y)
  | .ahead a, k | .notAhead a, k => do let _ ← check a k; pure k
  | .star a, k => do
      let k := { k with result := true }
      let x ← check a k
      if k.le { x with result := x.result && k.result } then pure k else none
  | .starLoop a, k => do
      let x ← check a k
      if k.le { x with result := x.result && k.result } then pure k else none
  | .label _ _ a, k | .capture a, k => check a k
  | .bind _ name a, k => do
      let x ← check a k
      pure { x with caps := name :: x.caps,
                    vals := if x.result then name :: x.vals else x.vals.filter (· != name) }
  | .action site a, k => do
      let x ← check a k
      match actions site with
      | none => pure { x with result := true }
      | some act => if actionReads x act then pure { x with result := true } else none

end Check

/-! ## The relation -/

structure Rel (k : Know) (a b : Env) : Prop where
  depth : k.depth = true → a.depth = b.depth
  result : k.result = true → a.resultDepth = b.resultDepth
  caps : ∀ n, n ∈ k.caps → a.lookup n = b.lookup n ∧ hasCapture a n = hasCapture b n
  vals : ∀ n, n ∈ k.vals → a.valueDepth n = b.valueDepth n

theorem Rel.refl (k : Know) (a : Env) : Rel k a a :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

theorem rel_bottom (a b : Env) : Rel Know.bottom a b :=
  ⟨fun h => (by cases h), fun h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem Rel.mono {k k' : Know} {a b : Env} (r : Rel k' a b) (le : k.le k' = true) : Rel k a b := by
  simp only [Know.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem] at le
  obtain ⟨⟨⟨hd, hr⟩, hc⟩, hv⟩ := le
  refine ⟨fun h => r.depth ?_, fun h => r.result ?_, fun n m => r.caps n (hc n m),
    fun n m => r.vals n (hv n m)⟩
  · rcases hd with e | e
    · rw [h] at e; cases e
    · exact e
  · rcases hr with e | e
    · rw [h] at e; cases e
    · exact e

theorem Rel.meet_left {k k' : Know} {a b : Env} (r : Rel k a b) : Rel (k.meet k') a b :=
  ⟨fun h => r.depth (by simp [Know.meet] at h; exact h.1),
    fun h => r.result (by simp [Know.meet] at h; exact h.1),
    fun n m => r.caps n (by simp [Know.meet] at m; exact m.1),
    fun n m => r.vals n (by simp [Know.meet] at m; exact m.1)⟩

theorem Rel.meet_right {k k' : Know} {a b : Env} (r : Rel k' a b) : Rel (k.meet k') a b :=
  ⟨fun h => r.depth (by simp [Know.meet] at h; exact h.2),
    fun h => r.result (by simp [Know.meet] at h; exact h.2),
    fun n m => r.caps n (by simp [Know.meet] at m; exact m.2),
    fun n m => r.vals n (by simp [Know.meet] at m; exact m.2)⟩

theorem Rel.setResult {k : Know} {a b : Env} (r : Rel k a b) (x y : Nat) (same : x = y) :
    Rel { k with result := true } { a with resultDepth := x } { b with resultDepth := y } :=
  ⟨r.depth, fun _ => same, r.caps, r.vals⟩

theorem Rel.loop {k x : Know} {a b n1 n2 : Env} (r : Rel k a b) (rn : Rel x n1 n2)
    (le : k.le { x with result := x.result && k.result } = true) :
    Rel k { n1 with resultDepth := max a.resultDepth n1.resultDepth }
      { n2 with resultDepth := max b.resultDepth n2.resultDepth } := by
  have rn' : Rel { x with result := x.result && k.result }
      { n1 with resultDepth := max a.resultDepth n1.resultDepth }
      { n2 with resultDepth := max b.resultDepth n2.resultDepth } := by
    refine ⟨rn.depth, fun h => ?_, rn.caps, rn.vals⟩
    simp only [Bool.and_eq_true] at h
    simp [r.result h.2, rn.result h.1]
  exact rn'.mono le

theorem Rel.bind {x : Know} {a b : Env} (r : Rel x a b) (name : String) (text : List Char) :
    Rel { x with caps := name :: x.caps,
                 vals := if x.result then name :: x.vals else x.vals.filter (· != name) }
      ((a.put name text).putDepth name a.resultDepth) ((b.put name text).putDepth name b.resultDepth) := by
  refine ⟨r.depth, r.result, fun n m => ?_, fun n m => ?_⟩
  · have lk : ∀ e : Env, ((e.put name text).putDepth name e.resultDepth).lookup n = (e.put name text).lookup n :=
      fun _ => rfl
    have pr : ∀ e : Env, hasCapture ((e.put name text).putDepth name e.resultDepth) n =
        hasCapture (e.put name text) n := fun _ => rfl
    rw [lk, lk, pr, pr, lookup_put, lookup_put, presence_put, presence_put]
    by_cases h : n = name
    · simp [h]
    · simp only [h, ↓reduceIte]
      simp only [List.mem_cons, h, false_or] at m
      exact r.caps n m
  · rw [valueDepth_put, valueDepth_put]
    by_cases h : n = name
    · subst h
      simp only [↓reduceIte]
      cases hr : x.result
      · simp [hr] at m
      · rw [r.result hr]
    · simp only [h, ↓reduceIte]
      have vd : ∀ e : Env, (e.put name text).valueDepth n = e.valueDepth n := fun _ => rfl
      rw [vd, vd]
      cases hr : x.result
      · simp [hr] at m; exact r.vals n m.1
      · simp [hr, h] at m; exact r.vals n m

theorem action_same {k : Know} {a b : Env} (r : Rel k a b) (act : DepthAction)
    (reads : actionReads k act = true) : DepthAction.eval a act = DepthAction.eval b act := by
  have pres : ∀ p, p ∈ k.caps → a.captures.any (fun pair => pair.1 == p) =
      b.captures.any (fun pair => pair.1 == p) := fun p m => (r.caps p m).2
  cases act with
  | zero => rfl
  | copy n =>
    simp only [actionReads, List.contains_iff_mem] at reads
    simp only [DepthAction.eval, r.vals n reads]
  | successor n =>
    simp only [actionReads, List.contains_iff_mem] at reads
    simp only [DepthAction.eval, r.vals n reads]
  | add x y =>
    simp only [actionReads, List.contains_iff_mem, Bool.and_eq_true] at reads
    simp only [DepthAction.eval, r.vals x reads.1, r.vals y reads.2]
  | maximum x y =>
    simp only [actionReads, List.contains_iff_mem, Bool.and_eq_true] at reads
    simp only [DepthAction.eval, r.vals x reads.1, r.vals y reads.2]
  | plusIfBound v p =>
    simp only [actionReads, List.contains_iff_mem, Bool.and_eq_true] at reads
    simp only [DepthAction.eval, r.vals v reads.1, pres p reads.2]

theorem arg_same {k : Know} {a b : Env} (r : Rel k a b) (arg : EnvironmentDepth.DepthArg)
    (reads : argReads k arg = true) :
    EnvironmentDepth.evalDepthArg a arg = EnvironmentDepth.evalDepthArg b arg := by
  cases arg with
  | zero => rfl
  | current => simp only [argReads] at reads; simp only [EnvironmentDepth.evalDepthArg, r.depth reads]
  | successor => simp only [argReads] at reads; simp only [EnvironmentDepth.evalDepthArg, r.depth reads]
  | plusValue n =>
    simp only [argReads, List.contains_iff_mem, Bool.and_eq_true] at reads
    simp only [EnvironmentDepth.evalDepthArg, r.depth reads.1, r.vals n reads.2]

theorem predicate_same {k : Know} {a b : Env} (r : Rel k a b) (cls : SemanticPredicates.Classes)
    (kind : SemanticPredicates.Kind) (reads : predReads k kind = true) :
    SemanticPredicates.eval cls kind (PredicateBindings.predicateEnv kind a) =
      SemanticPredicates.eval cls kind (PredicateBindings.predicateEnv kind b) := by
  cases kind with
  | depth =>
    simp only [predReads] at reads
    simp only [SemanticPredicates.eval, PredicateBindings.predicateEnv]
    exact decide_eq_decide.mpr (by rw [r.depth reads])
  | _ =>
    simp [predReads, PredicateBindings.captureName, List.contains_iff_mem] at reads
    simp [SemanticPredicates.eval, PredicateBindings.predicateEnv, PredicateBindings.captureName,
      (r.caps _ reads).1]

/-! ## Soundness -/

/-- Two replies of the same shape whose environments agree on `k`. -/
def RelReply (k : Know) : Option Reply → Option Reply → Prop
  | none, none => True
  | some (.ok n a), some (.ok m b) => n = m ∧ Rel k a b
  | some .fail, some .fail => True
  | some (.throwLabel p l m), some (.throwLabel p' l' m') => p = p' ∧ l = l' ∧ m = m'
  | _, _ => False

theorem RelReply.refl (k : Know) : ∀ o, RelReply k o o
  | none => trivial
  | some (.ok _ a) => ⟨rfl, Rel.refl k a⟩
  | some .fail => trivial
  | some (.throwLabel _ _ _) => ⟨rfl, rfl, rfl⟩

/-- What the soundness proof asks of the inputs. -/
structure Shape (ctx : Inputs) (calls : Nat → Option EnvironmentDepth.CallSite) (plain : Nat → Bool)
    (entry : Nat → Know) : Prop where
  hooks : ctx.hooks = EnvironmentDepth.hooks calls (fun _ _ _ => none)
  preds : ∀ site kind pol env, ctx.sites site = some (kind, pol) →
    ctx.predicateEnv site env = PredicateBindings.predicateEnv kind env
  plainEntry : ∀ r, plain r = true → entry r = Know.bottom
  rules : ∀ r, ∃ k', check ctx.sites ctx.actions calls plain (ctx.rules r) (entry r) = some k' ∧
    k'.result = true

/-- Case analysis on two related replies. -/
@[elab_as_elim] theorem relReply_elim {x : Know} {P : Option Reply → Option Reply → Prop} {o1 o2 : Option Reply}
    (h : RelReply x o1 o2) (none' : P none none)
    (ok : ∀ n a b, Rel x a b → P (some (.ok n a)) (some (.ok n b)))
    (fail : P (some .fail) (some .fail))
    (thr : ∀ p l m, P (some (.throwLabel p l m)) (some (.throwLabel p l m))) : P o1 o2 := by
  match o1, o2, h with
  | none, none, _ => exact none'
  | some (.ok n a), some (.ok m b), ⟨e, r⟩ => subst e; exact ok n a b r
  | some .fail, some .fail, _ => exact fail
  | some (.throwLabel p l m), some (.throwLabel p' l' m'), ⟨e1, e2, e3⟩ => subst e1 e2 e3; exact thr p l m

theorem invariant1_scope_sound (ctx : Inputs) (calls : Nat → Option EnvironmentDepth.CallSite)
    (plain : Nat → Bool) (entry : Nat → Know) (shape : Shape ctx calls plain entry) :
    ∀ fuel body k k' rem a b, check ctx.sites ctx.actions calls plain body k = some k' →
      Rel k a b → RelReply k' (runFuel ctx fuel body rem a) (runFuel ctx fuel body rem b) := by
  intro fuel
  induction fuel with
  | zero => intro body k k' rem a b _ _; exact trivial
  | succ fuel ih =>
    intro body k k' rem a b hc r
    cases body with
    | eps =>
      simp only [check, Option.some.injEq] at hc; subst hc
      exact ⟨rfl, r.setResult 0 0 rfl⟩
    | terminal site =>
      simp only [check, Option.some.injEq] at hc; subst hc
      simp only [runFuel]
      cases ctx.terms site with
      | none => exact trivial
      | some t =>
        simp only
        cases terminalOracle t ctx.input rem with
        | none => exact trivial
        | some rest =>
          simp only
          split
          · exact ⟨rfl, r.setResult 0 0 rfl⟩
          · exact trivial
    | predicate site =>
      simp only [runFuel]
      cases hs : ctx.sites site with
      | none => exact trivial
      | some pair =>
        obtain ⟨kind, pol⟩ := pair
        simp only [check, hs] at hc
        split at hc
        · rename_i reads
          simp only [Option.some.injEq] at hc; subst hc
          simp only
          rw [shape.preds site kind pol a hs, shape.preds site kind pol b hs,
            predicate_same r ctx.classes kind reads]
          split
          · exact ⟨rfl, r.setResult 0 0 rfl⟩
          · exact trivial
        · cases hc
    | call site rule =>
      simp only [runFuel, shape.hooks, EnvironmentDepth.hooks]
      obtain ⟨kr, hkr, kres⟩ := shape.rules rule
      have finish : ∀ o1 o2, RelReply kr o1 o2 → k' = { k with result := true } →
          RelReply k' (match o1 with
            | some (.ok rest inner) => some (.ok rest { a with resultDepth := inner.resultDepth })
            | some .fail => some .fail
            | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
            | none => none)
          (match o2 with
            | some (.ok rest inner) => some (.ok rest { b with resultDepth := inner.resultDepth })
            | some .fail => some .fail
            | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
            | none => none) := by
        intro o1 o2 ho e
        subst e
        refine relReply_elim (o1 := o1) (o2 := o2) ho trivial ?_ trivial (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
        intro n i1 i2 ri
        exact ⟨rfl, r.setResult _ _ (ri.result kres)⟩
      cases hcs : calls site with
      | none => simp [EnvironmentDepth.enterCall, hcs, RelReply]
      | some cs =>
        obtain ⟨caller, callee, args⟩ := cs
        match args with
        | [] =>
          simp only [check, hcs] at hc
          split at hc
          · rename_i isPlain
            simp only [Option.some.injEq] at hc
            have hk := ih (ctx.rules rule) (entry rule) kr rem a b hkr
              (by rw [shape.plainEntry rule isPlain]; exact rel_bottom a b)
            simp only [EnvironmentDepth.enterCall, hcs]
            exact finish _ _ hk hc.symm
          · cases hc
        | [src] =>
          simp only [check, hcs] at hc
          cases harg : EnvironmentDepth.depthArgOf src with
          | none => simp [EnvironmentDepth.enterCall, hcs, harg, RelReply]
          | some arg =>
            simp only [harg] at hc
            split at hc
            · rename_i reads
              simp only [Option.some.injEq] at hc
              have same := arg_same r arg reads
              simp [EnvironmentDepth.enterCall, hcs, harg, same]
              cases hv : EnvironmentDepth.evalDepthArg b arg with
              | none => simp [RelReply]
              | some d =>
                exact finish _ _ (RelReply.refl kr _) hc.symm
            · cases hc
        | _ :: _ :: _ => simp [EnvironmentDepth.enterCall, hcs, RelReply]
    | seq x y =>
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        rw [hx] at hc
        simp only [Option.bind_eq_bind, Option.bind_some] at hc
        simp only [runFuel]
        have h := ih x k kx rem a b hx r
        generalize runFuel ctx fuel x rem a = o1 at h ⊢
        generalize runFuel ctx fuel x rem b = o2 at h ⊢
        refine relReply_elim (o1 := o1) (o2 := o2) h trivial ?_ trivial (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
        intro n a' b' r'
        exact ih y kx k' n a' b' hc r'
    | alt x y =>
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        cases hy : check ctx.sites ctx.actions calls plain y k with
        | none => rw [hx, hy] at hc; cases hc
        | some ky =>
          rw [hx, hy] at hc
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hc
          subst hc
          simp only [runFuel]
          have h := ih x k kx rem a b hx r
          have hyr := ih y k ky rem a b hy r
          generalize runFuel ctx fuel x rem a = o1 at h ⊢
          generalize runFuel ctx fuel x rem b = o2 at h ⊢
          refine relReply_elim (o1 := o1) (o2 := o2) h trivial (fun n a' b' r' => ⟨rfl, r'.meet_left⟩) ?_
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
          simp only
          generalize runFuel ctx fuel y rem a = q1 at hyr ⊢
          generalize runFuel ctx fuel y rem b = q2 at hyr ⊢
          exact relReply_elim (o1 := q1) (o2 := q2) hyr trivial (fun n a' b' r' => ⟨rfl, r'.meet_right⟩) trivial
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    | ahead x =>
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        rw [hx] at hc
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hc
        subst hc
        simp only [runFuel]
        have h := ih x k kx rem a b hx r
        generalize runFuel ctx fuel x rem a = o1 at h ⊢
        generalize runFuel ctx fuel x rem b = o2 at h ⊢
        exact relReply_elim (o1 := o1) (o2 := o2) h trivial (fun _ _ _ _ => ⟨rfl, r⟩) trivial (fun _ _ _ => trivial)
    | notAhead x =>
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        rw [hx] at hc
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hc
        subst hc
        simp only [runFuel]
        have h := ih x k kx rem a b hx r
        generalize runFuel ctx fuel x rem a = o1 at h ⊢
        generalize runFuel ctx fuel x rem b = o2 at h ⊢
        exact relReply_elim (o1 := o1) (o2 := o2) h trivial (fun _ _ _ _ => trivial) ⟨rfl, r⟩ (fun _ _ _ => ⟨rfl, r⟩)
    | star x =>
      simp only [runFuel]
      cases fuel with
      | zero => exact trivial
      | succ fuel =>
        have hl : check ctx.sites ctx.actions calls plain (.starLoop x) { k with result := true } = some k' := by
          simpa only [check] using hc
        exact ih (.starLoop x) { k with result := true } k' rem _ _ hl (r.setResult 0 0 rfl)
    | starLoop x =>
      have hc0 := hc
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        rw [hx] at hc
        simp only [Option.bind_eq_bind, Option.bind_some] at hc
        split at hc
        · rename_i le
          simp only [Option.pure_def, Option.some.injEq] at hc
          subst hc
          simp only [runFuel]
          have h := ih x k kx rem a b hx r
          generalize runFuel ctx fuel x rem a = o1 at h ⊢
          generalize runFuel ctx fuel x rem b = o2 at h ⊢
          refine relReply_elim (o1 := o1) (o2 := o2) h trivial ?_ ⟨rfl, r⟩ (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
          intro n a' b' r'
          simp only
          split
          · exact ih (.starLoop x) k k n _ _ hc0 (r.loop r' le)
          · exact ⟨rfl, r⟩
        · cases hc
    | label name msg x =>
      simp only [check] at hc
      simp only [runFuel]
      have h := ih x k k' rem a b hc r
      generalize runFuel ctx fuel x rem a = o1 at h ⊢
      generalize runFuel ctx fuel x rem b = o2 at h ⊢
      exact relReply_elim (o1 := o1) (o2 := o2) h trivial (fun n a' b' r' => ⟨rfl, r'⟩) ⟨rfl, rfl, rfl⟩
        (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    | capture x =>
      simp only [check] at hc
      simp only [runFuel]
      exact ih x k k' rem a b hc r
    | bind site name x =>
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        rw [hx] at hc
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hc
        subst hc
        simp only [runFuel, shape.hooks, EnvironmentDepth.hooks, EnvironmentDepth.bindShape]
        have h := ih x k kx rem a b hx r
        generalize runFuel ctx fuel x rem a = o1 at h ⊢
        generalize runFuel ctx fuel x rem b = o2 at h ⊢
        exact relReply_elim (o1 := o1) (o2 := o2) h trivial (fun n a' b' r' => ⟨rfl, r'.bind name _⟩) trivial
          (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
    | action site x =>
      simp only [check] at hc
      cases hx : check ctx.sites ctx.actions calls plain x k with
      | none => rw [hx] at hc; cases hc
      | some kx =>
        rw [hx] at hc
        simp only [Option.bind_eq_bind, Option.bind_some] at hc
        simp only [runFuel]
        have h := ih x k kx rem a b hx r
        generalize runFuel ctx fuel x rem a = o1 at h ⊢
        generalize runFuel ctx fuel x rem b = o2 at h ⊢
        cases ha : ctx.actions site with
        | none =>
          exact relReply_elim (o1 := o1) (o2 := o2) h trivial (fun n a' b' r' => by simp [RelReply]) trivial
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
        | some act =>
          rw [ha] at hc
          simp only at hc
          split at hc
          · rename_i reads
            simp only [Option.pure_def, Option.some.injEq] at hc
            subst hc
            refine relReply_elim (o1 := o1) (o2 := o2) h trivial ?_ trivial (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
            intro n a' b' r'
            simp only [Option.bind_eq_bind, Option.bind_some, action_same r' act reads]
            cases DepthAction.eval b' act with
            | none => exact trivial
            | some d => exact ⟨rfl, r'.setResult d d rfl⟩
          · cases hc

/-! ## The strict metagrammar -/

/-- The call sites of the strict metagrammar. -/
def metaCalls (i : Nat) : Option EnvironmentDepth.CallSite := MetaTerminal1.callSites[i]?

def calledRules : Body → List (Nat × Nat)
  | .call site rule => [(site, rule)]
  | .seq a b | .alt a b => calledRules a ++ calledRules b
  | .ahead a | .notAhead a | .star a | .starLoop a | .label _ _ a | .capture a | .bind _ _ a
  | .action _ a => calledRules a
  | _ => []

/-- The rules that some call site passes an argument to. -/
def argTargets : List Nat :=
  (MetaTerminal1.environmentBodyTable.toList.flatMap calledRules).filterMap fun (s, r) =>
    match metaCalls s with
    | some (_, _, _ :: _) => some r
    | _ => none

def metaPlain (r : Nat) : Bool := !argTargets.contains r

def binders : Body → List String
  | .bind _ name a => name :: binders a
  | .seq a b | .alt a b => binders a ++ binders b
  | .ahead a | .notAhead a | .star a | .starLoop a | .label _ _ a | .capture a | .action _ a =>
    binders a
  | _ => []

/-- A rule called with an argument starts from `{ depth := d }` for every
caller, so everything about its own names is known at the start. -/
def metaEntry (r : Nat) : Know :=
  if metaPlain r then Know.bottom
  else ⟨true, true, binders (MetaTerminal1.environmentBody r), binders (MetaTerminal1.environmentBody r)⟩

/-- The analysis of every rule of the strict metagrammar ends with the result
depth known. Rules past the table are `.terminal 0`. -/
def metaRulesChecked : Bool :=
  (List.range MetaTerminal1.environmentBodyTable.size).all fun r =>
    match check (context false []).sites (context false []).actions metaCalls metaPlain
        (MetaTerminal1.environmentBody r) (metaEntry r) with
    | some k => k.result
    | none => false

theorem metaRulesChecked_eq : metaRulesChecked = true := by decide +kernel

theorem meta_rules_size : MetaTerminal1.environmentBodyTable.size = 59 := by decide

theorem invariant1_meta_scoped (input : List Char) :
    Shape (context false input) metaCalls metaPlain metaEntry := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro site kind pol env hs
    have unfold : (context false input).predicateEnv site env =
        match (context false input).sites site with
        | some (kind, _) => PredicateBindings.predicateEnv kind env
        | none => { captured := [], depth := env.depth } := rfl
    rw [unfold, hs]
  · intro r hr
    simp [metaEntry, hr]
  · intro r
    have rules : (context false input).rules r = MetaTerminal1.environmentBody r := rfl
    have sites : (context false input).sites = (context false []).sites := rfl
    have actions : (context false input).actions = (context false []).actions := rfl
    rw [rules, sites, actions]
    by_cases lt : r < MetaTerminal1.environmentBodyTable.size
    · have all := metaRulesChecked_eq
      simp only [metaRulesChecked, List.all_eq_true, List.mem_range] at all
      have hr := all r lt
      revert hr
      cases check (context false []).sites (context false []).actions metaCalls metaPlain
        (MetaTerminal1.environmentBody r) (metaEntry r) with
      | none => intro h; cases h
      | some k => intro h; exact ⟨k, rfl, h⟩
    · have past : MetaTerminal1.environmentBody r = .terminal 0 := by
        simp [MetaTerminal1.environmentBody, Array.getElem?_eq_none (Nat.le_of_not_lt lt)]
      rw [past]
      exact ⟨_, rfl, rfl⟩

/-- What a caller keeps of a callee's reply: the shape, the position, the
label, and the result depth. -/
def SameCall : Reply → Reply → Prop
  | .ok n a, .ok m b => n = m ∧ a.resultDepth = b.resultDepth
  | .fail, .fail => True
  | .throwLabel p l m, .throwLabel p' l' m' => p = p' ∧ l = l' ∧ m = m'
  | _, _ => False

/-- A rule of the strict metagrammar that no call site passes an argument to
returns, from any two environments and with any fuel that suffices, replies
that agree in everything a caller keeps. -/
theorem invariant1_plain_call_independent (input : List Char) {r : Nat} (plain : metaPlain r = true)
    {rem m n : Nat} {a b : Env} {x y : Reply}
    (hx : runFuel (context false input) m ((context false input).rules r) rem a = some x)
    (hy : runFuel (context false input) n ((context false input).rules r) rem b = some y) :
    SameCall x y := by
  have shape := invariant1_meta_scoped input
  obtain ⟨kr, hkr, kres⟩ := shape.rules r
  have hx' := invariant1_fuel_stable _ (Nat.le_max_left m n) hx
  have hy' := invariant1_fuel_stable _ (Nat.le_max_right m n) hy
  have rel := invariant1_scope_sound _ _ _ _ shape (max m n) _ _ kr rem a b hkr
    (by rw [shape.plainEntry r plain]; exact rel_bottom a b)
  rw [hx', hy'] at rel
  match x, y, rel with
  | .ok _ _, .ok _ _, ⟨e, ri⟩ => exact ⟨e, ri.result kres⟩
  | .fail, .fail, _ => trivial
  | .throwLabel _ _ _, .throwLabel _ _ _, h => exact h

#print axioms invariant1_scope_sound
#print axioms invariant1_meta_scoped
#print axioms invariant1_plain_call_independent

end PegHs.ScopedEnv
