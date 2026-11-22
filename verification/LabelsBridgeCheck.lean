import LabelsBridgeSim

/-!
The recursion of the label check through the visited set: the translated
`failed`, `succeeded`, `ruleFailed` and `ruleSucceeded` of Peg.Grammar.Labels
(LabelsTranslated, translated with fuel) against `run` of LabelCheckModel,
and the translated `labelWarnings` against the model's.

A model action `c : M` (from a visited set to a verdict and a visited set,
or `none` when its fuel ends) and a family of translated actions `t n` (one
per fuel) correspond (`MCorr`) when, whenever the model gives a result from
a visited set, the translated action gives the embedded verdict from every
translated set with the same members, at every fuel from some bound on, and
the two sets after it have the same members again.
-/

set_option linter.unusedSimpArgs false

namespace LabelsTranslated

/-- The body of the translated `failed` after its visit, at the fuel of its calls. -/
def tFailedBody (fuel : Nat) (ctx : LabelsTranslated.Ctx) (rule : String) (fs : List LabelsTranslated.Frame)
    (pre : List LabelsTranslated.Item) (lifts : Int) (k : LabelsTranslated.CharSet) : (LabelsTranslated.State (HsSet (String × (List (Int × Int)) × LabelsTranslated.Mode × LabelsTranslated.CharSet × String)) LabelsTranslated.Verdict) :=
  let kStart : LabelsTranslated.CharSet := (beforeItems ctx pre k)
  (let ν199 := fs; (match ν199 with
  | (List.cons (Frame.FSeq items j) (List.cons (Frame.FAlts alts i body) rest)) => (let growingAlt : Bool := (HsBase.and body (HsBase.and (HsSet.member rule (Ctx.ctxDirectLr ctx)) (Ctx.ctxGrowing ctx rule i)));
let later : (List (LabelsTranslated.Loc × (List LabelsTranslated.Item))) := (HsList.concatMap (fun ν200 => (match ν200 with
  | (i', (al, a)) => (if (HsBase.or (HsBase.not growingAlt) (Ctx.ctxGrowing ctx rule i')) then [(al, a)] else []))) (HsList.drop (HsInt.add i (1 : Int)) (HsList.zipFrom (0 : Int) alts)));
let matched : (List LabelsTranslated.Item) := (HsList.append (HsList.take j items) pre);
(if (HsBase.and body (HsBase.and (HsSet.member rule (Ctx.ctxOtherLr ctx)) (Ctx.ctxGrowing ctx rule i))) then (instApplicative_pure_State (Verdict.Unchecked (HsText.append "it is in a growing alternative of " (HsText.append rule ", which takes part in indirect or hidden left recursion")))) else (let ν204 := (HsList.foldr (fun ν201 ν202 => (andAlso ν201 ν202)) Verdict.Safe (List.map (fun ν203 => ((failed.laterCheck_541 fuel ctx items j matched k) ν203)) later)); (match ν204 with
  | Verdict.Safe => (if growingAlt then ((succeeded fuel) ctx rule List.nil ((failed.kAt_534 ctx k matched) (1 : Int))) else ((failed fuel) ctx rule rest (matched, lifts) k))
  | v => (instApplicative_pure_State v)))))
  | (List.cons (Frame.FStar _ _) rest) => ((succeeded fuel) ctx rule rest kStart)
  | (List.cons (Frame.FPlus _ _) rest) => (allOf [((failed fuel) ctx rule rest (pre, lifts) k), ((succeeded fuel) ctx rule rest kStart)])
  | (List.cons Frame.FOpt rest) => ((succeeded fuel) ctx rule rest kStart)
  | (List.cons (Frame.FAnd _) _) => (instApplicative_pure_State Verdict.Safe)
  | (List.cons (Frame.FNot _) _) => (instApplicative_pure_State Verdict.Safe)
  | (List.cons Frame.FLabel rest) => ((failed fuel) ctx rule rest (pre, lifts) k)
  | (List.cons Frame.FCapture rest) => ((failed fuel) ctx rule rest (pre, lifts) k)
  | List.nil => ((ruleFailed fuel) ctx rule (pre, lifts) k)
  | _ => (instApplicative_pure_State Verdict.Safe)))

/-- The body of the translated `succeeded` after its visit, at the fuel of its calls. -/
def tSucceededBody (fuel : Nat) (ctx : LabelsTranslated.Ctx) (rule : String) (fs : List LabelsTranslated.Frame)
    (k : LabelsTranslated.CharSet) : (LabelsTranslated.State (HsSet (String × (List (Int × Int)) × LabelsTranslated.Mode × LabelsTranslated.CharSet × String)) LabelsTranslated.Verdict) :=
  (let ν205 := fs; (match ν205 with
  | (List.cons (Frame.FSeq items j) (List.cons alts@(Frame.FAlts _ i body) rest)) => (let growingAlt : Bool := (HsBase.and body (HsBase.and (HsSet.member rule (Ctx.ctxDirectLr ctx)) (Ctx.ctxGrowing ctx rule i)));
let after : (List LabelsTranslated.Item) := (HsList.drop (HsInt.add j (1 : Int)) items);
let a : LabelsTranslated.Abs := (seqAbs (Ctx.ctxPass ctx) after);
(if (HsBase.and body (HsBase.and (HsSet.member rule (Ctx.ctxOtherLr ctx)) (Ctx.ctxGrowing ctx rule i))) then (instApplicative_pure_State (Verdict.Unchecked (HsText.append "it reaches a growing alternative of " (HsText.append rule ", which takes part in indirect or hidden left recursion")))) else (let ν206 := after; (match ν206 with
  | (List.cons next_ _) => (if (meets (Abs.absConsume a) k) then (instApplicative_pure_State (Verdict.Unsafe (HsText.append "the parse can continue at " (showLoc (Item.itemLoc next_))))) else (allOf (HsList.append (if (HsBase.not (HsList.null after)) then [((failed fuel) ctx rule (List.cons (Frame.FSeq items (HsInt.add j (1 : Int))) (List.cons alts rest)) (List.nil, (0 : Int)) k)] else []) (HsList.append (HsList.concatMap (fun ν207 => (match ν207 with
  | m => [((failed fuel) ctx rule (List.cons (Frame.FSeq items m) (List.cons alts rest)) (List.nil, (0 : Int)) everything)])) (HsList.enumFromTo (HsInt.add j (2 : Int)) (HsInt.sub (HsList.length items) (1 : Int)))) (if (meets (Abs.absEmpty a) k) then [((succeeded.ended_596 fuel ctx rule alts rest growingAlt) (intersect (Abs.absEmpty a) k))] else [])))))
  | _ => (allOf (HsList.append (if (HsBase.not (HsList.null after)) then [((failed fuel) ctx rule (List.cons (Frame.FSeq items (HsInt.add j (1 : Int))) (List.cons alts rest)) (List.nil, (0 : Int)) k)] else []) (HsList.append (HsList.concatMap (fun ν208 => (match ν208 with
  | m => [((failed fuel) ctx rule (List.cons (Frame.FSeq items m) (List.cons alts rest)) (List.nil, (0 : Int)) everything)])) (HsList.enumFromTo (HsInt.add j (2 : Int)) (HsInt.sub (HsList.length items) (1 : Int)))) (if (meets (Abs.absEmpty a) k) then [((succeeded.ended_596 fuel ctx rule alts rest growingAlt) (intersect (Abs.absEmpty a) k))] else []))))))))
  | (List.cons (Frame.FStar x l) rest) => ((succeeded.again_621 fuel ctx rule k) x l rest)
  | (List.cons (Frame.FPlus x l) rest) => ((succeeded.again_621 fuel ctx rule k) x l rest)
  | (List.cons Frame.FOpt rest) => ((succeeded fuel) ctx rule rest k)
  | (List.cons (Frame.FAnd l) _) => (instApplicative_pure_State (Verdict.Unsafe (HsText.append "the lookahead at " (HsText.append (showLoc l) " can match"))))
  | (List.cons (Frame.FNot l) _) => (instApplicative_pure_State (Verdict.Unsafe (HsText.append "the lookahead at " (HsText.append (showLoc l) " can match"))))
  | (List.cons Frame.FLabel rest) => ((succeeded fuel) ctx rule rest k)
  | (List.cons Frame.FCapture rest) => ((succeeded fuel) ctx rule rest k)
  | List.nil => ((ruleSucceeded fuel) ctx rule k)
  | _ => (instApplicative_pure_State Verdict.Safe)))

theorem failed_succ (fuel : Nat) (ctx : LabelsTranslated.Ctx) (rule : String) (fs : List LabelsTranslated.Frame)
    (pre0 : List LabelsTranslated.Item) (lifts : Int) (k0 : LabelsTranslated.CharSet) :
    failed (fuel + 1) ctx rule fs (pre0, lifts) k0 =
      (let (pre, k) := (if (HsInt.gt (HsList.length pre0) maxPrefix) then (List.nil, (beforeItems ctx pre0 k0)) else (pre0, k0))
       visit rule fs Mode.Failed (pre, lifts) k (tFailedBody fuel ctx rule fs pre lifts k)) := by
  rw [failed]
  rfl

theorem succeeded_succ (fuel : Nat) (ctx : LabelsTranslated.Ctx) (rule : String) (fs : List LabelsTranslated.Frame)
    (k : LabelsTranslated.CharSet) :
    succeeded (fuel + 1) ctx rule fs k = visit rule fs Mode.Succeeded (List.nil, (0 : Int)) k (tSucceededBody fuel ctx rule fs k) := by
  rw [succeeded]
  rfl


end LabelsTranslated

namespace PegHs.LabelsBridge

open PegHs.LabelCheck

/-! ## The visited set -/

abbrev TKey := String × List (Int × Int) × LabelsTranslated.Mode × LabelsTranslated.CharSet × String
abbrev TSt := LabelsTranslated.State (HsSet TKey) LabelsTranslated.Verdict

def eKey (key : Key) : TKey :=
  (key.1, key.2.1.map (fun p => ((p.1 : Int), (p.2 : Int))), eMode key.2.2.1, eCS key.2.2.2.1, key.2.2.2.2)

theorem mode_beq_e (a b : Mode) : (eMode a == eMode b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

theorem key_beq_e (a b : Key) : (eKey a == eKey b) = decide (a = b) := by
  obtain ⟨r, fk, md, k, s⟩ := a
  obtain ⟨r', fk', md', k', s'⟩ := b
  have hprod : ∀ {α β : Type} [BEq α] [BEq β] (a c : α) (b d : β), ((a, b) == (c, d)) = (a == c && b == d) :=
    fun _ _ _ _ => rfl
  apply Bool.eq_iff_iff.2
  simp only [eKey, hprod, mode_beq_e, charSet_beq_e]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, map_cp_inj h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, by rw [h2], h3, h4, h5⟩

/-- A translated visited set and a model one with the same members. -/
def VRel (VT : HsSet TKey) (V : Visited) : Prop := ∀ key, HsSet.member (eKey key) VT = V.contains key

theorem member_e {VT : HsSet TKey} {V : Visited} (h : VRel VT V) (key : Key) :
    HsSet.member (eKey key) VT = V.contains key := h key

theorem vrel_insert {VT : HsSet TKey} {V : Visited} (h : VRel VT V) (key : Key) :
    VRel (HsSet.insert (eKey key) VT) (key :: V) := by
  intro k'
  unfold HsSet.insert
  split
  · rename_i hm
    rw [h key] at hm
    rw [h k', List.contains_cons]
    by_cases he : k' = key
    · subst he; simpa using hm
    · simp [he]
  · simp only [HsSet.member, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    have := h k'
    simp only [HsSet.member] at this
    rw [this, key_beq_e, List.contains_cons]
    by_cases he : k' = key
    · subst he; simp
    · simp [he, Ne.symm he]

/-! ## The state monad of the translation -/

theorem run_pure {σ α : Type} [Inhabited σ] [Inhabited α] (v : α) (s : σ) :
    (LabelsTranslated.instApplicative_pure_State v : LabelsTranslated.State σ α).runState s = (v, s) := rfl

theorem run_bind {σ α β : Type} [Inhabited σ] [Inhabited α] [Inhabited β] (m : LabelsTranslated.State σ α)
    (k : α → LabelsTranslated.State σ β) (s : σ) :
    (LabelsTranslated.instMonad_gtgteq_State m k).runState s = (k (m.runState s).1).runState (m.runState s).2 := by
  cases m; rfl

def tVisitKey (rule : String) (fs : List LabelsTranslated.Frame) (mode : LabelsTranslated.Mode)
    (pre : List LabelsTranslated.Item) (lifts : Int) (k : LabelsTranslated.CharSet) : TKey :=
  (rule, fs.map LabelsTranslated.frameKey, mode, k, HsText.pack (HsShow.viaRepr
    (lifts, pre.map (fun i => LabelsTranslated.plainExpr (LabelsTranslated.Item.itemExpr i)))))

theorem run_visit (rule : String) (fs : List LabelsTranslated.Frame) (mode : LabelsTranslated.Mode)
    (pre : List LabelsTranslated.Item) (lifts : Int) (k : LabelsTranslated.CharSet) (act : TSt) (s : HsSet TKey) :
    (LabelsTranslated.visit rule fs mode (pre, lifts) k act).runState s =
      if HsSet.member (tVisitKey rule fs mode pre lifts k) s then (LabelsTranslated.Verdict.Safe, s)
      else act.runState (HsSet.insert (tVisitKey rule fs mode pre lifts k) s) := by
  cases act
  unfold LabelsTranslated.visit
  dsimp only
  rw [run_bind]
  simp only [LabelsTranslated.gets, LabelsTranslated.State.runState]
  by_cases hm : HsSet.member (tVisitKey rule fs mode pre lifts k) s = true
  · simp only [tVisitKey] at hm
    simp [hm, tVisitKey, LabelsTranslated.instApplicative_pure_State]
  · simp only [tVisitKey] at hm
    simp [hm, tVisitKey, LabelsTranslated.instMonad_gtgteq_State,
      LabelsTranslated.modify', LabelsTranslated.State.runState, HsBase.seq]

theorem run_allOf_cons (a : TSt) (as : List TSt) (s : HsSet TKey) :
    (LabelsTranslated.allOf (a :: as)).runState s =
      if HsBase.eq (a.runState s).1 LabelsTranslated.Verdict.Safe then (LabelsTranslated.allOf as).runState (a.runState s).2
      else ((a.runState s).1, (a.runState s).2) := by
  simp only [LabelsTranslated.allOf, HsList.foldr, List.foldr_cons, run_bind]
  split <;> rfl

theorem run_allOf_nil (s : HsSet TKey) : (LabelsTranslated.allOf []).runState s = (LabelsTranslated.Verdict.Safe, s) := rfl

theorem verdict_eq_safe (v : Verdict) : HsBase.eq (eVerdict v) LabelsTranslated.Verdict.Safe = decide (v = .safe) := by
  cases v <;> rfl

/-! ## Corresponding actions -/

/-- A model action and a family of translated actions, one per fuel, correspond. -/
def MCorr (c : PegHs.LabelCheck.M) (t : Nat → TSt) : Prop :=
  ∀ V r, c V = some r → Eventually (fun n => ∀ VT, VRel VT V →
    ∃ VT', (t n).runState VT = (eVerdict r.1, VT') ∧ VRel VT' r.2)

theorem mcorr_ret (v : Verdict) : MCorr (ret v) (fun _ => LabelsTranslated.instApplicative_pure_State (eVerdict v)) := by
  intro V r h
  simp only [ret, Option.some.injEq] at h
  subst h
  exact Eventually.of (fun _ VT hV => ⟨VT, rfl, hV⟩)

theorem mcorr_congr {c : PegHs.LabelCheck.M} {t t' : Nat → TSt} (h : MCorr c t) (N : Nat) (he : ∀ n, N ≤ n → t' n = t n) :
    MCorr c t' := by
  intro V r hc
  obtain ⟨M, hM⟩ := h V r hc
  refine ⟨max M N, fun n hn VT hV => ?_⟩
  rw [he n (by omega)]
  exact hM n (by omega) VT hV

theorem mcorr_pred {c : PegHs.LabelCheck.M} {t : Nat → TSt} (h : MCorr c t) : MCorr c (fun n => t (n - 1)) := by
  intro V r hc
  obtain ⟨M, hM⟩ := h V r hc
  exact ⟨M + 1, fun n hn VT hV => hM (n - 1) (by omega) VT hV⟩

inductive MCorrList : List PegHs.LabelCheck.M → List (Nat → TSt) → Prop
  | nil : MCorrList [] []
  | cons {c t cs ts} : MCorr c t → MCorrList cs ts → MCorrList (c :: cs) (t :: ts)

theorem mcorr_allOf : ∀ {cs : List PegHs.LabelCheck.M} {ts : List (Nat → TSt)}, MCorrList cs ts →
    MCorr (allOf cs) (fun n => LabelsTranslated.allOf (ts.map (fun t => t n)))
  | [], [], .nil => by
    intro V r h
    simp only [allOf, ret, Option.some.injEq] at h
    subst h
    exact Eventually.of (fun _ VT hV => ⟨VT, rfl, hV⟩)
  | c :: cs, t :: ts, .cons hc hs => by
    intro V r h
    simp only [allOf] at h
    cases hcV : c V with
    | none => rw [hcV] at h; cases h
    | some q =>
      rw [hcV] at h
      obtain ⟨v, V'⟩ := q
      obtain ⟨N1, h1⟩ := hc V (v, V') hcV
      by_cases hv : v = .safe
      · subst hv
        simp only [↓reduceIte] at h
        obtain ⟨N2, h2⟩ := mcorr_allOf hs V' r h
        refine ⟨max N1 N2, fun n hn VT hV => ?_⟩
        obtain ⟨VT1, e1, hV1⟩ := h1 n (by omega) VT hV
        obtain ⟨VT2, e2, hV2⟩ := h2 n (by omega) VT1 hV1
        refine ⟨VT2, ?_, hV2⟩
        simp only [List.map_cons, run_allOf_cons, e1, eVerdict, HsBase.eq]
        exact e2
      · simp only [hv, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨N1, fun n hn VT hV => ?_⟩
        obtain ⟨VT1, e1, hV1⟩ := h1 n hn VT hV
        refine ⟨VT1, ?_, hV1⟩
        simp only [List.map_cons, run_allOf_cons, e1, verdict_eq_safe, hv, decide_false, Bool.false_eq_true,
          ↓reduceIte]

/-- The text of the matched items in the keys of the translated visited set. -/
def tKeyOf (lifts : Nat) (pre : List Item) : String :=
  HsText.pack (HsShow.viaRepr ((lifts : Int),
    (eItems pre).map (fun i => LabelsTranslated.plainExpr (LabelsTranslated.Item.itemExpr i))))

theorem mcorr_visit {ctx : Ctx} (hk : ctx.keyOf = tKeyOf) {c : PegHs.LabelCheck.M} {t : Nat → TSt} (h : MCorr c t)
    (rule : String) (fs : List Frame) (mode : Mode) (pre : List Item) (lifts : Nat) (k : CharSet) :
    MCorr (visit (rule, fs.map frameKey, mode, k, ctx.keyOf lifts pre) c)
      (fun n => LabelsTranslated.visit rule (fs.map eFrame) (eMode mode) (eItems pre, (lifts : Int)) (eCS k) (t n)) := by
  intro V r hc
  have hkey : tVisitKey rule (fs.map eFrame) (eMode mode) (eItems pre) lifts (eCS k) =
      eKey (rule, fs.map frameKey, mode, k, ctx.keyOf lifts pre) := by
    simp [tVisitKey, eKey, hk, tKeyOf, List.map_map, Function.comp_def, frameKey_e]
  simp only [visit] at hc
  by_cases hm : V.contains (rule, fs.map frameKey, mode, k, ctx.keyOf lifts pre) = true
  · simp only [hm, ↓reduceIte, Option.some.injEq] at hc
    subst hc
    refine Eventually.of (fun n VT hV => ⟨VT, ?_, hV⟩)
    rw [run_visit]
    simp only [hkey, member_e hV, hm, ↓reduceIte]
    rfl
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hc
    obtain ⟨N, hN⟩ := h _ r hc
    refine ⟨N, fun n hn VT hV => ?_⟩
    rw [run_visit]
    simp only [hkey, member_e hV]
    have hm' : V.contains (rule, fs.map frameKey, mode, k, ctx.keyOf lifts pre) = false := by simpa using hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte]
    exact hN n hn _ (vrel_insert hV _)


/-! ## The functions of a step -/

theorem mcorrList_map {α : Type} {f : α → PegHs.LabelCheck.M} {g : α → Nat → TSt} :
    ∀ (l : List α), (∀ x ∈ l, MCorr (f x) (g x)) → MCorrList (l.map f) (l.map g)
  | [], _ => .nil
  | x :: xs, h => .cons (h x (by simp)) (mcorrList_map xs (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem mcorrList_append : ∀ {cs ts cs' ts'}, MCorrList cs ts → MCorrList cs' ts' → MCorrList (cs ++ cs') (ts ++ ts')
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (mcorrList_append h2 h)

variable {tc : LabelsTranslated.Ctx} {mc : Ctx}

/-- The translated recursive functions at every fuel correspond to the model's `R`. -/
structure RecCorr (tc : LabelsTranslated.Ctx) (mc : Ctx) (R : Rec) : Prop where
  failed : ∀ rule fs pre (lifts : Nat) k, MCorr (R.failed rule fs (pre, lifts) k)
    (fun n => LabelsTranslated.failed n tc rule (fs.map eFrame) (eItems pre, (lifts : Int)) (eCS k))
  succeeded : ∀ rule fs k, MCorr (R.succeeded rule fs k)
    (fun n => LabelsTranslated.succeeded n tc rule (fs.map eFrame) (eCS k))

theorem siteRule_e (s : Site) : LabelsTranslated.siteRule (eSite s) = s.rule := rfl
theorem siteFrames_e (s : Site) : LabelsTranslated.siteFrames (eSite s) = s.frames.map eFrame := rfl

theorem ruleFailed_corr (h : CtxCorr tc mc) {R : Rec} (hR : RecCorr tc mc R) (rule : String) (pre : List Item)
    (lifts : Nat) (k : CharSet) :
    MCorr (ruleFailed mc R rule pre lifts k)
      (fun n => LabelsTranslated.ruleFailed n tc rule (eItems pre, (lifts : Int)) (eCS k)) := by
  obtain ⟨N, hN⟩ := lift_ev h pre
  by_cases hr : mc.recovery.contains rule = true
  · have hm : ruleFailed mc R rule pre lifts k = ret .safe := by simp only [ruleFailed, hr, ↓reduceIte]
    rw [hm]
    apply mcorr_congr (mcorr_ret .safe) 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.ruleFailed]
    simp only [h.recovery rule, hr, ↓reduceIte]
    rfl
  · have hm : ruleFailed mc R rule pre lifts k = allOf ((callersOf mc rule).map fun s =>
        R.failed s.rule s.frames (lift mc rule pre lifts k s).1 (lift mc rule pre lifts k s).2) := by
      have hr0 : mc.recovery.contains rule = false := by simpa using hr
      simp only [ruleFailed, hr0, Bool.false_eq_true, ↓reduceIte]
    rw [hm]
    have hl := mcorrList_map (f := fun s => R.failed s.rule s.frames (lift mc rule pre lifts k s).1
        (lift mc rule pre lifts k s).2)
      (g := fun s => fun n => LabelsTranslated.failed (n - 1) tc s.rule (s.frames.map eFrame)
        (eItems (lift mc rule pre lifts k s).1.1, ((lift mc rule pre lifts k s).1.2 : Int))
        (eCS (lift mc rule pre lifts k s).2))
      (callersOf mc rule) (fun s _ => mcorr_pred (hR.failed _ _ _ _ _))
    apply mcorr_congr (mcorr_allOf hl) (N + 1)
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.ruleFailed]
    have hr' : HsSet.member rule tc.ctxRecovery = false := by rw [h.recovery rule]; simpa using hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte, callersOf_e h, HsList.concatMap, flatMap_single, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_def, HsBase.uncurry, hN m (by omega), siteRule_e, siteFrames_e]
    rfl

theorem ruleSucceeded_corr (h : CtxCorr tc mc) {R : Rec} (hR : RecCorr tc mc R) (rule : String) (k : CharSet) :
    MCorr (ruleSucceeded mc R rule k) (fun n => LabelsTranslated.ruleSucceeded n tc rule (eCS k)) := by
  by_cases hr : mc.recovery.contains rule = true
  · have hm : ruleSucceeded mc R rule k = ret .safe := by simp only [ruleSucceeded, hr, ↓reduceIte]
    rw [hm]
    apply mcorr_congr (mcorr_ret .safe) 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.ruleSucceeded]
    simp only [h.recovery rule, hr, ↓reduceIte]
    rfl
  · have hr' : HsSet.member rule tc.ctxRecovery = false := by rw [h.recovery rule]; simpa using hr
    by_cases he : (mc.entries.contains rule && k.meets endOfInput) = true
    · have hm : ruleSucceeded mc R rule k =
          ret (.mayReject ("the input can end after the rule " ++ rule ++ ", which is an entry")) := by
        have hr0 : mc.recovery.contains rule = false := by simpa using hr
        simp only [ruleSucceeded, hr0, Bool.false_eq_true, ↓reduceIte, he]
      rw [hm]
      apply mcorr_congr (mcorr_ret _) 1
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [LabelsTranslated.ruleSucceeded]
      have he' : HsBase.and (HsSet.member rule tc.ctxEntries) (LabelsTranslated.meets (eCS k)
          LabelsTranslated.endOfInput) = true := by
        rw [h.entries rule, endOfInput_e, meets_e]; exact he
      simp only [hr', Bool.false_eq_true, ↓reduceIte, he']
      simp [eVerdict, HsText.append, String.append_assoc]
    · have hm : ruleSucceeded mc R rule k = allOf ((callersOf mc rule).map fun s => R.succeeded s.rule s.frames k) := by
        have hr0 : mc.recovery.contains rule = false := by simpa using hr
        have he0 : (mc.entries.contains rule && k.meets endOfInput) = false := by simpa using he
        simp only [ruleSucceeded, hr0, Bool.false_eq_true, ↓reduceIte, he0]
      rw [hm]
      have hl := mcorrList_map (f := fun s => R.succeeded s.rule s.frames k)
        (g := fun s => fun n => LabelsTranslated.succeeded (n - 1) tc s.rule (s.frames.map eFrame) (eCS k))
        (callersOf mc rule) (fun s _ => mcorr_pred (hR.succeeded _ _ _))
      apply mcorr_congr (mcorr_allOf hl) 1
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [LabelsTranslated.ruleSucceeded]
      have he' : HsBase.and (HsSet.member rule tc.ctxEntries) (LabelsTranslated.meets (eCS k)
          LabelsTranslated.endOfInput) = false := by
        rw [h.entries rule, endOfInput_e, meets_e]; simp only [HsBase.and]; exact Bool.eq_false_iff.2 he
      simp only [hr', Bool.false_eq_true, ↓reduceIte, he', callersOf_e h, HsList.concatMap, flatMap_single,
        List.map_map]
      rfl

theorem again_corr (h : CtxCorr tc mc) {R : Rec} (hR : RecCorr tc mc R) (rule : String) (k : CharSet) (x : Expr)
    (l : Loc) (rest : List Frame) :
    MCorr (if (possible (exprAbs mc.pass x)).meets k then
        ret (.mayReject ("the repetition at " ++ showLoc l ++ " can continue"))
      else R.succeeded rule rest k)
      (fun n => LabelsTranslated.succeeded.again_621 n tc rule (eCS k) (eExpr x) (eLoc l) (rest.map eFrame)) := by
  have hc : LabelsTranslated.meets (LabelsTranslated.possible (LabelsTranslated.exprAbs tc.ctxPass (eExpr x))) (eCS k) =
      (possible (exprAbs mc.pass x)).meets k := by rw [exprAbs_e h.pass, possible_e, meets_e]
  by_cases hm : (possible (exprAbs mc.pass x)).meets k = true
  · simp only [hm, ↓reduceIte]
    apply mcorr_congr (mcorr_ret _) 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.succeeded.again_621]
    simp only [hc, hm, ↓reduceIte]
    simp [eVerdict, HsText.append, showLoc_e, String.append_assoc]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    apply mcorr_congr (mcorr_pred (hR.succeeded rule rest k)) 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.succeeded.again_621]
    simp only [hc, hm, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem growingSeeds_e (g : String → Int → Bool) (gm : String → Nat → Bool) (hg : ∀ n (i : Nat), g n i = gm n i)
    (rule : String) (as' : List (Loc × List Item)) (f : List LabelsTranslated.Frame → TSt) :
    ∀ (k0 : Nat) (rest : List (Loc × List Item)),
      HsList.concatMap (fun p => if g rule p.1 then [f [LabelsTranslated.Frame.FSeq p.2.2 0,
          LabelsTranslated.Frame.FAlts (eGalts as') p.1 true]] else []) (HsList.zipFrom (k0 : Int) (eGalts rest)) =
        ((indexed k0 rest).filter (fun p => gm rule p.1)).map
          (fun p => f ([Frame.seq p.2.2 0, Frame.alts as' p.1 true].map eFrame))
  | _, [] => rfl
  | k0, (l, is) :: rest => by
    have ih := growingSeeds_e g gm hg rule as' f (k0 + 1) rest
    simp only [HsList.concatMap, eGalts] at ih ⊢
    rw [List.map_cons, zipFrom_cons, List.flatMap_cons, indexed, List.filter_cons]
    rw [show ((k0 : Int) + 1) = ((k0 + 1 : Nat) : Int) by omega]
    rw [ih, hg]
    split <;> simp [eFrame, eGalts]

theorem ended_corr (h : CtxCorr tc mc) {R : Rec} (hR : RecCorr tc mc R) (rule : String)
    (as' : List (Loc × List Item)) (i : Nat) (body : Bool) (rest : List Frame) (k' : CharSet) :
    MCorr (if (body && mc.directLr.contains rule && mc.growing rule i) then
        allOf (R.succeeded rule [] k' ::
          ((indexed 0 as').filter (fun p => mc.growing rule p.1)).map
            (fun p => R.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k'))
      else R.succeeded rule rest k')
      (fun n => LabelsTranslated.succeeded.ended_596 n tc rule (eFrame (.alts as' i body)) (rest.map eFrame)
        (HsBase.and body (HsBase.and (HsSet.member rule tc.ctxDirectLr) (tc.ctxGrowing rule i))) (eCS k')) := by
  have hga : HsBase.and body (HsBase.and (HsSet.member rule tc.ctxDirectLr) (tc.ctxGrowing rule i)) =
      (body && mc.directLr.contains rule && mc.growing rule i) := by
    simp [HsBase.and, h.directLr rule, h.growing rule i, Bool.and_assoc]
  rw [hga]
  by_cases hg : (body && mc.directLr.contains rule && mc.growing rule i) = true
  · simp only [hg, ↓reduceIte]
    have hl := MCorrList.cons (mcorr_pred (hR.succeeded rule [] k'))
      (mcorrList_map (f := fun p => R.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k')
        (g := fun p => fun n => LabelsTranslated.succeeded (n - 1) tc rule
          ([Frame.seq p.2.2 0, Frame.alts as' p.1 true].map eFrame) (eCS k'))
        ((indexed 0 as').filter (fun p => mc.growing rule p.1)) (fun p _ => mcorr_pred (hR.succeeded _ _ _)))
    apply mcorr_congr (mcorr_allOf hl) 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.succeeded.ended_596]
    simp only [hg, ↓reduceIte, eFrame, HsList.concatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have := growingSeeds_e tc.ctxGrowing mc.growing h.growing rule as'
      (fun fs => LabelsTranslated.succeeded m tc rule fs (eCS k')) 0 as'
    simp only [HsList.concatMap] at this
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_sub_cancel]
    congr 2
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    apply mcorr_congr (mcorr_pred (hR.succeeded rule rest k')) 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.succeeded.ended_596]
    simp only [hg, Bool.false_eq_true, ↓reduceIte]
    rfl


/-! ## The bodies of `failed` and `succeeded` -/

theorem mcorr_of_eq {c : PegHs.LabelCheck.M} {t t' : Nat → TSt} (h : MCorr c t) (he : ∀ n, t' n = t n) : MCorr c t' :=
  mcorr_congr h 0 (fun n _ => he n)

theorem laterList_e (g : String → Int → Bool) (gm : String → Nat → Bool) (hg : ∀ n (i : Nat), g n i = gm n i)
    (rule : String) (ga : Bool) (alts : List (Loc × List Item)) (i : Nat) :
    HsList.concatMap (fun p => if HsBase.or (HsBase.not ga) (g rule p.1) = true then [(p.2.1, p.2.2)] else [])
      (HsList.drop (HsInt.add (i : Int) 1) (HsList.zipFrom 0 (eGalts alts))) =
    (((indexed 0 alts).drop (i + 1)).filter (fun p => !ga || gm rule p.1)).map
      (fun p => (eLoc p.2.1, eItems p.2.2)) := by
  have hz : ∀ (k : Nat) (l : List (Loc × List Item)),
      HsList.zipFrom (k : Int) (eGalts l) = (indexed k l).map (fun p => ((p.1 : Int), eLoc p.2.1, eItems p.2.2)) := by
    intro k l
    induction l generalizing k with
    | nil => rfl
    | cons x xs ih =>
      rw [eGalts, List.map_cons, zipFrom_cons, show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega]
      simp only [eGalts] at ih
      rw [ih]
      rfl
  rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, hz]
  simp only [HsList.drop, HsInt.add, show ((i : Int) + 1).toNat = i + 1 by omega, ← List.map_drop]
  generalize (indexed 0 alts).drop (i + 1) = l
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [HsList.concatMap] at ih ⊢
    rw [List.map_cons, List.flatMap_cons, ih, List.filter_cons]
    simp only [HsBase.or, HsBase.not, hg]
    split <;> simp_all

theorem failedBody_seqAlts (ctx : Ctx) (R : Rec) (rule : String) (items : List Item) (j : Nat)
    (alts : List (Loc × List Item)) (i : Nat) (body : Bool) (rest : List Frame) (pre : List Item) (lifts : Nat)
    (k : CharSet) :
    failedBody ctx R rule (.seq items j :: .alts alts i body :: rest) pre lifts k =
      (if body && ctx.otherLr.contains rule && ctx.growing rule i then
        ret (.unchecked ("it is in a growing alternative of " ++ rule ++
          ", which takes part in indirect or hidden left recursion"))
      else match ((((indexed 0 alts).drop (i + 1)).filter
          (fun p => !(body && ctx.directLr.contains rule && ctx.growing rule i) || ctx.growing rule p.1)).map
            (mLaterCheck ctx items j (items.take j ++ pre) k)).foldr andAlso .safe with
        | .safe => if (body && ctx.directLr.contains rule && ctx.growing rule i) then
            R.succeeded rule [] (beforeItems ctx ((items.take j ++ pre).drop 1) k)
          else R.failed rule rest (items.take j ++ pre, lifts) k
        | v => ret v) := rfl

theorem failedBody_corr (h : CtxCorr tc mc) {E : Nat}
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    {R : Rec} (hR : RecCorr tc mc R) (rule : String) (fs : List Frame) (pre : List Item) (lifts : Nat) (k : CharSet) :
    MCorr (failedBody mc R rule fs pre lifts k)
      (fun n => LabelsTranslated.tFailedBody n tc rule (fs.map eFrame) (eItems pre) lifts (eCS k)) := by
  have hks : LabelsTranslated.beforeItems tc (eItems pre) (eCS k) = eCS (beforeItems mc pre k) := beforeItems_e h pre k
  match fs with
  | [] =>
    simp only [failedBody]
    exact mcorr_of_eq (ruleFailed_corr h hR rule pre lifts k) (fun n => by simp [LabelsTranslated.tFailedBody])
  | .star x l :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (hR.succeeded rule rest _) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame, hks])
  | .opt :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (hR.succeeded rule rest _) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame, hks])
  | .plus x l :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (mcorr_allOf (.cons (hR.failed rule rest pre lifts k) (.cons (hR.succeeded rule rest _) .nil)))
      (fun n => by simp [LabelsTranslated.tFailedBody, eFrame, hks])
  | .and l :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame]; rfl)
  | .not l :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame]; rfl)
  | .label :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (hR.failed rule rest pre lifts k) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame])
  | .capture :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (hR.failed rule rest pre lifts k) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame])
  | .alts as i b :: rest =>
    simp only [failedBody]
    exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame]; rfl)
  | [.seq items j] =>
    simp only [failedBody]
    exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame]; rfl)
  | .seq items j :: f2 :: rest =>
    cases f2 with
    | alts alts i body =>
      rw [failedBody_seqAlts]
      have hga : HsBase.and body (HsBase.and (HsSet.member rule tc.ctxDirectLr) (tc.ctxGrowing rule i)) =
          (body && mc.directLr.contains rule && mc.growing rule i) := by
        simp [HsBase.and, h.directLr rule, h.growing rule i, Bool.and_assoc]
      have hun : HsBase.and body (HsBase.and (HsSet.member rule tc.ctxOtherLr) (tc.ctxGrowing rule i)) =
          (body && mc.otherLr.contains rule && mc.growing rule i) := by
        simp [HsBase.and, h.otherLr rule, h.growing rule i, Bool.and_assoc]
      have hmatched : HsList.append (HsList.take (j : Int) (eItems items)) (eItems pre) = eItems (items.take j ++ pre) := by
        rw [eItems_take, eItems_append]; rfl
      have hlater := laterList_e tc.ctxGrowing mc.growing h.growing rule
        (body && mc.directLr.contains rule && mc.growing rule i) alts i
      have hlc : Eventually (fun n => ∀ p ∈ ((indexed 0 alts).drop (i + 1)).filter
          (fun p => !(body && mc.directLr.contains rule && mc.growing rule i) || mc.growing rule p.1),
          LabelsTranslated.failed.laterCheck_541 n tc (eItems items) j (eItems (items.take j ++ pre)) (eCS k)
            (eLoc p.2.1, eItems p.2.2) = eVerdict (mLaterCheck mc items j (items.take j ++ pre) k p)) :=
        Eventually.forall_mem _ (fun p _ => laterCheck_ev h hE items j (items.take j ++ pre) k p)
      obtain ⟨N, hN⟩ := hlc
      have hT : ∀ n, N ≤ n → LabelsTranslated.tFailedBody n tc rule ((Frame.seq items j :: Frame.alts alts i body :: rest).map eFrame)
          (eItems pre) lifts (eCS k) =
          (if (body && mc.otherLr.contains rule && mc.growing rule i) then
            LabelsTranslated.instApplicative_pure_State (LabelsTranslated.Verdict.Unchecked
              ("it is in a growing alternative of " ++ rule ++ ", which takes part in indirect or hidden left recursion"))
          else match ((((indexed 0 alts).drop (i + 1)).filter
              (fun p => !(body && mc.directLr.contains rule && mc.growing rule i) || mc.growing rule p.1)).map
                (mLaterCheck mc items j (items.take j ++ pre) k)).foldr andAlso .safe with
            | .safe => if (body && mc.directLr.contains rule && mc.growing rule i) then
                LabelsTranslated.succeeded n tc rule [] (eCS (beforeItems mc ((items.take j ++ pre).drop 1) k))
              else LabelsTranslated.failed n tc rule (rest.map eFrame) (eItems (items.take j ++ pre), (lifts : Int)) (eCS k)
            | v => LabelsTranslated.instApplicative_pure_State (eVerdict v)) := by
        intro n hn
        simp only [LabelsTranslated.tFailedBody, List.map_cons, eFrame]
        rw [hun]
        split
        · simp [HsText.append, String.append_assoc]
        · simp only [hga, hmatched]
          rw [hlater, List.map_map]
          have hv : HsList.foldr (fun a b => LabelsTranslated.andAlso a b) LabelsTranslated.Verdict.Safe
              ((((indexed 0 alts).drop (i + 1)).filter (fun p => !(body && mc.directLr.contains rule && mc.growing rule i) ||
                mc.growing rule p.1)).map ((fun p => LabelsTranslated.failed.laterCheck_541 n tc (eItems items) j
                  (eItems (items.take j ++ pre)) (eCS k) p) ∘ fun p => (eLoc p.2.1, eItems p.2.2))) =
              eVerdict (((((indexed 0 alts).drop (i + 1)).filter (fun p => !(body && mc.directLr.contains rule &&
                mc.growing rule i) || mc.growing rule p.1)).map (mLaterCheck mc items j (items.take j ++ pre) k)).foldr
                  andAlso .safe) := by
            rw [← foldrAndAlso_e, List.map_map]
            congr 1
            apply List.map_congr_left
            intro p hp
            exact hN n hn p hp
          rw [hv]
          generalize ((((indexed 0 alts).drop (i + 1)).filter (fun p => !(body && mc.directLr.contains rule &&
            mc.growing rule i) || mc.growing rule p.1)).map (mLaterCheck mc items j (items.take j ++ pre) k)).foldr
              andAlso .safe = v
          cases v with
          | safe =>
            simp only [eVerdict]
            rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, kAt_e h]
          | mayReject w => rfl
          | unchecked w => rfl
      apply mcorr_congr ?_ N hT
      by_cases hc : (body && mc.otherLr.contains rule && mc.growing rule i) = true
      · simp only [hc, ↓reduceIte]
        exact mcorr_ret _
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        generalize ((((indexed 0 alts).drop (i + 1)).filter (fun p => !(body && mc.directLr.contains rule &&
          mc.growing rule i) || mc.growing rule p.1)).map (mLaterCheck mc items j (items.take j ++ pre) k)).foldr
            andAlso .safe = v
        cases v with
        | safe =>
          by_cases hg : (body && mc.directLr.contains rule && mc.growing rule i) = true
          · simp only [hg, ↓reduceIte]
            exact hR.succeeded rule [] _
          · simp only [hg, Bool.false_eq_true, ↓reduceIte]
            exact hR.failed rule rest _ lifts k
        | mayReject w => exact mcorr_ret _
        | unchecked w => exact mcorr_ret _
    | _ =>
      simp only [failedBody]
      exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tFailedBody, eFrame]; rfl)

/-- `ended` of `succeeded`, in the model. -/
def mEnded (ctx : Ctx) (R : Rec) (rule : String) (as' : List (Loc × List Item)) (i : Nat) (body : Bool)
    (rest : List Frame) (k' : CharSet) : PegHs.LabelCheck.M :=
  if (body && ctx.directLr.contains rule && ctx.growing rule i) then
    allOf (R.succeeded rule [] k' ::
      ((indexed 0 as').filter (fun p => ctx.growing rule p.1)).map
        (fun p => R.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k'))
  else R.succeeded rule rest k'

theorem succeededBody_seqAlts (ctx : Ctx) (R : Rec) (rule : String) (items : List Item) (j : Nat)
    (as' : List (Loc × List Item)) (i : Nat) (body : Bool) (rest : List Frame) (k : CharSet) :
    succeededBody ctx R rule (.seq items j :: .alts as' i body :: rest) k =
      (if body && ctx.otherLr.contains rule && ctx.growing rule i then
        ret (.unchecked ("it reaches a growing alternative of " ++ rule ++
          ", which takes part in indirect or hidden left recursion"))
      else match items.drop (j + 1) with
        | next :: _ =>
          if (seqAbs ctx.pass (items.drop (j + 1))).consume.meets k then
            ret (.mayReject ("the parse can continue at " ++ showLoc (itemLoc next)))
          else allOf ([R.failed rule (.seq items (j + 1) :: .alts as' i body :: rest) ([], 0) k] ++
            ((List.range' (j + 2) (items.length - (j + 2))).map
              (fun m => R.failed rule (.seq items m :: .alts as' i body :: rest) ([], 0) everything)) ++
            (if (seqAbs ctx.pass (items.drop (j + 1))).empty.meets k then
              [mEnded ctx R rule as' i body rest ((seqAbs ctx.pass (items.drop (j + 1))).empty.intersect k)] else []))
        | [] => allOf ((if (seqAbs ctx.pass (items.drop (j + 1))).empty.meets k then
              [mEnded ctx R rule as' i body rest ((seqAbs ctx.pass (items.drop (j + 1))).empty.intersect k)] else []))) :=
  rfl

theorem enumFromTo_e (a len : Nat) :
    HsList.enumFromTo ((a : Int)) (HsInt.sub (len : Int) 1) = (List.range' a (len - a)).map (fun m : Nat => (m : Int)) := by
  simp only [HsList.enumFromTo, HsInt.sub, List.range'_eq_map_range, List.map_map]
  have : ((len : Int) - 1 + 1 - (a : Int)).toNat = len - a := by omega
  rw [this]
  apply List.map_congr_left
  intro m _
  simp [Function.comp_def]

theorem succeededBody_corr (h : CtxCorr tc mc) {R : Rec} (hR : RecCorr tc mc R) (rule : String) (fs : List Frame)
    (k : CharSet) :
    MCorr (succeededBody mc R rule fs k)
      (fun n => LabelsTranslated.tSucceededBody n tc rule (fs.map eFrame) (eCS k)) := by
  match fs with
  | [] =>
    simp only [succeededBody]
    exact mcorr_of_eq (ruleSucceeded_corr h hR rule k) (fun n => by simp [LabelsTranslated.tSucceededBody])
  | .star x l :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (again_corr h hR rule k x l rest) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame])
  | .plus x l :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (again_corr h hR rule k x l rest) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame])
  | .opt :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (hR.succeeded rule rest k) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame])
  | .and l :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (mcorr_ret _) (fun n => by
      simp [LabelsTranslated.tSucceededBody, eFrame, eVerdict, HsText.append, showLoc_e, String.append_assoc])
  | .not l :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (mcorr_ret _) (fun n => by
      simp [LabelsTranslated.tSucceededBody, eFrame, eVerdict, HsText.append, showLoc_e, String.append_assoc])
  | .label :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (hR.succeeded rule rest k) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame])
  | .capture :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (hR.succeeded rule rest k) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame])
  | .alts as i b :: rest =>
    simp only [succeededBody]
    exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame]; rfl)
  | [.seq items j] =>
    simp only [succeededBody]
    exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame]; rfl)
  | .seq items j :: f2 :: rest =>
    cases f2 with
    | alts as' i body =>
      rw [succeededBody_seqAlts]
      have hun : HsBase.and body (HsBase.and (HsSet.member rule tc.ctxOtherLr) (tc.ctxGrowing rule i)) =
          (body && mc.otherLr.contains rule && mc.growing rule i) := by
        simp [HsBase.and, h.otherLr rule, h.growing rule i, Bool.and_assoc]
      have hafter : HsList.drop (HsInt.add (j : Int) 1) (eItems items) = eItems (items.drop (j + 1)) := by
        rw [show HsInt.add (j : Int) 1 = ((j + 1 : Nat) : Int) by simp [HsInt.add], eItems_drop]
      have hA : LabelsTranslated.seqAbs tc.ctxPass (eItems (items.drop (j + 1))) =
          eAbs (seqAbs mc.pass (items.drop (j + 1))) := seqAbs_e h.pass _
      have hended : ∀ k', MCorr (mEnded mc R rule as' i body rest k')
          (fun n => LabelsTranslated.succeeded.ended_596 n tc rule (eFrame (.alts as' i body)) (rest.map eFrame)
            (HsBase.and body (HsBase.and (HsSet.member rule tc.ctxDirectLr) (tc.ctxGrowing rule i))) (eCS k')) :=
        fun k' => ended_corr h hR rule as' i body rest k'
      by_cases hc : (body && mc.otherLr.contains rule && mc.growing rule i) = true
      · simp only [hc, ↓reduceIte]
        exact mcorr_of_eq (mcorr_ret _) (fun n => by
          simp only [LabelsTranslated.tSucceededBody, List.map_cons, eFrame, hun, hc, ↓reduceIte]
          simp [eVerdict, HsText.append, String.append_assoc])
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        have hc' : (body && mc.otherLr.contains rule && mc.growing rule i) = false := by simpa using hc
        have hlen : HsInt.add (j : Int) 2 = ((j + 2 : Nat) : Int) := by simp [HsInt.add]
        have hlen2 : HsList.length (eItems items) = ((items.length : Nat) : Int) := eItems_length items
        have hj1 : HsInt.add (j : Int) 1 = ((j + 1 : Nat) : Int) := by simp [HsInt.add]
        have hemp : ∀ c : Bool, ∀ (k' : CharSet),
            MCorrList (if c then [mEnded mc R rule as' i body rest k'] else [])
              (if c then [fun n => LabelsTranslated.succeeded.ended_596 n tc rule (eFrame (.alts as' i body))
                (rest.map eFrame) (HsBase.and body (HsBase.and (HsSet.member rule tc.ctxDirectLr)
                  (tc.ctxGrowing rule i))) (eCS k')] else []) := by
          intro c k'
          cases c
          · exact .nil
          · exact .cons (hended k') .nil
        cases hd : items.drop (j + 1) with
        | nil =>
          have hl : items.length ≤ j + 1 := by
            have := congrArg List.length hd
            simp at this; omega
          have hA0 : LabelsTranslated.seqAbs tc.ctxPass [] = eAbs (seqAbs mc.pass []) := by
            have := seqAbs_e h.pass []
            simpa [eItems] using this
          apply mcorr_of_eq (mcorr_allOf (hemp ((seqAbs mc.pass []).empty.meets k)
            ((seqAbs mc.pass []).empty.intersect k)))
          intro n
          simp only [LabelsTranslated.tSucceededBody, List.map_cons, eFrame, hun, hc', Bool.false_eq_true,
            ↓reduceIte]
          simp only [hafter, hd]
          simp only [eItems, hA0, eAbs, LabelsTranslated.Abs.absEmpty, meets_e, intersect_e,
            HsList.null, HsBase.not, hlen, hlen2, enumFromTo_e, HsList.append, HsList.concatMap]
          simp only [show items.length - (j + 2) = 0 by omega, List.range'_zero, List.map_nil, List.flatMap_nil,
            List.nil_append, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hcm : (seqAbs mc.pass []).empty.meets k = true
          · simp [hcm]
          · simp [hcm]
        | cons next tl =>
          obtain ⟨l0, b0, e0⟩ := next
          have hA1 : LabelsTranslated.seqAbs tc.ctxPass (eItems ((l0, b0, e0) :: tl)) = eAbs (seqAbs mc.pass ((l0, b0, e0) :: tl)) :=
            seqAbs_e h.pass _
          by_cases hcm : (seqAbs mc.pass ((l0, b0, e0) :: tl)).consume.meets k = true
          · simp only [hcm, ↓reduceIte]
            apply mcorr_of_eq (mcorr_ret _)
            intro n
            simp only [LabelsTranslated.tSucceededBody, List.map_cons, eFrame, hun, hc', Bool.false_eq_true,
              ↓reduceIte]
            simp only [hafter, hd]
            simp only [hA1]
            simp only [eAbs, LabelsTranslated.Abs.absConsume, meets_e, hcm]
            simp [eItems, LabelsTranslated.Item.itemLoc, showLoc_e, eVerdict, HsText.append, String.append_assoc,
              itemLoc]
          · simp only [hcm, Bool.false_eq_true, ↓reduceIte]
            have hl := MCorrList.cons (hR.failed rule (.seq items (j + 1) :: .alts as' i body :: rest) [] 0 k)
              (mcorrList_append (mcorrList_map
                (f := fun m => R.failed rule (.seq items m :: .alts as' i body :: rest) ([], 0) everything)
                (g := fun m => fun n => LabelsTranslated.failed n tc rule
                  ((Frame.seq items m :: .alts as' i body :: rest).map eFrame) (eItems [], ((0 : Nat) : Int))
                  (eCS everything))
                (List.range' (j + 2) (items.length - (j + 2))) (fun m _ => hR.failed _ _ _ _ _))
                (hemp ((seqAbs mc.pass ((l0, b0, e0) :: tl)).empty.meets k) ((seqAbs mc.pass ((l0, b0, e0) :: tl)).empty.intersect k)))
            apply mcorr_of_eq (mcorr_allOf hl)
            intro n
            simp only [LabelsTranslated.tSucceededBody, List.map_cons, eFrame, hun, hc', Bool.false_eq_true,
              ↓reduceIte]
            simp only [hafter, hd]
            simp only [hA1]
            have hne : HsBase.not (HsList.null (eItems ((l0, b0, e0) :: tl))) = true := by simp [HsList.null, eItems, HsBase.not]
            simp only [eAbs, LabelsTranslated.Abs.absConsume, LabelsTranslated.Abs.absEmpty,
              meets_e, hcm, intersect_e, hne, hlen, hlen2, hj1, enumFromTo_e, HsList.append,
              HsList.concatMap, everything_e, flatMap_single, List.map_map, List.map_append]
            have he0 : eItems [] = [] := rfl
            simp only [he0, Int.natCast_zero, eItems]
            by_cases hce : (seqAbs mc.pass ((l0, b0, e0) :: tl)).empty.meets k = true
            · simp [hce, Function.comp_def]
            · simp [hce, Function.comp_def]
    | _ =>
      simp only [succeededBody]
      exact mcorr_of_eq (mcorr_ret .safe) (fun n => by simp [LabelsTranslated.tSucceededBody, eFrame]; rfl)


/-! ## A step, the run, the verdict -/

variable {E : Nat}

theorem truncate_e (h : CtxCorr tc mc) (pre0 : List Item) (k0 : CharSet) :
    (if HsInt.gt (HsList.length (eItems pre0)) LabelsTranslated.maxPrefix then
      (([] : List LabelsTranslated.Item), LabelsTranslated.beforeItems tc (eItems pre0) (eCS k0))
    else (eItems pre0, eCS k0)) = (eItems (truncate mc pre0 k0).1, eCS (truncate mc pre0 k0).2) := by
  simp only [truncate, HsInt.gt, eItems_length, LabelsTranslated.maxPrefix, maxPrefix]
  by_cases hl : pre0.length > 8
  · have hl' : ((pre0.length : Int) > 8) := by omega
    simp [hl, hl', beforeItems_e h, eItems]
  · have hl' : ¬ ((pre0.length : Int) > 8) := by omega
    simp [hl, hl']

theorem step_corr (hk : mc.keyOf = tKeyOf) (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    {R : Rec} (hR : RecCorr tc mc R) : RecCorr tc mc (step mc R) where
  failed rule fs pre0 lifts k0 := by
    have hv := mcorr_pred (mcorr_visit hk (failedBody_corr h hE hR rule fs (truncate mc pre0 k0).1 lifts
      (truncate mc pre0 k0).2) rule fs .failed (truncate mc pre0 k0).1 lifts (truncate mc pre0 k0).2)
    apply mcorr_congr hv 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.failed_succ]
    simp only [truncate_e h]
    rfl
  succeeded rule fs k := by
    have hv := mcorr_pred (mcorr_visit hk (succeededBody_corr h hR rule fs k) rule fs .succeeded [] 0 k)
    apply mcorr_congr hv 1
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [LabelsTranslated.succeeded_succ]
    rfl

theorem run_corr (hk : mc.keyOf = tKeyOf) (h : CtxCorr tc mc)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts) :
    ∀ m, RecCorr tc mc (run mc m)
  | 0 => ⟨fun _ _ _ _ _ _ _ hc => by simp [run] at hc, fun _ _ _ _ _ hc => by simp [run] at hc⟩
  | m + 1 => step_corr hk h hE (run_corr hk h hE m)

theorem startSet_e (h : CtxCorr tc mc) (x : Expr) :
    LabelsTranslated.minus LabelsTranslated.everything
      (LabelsTranslated.Abs.absSure (LabelsTranslated.exprAbs tc.ctxPass (eExpr x))) = eCS (startSet mc x) := by
  simp [startSet, exprAbs_e h.pass, eAbs, LabelsTranslated.Abs.absSure, everything_e, minus_e]

theorem vrel_empty : VRel HsSet.empty [] := fun _ => rfl

/-- The translated check of a label gives the model's verdict, at every fuel from some bound on. -/
theorem verdictOf_ev (hk : mc.keyOf = tKeyOf) (h : CtxCorr tc mc) (hp : PassWF mc.pass)
    (hE : ∀ f, E ≤ f → ∀ (name : String) (args : List (Loc × String)),
      LabelsTranslated.expandCall f tc name (args.map eLocated) = (expandCall mc name args).map eAlts)
    (rule : String) (fs : List Frame) (x : Expr) :
    Eventually (fun n => LabelsTranslated.verdictOf n tc rule (fs.map eFrame) (eExpr x) =
      eVerdict (verdictOf mc rule fs x)) := by
  have hb := verdictFuel_bound hp rule fs x
  simp only [verdictFuel, Option.map_eq_some_iff] at hb
  obtain ⟨r, hr, hv⟩ := hb
  obtain ⟨N, hN⟩ := (run_corr hk h hE (fuelBound mc rule fs)).failed rule fs [] 0 (startSet mc x) [] r hr
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨VT', e, _⟩ := hN n hn HsSet.empty vrel_empty
  simp only [LabelsTranslated.verdictOf, LabelsTranslated.evalState, startSet_e h]
  have : (([] : List LabelsTranslated.Item), (0 : Int)) = (eItems [], ((0 : Nat) : Int)) := rfl
  rw [this, e, hv]


/-! ## The translated context does not change with more fuel -/

theorem fixpointGo_stable (rules : List LabelsTranslated.Rule)
    (mk : HsMap String LabelsTranslated.Abs → LabelsTranslated.Pass) :
    ∀ (b c : Nat) (env : HsMap String LabelsTranslated.Abs), 1001 - c ≤ b → ∀ n m, b + 1 ≤ n → b + 1 ≤ m →
      LabelsTranslated.fixpoint.go_197 n rules mk env c = LabelsTranslated.fixpoint.go_197 m rules mk env c := by
  intro b
  induction b with
  | zero =>
    intro c env hb n m hn hm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [LabelsTranslated.fixpoint.go_197, LabelsTranslated.fixpoint.go_197]
    have hc : HsInt.gt (c : Int) 1000 = true := by simp [HsInt.gt]; omega
    simp [HsBase.or, hc]
  | succ b ih =>
    intro c env hb n m hn hm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [LabelsTranslated.fixpoint.go_197, LabelsTranslated.fixpoint.go_197]
    simp only [HsInt.add, show (c : Int) + 1 = ((c + 1 : Nat) : Int) by omega]
    split
    · rfl
    · rename_i hcond
      have : c ≤ 1000 := by
        simp only [HsBase.or, HsInt.gt, Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
        omega
      exact ih (c + 1) _ (by omega) n' m' (by omega) (by omega)

theorem fixpoint_stable (rules : List LabelsTranslated.Rule)
    (mk : HsMap String LabelsTranslated.Abs → LabelsTranslated.Pass) (n m : Nat) (hn : 1002 ≤ n) (hm : 1002 ≤ m) :
    LabelsTranslated.fixpoint n rules mk = LabelsTranslated.fixpoint m rules mk := by
  simp only [LabelsTranslated.fixpoint]
  exact fixpointGo_stable rules mk 1001 0 _ (by omega) n m hn hm

theorem abstractions_stable (rules : List LabelsTranslated.Rule) (n m : Nat) (hn : 1002 ≤ n) (hm : 1002 ≤ m) :
    LabelsTranslated.abstractions n rules = LabelsTranslated.abstractions m rules := by
  simp only [LabelsTranslated.abstractions]
  have e1 := fixpoint_stable rules (fun ν => LabelsTranslated.abstractions.pass1_206 ν) n m hn hm
  rw [e1]
  have e2 := fixpoint_stable rules (fun ν => LabelsTranslated.abstractions.pass2_209 (LabelsTranslated.fixpoint m rules
    (fun ν => LabelsTranslated.abstractions.pass1_206 ν)) ν) n m hn hm
  rw [e2]
  have e3 := fixpoint_stable rules (fun ν => LabelsTranslated.abstractions.pass3_212 (LabelsTranslated.fixpoint m rules
    (fun ν => LabelsTranslated.abstractions.pass1_206 ν)) (LabelsTranslated.fixpoint m rules (fun ν =>
      LabelsTranslated.abstractions.pass2_209 (LabelsTranslated.fixpoint m rules
        (fun ν => LabelsTranslated.abstractions.pass1_206 ν)) ν)) ν) n m hn hm
  rw [e3]

theorem nullableGo_stable {rulesT : List LabelsTranslated.Rule} {rulesM : List Rule} (hr : RulesCorr rulesT rulesM) :
    ∀ (b : Nat) (k : List String), Sub k (nullStep rulesM k) → ∀ (s : HsSet String),
      ((rulesM.map (·.name)).filter (fun x => !k.contains x)).length ≤ b → SetCorr s k →
      ∀ n m, b + 1 ≤ n → b + 1 ≤ m →
        LabelsTranslated.nullableRules.go_948 n rulesT s = LabelsTranslated.nullableRules.go_948 m rulesT s := by
  intro b
  induction b with
  | zero =>
    intro k hk s hb hs n m hn hm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [LabelsTranslated.nullableRules.go_948, LabelsTranslated.nullableRules.go_948]
    simp only [nullStep_e hr hs]
    rw [setCorr_beq (setCorr_fromList _) hs]
    by_cases he : setEq (nullStep rulesM k) k = true
    · simp [he]
    · exfalso
      have := missing_lt (names := rulesM.map (·.name)) hk (nullStep_names rulesM k) (by simpa using he)
      omega
  | succ b ih =>
    intro k hk s hb hs n m hn hm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [LabelsTranslated.nullableRules.go_948, LabelsTranslated.nullableRules.go_948]
    simp only [nullStep_e hr hs]
    rw [setCorr_beq (setCorr_fromList _) hs]
    by_cases he : setEq (nullStep rulesM k) k = true
    · simp [he]
    · have hlt := missing_lt (names := rulesM.map (·.name)) hk (nullStep_names rulesM k) (by simpa using he)
      have he' : setEq (nullStep rulesM k) k = false := by simpa using he
      simp only [he', Bool.false_eq_true, ↓reduceIte]
      exact ih _ (nullStep_mono hk) _ (by omega) (setCorr_fromList _) n' m' (by omega) (by omega)

theorem nullableRules_stable {rulesT : List LabelsTranslated.Rule} {rulesM : List Rule} (hr : RulesCorr rulesT rulesM)
    (n m : Nat) (hn : rulesM.length + 1 ≤ n) (hm : rulesM.length + 1 ≤ m) :
    LabelsTranslated.nullableRules n rulesT = LabelsTranslated.nullableRules m rulesT := by
  unfold LabelsTranslated.nullableRules
  apply nullableGo_stable hr rulesM.length [] (fun _ h => by simp at h) HsSet.empty _
    (fun n => by simp [HsSet.member, HsSet.empty]) n m hn hm
  have := List.length_filter_le (fun x => !([] : List String).contains x) (rulesM.map (·.name))
  simpa using this

theorem context_stable {tg : LabelsTranslated.Grammar} {mg : Grammar} (h : GrammarCorr tg mg) :
    ∃ N, ∀ n m, N ≤ n → N ≤ m → LabelsTranslated.context n tg = LabelsTranslated.context m tg := by
  obtain ⟨S, hS⟩ := rulesSites_ev h.rules
  refine ⟨max S (max 1002 (mg.rules.length + 1)), fun n m hn hm => ?_⟩
  rw [tContext_eq, tContext_eq]
  simp only [tContext]
  rw [abstractions_stable _ n m (by omega) (by omega)]
  have hs : HsList.concatMap (fun r => HsList.concatMap tCallerPairs (LabelsTranslated.sites n r)) tg.grammarRules =
      HsList.concatMap (fun r => HsList.concatMap tCallerPairs (LabelsTranslated.sites m r)) tg.grammarRules := by
    have h1 : HsList.concatMap (fun r => LabelsTranslated.sites n r) tg.grammarRules =
        HsList.concatMap (fun r => LabelsTranslated.sites m r) tg.grammarRules := by
      rw [hS n (by omega), hS m (by omega)]
    simp only [HsList.concatMap] at h1 ⊢
    rw [← List.flatMap_assoc, ← List.flatMap_assoc, h1]
  rw [hs]
  have hl : LabelsTranslated.leftRecursion n tg.grammarRules = LabelsTranslated.leftRecursion m tg.grammarRules := by
    rw [tLeftRecursion_eq, tLeftRecursion_eq]
    simp only [tLeftRecursion]
    rw [nullableRules_stable h.rules n m (by omega) (by omega)]
  rw [hl]


/-! ## The warnings -/

theorem flatMap_toList {α β : Type} (o : α → Option β) : ∀ (l : List α),
    l.flatMap (fun x => (o x).toList) = l.filterMap o
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.filterMap_cons, flatMap_toList o xs]
    cases o x <;> simp

theorem notElem_e (name : String) (safe : List (Loc × String)) :
    HsList.notElem name (safe.map (·.2)) = !(safe.map (·.2)).contains name := by
  simp only [HsList.notElem]
  congr 1
  rw [← elem_contains]
  rfl

theorem safe_e {tg : LabelsTranslated.Grammar} {mg : Grammar} (h : GrammarCorr tg mg) :
    tg.grammarSafe.map LabelsTranslated.Located.unLoc = mg.safe.map (·.2) := by
  rw [h.safe]
  simp [eLocated, LabelsTranslated.Located.unLoc, Function.comp_def]

/-- **The translated `labelWarnings` is the model's.** For every grammar of the
model and every translated grammar with the same fields that the check reads,
the translated `labelWarnings` (with its fuel) gives, at every fuel from some
bound on, the warnings of `labelWarningsBy tKeyOf`, embedded. The visited set
of the model reads its keys with `tKeyOf`, the text that the translated
function builds with `show` (rule H7). -/
theorem labelWarnings_translated {tg : LabelsTranslated.Grammar} {mg : Grammar} (h : GrammarCorr tg mg) :
    Eventually (fun n => LabelsTranslated.labelWarnings n tg = (labelWarningsBy tKeyOf mg).map eDiag) := by
  have hu := unlabelGrammar_e h
  obtain ⟨N0, hN0⟩ := context_e tKeyOf hu
  obtain ⟨N1, hN1⟩ := context_stable hu
  let tc := LabelsTranslated.context (max N0 N1) (LabelsTranslated.unlabelGrammar tg)
  let mc := contextWith tKeyOf (unlabelGrammar mg)
  have hc : CtxCorr tc mc := hN0 _ (by omega)
  have hstab : ∀ n, max N0 N1 ≤ n → LabelsTranslated.context n (LabelsTranslated.unlabelGrammar tg) = tc :=
    fun n hn => hN1 n (max N0 N1) (by omega) (by omega)
  have hk : mc.keyOf = tKeyOf := contextWith_keyOf _ _
  have hp : PassWF mc.pass := contextWith_pass_wf tKeyOf (unlabelGrammar mg)
  obtain ⟨E, hE⟩ := expandCall_ev hc
  have hv : Eventually (fun n => ∀ s ∈ mg.rules.flatMap sites, ∀ l x name, s.expr = .label l x name →
      LabelsTranslated.verdictOf n tc s.rule (LabelsTranslated.unlabelFrames (s.frames.map eFrame))
        (LabelsTranslated.unlabelExpr (eExpr x)) =
        eVerdict (verdictOf mc s.rule (unlabelFrames s.frames) (unlabelExpr x))) := by
    refine Eventually.forall_mem _ (fun s _ => ?_)
    cases hx : s.expr with
    | label l x name =>
      refine (verdictOf_ev hk hc hp hE s.rule (unlabelFrames s.frames) (unlabelExpr x)).mono (fun n hn l' x' name' he => ?_)
      cases he
      rw [unlabelFrames_e, unlabelExpr_e]
      exact hn
    | _ => exact Eventually.of (fun _ _ _ _ he => by cases he)
  obtain ⟨Nv, hNv⟩ := hv
  obtain ⟨Ns, hNs⟩ := rulesSites_ev h.rules
  refine ⟨max (max N0 N1) (max Nv Ns), fun n hn => ?_⟩
  simp only [LabelsTranslated.labelWarnings, hstab n (by omega), safe_e h]
  rw [hNs n (by omega)]
  simp only [HsList.concatMap, List.flatMap_map]
  unfold labelWarningsBy labelWarningsWith
  rw [← flatMap_toList, List.map_flatMap]
  apply flatMap_congr_mem
  intro s hs
  obtain ⟨r, fs, l, e⟩ := s
  cases e with
  | label l' x name =>
    have hvs := hNv n (by omega) ⟨r, fs, l, .label l' x name⟩ hs l' x name rfl
    simp only [eSite, eExpr, notElem_e]
    by_cases hsafe : (mg.safe.map (·.2)).contains name = true
    · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    · have hsafe' : (mg.safe.map (·.2)).contains name = false := by simpa using hsafe
      simp only [hsafe', Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      simp only at hvs
      rw [hvs, verdictMessage_e]
      cases verdictMessage name (verdictOf mc r (unlabelFrames fs) (unlabelExpr x)) <;> simp [eDiag]
  | _ => simp [eSite, eExpr]


/-- The translated `matchesEmpty` is `nullableExpr` of the model with the model's nullable rules. -/
theorem matchesEmpty_translated {tg : LabelsTranslated.Grammar} {mg : Grammar} (h : GrammarCorr tg mg) (e : Expr) :
    Eventually (fun n => LabelsTranslated.matchesEmpty n tg (eExpr e) = nullableExpr (nullableRules mg.rules) e) :=
  ⟨mg.rules.length + 1, fun n hn => by
    simp only [LabelsTranslated.matchesEmpty]
    exact nullableExpr_e (nullableRules_e h.rules n hn) e⟩

end PegHs.LabelsBridge
