import LabelCheckModel

/-!
The termination of the label check of packages/peg-grammar/src/Peg/Grammar/Labels.hs
(ADR 0028, ADR 0029, ADR 0038, ADR 0087).

The Haskell functions `failed`, `succeeded`, `ruleFailed` and `ruleSucceeded`
call each other through the state monad, and only the set of visited contexts
stops recursion in the grammar. LabelCheckModel writes them as `run ctx n`,
one step per unit of fuel. This module proves:

- every set of characters the check builds is well formed (`exprAbs_wf`,
  `context_pass_wf`, `beforeItems_wf`), so it is one of the finitely many sets
  of `charSetUniverse`;
- the contexts that the check visits for a label are in the finite list
  `keyUniverse`: the rule is the label's or a caller's, the frames are a tail of
  the label's frames or of a call's (`frameUniverse`), the matched items are
  at most `maxPrefix` items of the frames with the parameters replaced at most
  `maxLifts` times (`itemUniverse`);
- each step either stops at a visited context or visits a new one, so the
  fuel `keyUniverse.length + 1` suffices (`run_terminates`), and more fuel gives
  the same result (`run_mono`): the Haskell recursion makes at most that many
  nested calls, so it ends;
- `verdictOf` and `labelWarnings` are therefore well defined, and
  `labelWarningsFuel` of the probe equals `labelWarnings` whenever the probe's
  fuel gives a verdict on every label (`labelWarnings_eq_fuel`).

The other recursive functions of the module are total Lean definitions in
LabelCheckModel: structural recursion on the expression, the depth of
`expansions` and of the simulation, the length of the text in `star`, the
counter of `fixpoint` (at most 1001 rounds), and the rules not yet known to
be nullable in `nullableGo`.

Premises: those of LabelCheckModel.
-/

namespace PegHs.LabelCheck

/-! ## Well-formed abstractions -/

def Abs.WF (a : Abs) : Prop := a.consume.WF ∧ a.empty.WF ∧ a.sure.WF

structure PassWF (p : Pass) : Prop where
  env : ∀ q ∈ p.env, q.2.WF
  notEmpty : ∀ x, (p.notEmpty x).WF
  notSure : ∀ x, (p.notSure x).WF

theorem bottom_wf : bottom.WF := ⟨none_wf, none_wf, none_wf⟩

theorem epsilon_wf : epsilon.WF := ⟨none_wf, everything_wf, everything_wf⟩

theorem possible_wf {a : Abs} (h : a.WF) : (possible a).WF := union_wf h.1 h.2.1

theorem andThen_wf {x y : Abs} (hx : x.WF) (hy : y.WF) : (andThen x y).WF := by
  refine ⟨union_wf hx.1 (intersect_wf hx.2.1 hy.1), intersect_wf hx.2.1 hy.2.1, ?_⟩
  show (if y.sure = everything then x.sure else CharSet.none).WF
  split
  · exact hx.2.2
  · exact none_wf

theorem orElse_wf {x y : Abs} (hx : x.WF) (hy : y.WF) : (orElse x y).WF :=
  ⟨union_wf hx.1 hy.1, union_wf hx.2.1 hy.2.1, union_wf hx.2.2 hy.2.2⟩

theorem foldl_findLast {α : Type} {n : String} {a : α} :
    ∀ (xs : List (String × α)) (acc : Option α),
      xs.foldl (fun acc p => if p.1 == n then some p.2 else acc) acc = some a → acc = some a ∨ (n, a) ∈ xs
  | [], acc, h => Or.inl h
  | p :: ps, acc, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_findLast ps _ h with h' | h'
    · split at h'
      · rename_i hp
        simp only [Option.some.injEq] at h'
        right
        simp only [beq_iff_eq] at hp
        subst h'
        have : p = (n, p.2) := by cases p; simp_all
        rw [this]; simp
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem findLast_mem {α : Type} {xs : List (String × α)} {n : String} {a : α}
    (h : findLast xs n = some a) : (n, a) ∈ xs := by
  rcases foldl_findLast xs none h with h' | h'
  · cases h'
  · exact h'

mutual
theorem exprAbs_wf {p : Pass} (hp : PassWF p) : (e : Expr) → (exprAbs p e).WF
  | .lit t _ => by
    simp only [exprAbs]
    split
    · exact epsilon_wf
    · refine ⟨single_wf _, none_wf, ?_⟩
      split
      · exact single_wf _
      · exact none_wf
  | .cls rs _ => by simp only [exprAbs]; exact ⟨ranges_wf rs, none_wf, ranges_wf rs⟩
  | .any => by simp only [exprAbs]; exact ⟨anyChar_wf, none_wf, anyChar_wf⟩
  | .ref _ n _ => by
    simp only [exprAbs]
    cases h : findLast p.env n with
    | none => exact bottom_wf
    | some a => exact hp.env (n, a) (findLast_mem h)
  | .group alts => by
    simp only [exprAbs]
    exact altsAbs_wf hp alts
  | .star x => by
    simp only [exprAbs]
    exact ⟨(exprAbs_wf hp x).1, everything_wf, everything_wf⟩
  | .plus x => by
    simp only [exprAbs]
    have h := exprAbs_wf hp x
    exact ⟨h.1, h.2.1, h.2.2⟩
  | .opt x => by
    simp only [exprAbs]
    exact ⟨(exprAbs_wf hp x).1, everything_wf, everything_wf⟩
  | .and x => by
    simp only [exprAbs]
    have h := exprAbs_wf hp x
    exact ⟨none_wf, possible_wf h, h.2.2⟩
  | .not x => by simp only [exprAbs]; exact ⟨none_wf, hp.notEmpty x, hp.notSure x⟩
  | .capture x => by simp only [exprAbs]; exact exprAbs_wf hp x
  | .label _ x _ => by simp only [exprAbs]; exact exprAbs_wf hp x
  | .discard x => by simp only [exprAbs]; exact exprAbs_wf hp x
  | .template .. => by simp only [exprAbs]; exact ⟨everything_wf, everything_wf, none_wf⟩
  | .pred b c => by
    simp only [exprAbs]
    split
    · exact epsilon_wf
    · exact bottom_wf
    · exact ⟨none_wf, everything_wf, none_wf⟩
termination_by e => sizeOf e

theorem seqAbs_wf {p : Pass} (hp : PassWF p) : (is : List Item) → (seqAbs p is).WF
  | [] => by simp only [seqAbs]; exact epsilon_wf
  | (_, _, e) :: is => by
    simp only [seqAbs]
    exact andThen_wf (exprAbs_wf hp e) (seqAbs_wf hp is)
termination_by is => sizeOf is

theorem altsAbs_wf {p : Pass} (hp : PassWF p) : (as : List (List Item)) → (altsAbs p as).WF
  | [] => by simp only [altsAbs]; exact bottom_wf
  | a :: as => by
    simp only [altsAbs]
    exact orElse_wf (seqAbs_wf hp a) (altsAbs_wf hp as)
termination_by as => sizeOf as
end

def EnvWF (env : Env) : Prop := ∀ q ∈ env, q.2.WF

theorem fixpointGo_wf (rules : List Rule) (mk : Env → Pass) (hmk : ∀ env, EnvWF env → PassWF (mk env)) :
    ∀ (env : Env) (n : Nat), EnvWF env → EnvWF (fixpointGo rules mk env n) := by
  have key : ∀ (b : Nat) (env : Env) (n : Nat), 1001 - n ≤ b → EnvWF env →
      EnvWF (fixpointGo rules mk env n) := by
    intro b
    induction b with
    | zero =>
      intro env n hb he
      rw [fixpointGo]
      split
      · exact he
      · rename_i hn
        simp at hn
        omega
    | succ b ih =>
      intro env n hb he
      rw [fixpointGo]
      split
      · exact he
      · rename_i hn
        simp at hn
        apply ih _ (n + 1) (by omega)
        intro q hq
        simp only [List.mem_map] at hq
        obtain ⟨r, _, rfl⟩ := hq
        exact altsAbs_wf (hmk env he) _
  exact fun env n he => key _ env n (Nat.le_refl _) he

theorem fixpoint_wf (rules : List Rule) (mk : Env → Pass) (hmk : ∀ env, EnvWF env → PassWF (mk env)) :
    EnvWF (fixpoint rules mk) := by
  apply fixpointGo_wf rules mk hmk
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨r, _, rfl⟩ := hq
  exact bottom_wf

theorem abstractions_wf (rules : List Rule) : PassWF (abstractions rules).2 := by
  have h1 : ∀ env, EnvWF env → PassWF (pass1 env) :=
    fun env he => ⟨he, fun _ => everything_wf, fun _ => none_wf⟩
  have e1 := fixpoint_wf rules pass1 h1
  have hposs : ∀ x, (possible1 (fixpoint rules pass1) x).WF :=
    fun x => possible_wf (exprAbs_wf (h1 _ e1) x)
  have h2 : ∀ env, EnvWF env → PassWF (pass2 (fixpoint rules pass1) env) :=
    fun env he => ⟨he, fun _ => everything_wf, fun x => minus_wf everything_wf (hposs x)⟩
  have e2 := fixpoint_wf rules _ h2
  have h3 : ∀ env, EnvWF env → PassWF (pass3 (fixpoint rules pass1) (fixpoint rules (pass2 (fixpoint rules pass1))) env) :=
    fun env he => ⟨he, fun x => minus_wf everything_wf (exprAbs_wf (h2 _ e2) x).2.2,
      fun x => minus_wf everything_wf (hposs x)⟩
  exact h3 _ (fixpoint_wf rules _ h3)

theorem contextWith_pass_wf (keyOf : Nat → List Item → String) (g : Grammar) :
    PassWF (contextWith keyOf g).pass := abstractions_wf g.rules

theorem context_pass_wf (g : Grammar) : PassWF (context g).pass := abstractions_wf g.rules

theorem beforeItems_wf {ctx : Ctx} (hp : PassWF ctx.pass) (pre : List Item) {k : CharSet} (hk : k.WF) :
    (beforeItems ctx pre k).WF :=
  union_wf (seqAbs_wf hp pre).1 (intersect_wf (seqAbs_wf hp pre).2.1 hk)

theorem startSet_wf {ctx : Ctx} (hp : PassWF ctx.pass) (x : Expr) : (startSet ctx x).WF :=
  minus_wf everything_wf (exprAbs_wf hp x).2.2


/-! ## The finite universe of visited contexts -/

def tailsOf {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (x :: xs) :: tailsOf xs

theorem self_mem_tailsOf {α : Type} (l : List α) : l ∈ tailsOf l := by
  cases l <;> simp [tailsOf]

theorem nil_mem_tailsOf {α : Type} : ∀ (l : List α), [] ∈ tailsOf l
  | [] => by simp [tailsOf]
  | _ :: xs => by simp only [tailsOf, List.mem_cons]; exact Or.inr (nil_mem_tailsOf xs)

theorem tailsOf_tail {α : Type} {x : α} {xs : List α} : ∀ {l : List α}, x :: xs ∈ tailsOf l → xs ∈ tailsOf l
  | [], h => by simp [tailsOf] at h
  | y :: ys, h => by
    simp only [tailsOf, List.mem_cons] at h ⊢
    rcases h with h | h
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (self_mem_tailsOf _)
    · exact Or.inr (tailsOf_tail h)

theorem tailsOf_sub {α : Type} {f : α} {xs : List α} : ∀ {l : List α}, xs ∈ tailsOf l → f ∈ xs → f ∈ l
  | [], h, hf => by simp [tailsOf] at h; subst h; simp at hf
  | y :: ys, h, hf => by
    simp only [tailsOf, List.mem_cons] at h
    rcases h with rfl | h
    · exact hf
    · exact List.mem_cons_of_mem _ (tailsOf_sub h hf)

-- A tail of a frame list and the same tail with another item of its sequence.
def variants (fs : List Frame) : List (List Frame) :=
  fs :: match fs with
    | .seq items _ :: rest => (List.range items.length).map (fun m => .seq items m :: rest)
    | _ => []

theorem self_mem_variants (fs : List Frame) : fs ∈ variants fs := by simp [variants]

theorem variants_shape {x s : List Frame} (h : x ∈ variants s) :
    x = s ∨ ∃ items j m rest, s = .seq items j :: rest ∧ x = .seq items m :: rest ∧ m < items.length := by
  unfold variants at h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    split at h
    · rename_i items j rest
      simp only [List.mem_map, List.mem_range] at h
      obtain ⟨m, hm, rfl⟩ := h
      exact ⟨items, j, m, rest, rfl, rfl, hm⟩
    · simp at h

theorem variants_seq {items : List Item} {j m : Nat} {rest s : List Frame}
    (h : Frame.seq items j :: rest ∈ variants s) (hm : m < items.length) :
    Frame.seq items m :: rest ∈ variants s := by
  rcases variants_shape h with h | ⟨items', j', m', rest', hs, hx, _⟩
  · subst h
    simp only [variants, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr ⟨m, hm, rfl⟩
  · simp only [List.cons.injEq, Frame.seq.injEq] at hx
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hx
    subst hs
    simp only [variants, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr ⟨m, hm, rfl⟩

def seedsOf (fs : List Frame) : List (List Frame) :=
  fs.flatMap fun f => match f with
    | .alts as' _ _ => (indexed 0 as').map (fun p => [Frame.seq p.2.2 0, .alts as' p.1 true])
    | _ => []

def frameBases (ctx : Ctx) (fs0 : List Frame) : List (List Frame) := fs0 :: ctx.refSites.map (·.frames)

def frameBases2 (ctx : Ctx) (fs0 : List Frame) : List (List Frame) :=
  frameBases ctx fs0 ++ (frameBases ctx fs0).flatMap seedsOf

-- Every list of frames the check follows for a label at the frames fs0.
def frameUniverse (ctx : Ctx) (fs0 : List Frame) : List (List Frame) :=
  (frameBases2 ctx fs0).flatMap (fun b => (tailsOf b).flatMap variants)

theorem mem_frameUniverse {ctx : Ctx} {fs0 x : List Frame} :
    x ∈ frameUniverse ctx fs0 ↔ ∃ b ∈ frameBases2 ctx fs0, ∃ s ∈ tailsOf b, x ∈ variants s := by
  simp [frameUniverse]

theorem base_mem_frameUniverse {ctx : Ctx} {fs0 b : List Frame} (h : b ∈ frameBases2 ctx fs0) :
    b ∈ frameUniverse ctx fs0 :=
  mem_frameUniverse.2 ⟨b, h, b, self_mem_tailsOf b, self_mem_variants b⟩

theorem start_mem_frameUniverse (ctx : Ctx) (fs0 : List Frame) : fs0 ∈ frameUniverse ctx fs0 :=
  base_mem_frameUniverse (by simp [frameBases2, frameBases])

theorem site_mem_frameUniverse {ctx : Ctx} {fs0 : List Frame} {s : Site} (h : s ∈ ctx.refSites) :
    s.frames ∈ frameUniverse ctx fs0 :=
  base_mem_frameUniverse (by
    simp only [frameBases2, frameBases, List.mem_append, List.mem_cons, List.mem_map]
    exact Or.inl (Or.inr ⟨s, h, rfl⟩))

theorem nil_mem_frameUniverse (ctx : Ctx) (fs0 : List Frame) : [] ∈ frameUniverse ctx fs0 :=
  mem_frameUniverse.2 ⟨fs0, by simp [frameBases2, frameBases], [], nil_mem_tailsOf fs0, self_mem_variants []⟩

theorem frameUniverse_tail {ctx : Ctx} {fs0 : List Frame} {f : Frame} {rest : List Frame}
    (h : f :: rest ∈ frameUniverse ctx fs0) : rest ∈ frameUniverse ctx fs0 := by
  obtain ⟨b, hb, s, hs, hx⟩ := mem_frameUniverse.1 h
  refine mem_frameUniverse.2 ⟨b, hb, rest, ?_, self_mem_variants rest⟩
  rcases variants_shape hx with rfl | ⟨items, j, m, rest', rfl, hx', _⟩
  · exact tailsOf_tail hs
  · simp only [List.cons.injEq] at hx'
    rw [hx'.2]
    exact tailsOf_tail hs

theorem frameUniverse_seq {ctx : Ctx} {fs0 : List Frame} {items : List Item} {j m : Nat} {rest : List Frame}
    (h : Frame.seq items j :: rest ∈ frameUniverse ctx fs0) (hm : m < items.length) :
    Frame.seq items m :: rest ∈ frameUniverse ctx fs0 := by
  obtain ⟨b, hb, s, hs, hx⟩ := mem_frameUniverse.1 h
  exact mem_frameUniverse.2 ⟨b, hb, s, hs, variants_seq hx hm⟩

theorem variants_alts {x s : List Frame} {f : Frame} (hx : x ∈ variants s) (hf : f ∈ x)
    (ha : ∀ items j, f ≠ .seq items j) : f ∈ s := by
  rcases variants_shape hx with rfl | ⟨items, j, m, rest, rfl, rfl, _⟩
  · exact hf
  · simp only [List.mem_cons] at hf ⊢
    rcases hf with rfl | hf
    · exact absurd rfl (ha items m)
    · exact Or.inr hf

theorem alts_from_base {ctx : Ctx} {fs0 x : List Frame} {as' : List (Loc × List Item)} {i : Nat} {body : Bool}
    (hx : x ∈ frameUniverse ctx fs0) (hf : Frame.alts as' i body ∈ x) :
    ∃ b ∈ frameBases ctx fs0, ∃ i' body', Frame.alts as' i' body' ∈ b := by
  obtain ⟨b, hb, s, hs, hv⟩ := mem_frameUniverse.1 hx
  have hfs := variants_alts hv hf (by intro items j h; cases h)
  have hfb := tailsOf_sub hs hfs
  simp only [frameBases2, List.mem_append, List.mem_flatMap] at hb
  rcases hb with hb | ⟨b0, hb0, hseed⟩
  · exact ⟨b, hb, i, body, hfb⟩
  · simp only [seedsOf, List.mem_flatMap] at hseed
    obtain ⟨f0, hf0, hseed⟩ := hseed
    split at hseed
    · rename_i as0 i0 body0
      simp only [List.mem_map] at hseed
      obtain ⟨p, _, rfl⟩ := hseed
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hfb
      rcases hfb with hfb | hfb
      · cases hfb
      · simp only [Frame.alts.injEq] at hfb
        obtain ⟨rfl, _, _⟩ := hfb
        exact ⟨b0, hb0, i0, body0, hf0⟩
    · simp at hseed

theorem seed_mem_frameUniverse {ctx : Ctx} {fs0 x : List Frame} {as' : List (Loc × List Item)} {i : Nat}
    {body : Bool} {p : Nat × Loc × List Item}
    (hx : x ∈ frameUniverse ctx fs0) (hf : Frame.alts as' i body ∈ x) (hp : p ∈ indexed 0 as') :
    [Frame.seq p.2.2 0, .alts as' p.1 true] ∈ frameUniverse ctx fs0 := by
  obtain ⟨b, hb, i', body', hfb⟩ := alts_from_base hx hf
  apply base_mem_frameUniverse
  simp only [frameBases2, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨b, hb, ?_⟩
  simp only [seedsOf, List.mem_flatMap]
  exact ⟨_, hfb, by simp only [List.mem_map]; exact ⟨p, hp, rfl⟩⟩

def frameItems (fs : List Frame) : List Item :=
  fs.flatMap fun f => match f with
    | .seq items _ => items
    | _ => []

-- The parameter maps of the calls.
def pmUniverse (ctx : Ctx) : List (List (String × String)) :=
  ctx.rules.flatMap fun q => ctx.refSites.filterMap fun s => match s.expr with
    | .ref _ _ args => paramMap q.2 args
    | _ => none

-- The items of the frames with the parameters replaced at most n times.
def itemUniverse (ctx : Ctx) (fs0 : List Frame) : Nat → List Item
  | 0 => (frameUniverse ctx fs0).flatMap frameItems
  | n + 1 => itemUniverse ctx fs0 n ++
      (itemUniverse ctx fs0 n).flatMap (fun i => (pmUniverse ctx).filterMap (fun pm => substItem pm i))

theorem itemUniverse_succ {ctx : Ctx} {fs0 : List Frame} {n : Nat} {i : Item}
    (h : i ∈ itemUniverse ctx fs0 n) : i ∈ itemUniverse ctx fs0 (n + 1) := by
  simp only [itemUniverse, List.mem_append]
  exact Or.inl h

theorem itemUniverse_mono {ctx : Ctx} {fs0 : List Frame} {n : Nat} {i : Item} (h : i ∈ itemUniverse ctx fs0 n) :
    ∀ m, n ≤ m → i ∈ itemUniverse ctx fs0 m := by
  intro m hm
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact itemUniverse_succ (ih (by omega))
    · have : n = m + 1 := by omega
      subst this; exact h

theorem seq_items_mem {ctx : Ctx} {fs0 : List Frame} {items : List Item} {j : Nat} {rest : List Frame}
    (h : Frame.seq items j :: rest ∈ frameUniverse ctx fs0) {i : Item} (hi : i ∈ items) :
    i ∈ itemUniverse ctx fs0 0 := by
  simp only [itemUniverse, List.mem_flatMap]
  refine ⟨_, h, ?_⟩
  simp only [frameItems, List.mem_flatMap]
  exact ⟨Frame.seq items j, List.mem_cons_self, hi⟩

theorem substItemsL_mem {pm : List (String × String)} :
    ∀ (pre pre' : List Item), substItemsL pm pre = some pre' → ∀ i' ∈ pre', ∃ i ∈ pre, substItem pm i = some i'
  | [], pre', h => by
    rw [substItemsL] at h
    simp at h; subst h; simp
  | i :: is, pre', h => by
    rw [substItemsL] at h
    split at h
    · rename_i i' is' hi his
      simp at h
      subst h
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨i, by simp, hi⟩
      · obtain ⟨y, hy, hy'⟩ := substItemsL_mem is is' his x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩
    · simp at h

def preUniverse (ctx : Ctx) (fs0 : List Frame) : List String :=
  (List.range (maxLifts + 1)).flatMap fun l =>
    (listsUpTo (itemUniverse ctx fs0 maxLifts) maxPrefix).map (ctx.keyOf l)

def ruleUniverse (ctx : Ctx) (rule0 : String) : List String := rule0 :: ctx.refSites.map (·.rule)

noncomputable def keyUniverse (ctx : Ctx) (rule0 : String) (fs0 : List Frame) : List Key :=
  (ruleUniverse ctx rule0).flatMap fun r =>
    (frameUniverse ctx fs0).flatMap fun fs =>
      [Mode.failed, Mode.succeeded].flatMap fun md =>
        charSetUniverse.flatMap fun k =>
          (preUniverse ctx fs0).map fun pk => (r, fs.map frameKey, md, k, pk)

-- What holds of the arguments of failed and succeeded.
structure FInv (ctx : Ctx) (rule0 : String) (fs0 : List Frame) (rule : String) (fs : List Frame)
    (pre : List Item) (lifts : Nat) (k : CharSet) : Prop where
  hrule : rule ∈ ruleUniverse ctx rule0
  hframes : fs ∈ frameUniverse ctx fs0
  hlifts : lifts ≤ maxLifts
  hpre : ∀ i ∈ pre, i ∈ itemUniverse ctx fs0 lifts
  hk : k.WF

structure SInv (ctx : Ctx) (rule0 : String) (fs0 : List Frame) (rule : String) (fs : List Frame)
    (k : CharSet) : Prop where
  hrule : rule ∈ ruleUniverse ctx rule0
  hframes : fs ∈ frameUniverse ctx fs0
  hk : k.WF

theorem key_mem {ctx : Ctx} {rule0 rule : String} {fs0 fs : List Frame} {md : Mode} {k : CharSet} {pk : String}
    (hr : rule ∈ ruleUniverse ctx rule0) (hf : fs ∈ frameUniverse ctx fs0) (hk : k.WF)
    (hpk : pk ∈ preUniverse ctx fs0) :
    (rule, fs.map frameKey, md, k, pk) ∈ keyUniverse ctx rule0 fs0 := by
  simp only [keyUniverse, List.mem_flatMap, List.mem_map]
  refine ⟨rule, hr, fs, hf, md, by cases md <;> simp, k, wf_mem_universe hk, pk, hpk, rfl⟩

theorem failedKey_mem {ctx : Ctx} {rule0 rule : String} {fs0 fs : List Frame} {pre : List Item} {lifts : Nat}
    {k : CharSet} (h : FInv ctx rule0 fs0 rule fs pre lifts k) (hlen : pre.length ≤ maxPrefix) :
    failedKey ctx rule fs pre lifts k ∈ keyUniverse ctx rule0 fs0 := by
  apply key_mem h.hrule h.hframes h.hk
  simp only [preUniverse, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨lifts, by have := h.hlifts; omega, pre, ?_, rfl⟩
  exact mem_listsUpTo _ _ _ hlen (fun i hi => itemUniverse_mono (h.hpre i hi) _ h.hlifts)

theorem succeededKey_mem {ctx : Ctx} {rule0 rule : String} {fs0 fs : List Frame} {k : CharSet}
    (h : SInv ctx rule0 fs0 rule fs k) : succeededKey ctx rule fs k ∈ keyUniverse ctx rule0 fs0 := by
  apply key_mem h.hrule h.hframes h.hk
  simp only [preUniverse, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨0, by simp [maxLifts], [], mem_listsUpTo _ _ _ (by simp) (by simp), rfl⟩

/-! ## Each step visits a new context -/

def unvisited (U : List Key) (V : Visited) : Nat := (U.filter (fun x => !V.contains x)).length

def Ext (V V' : Visited) : Prop := ∀ x ∈ V, x ∈ V'

theorem unvisited_mono {U : List Key} {V V' : Visited} (h : Ext V V') : unvisited U V' ≤ unvisited U V := by
  apply filter_length_le
  intro y hy
  simp at hy ⊢
  exact fun h' => hy (h y h')

theorem unvisited_insert {U : List Key} {V : Visited} {x : Key} (hx : x ∈ U) (hn : V.contains x = false) :
    unvisited U (x :: V) < unvisited U V := by
  apply filter_length_lt U _ _ _ x hx
  · simpa using hn
  · simp
  · intro y hy
    simp only [List.contains_cons, Bool.not_or, Bool.and_eq_true] at hy
    exact hy.2

-- c returns, and keeps the visited contexts, from every state with fewer than m unvisited contexts.
def GoodM (U : List Key) (m : Nat) (c : M) : Prop :=
  ∀ V, unvisited U V < m → ∃ r, c V = some r ∧ Ext V r.2

structure Good (ctx : Ctx) (rule0 : String) (fs0 : List Frame) (m : Nat) (R : Rec) : Prop where
  failed : ∀ rule fs pre lifts k, FInv ctx rule0 fs0 rule fs pre lifts k →
    GoodM (keyUniverse ctx rule0 fs0) m (R.failed rule fs (pre, lifts) k)
  succeeded : ∀ rule fs k, SInv ctx rule0 fs0 rule fs k →
    GoodM (keyUniverse ctx rule0 fs0) m (R.succeeded rule fs k)

theorem goodM_ret {U : List Key} {m : Nat} (v : Verdict) : GoodM U m (ret v) :=
  fun V _ => ⟨(v, V), rfl, fun _ h => h⟩

theorem goodM_allOf {U : List Key} {m : Nat} : ∀ {cs : List M}, (∀ c ∈ cs, GoodM U m c) → GoodM U m (allOf cs)
  | [], _ => goodM_ret .safe
  | c :: cs, h => by
    intro V hV
    obtain ⟨⟨v, V'⟩, hc, hext⟩ := h c (by simp) V hV
    simp only [allOf, hc]
    split
    · obtain ⟨r, hr, hext'⟩ := goodM_allOf (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) V'
        (Nat.lt_of_le_of_lt (unvisited_mono hext) hV)
      exact ⟨r, hr, fun x hx => hext' x (hext x hx)⟩
    · exact ⟨(v, V'), rfl, hext⟩

theorem goodM_visit {U : List Key} {m : Nat} {key : Key} {c : M} (hk : key ∈ U) (hc : GoodM U m c) :
    GoodM U (m + 1) (visit key c) := by
  intro V hV
  simp only [visit]
  split
  · exact ⟨(.safe, V), rfl, fun _ h => h⟩
  · rename_i hn
    have hlt := unvisited_insert hk (by simpa using hn)
    obtain ⟨r, hr, hext⟩ := hc (key :: V) (by omega)
    exact ⟨r, hr, fun x hx => hext x (List.mem_cons_of_mem _ hx)⟩


theorem callersOf_sub {ctx : Ctx} {rule : String} {s : Site} (h : s ∈ callersOf ctx rule) : s ∈ ctx.refSites := by
  simp only [callersOf, callers, List.mem_filter] at h
  exact h.1.1

theorem site_rule_mem {ctx : Ctx} {rule0 : String} {s : Site} (h : s ∈ ctx.refSites) :
    s.rule ∈ ruleUniverse ctx rule0 := by
  simp only [ruleUniverse, List.mem_cons, List.mem_map]
  exact Or.inr ⟨s, h, rfl⟩

theorem lift_inv {ctx : Ctx} {fs0 : List Frame} {rule : String} {pre : List Item} {lifts : Nat}
    {k : CharSet} {s : Site} (hp : PassWF ctx.pass)
    (hpre : ∀ i ∈ pre, i ∈ itemUniverse ctx fs0 lifts) (hk : k.WF) (hs : s ∈ ctx.refSites) :
    (lift ctx rule pre lifts k s).1.2 ≤ maxLifts ∧
      (∀ i ∈ (lift ctx rule pre lifts k s).1.1, i ∈ itemUniverse ctx fs0 (lift ctx rule pre lifts k s).1.2) ∧
      (lift ctx rule pre lifts k s).2.WF := by
  have hfb : (0 : Nat) ≤ maxLifts ∧ (∀ i ∈ ([] : List Item), i ∈ itemUniverse ctx fs0 0) ∧
      (beforeItems ctx pre k).WF := ⟨Nat.zero_le _, by simp, beforeItems_wf hp pre hk⟩
  unfold lift
  split
  · rename_i l n args hexpr
    split
    · rename_i hlt
      split
      · rename_i pre' hpre'
        split
        · refine ⟨by simp only [maxLifts] at hlt ⊢; omega, ?_, hk⟩
          intro i' hi'
          simp only [Option.bind_eq_some_iff] at hpre'
          obtain ⟨r, hr, pm, hpm, hsub⟩ := hpre'
          obtain ⟨i, hi, hsi⟩ := substItemsL_mem pre pre' hsub i' hi'
          simp only [itemUniverse, List.mem_append, List.mem_flatMap, List.mem_filterMap]
          refine Or.inr ⟨i, hpre i hi, pm, ?_, hsi⟩
          simp only [pmUniverse, List.mem_flatMap, List.mem_filterMap]
          exact ⟨(rule, r), findLast_mem hr, s, hs, by simp only [hexpr]; exact hpm⟩
        · exact hfb
      · exact hfb
    · exact hfb
  · exact hfb

theorem ruleFailed_good {ctx : Ctx} {rule0 : String} {fs0 : List Frame} {m : Nat} {R : Rec}
    (hp : PassWF ctx.pass) (hR : Good ctx rule0 fs0 m R) {rule : String} {pre : List Item} {lifts : Nat}
    {k : CharSet} (hpre : ∀ i ∈ pre, i ∈ itemUniverse ctx fs0 lifts) (hk : k.WF) :
    GoodM (keyUniverse ctx rule0 fs0) m (ruleFailed ctx R rule pre lifts k) := by
  unfold ruleFailed
  split
  · exact goodM_ret _
  · apply goodM_allOf
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨s, hs, rfl⟩ := hc
    have hs' := callersOf_sub hs
    obtain ⟨h1, h2, h3⟩ := lift_inv (rule := rule) hp hpre hk hs'
    exact hR.failed _ _ _ _ _ ⟨site_rule_mem hs', site_mem_frameUniverse hs', h1, h2, h3⟩

theorem ruleSucceeded_good {ctx : Ctx} {rule0 : String} {fs0 : List Frame} {m : Nat} {R : Rec}
    (hR : Good ctx rule0 fs0 m R) {rule : String} {k : CharSet} (hk : k.WF) :
    GoodM (keyUniverse ctx rule0 fs0) m (ruleSucceeded ctx R rule k) := by
  unfold ruleSucceeded
  split
  · exact goodM_ret _
  · split
    · exact goodM_ret _
    · apply goodM_allOf
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨s, hs, rfl⟩ := hc
      have hs' := callersOf_sub hs
      exact hR.succeeded _ _ _ ⟨site_rule_mem hs', site_mem_frameUniverse hs', hk⟩

theorem failedBody_good {ctx : Ctx} {rule0 : String} {fs0 : List Frame} {m : Nat} {R : Rec}
    (hp : PassWF ctx.pass) (hR : Good ctx rule0 fs0 m R) {rule : String} {fs : List Frame}
    {pre : List Item} {lifts : Nat} {k : CharSet} (h : FInv ctx rule0 fs0 rule fs pre lifts k) :
    GoodM (keyUniverse ctx rule0 fs0) m (failedBody ctx R rule fs pre lifts k) := by
  have hstart : (beforeItems ctx pre k).WF := beforeItems_wf hp pre h.hk
  obtain ⟨hrule, hframes, hlifts, hpre, hk⟩ := h
  unfold failedBody
  split
  next items j alts i body rest =>
    have hrest := frameUniverse_tail (frameUniverse_tail hframes)
    dsimp only
    split
    · exact goodM_ret _
    · split
      · split
        · exact hR.succeeded _ _ _ ⟨hrule, nil_mem_frameUniverse _ _, beforeItems_wf hp _ hk⟩
        · refine hR.failed _ _ _ _ _ ⟨hrule, hrest, hlifts, ?_, hk⟩
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact itemUniverse_mono (seq_items_mem hframes (List.mem_of_mem_take hx)) _ (Nat.zero_le _)
          · exact hpre x hx
      · exact goodM_ret _
  next => exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hstart⟩
  next =>
    apply goodM_allOf
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hR.failed _ _ _ _ _ ⟨hrule, frameUniverse_tail hframes, hlifts, hpre, hk⟩
    · exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hstart⟩
  next => exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hstart⟩
  next => exact goodM_ret _
  next => exact goodM_ret _
  next => exact hR.failed _ _ _ _ _ ⟨hrule, frameUniverse_tail hframes, hlifts, hpre, hk⟩
  next => exact hR.failed _ _ _ _ _ ⟨hrule, frameUniverse_tail hframes, hlifts, hpre, hk⟩
  next => exact ruleFailed_good hp hR hpre hk
  next => exact goodM_ret _

theorem succeededBody_good {ctx : Ctx} {rule0 : String} {fs0 : List Frame} {m : Nat} {R : Rec}
    (hp : PassWF ctx.pass) (hR : Good ctx rule0 fs0 m R) {rule : String} {fs : List Frame}
    {k : CharSet} (h : SInv ctx rule0 fs0 rule fs k) :
    GoodM (keyUniverse ctx rule0 fs0) m (succeededBody ctx R rule fs k) := by
  obtain ⟨hrule, hframes, hk⟩ := h
  unfold succeededBody
  split
  next items j as' i body rest =>
    have hrest := frameUniverse_tail (frameUniverse_tail hframes)
    have halts : Frame.alts as' i body ∈ Frame.seq items j :: Frame.alts as' i body :: rest := by simp
    have hended : ∀ k', k'.WF → GoodM (keyUniverse ctx rule0 fs0) m
        (if (body && ctx.directLr.contains rule && ctx.growing rule i) = true then
          allOf (R.succeeded rule [] k' ::
            ((indexed 0 as').filter (fun p => ctx.growing rule p.1)).map
              (fun p => R.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k'))
        else R.succeeded rule rest k') := by
      intro k' hk'
      split
      · apply goodM_allOf
        intro c hc
        simp only [List.mem_cons, List.mem_map, List.mem_filter] at hc
        rcases hc with rfl | ⟨p, ⟨hp', _⟩, rfl⟩
        · exact hR.succeeded _ _ _ ⟨hrule, nil_mem_frameUniverse _ _, hk'⟩
        · exact hR.succeeded _ _ _ ⟨hrule, seed_mem_frameUniverse hframes halts hp', hk'⟩
      · exact hR.succeeded _ _ _ ⟨hrule, hrest, hk'⟩
    have hempty := (seqAbs_wf hp (items.drop (j + 1))).2.1
    dsimp only
    split
    · exact goodM_ret _
    · split
      next next' more hafter =>
        split
        · exact goodM_ret _
        · have hj : j + 1 < items.length := by
            have := congrArg List.length hafter
            simp at this
            omega
          apply goodM_allOf
          intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
            List.mem_range'] at hc
          rcases hc with (rfl | ⟨mm, ⟨hm1, hm2⟩, rfl⟩) | hc
          · exact hR.failed _ _ _ _ _ ⟨hrule, frameUniverse_seq hframes hj, Nat.zero_le _, by simp, hk⟩
          · exact hR.failed _ _ _ _ _ ⟨hrule, frameUniverse_seq hframes (by omega), Nat.zero_le _, by simp,
              everything_wf⟩
          · split at hc
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
              subst hc
              exact hended _ (intersect_wf hempty hk)
            · simp at hc
      next =>
        apply goodM_allOf
        intro c hc
        split at hc
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          subst hc
          exact hended _ (intersect_wf hempty hk)
        · simp at hc
  next x l rest =>
    dsimp only
    split
    · exact goodM_ret _
    · exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hk⟩
  next x l rest =>
    dsimp only
    split
    · exact goodM_ret _
    · exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hk⟩
  next => exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hk⟩
  next => exact goodM_ret _
  next => exact goodM_ret _
  next => exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hk⟩
  next => exact hR.succeeded _ _ _ ⟨hrule, frameUniverse_tail hframes, hk⟩
  next => exact ruleSucceeded_good hR hk
  next => exact goodM_ret _

theorem truncate_inv {ctx : Ctx} {rule0 : String} {fs0 : List Frame} (hp : PassWF ctx.pass) {rule : String}
    {fs : List Frame} {pre : List Item} {lifts : Nat} {k : CharSet} (h : FInv ctx rule0 fs0 rule fs pre lifts k) :
    FInv ctx rule0 fs0 rule fs (truncate ctx pre k).1 lifts (truncate ctx pre k).2 ∧
      (truncate ctx pre k).1.length ≤ maxPrefix := by
  unfold truncate
  split
  · exact ⟨⟨h.hrule, h.hframes, h.hlifts, by simp, beforeItems_wf hp pre h.hk⟩, by simp⟩
  · rename_i hlen
    exact ⟨h, by simp only; omega⟩

theorem step_good {ctx : Ctx} {rule0 : String} {fs0 : List Frame} {m : Nat} {R : Rec}
    (hp : PassWF ctx.pass) (hR : Good ctx rule0 fs0 m R) : Good ctx rule0 fs0 (m + 1) (step ctx R) where
  failed := by
    intro rule fs pre lifts k h
    have ht := truncate_inv hp h
    exact goodM_visit (failedKey_mem ht.1 ht.2) (failedBody_good hp hR ht.1)
  succeeded := by
    intro rule fs k h
    exact goodM_visit (succeededKey_mem h) (succeededBody_good hp hR h)

theorem run_good {ctx : Ctx} (hp : PassWF ctx.pass) (rule0 : String) (fs0 : List Frame) :
    ∀ n, Good ctx rule0 fs0 n (run ctx n)
  | 0 => ⟨fun _ _ _ _ _ _ _ hV => absurd hV (Nat.not_lt_zero _),
          fun _ _ _ _ _ hV => absurd hV (Nat.not_lt_zero _)⟩
  | n + 1 => step_good hp (run_good hp rule0 fs0 n)

/-- The check of a label at the frames fs0 of rule0 ends: the fuel
`(keyUniverse ctx rule0 fs0).length + 1` gives a result. -/
theorem run_terminates {ctx : Ctx} (hp : PassWF ctx.pass) (rule0 : String) (fs0 : List Frame)
    {k : CharSet} (hk : k.WF) :
    ∃ r, (run ctx ((keyUniverse ctx rule0 fs0).length + 1)).failed rule0 fs0 ([], 0) k [] = some r := by
  have hinv : FInv ctx rule0 fs0 rule0 fs0 [] 0 k :=
    ⟨by simp [ruleUniverse], start_mem_frameUniverse ctx fs0, Nat.zero_le _, by simp, hk⟩
  have hU : unvisited (keyUniverse ctx rule0 fs0) [] < (keyUniverse ctx rule0 fs0).length + 1 := by
    have := List.length_filter_le (fun _ => true) (keyUniverse ctx rule0 fs0)
    simp only [unvisited, List.contains_nil, Bool.not_false]
    omega
  obtain ⟨r, hr, _⟩ := (run_good hp rule0 fs0 _).failed _ _ _ _ _ hinv [] hU
  exact ⟨r, hr⟩


/-! ## More fuel gives the same result -/

def MLe (c c' : M) : Prop := ∀ V r, c V = some r → c' V = some r

structure RLe (R R' : Rec) : Prop where
  failed : ∀ rule fs p k, MLe (R.failed rule fs p k) (R'.failed rule fs p k)
  succeeded : ∀ rule fs k, MLe (R.succeeded rule fs k) (R'.succeeded rule fs k)

theorem mle_refl (c : M) : MLe c c := fun _ _ h => h

def Pointwise : List M → List M → Prop
  | [], [] => True
  | a :: as, b :: bs => MLe a b ∧ Pointwise as bs
  | _, _ => False

theorem pointwise_map {α : Type} (f g : α → M) (h : ∀ x, MLe (f x) (g x)) :
    ∀ (l : List α), Pointwise (l.map f) (l.map g)
  | [] => trivial
  | x :: xs => ⟨h x, pointwise_map f g h xs⟩

theorem pointwise_append : ∀ {as bs cs ds : List M}, Pointwise as bs → Pointwise cs ds →
    Pointwise (as ++ cs) (bs ++ ds)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ⟨h1, h2⟩, h => ⟨h1, pointwise_append h2 h⟩
  | [], _ :: _, _, _, h, _ => absurd h id
  | _ :: _, [], _, _, h, _ => absurd h id

theorem pointwise_ite {p : Prop} [Decidable p] {as bs cs ds : List M} (h1 : Pointwise as bs)
    (h2 : Pointwise cs ds) : Pointwise (if p then as else cs) (if p then bs else ds) := by
  split
  · exact h1
  · exact h2

theorem mle_allOf : ∀ {cs cs' : List M}, Pointwise cs cs' → MLe (allOf cs) (allOf cs')
  | [], [], _ => mle_refl _
  | c :: cs, c' :: cs', ⟨h1, h2⟩ => by
    intro V r h
    simp only [allOf] at h ⊢
    cases hc : c V with
    | none => simp [hc] at h
    | some q =>
      rw [h1 V q hc]
      rw [hc] at h
      simp only at h ⊢
      split
      · rename_i hs
        simp only [hs, ↓reduceIte] at h
        exact mle_allOf h2 _ _ h
      · rename_i hs
        simp only [hs, ↓reduceIte] at h
        exact h
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id

theorem mle_visit {key : Key} {c c' : M} (h : MLe c c') : MLe (visit key c) (visit key c') := by
  intro V r hv
  simp only [visit] at hv ⊢
  split
  · rename_i hc; simp only [hc, ↓reduceIte] at hv; exact hv
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at hv; exact h _ _ hv

theorem mle_ite {p : Prop} [Decidable p] {a b c d : M} (h1 : MLe a b) (h2 : MLe c d) :
    MLe (if p then a else c) (if p then b else d) := by
  split
  · exact h1
  · exact h2

theorem ruleFailed_mono {ctx : Ctx} {R R' : Rec} (h : RLe R R') (rule : String) (pre : List Item)
    (lifts : Nat) (k : CharSet) : MLe (ruleFailed ctx R rule pre lifts k) (ruleFailed ctx R' rule pre lifts k) := by
  unfold ruleFailed
  exact mle_ite (mle_refl _) (mle_allOf (pointwise_map _ _ (fun s => h.failed _ _ _ _) _))

theorem ruleSucceeded_mono {ctx : Ctx} {R R' : Rec} (h : RLe R R') (rule : String) (k : CharSet) :
    MLe (ruleSucceeded ctx R rule k) (ruleSucceeded ctx R' rule k) := by
  unfold ruleSucceeded
  exact mle_ite (mle_refl _) (mle_ite (mle_refl _)
    (mle_allOf (pointwise_map _ _ (fun s => h.succeeded _ _ _) _)))

theorem failedBody_mono {ctx : Ctx} {R R' : Rec} (h : RLe R R') (rule : String) (fs : List Frame)
    (pre : List Item) (lifts : Nat) (k : CharSet) :
    MLe (failedBody ctx R rule fs pre lifts k) (failedBody ctx R' rule fs pre lifts k) := by
  unfold failedBody
  split
  next =>
    dsimp only
    apply mle_ite (mle_refl _)
    split
    · exact mle_ite (h.succeeded _ _ _) (h.failed _ _ _ _)
    · exact mle_refl _
  next => exact h.succeeded _ _ _
  next => exact mle_allOf ⟨h.failed _ _ _ _, h.succeeded _ _ _, trivial⟩
  next => exact h.succeeded _ _ _
  next => exact mle_refl _
  next => exact mle_refl _
  next => exact h.failed _ _ _ _
  next => exact h.failed _ _ _ _
  next => exact ruleFailed_mono h _ _ _ _
  next => exact mle_refl _

theorem succeededBody_mono {ctx : Ctx} {R R' : Rec} (h : RLe R R') (rule : String) (fs : List Frame)
    (k : CharSet) : MLe (succeededBody ctx R rule fs k) (succeededBody ctx R' rule fs k) := by
  unfold succeededBody
  split
  next items j as' i body rest =>
    dsimp only
    have hended : ∀ k', MLe
        (if (body && ctx.directLr.contains rule && ctx.growing rule i) = true then
          allOf (R.succeeded rule [] k' ::
            ((indexed 0 as').filter (fun p => ctx.growing rule p.1)).map
              (fun p => R.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k'))
        else R.succeeded rule rest k')
        (if (body && ctx.directLr.contains rule && ctx.growing rule i) = true then
          allOf (R'.succeeded rule [] k' ::
            ((indexed 0 as').filter (fun p => ctx.growing rule p.1)).map
              (fun p => R'.succeeded rule [.seq p.2.2 0, .alts as' p.1 true] k'))
        else R'.succeeded rule rest k') := fun k' =>
      mle_ite (mle_allOf ⟨h.succeeded _ _ _, pointwise_map _ _ (fun _ => h.succeeded _ _ _) _⟩)
        (h.succeeded _ _ _)
    apply mle_ite (mle_refl _)
    split
    · apply mle_ite (mle_refl _)
      apply mle_allOf
      refine pointwise_append (pointwise_append ⟨h.failed _ _ _ _, trivial⟩
        (pointwise_map _ _ (fun _ => h.failed _ _ _ _) _)) ?_
      exact pointwise_ite ⟨hended _, trivial⟩ trivial
    · exact mle_allOf (pointwise_ite ⟨hended _, trivial⟩ trivial)
  next => exact mle_ite (mle_refl _) (h.succeeded _ _ _)
  next => exact mle_ite (mle_refl _) (h.succeeded _ _ _)
  next => exact h.succeeded _ _ _
  next => exact mle_refl _
  next => exact mle_refl _
  next => exact h.succeeded _ _ _
  next => exact h.succeeded _ _ _
  next => exact ruleSucceeded_mono h _ _
  next => exact mle_refl _

theorem step_mono {ctx : Ctx} {R R' : Rec} (h : RLe R R') : RLe (step ctx R) (step ctx R') where
  failed := fun _ _ _ _ => mle_visit (failedBody_mono h _ _ _ _ _)
  succeeded := fun _ _ _ => mle_visit (succeededBody_mono h _ _ _)

theorem run_mono_succ (ctx : Ctx) : ∀ n, RLe (run ctx n) (run ctx (n + 1))
  | 0 => ⟨fun _ _ _ _ _ _ h => by simp [run] at h, fun _ _ _ _ _ h => by simp [run] at h⟩
  | n + 1 => step_mono (run_mono_succ ctx n)

theorem run_mono (ctx : Ctx) {n : Nat} : ∀ {m : Nat}, n ≤ m → RLe (run ctx n) (run ctx m)
  | 0, h => by
    have : n = 0 := by omega
    subst this
    exact ⟨fun _ _ _ _ => mle_refl _, fun _ _ _ => mle_refl _⟩
  | m + 1, h => by
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have h1 := run_mono ctx (n := n) (m := m) (by omega)
      have h2 := run_mono_succ ctx m
      exact ⟨fun a b c d V r hr => h2.failed a b c d V r (h1.failed a b c d V r hr),
        fun a b c V r hr => h2.succeeded a b c V r (h1.succeeded a b c V r hr)⟩
    · have : n = m + 1 := by omega
      subst this
      exact ⟨fun _ _ _ _ => mle_refl _, fun _ _ _ => mle_refl _⟩

/-! ## The verdict and the warnings -/

/-- The fuel that suffices for the check of a label at the frames fs of rule. -/
noncomputable def fuelBound (ctx : Ctx) (rule : String) (fs : List Frame) : Nat :=
  (keyUniverse ctx rule fs).length + 1

/-- `verdictOf` of Labels.hs: the verdict with a fuel that suffices. -/
noncomputable def verdictOf (ctx : Ctx) (rule : String) (fs : List Frame) (x : Expr) : Verdict :=
  (verdictFuel ctx (fuelBound ctx rule fs) rule fs x).getD .safe

theorem verdictFuel_bound {ctx : Ctx} (hp : PassWF ctx.pass) (rule : String) (fs : List Frame) (x : Expr) :
    verdictFuel ctx (fuelBound ctx rule fs) rule fs x = some (verdictOf ctx rule fs x) := by
  obtain ⟨r, hr⟩ := run_terminates hp rule fs (startSet_wf hp x)
  simp [verdictOf, verdictFuel, fuelBound, hr]

/-- Every fuel that gives a verdict gives `verdictOf`. -/
theorem verdictFuel_eq {ctx : Ctx} (hp : PassWF ctx.pass) {n : Nat} {rule : String} {fs : List Frame}
    {x : Expr} {v : Verdict} (h : verdictFuel ctx n rule fs x = some v) : verdictOf ctx rule fs x = v := by
  have hb := verdictFuel_bound hp rule fs x
  simp only [verdictFuel, Option.map_eq_some_iff] at h hb
  obtain ⟨r1, h1, rfl⟩ := h
  obtain ⟨r2, h2, e2⟩ := hb
  have a1 := (run_mono ctx (Nat.le_max_left n (fuelBound ctx rule fs))).failed _ _ _ _ _ _ h1
  have a2 := (run_mono ctx (Nat.le_max_right n (fuelBound ctx rule fs))).failed _ _ _ _ _ _ h2
  rw [a1] at a2
  simp only [Option.some.injEq] at a2
  rw [← e2, a2]

/-- `labelWarnings` of Labels.hs, with `keyOf` the text of the keys of the
visited set. -/
noncomputable def labelWarningsBy (keyOf : Nat → List Item → String) (g : Grammar) : List Diagnostic :=
  labelWarningsWith keyOf verdictOf g

/-- `labelWarnings` of Labels.hs, with the keys that `repr` writes. -/
noncomputable def labelWarnings (g : Grammar) : List Diagnostic := labelWarningsBy preKey g

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x (by simp)]
    rw [filterMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem mapM_filterMap {α β : Type} {f : α → Option (Option β)} {h : α → Option β} :
    ∀ {l : List α} {l' : List (Option β)}, (∀ x ∈ l, ∀ y, f x = some y → y = h x) →
      l.mapM f = some l' → l'.filterMap id = l.filterMap h
  | [], l', _, hm => by simp at hm; subst hm; rfl
  | x :: xs, l', hf, hm => by
    rw [List.mapM_cons] at hm
    cases hfx : f x with
    | none => simp [hfx] at hm
    | some y =>
      cases hrest : xs.mapM f with
      | none => simp [hfx, hrest] at hm
      | some ys =>
        simp [hfx, hrest] at hm
        subst hm
        have h1 := hf x (by simp) y hfx
        have h2 := mapM_filterMap (fun z hz => hf z (List.mem_cons_of_mem _ hz)) hrest
        subst h1
        cases hx : h x <;> simp [hx, h2]

/-- The warnings of the probe, whenever its fuel gives a verdict on every label, are `labelWarnings`. -/
theorem labelWarnings_eq_fuel {n : Nat} {g : Grammar} {ws : List Diagnostic}
    (h : labelWarningsFuel n g = some ws) : ws = labelWarnings g := by
  have hp := contextWith_pass_wf preKey (unlabelGrammar g)
  unfold labelWarningsFuel at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l', hl', rfl⟩ := h
  unfold labelWarnings labelWarningsBy labelWarningsWith
  apply mapM_filterMap _ hl'
  intro s _ y hy
  unfold warningAt at hy
  split
  · rename_i l x name hexpr
    rw [hexpr] at hy
    simp only at hy
    split at hy
    · rename_i hsafe
      simp at hy
      subst hy
      simp only [hsafe, ↓reduceIte]
    · rename_i hsafe
      simp only [hsafe, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hy
      rw [verdictFuel_eq hp hv]
  · rename_i hne
    split at hy
    · rename_i l x name hexpr
      exact absurd hexpr (hne l x name)
    · simp at hy
      exact hy.symm

end PegHs.LabelCheck
