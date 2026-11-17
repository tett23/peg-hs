import CheckGroupsModel

/-!
The loops of CheckGroupsModel: what `reach`, the reachable rules, the rules
in left recursion and the nullable rules are.

`reach` is total by its measure (the names of `univ` not yet seen, the roots
left, the stack); `mem_reach_iff` shows that it returns the names seen at the
start and those reachable from them by at least one edge. `mem_reachable_iff`
applies it to the reachability of checkRules, and `mem_leftRecursiveRules_iff`
to left recursion: a rule is in left recursion exactly when it reaches itself
by at least one edge, without `partial def`. `nullableRulesWith_fixed` shows
that the loop of nullableRulesWith stops at a fixed point of its step.
-/

namespace PegHs.CheckGroups

open PegHs.LabelCheck (Loc Expr Item Diagnostic findLast Sub setEq)

theorem findLast_mem' {α : Type} {n : String} {a : α} :
    ∀ (xs : List (String × α)) (acc : Option α),
      xs.foldl (fun acc p => if p.1 == n then some p.2 else acc) acc = some a → acc = some a ∨ (n, a) ∈ xs
  | [], acc, h => Or.inl h
  | p :: ps, acc, h => by
    simp only [List.foldl_cons] at h
    rcases findLast_mem' ps _ h with h' | h'
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
  rcases findLast_mem' xs none h with h' | h'
  · cases h'
  · exact h'

theorem lookupRule_mem {rules : List Rule} {n : String} {r : Rule} (h : lookupRule rules n = some r) :
    r ∈ rules ∧ r.name = n := by
  have := findLast_mem h
  simp only [List.mem_map, Prod.mk.injEq] at this
  obtain ⟨r', hr', h1, h2⟩ := this
  subst h2
  exact ⟨hr', h1⟩

/-! ## reach -/

-- Paths of at least one edge.
inductive Plus (succ : String → List String) : String → String → Prop
  | single {n m : String} : m ∈ succ n → Plus succ n m
  | tail {n m p : String} : Plus succ n m → p ∈ succ m → Plus succ n p

theorem Plus.head {succ : String → List String} {n m p : String} (h : m ∈ succ n) (hp : Plus succ m p) :
    Plus succ n p := by
  induction hp with
  | single h' => exact .tail (.single h) h'
  | tail _ h' ih => exact .tail ih h'

-- The names seen at the start, or reachable from them.
def Reached (succ : String → List String) (seen0 : List String) (v : String) : Prop :=
  v ∈ seen0 ∨ ∃ s ∈ seen0, Plus succ s v

theorem Reached.step {succ : String → List String} {seen0 : List String} {v m : String}
    (h : Reached succ seen0 v) (hm : m ∈ succ v) : Reached succ seen0 m := by
  rcases h with h | ⟨s, hs, hp⟩
  · exact Or.inr ⟨v, h, .single hm⟩
  · exact Or.inr ⟨s, hs, .tail hp hm⟩

-- The invariants of the loop: every name seen is on the stack, a root, or
-- has all its successors in `univ` seen; every name seen and every name on
-- the stack or a root is reached.
structure ReachInv (univ : List String) (succ : String → List String) (seen0 seen ns es : List String) : Prop where
  closed : ∀ v ∈ seen, v ∈ ns ∨ v ∈ es ∨ ∀ m ∈ succ v, m ∈ univ → m ∈ seen
  sound : ∀ v ∈ seen, Reached succ seen0 v
  pending : ∀ v, v ∈ ns ∨ v ∈ es → Reached succ seen0 v
  base : ∀ v ∈ seen0, v ∈ seen

theorem reach_inv {univ : List String} {succ : String → List String} {seen0 : List String} :
    ∀ (seen ns es : List String), ReachInv univ succ seen0 seen ns es →
      ReachInv univ succ seen0 (reach univ succ seen ns es) [] [] := by
  intro seen ns es
  fun_induction reach univ succ seen ns es with
  | case1 seen => exact id
  | case2 seen e es ih =>
    intro h
    apply ih
    refine ⟨fun v hv => ?_, h.sound, fun v hv => ?_, h.base⟩
    · rcases h.closed v hv with h1 | h1 | h1
      · simp at h1
      · simp only [List.mem_cons] at h1 ⊢
        rcases h1 with rfl | h1
        · simp
        · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · simp only [List.mem_singleton] at hv
      rcases hv with rfl | hv
      · exact h.pending _ (Or.inr (by simp))
      · exact h.pending _ (Or.inr (by simp [hv]))
  | case3 seen n ns es next hnil ih =>
    intro h
    apply ih
    refine ⟨fun v hv => ?_, h.sound, fun v hv => h.pending v (by rcases hv with hv | hv <;> simp [hv]), h.base⟩
    rcases h.closed v hv with h1 | h1 | h1
    · simp only [List.mem_cons] at h1
      rcases h1 with rfl | h1
      · right; right
        intro m hm hu
        by_cases hs : m ∈ seen
        · exact hs
        · have : m ∈ next := by
            simp [next, hm, hu, hs]
          rw [hnil] at this
          simp at this
      · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  | case4 seen n ns es next hnil ih =>
    intro h
    have hpn : Reached succ seen0 n := h.pending n (Or.inl (by simp))
    have hnext : ∀ m ∈ next, m ∈ succ n := by
      intro m hm
      simp only [next, List.mem_filter] at hm
      exact hm.1
    apply ih
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => by simp [h.base v hv]⟩
    · rcases List.mem_append.1 hv with hv | hv
      · rcases h.closed v hv with h1 | h1 | h1
        · simp only [List.mem_cons] at h1
          rcases h1 with rfl | h1
          · right; right
            intro m hm hu
            by_cases hs : m ∈ seen
            · exact List.mem_append_left _ hs
            · apply List.mem_append_right
              simp [next, hm, hu, hs]
          · exact Or.inl (List.mem_append_right _ h1)
        · exact Or.inr (Or.inl h1)
        · right; right
          intro m hm hu
          exact List.mem_append_left _ (h1 m hm hu)
      · exact Or.inl (List.mem_append_left _ hv)
    · rcases List.mem_append.1 hv with hv | hv
      · exact h.sound v hv
      · exact hpn.step (hnext v hv)
    · rcases hv with hv | hv
      · rcases List.mem_append.1 hv with hv | hv
        · exact hpn.step (hnext v hv)
        · exact h.pending v (Or.inl (by simp [hv]))
      · exact h.pending v (Or.inr hv)

-- What `reach` returns, when every successor is in `univ` and the names
-- seen at the start are those on the stack and the roots.
theorem mem_reach_iff {univ : List String} {succ : String → List String}
    (hsucc : ∀ v, ∀ m ∈ succ v, m ∈ univ) {seen ns es : List String}
    (hstart : ∀ v, v ∈ seen ↔ v ∈ ns ∨ v ∈ es) (v : String) :
    v ∈ reach univ succ seen ns es ↔ Reached succ seen v := by
  have h0 : ReachInv univ succ seen seen ns es :=
    ⟨fun v hv => by rcases (hstart v).1 hv with h | h <;> simp [h],
     fun v hv => Or.inl hv,
     fun v hv => Or.inl ((hstart v).2 hv),
     fun _ hv => hv⟩
  have h := reach_inv seen ns es h0
  constructor
  · exact h.sound v
  · intro hr
    have hclosed : ∀ w ∈ reach univ succ seen ns es, ∀ m ∈ succ w, m ∈ reach univ succ seen ns es := by
      intro w hw m hm
      rcases h.closed w hw with h1 | h1 | h1
      · simp at h1
      · simp at h1
      · exact h1 m hm (hsucc w m hm)
    rcases hr with hr | ⟨s, hs, hp⟩
    · exact h.base v hr
    · have hs' := h.base s hs
      clear hs
      induction hp with
      | single hm => exact hclosed _ hs' _ hm
      | tail _ hm ih => exact hclosed _ ih _ hm

/-! ## The reachable rules -/

theorem itemsRefs_names_mem {g : Grammar} {r : Rule} (hr : r ∈ g.rules) {m : String}
    (hm : m ∈ r.alts.flatMap (fun a => (itemsRefs a.items).map (fun x => x.2.1))) :
    m ∈ (refs g).map (fun x => x.2.1) := by
  simp only [List.mem_flatMap, List.mem_map] at hm ⊢
  obtain ⟨a, ha, x, hx, rfl⟩ := hm
  exact ⟨x, by simp only [refs, List.mem_flatMap]; exact ⟨r, hr, a, ha, hx⟩, rfl⟩

theorem callees_univ (g : Grammar) (fr : Rule) : ∀ v, ∀ m ∈ callees g v, m ∈ reachUniverse g fr := by
  intro v m hm
  unfold callees at hm
  split at hm
  · rename_i r hr
    have := itemsRefs_names_mem (lookupRule_mem hr).1 hm
    simp [reachUniverse, this]
  · simp at hm

-- The reachable rules of checkRules: the start rule, the entry rules, the
-- recovery rules, and the rules that they call, directly or not.
theorem mem_reachable_iff (g : Grammar) (fr : Rule) (v : String) :
    v ∈ reachable g fr ↔ Reached (callees g) (startName g fr :: roots g) v := by
  unfold reachable
  apply mem_reach_iff (callees_univ g fr)
  intro w
  simp

/-! ## Left recursion -/

-- The successors of a rule in the graph of left calls, as in leftRecursiveRules.
def lrSucc (rec : Recovery) (rules : List Rule) (n : String) : List String :=
  match findLast (rules.map (fun r => (r.name, r))) n with
  | some r => (edges rec (nullableRulesWith rec rules) r).filter ((rules.map (·.name)).contains ·)
  | none => []

theorem plus_iff_reached {succ : String → List String} {n v : String} :
    Plus succ n v ↔ Reached succ (succ n) v := by
  constructor
  · intro h
    induction h with
    | single hm => exact Or.inl hm
    | tail _ hm ih => exact ih.step hm
  · rintro (h | ⟨s, hs, hp⟩)
    · exact .single h
    · exact Plus.head hs hp

-- A rule is in left recursion exactly when it is a rule of the grammar and
-- reaches itself by at least one left call (`partial def` is not used).
theorem mem_leftRecursiveRules_iff (rec : Recovery) (rules : List Rule) (n : String) :
    n ∈ leftRecursiveRules rec rules ↔ n ∈ rules.map (·.name) ∧ Plus (lrSucc rec rules) n n := by
  unfold leftRecursiveRules
  simp only [List.mem_filter, List.contains_iff_mem]
  apply and_congr_right
  intro _
  rw [plus_iff_reached]
  have hsucc : ∀ v, ∀ m ∈ lrSucc rec rules v, m ∈ rules.map (·.name) := by
    intro v m hm
    unfold lrSucc at hm
    split at hm
    · simp only [List.mem_filter, List.contains_iff_mem] at hm
      exact hm.2
    · simp at hm
  exact mem_reach_iff (succ := lrSucc rec rules) hsucc (fun w => by simp) n

/-! ## Nullable rules -/

theorem nullableGoWith_fixed (rec : Recovery) (rules : List Rule) :
    ∀ (known : List String) (h : Sub known (nullStepWith rec rules known)),
      setEq (nullStepWith rec rules (nullableGoWith rec rules known h)) (nullableGoWith rec rules known h) = true := by
  intro known h
  fun_induction nullableGoWith rec rules known h with
  | case1 known h next hne => exact hne
  | case2 known h next hne ih => exact ih

-- The loop of nullableRulesWith stops at a set that its step does not
-- change.
theorem nullableRulesWith_fixed (rec : Recovery) (rules : List Rule) :
    setEq (nullStepWith rec rules (nullableRulesWith rec rules)) (nullableRulesWith rec rules) = true :=
  nullableGoWith_fixed rec rules _ _

/-! ## The values of Peg.Grammar.Types -/

theorem valuedL_eq (u : List String) : ∀ is : List Item, valuedL u is = is.filter (fun i => hasValue u i.2.2)
  | [] => by simp [valuedL]
  | (l, b, e) :: is => by
    rw [valuedL, valuedL_eq u is]
    by_cases h : hasValue u e <;> simp [h]

theorem sigL_eq (u : List String) :
    ∀ is : List Item, sigL u is = (is.filter (fun i => hasValue u i.2.2)).filter (fun i => i.2.1.isSome || !isUnit u i.2.2)
  | [] => by simp [sigL]
  | (l, b, e) :: is => by
    rw [sigL, sigL_eq u is]
    by_cases h : hasValue u e <;> by_cases h' : (b.isSome || !isUnit u e) <;> simp_all

-- `countedItems` is the definition of Peg.Grammar.Types.
theorem countedItems_eq (u : List String) (is : List Item) :
    countedItems u is =
      let valued := is.filter (fun i => hasValue u i.2.2)
      let significant := valued.filter (fun i => i.2.1.isSome || !isUnit u i.2.2)
      if significant = [] then valued else significant := by
  rw [countedItems, valuedL_eq, sigL_eq]

theorem allUnitValued_eq (u : List String) :
    ∀ is : List Item, allUnitValued u is = (valuedL u is).all (fun i => isUnit u i.2.2)
  | [] => by simp [allUnitValued, valuedL]
  | (l, b, e) :: is => by
    rw [allUnitValued, valuedL, allUnitValued_eq u is]
    by_cases h : hasValue u e <;> simp [h]

theorem allUnitSig_eq (u : List String) :
    ∀ is : List Item, allUnitSig u is = (sigL u is).all (fun i => isUnit u i.2.2)
  | [] => by simp [allUnitSig, sigL]
  | (l, b, e) :: is => by
    rw [allUnitSig, sigL, allUnitSig_eq u is]
    cases b <;> by_cases h1 : hasValue u e <;> by_cases h3 : isUnit u e <;> simp [h1, h3]

-- `all (isUnit units . itemExpr) (countedItems units items)`.
theorem allUnitCounted_eq (u : List String) (is : List Item) :
    allUnitCounted u is = (countedItems u is).all (fun i => isUnit u i.2.2) := by
  rw [allUnitCounted, countedItems]
  split <;> simp [allUnitValued_eq, allUnitSig_eq]

theorem groupOne_eq (u : List String) :
    ∀ as : List (List Item), groupOne u as = as.all (fun a => (countedItems u a).length == 1)
  | [] => by simp [groupOne]
  | a :: as => by rw [groupOne, groupOne_eq u as]; simp

theorem unitAlts_eq (u : List String) :
    ∀ as : List (List Item), unitAlts u as = as.all (fun a => (countedItems u a).all (fun i => isUnit u i.2.2))
  | [] => by simp [unitAlts]
  | a :: as => by rw [unitAlts, unitAlts_eq u as, allUnitCounted_eq]; simp

end PegHs.CheckGroups
