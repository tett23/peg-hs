import CheckGroupsReach

/-!
What each group of errors of checkRules rejects and accepts, and the branch
of `check` (ADR 0097, invariant 2).

Each `*_nil` theorem states when a group has no error: the group accepts
exactly the grammars of its right-hand side and rejects the others with at
least one error. `check_error_ne_nil`, `check_ok_iff` and `check_rejects`
show that `check` runs all fifteen groups without stopping at the first
that fails, sorts their errors, and rejects with at least one error and no
`Analysis` exactly when the grammar is a library, has no rules, or one group
has an error. `generation_rejects` carries the rejection to `generate` and
`generateWithWarnings`, whose `Left` holds no generated text.
-/

namespace PegHs.CheckGroups

open PegHs.LabelCheck (Loc Expr Item Diagnostic findLast lookupFirst indexed)

/-! ## The root -/

theorem sortOnLoc_perm (ds : List Diagnostic) : (sortOnLoc ds).Perm ds :=
  List.mergeSort_perm ds _

theorem sortOnLoc_eq_nil (ds : List Diagnostic) : sortOnLoc ds = [] ↔ ds = [] := by
  constructor
  · intro h
    have := (sortOnLoc_perm ds).length_eq
    rw [h] at this
    exact List.eq_nil_of_length_eq_zero this.symm
  · rintro rfl; simp [sortOnLoc]

theorem groups_length (g : Grammar) (fr : Rule) (o : Oracle) : (groups g fr o).length = 15 := rfl

theorem errors_eq_nil (g : Grammar) (fr : Rule) (o : Oracle) :
    errors g fr o = [] ↔ ∀ G ∈ groups g fr o, G = [] := by
  simp [errors, List.flatten_eq_nil_iff]

-- checkRules sorts the errors of all the groups; it accepts exactly when
-- there is none, and then returns the analysis.
theorem checkRules_ok_iff (root : Bool) (g : Grammar) (fr : Rule) (o : Oracle) :
    (∃ a, checkRules root g fr o = .ok a) ↔ (if root then errors g fr o else libraryErrors g o) = [] := by
  unfold checkRules
  constructor
  · rintro ⟨a, h⟩
    split at h
    · rename_i hs; exact (sortOnLoc_eq_nil _).1 hs
    · cases h
  · intro h
    rw [(sortOnLoc_eq_nil _).2 h]
    exact ⟨_, rfl⟩

theorem checkRules_error (root : Bool) (g : Grammar) (fr : Rule) (o : Oracle) {ds : List Diagnostic}
    (h : checkRules root g fr o = .error ds) :
    ds ≠ [] ∧ ds.Perm (if root then errors g fr o else libraryErrors g o) := by
  unfold checkRules at h
  generalize hs : sortOnLoc (if root then errors g fr o else libraryErrors g o) = s at h
  cases s with
  | nil => cases h
  | cons d ds' =>
    cases h
    refine ⟨by simp, ?_⟩
    rw [← hs]
    exact sortOnLoc_perm _

-- Invariant 2: a rejection has at least one error.
theorem check_error_ne_nil (g : Grammar) (o : Oracle) {ds : List Diagnostic}
    (h : check g o = .error ds) : ds ≠ [] := by
  unfold check at h
  split at h
  · cases h; simp
  · cases h; simp
  · exact (checkRules_error true g _ o h).1

-- `check` accepts exactly a grammar that is not a library, has rules, and
-- has no error in any of the fifteen groups.
theorem check_ok_iff (g : Grammar) (o : Oracle) :
    (∃ a, check g o = .ok a) ↔
      g.library = none ∧ ∃ fr rs, g.rules = fr :: rs ∧ ∀ G ∈ groups g fr o, G = [] := by
  unfold check
  split
  · rename_i l rs hl
    simp [hl]
  · rename_i hl hr
    simp [hl, hr]
  · rename_i fr rs hl hr
    rw [checkRules_ok_iff]
    simp [hl, hr, errors_eq_nil]

-- Every error of every group is reported: the groups do not stop at the
-- first that fails.
theorem check_rejects (g : Grammar) (o : Oracle) {fr : Rule} {rs : List Rule}
    (hl : g.library = none) (hr : g.rules = fr :: rs) {G : List Diagnostic} (hG : G ∈ groups g fr o)
    {d : Diagnostic} (hd : d ∈ G) : ∃ ds, check g o = .error ds ∧ d ∈ ds := by
  have hmem : d ∈ errors g fr o := List.mem_flatten.2 ⟨G, hG, hd⟩
  unfold check
  simp only [hl, hr]
  cases h : checkRules true g fr o with
  | error ds =>
    refine ⟨ds, rfl, ?_⟩
    have := (checkRules_error true g fr o h).2
    exact this.mem_iff.2 hmem
  | ok a =>
    have : errors g fr o = [] := (checkRules_ok_iff true g fr o).1 ⟨a, h⟩
    rw [this] at hmem
    cases hmem

-- The rejection of `generate` and `generateWithWarnings`: `either (Left .
-- templateNotes g0) Right (check g)`, where templateNotes is `nub . map note`.
def generation {α : Type} (note : Diagnostic → Diagnostic) (render : Analysis → α)
    (r : Except (List Diagnostic) Analysis) : Except (List Diagnostic) α :=
  match r with
  | .error ds => .error (ds.map note).eraseDups
  | .ok a => .ok (render a)

theorem eraseDups_ne_nil {β : Type} [BEq β] {l : List β} (h : l ≠ []) : l.eraseDups ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => simp [List.eraseDups_cons]

-- Invariant 2 at the generation: when `check` rejects, the generation
-- returns at least one error and no text.
theorem generation_rejects {α : Type} (g : Grammar) (o : Oracle) (note : Diagnostic → Diagnostic)
    (render : Analysis → α) {ds : List Diagnostic} (h : check g o = .error ds) :
    ∃ es, generation note render (check g o) = .error es ∧ es ≠ [] := by
  rw [h]
  refine ⟨_, rfl, eraseDups_ne_nil ?_⟩
  simpa using check_error_ne_nil g o h

/-! ## Lists of keys -/

theorem mem_indexed {α : Type} :
    ∀ (xs : List α) (n k : Nat) (x : α), (k, x) ∈ indexed n xs ↔ ∃ i, ∃ h : i < xs.length, k = n + i ∧ xs[i] = x
  | [], n, k, x => by simp [indexed]
  | y :: ys, n, k, x => by
    simp only [indexed, List.mem_cons, Prod.mk.injEq, mem_indexed ys (n + 1) k x]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
      · exact ⟨0, by simp, by simp, rfl⟩
      · exact ⟨i + 1, by simp; omega, by omega, rfl⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      cases i with
      | zero => exact Or.inl ⟨by simp, rfl⟩
      | succ i => exact Or.inr ⟨i, by simp at hi; omega, by omega, rfl⟩

theorem mem_indexed_zero_iff {α : Type} (xs : List α) (x : α) : (∃ k, (k, x) ∈ indexed 0 xs) ↔ x ∈ xs := by
  simp only [mem_indexed]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, i, hi, _, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, i, hi, by simp, rfl⟩

theorem mem_indexed_shift {α : Type} (xs : List α) (n k : Nat) (x : α) :
    (k, x) ∈ indexed (n + 1) xs ↔ ∃ k', k = k' + 1 ∧ (k', x) ∈ indexed n xs := by
  simp only [mem_indexed]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨n + i, by omega, i, hi, rfl, rfl⟩
  · rintro ⟨k', rfl, i, hi, rfl, rfl⟩; exact ⟨i, hi, by omega, rfl⟩

-- No element has the key of an earlier one: the keys are distinct.
theorem indexed_take_nodup {α : Type} (f : α → String) (xs : List α) :
    (∀ k x, (k, x) ∈ indexed 0 xs → f x ∉ (xs.take k).map f) ↔ (xs.map f).Nodup := by
  induction xs with
  | nil => simp [indexed]
  | cons y ys ih =>
    rw [List.map_cons, List.nodup_cons, ← ih]
    simp only [indexed, List.mem_cons, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨fun hy => ?_, fun k x hx => ?_⟩
      · obtain ⟨x, hx, hfx⟩ := List.mem_map.1 hy
        obtain ⟨k, hk⟩ := (mem_indexed_zero_iff ys x).2 hx
        have := h (k + 1) x (Or.inr ((mem_indexed_shift ys 0 (k + 1) x).2 ⟨k, rfl, hk⟩))
        simp [List.take_succ_cons, hfx] at this
      · have := h (k + 1) x (Or.inr ((mem_indexed_shift ys 0 (k + 1) x).2 ⟨k, rfl, hx⟩))
        intro hm
        apply this
        simp only [List.take_succ_cons, List.map_cons, List.mem_cons]
        exact Or.inr hm
    · rintro ⟨hy, h⟩ k x (⟨rfl, rfl⟩ | hx)
      · simp
      · obtain ⟨k', rfl, hk⟩ := (mem_indexed_shift ys 0 k x).1 hx
        simp only [List.take_succ_cons, List.map_cons, List.mem_cons, not_or]
        refine ⟨fun he => hy ?_, h k' x hk⟩
        rw [← he]
        exact List.mem_map_of_mem ((mem_indexed_zero_iff ys x).1 ⟨k', hk⟩)

theorem secondOf_nil (n : String) (l : List Loc) : secondOf n l = [] ↔ l.length ≤ 1 := by
  match l with
  | [] => simp [secondOf]
  | [_] => simp [secondOf]
  | _ :: _ :: _ => simp [secondOf]

theorem secondOccurrences_nil (xs : List (String × Loc)) :
    secondOccurrences xs = [] ↔ (xs.map Prod.fst).Nodup := by
  have key : ∀ n, secondOf n ((xs.filter (fun x => x.1 == n)).map Prod.snd) = [] ↔ (xs.map Prod.fst).count n ≤ 1 := by
    intro n
    rw [secondOf_nil, List.length_map, List.count_eq_length_filter, List.filter_map, List.length_map]
    rfl
  unfold secondOccurrences
  rw [List.flatMap_eq_nil_iff, List.nodup_iff_count]
  simp only [List.mem_mergeSort, List.mem_eraseDups, key]
  constructor
  · intro h n
    by_cases hn : n ∈ xs.map Prod.fst
    · exact h n hn
    · rw [List.count_eq_zero.2 hn]; omega
  · intro h n _; exact h n

theorem lookupFirst_none {α : Type} (xs : List (String × α)) (n : String) :
    lookupFirst xs n = none ↔ n ∉ xs.map Prod.fst := by
  simp only [lookupFirst, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq, List.mem_map, not_exists, not_and]

/-! ## The groups -/

theorem undefinedErrors_nil (g : Grammar) :
    undefinedErrors g = [] ↔
      (∀ l n k, (l, n, k) ∈ refs g → n ∈ ruleNames g) ∧ (∀ l n, (l, n) ∈ directiveNames g → n ∈ ruleNames g) := by
  simp [undefinedErrors, List.flatMap_eq_nil_iff]

theorem arityErrors_nil (g : Grammar) :
    arityErrors g = [] ↔ ∀ l n k, (l, n, k) ∈ refs g → ∀ r, lookupRule g.rules n = some r → k = r.params.length := by
  simp only [arityErrors, List.flatMap_eq_nil_iff, Prod.forall]
  apply forall_congr'; intro l; apply forall_congr'; intro n; apply forall_congr'; intro k
  apply imp_congr_right; intro _
  cases lookupRule g.rules n <;> simp

theorem entryErrors_nil (g : Grammar) (fr : Rule) :
    entryErrors g fr = [] ↔
      (∀ l n, (l, n) ∈ (startLoc g fr, startName g fr) :: g.entries → ∀ r, lookupRule g.rules n = some r → r.params = []) ∧
        (g.entries.map Prod.snd).Nodup := by
  rw [← indexed_take_nodup]
  simp only [entryErrors, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, Prod.forall]
  apply and_congr
  · apply forall_congr'; intro l; apply forall_congr'; intro n
    apply imp_congr_right; intro _
    cases lookupRule g.rules n <;> simp
  · apply forall_congr'; intro k; apply forall_congr'; intro l; apply forall_congr'; intro n
    apply imp_congr_right; intro _
    simp

theorem reachabilityErrors_nil (g : Grammar) (fr : Rule) :
    reachabilityErrors g fr = [] ↔
      ∀ r ∈ g.rules, r.loc.file = 0 → Reached (callees g) (startName g fr :: roots g) r.name := by
  simp only [reachabilityErrors, List.flatMap_eq_nil_iff, ← mem_reachable_iff]
  apply forall_congr'; intro r; apply imp_congr_right; intro _
  simp

theorem languageErrors_nil (g : Grammar) :
    languageErrors g = [] ↔ ∀ l x, (l, x) ∈ g.languages → x ≠ "RebindableSyntax" := by
  simp [languageErrors, List.flatMap_eq_nil_iff]

theorem nomemoErrors_nil (g : Grammar) :
    nomemoErrors g = [] ↔ ∀ l n, (l, n) ∈ g.noMemo → n ∉ lrOf g := by
  simp [nomemoErrors, List.flatMap_eq_nil_iff]

theorem paramLrErrors_nil (g : Grammar) :
    paramLrErrors g = [] ↔ ∀ r ∈ g.rules, r.params ≠ [] → r.name ∉ lrOf g := by
  simp [paramLrErrors, List.flatMap_eq_nil_iff]

-- With the characterization of left recursion: a rule with parameters
-- does not reach itself by left calls.
theorem paramLrErrors_nil' (g : Grammar) :
    paramLrErrors g = [] ↔ ∀ r ∈ g.rules, r.params ≠ [] → ¬ Plus (lrSucc (recovery g) g.rules) r.name r.name := by
  rw [paramLrErrors_nil]
  apply forall_congr'; intro r; apply imp_congr_right; intro hr; apply imp_congr_right; intro _
  rw [lrOf, mem_leftRecursiveRules_iff]
  simp only [List.mem_map, not_and]
  exact ⟨fun h hp => h ⟨r, hr, rfl⟩ hp, fun h _ => h⟩

theorem syntaxErrors_nil (g : Grammar) (fr : Rule) :
    syntaxErrors g fr = [] ↔
      match g.syntaxLoc with
      | none => g.tokens = [] ∧ g.trivia = [] ∧ g.inline = []
      | some _ =>
        (∀ l n, (l, n) ∈ g.trivia → n ∈ g.tokens.map Prod.snd) ∧
        (∀ l n, (l, n) ∈ g.inline → n ∉ g.tokens.map Prod.snd) ∧
        (∀ l n, (l, n) ∈ g.inline → n ≠ startName g fr ∧ n ∉ g.entries.map Prod.snd) := by
  unfold syntaxErrors
  cases h : g.syntaxLoc with
  | none => simp [List.flatMap_cons, List.flatMap_nil]
  | some _ => simp [List.flatMap_eq_nil_iff]

theorem recoverErrors_nil (g : Grammar) :
    recoverErrors g = [] ↔
      (∀ a l n, (a, l, n) ∈ g.recovers → n ∈ ruleNames g) ∧
      (∀ a l n, (a, l, n) ∈ g.recovers → ∀ r, lookupRule g.rules n = some r → r.params = []) ∧
      (g.recovers.map (fun p => p.1.2)).Nodup ∧
      (∀ l n b, ((l, n), b) ∈ g.recovers → n ∈ usedLabels g) ∧
      (∀ l n, (l, n) ∈ g.safe → n ∈ usedLabels g) ∧
      (∀ l n b, ((l, n), b) ∈ g.messages → n ∈ usedLabels g) := by
  have hs := secondOccurrences_nil (g.recovers.map fun p => (p.1.2, p.1.1))
  simp only [List.map_map] at hs
  have hf : (Prod.fst ∘ fun p : (Loc × String) × (Loc × String) => (p.1.2, p.1.1)) = (fun p => p.1.2) := rfl
  rw [hf] at hs
  simp only [recoverErrors, List.append_eq_nil_iff, List.map_eq_nil_iff, hs, and_assoc]
  simp only [List.flatMap_eq_nil_iff, Prod.forall]
  apply and_congr
  · apply forall_congr'; intro a; apply forall_congr'; intro b; apply forall_congr'; intro l; apply forall_congr'; intro n
    apply imp_congr_right; intro _; simp
  apply and_congr
  · apply forall_congr'; intro a; apply forall_congr'; intro b; apply forall_congr'; intro l; apply forall_congr'; intro n
    apply imp_congr_right; intro _
    cases lookupRule g.rules n <;> simp
  apply and_congr Iff.rfl
  apply and_congr
  · apply forall_congr'; intro l; apply forall_congr'; intro n; apply forall_congr'; intro a; apply forall_congr'; intro b
    apply imp_congr_right; intro _; simp
  apply and_congr
  · apply forall_congr'; intro l; apply forall_congr'; intro n
    apply imp_congr_right; intro _; simp
  · apply forall_congr'; intro l; apply forall_congr'; intro n; apply forall_congr'; intro a; apply forall_congr'; intro b
    apply imp_congr_right; intro _; simp

/-! ### Repetitions -/

-- The repeated expressions: the operand of each `*` and `+`, outside and
-- inside one another, in the traversal of repetitionErrors.
def repeatedExpr : Expr → List Expr
  | .star x | .plus x => x :: repeatedExpr x
  | .opt x | .and x | .not x | .capture x | .discard x => repeatedExpr x
  | .label _ x _ => repeatedExpr x
  | .group alts => repeatedExpr.alts alts
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts : List (List Item) → List Expr
    | [] => []
    | a :: as => repeatedExpr.seq a ++ repeatedExpr.alts as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  seq : List Item → List Expr
    | [] => []
    | (_, _, e) :: is => repeatedExpr e ++ repeatedExpr.seq is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega

mutual
theorem repExprErrs_nil (known : List String) (l : Loc) :
    (e : Expr) → (repExprErrs known l e = [] ↔ ∀ x ∈ repeatedExpr e, exprNullable known x = false)
  | .star x => by
    rw [repExprErrs, repeatedExpr, List.append_eq_nil_iff, repExprErrs_nil known l x]
    by_cases h : exprNullable known x <;> simp [h]
  | .plus x => by
    rw [repExprErrs, repeatedExpr, List.append_eq_nil_iff, repExprErrs_nil known l x]
    by_cases h : exprNullable known x <;> simp [h]
  | .opt x | .and x | .not x | .capture x | .discard x => by
    rw [repExprErrs, repeatedExpr]; exact repExprErrs_nil known l x
  | .label _ x _ => by
    rw [repExprErrs, repeatedExpr]; exact repExprErrs_nil known l x
  | .group alts => by
    rw [repExprErrs, repeatedExpr]; exact repExprErrs_alts_nil known alts
  | .lit .. | .cls .. | .any | .ref .. | .pred .. | .template .. => by
    simp [repExprErrs, repeatedExpr]
termination_by e => sizeOf e

theorem repExprErrs_alts_nil (known : List String) :
    (as : List (List Item)) →
      (repExprErrs.alts known as = [] ↔ ∀ x ∈ repeatedExpr.alts as, exprNullable known x = false)
  | [] => by simp [repExprErrs.alts, repeatedExpr.alts]
  | a :: as => by
    rw [repExprErrs.alts, repeatedExpr.alts, List.append_eq_nil_iff, repExprErrs_seq_nil known a,
      repExprErrs_alts_nil known as]
    simp only [List.mem_append]
    exact ⟨fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x), fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩⟩
termination_by as => sizeOf as

theorem repExprErrs_seq_nil (known : List String) :
    (is : List Item) →
      (repExprErrs.seq known is = [] ↔ ∀ x ∈ repeatedExpr.seq is, exprNullable known x = false)
  | [] => by simp [repExprErrs.seq, repeatedExpr.seq]
  | (l, b, e) :: is => by
    rw [repExprErrs.seq, repeatedExpr.seq, List.append_eq_nil_iff, repExprErrs_nil known l e,
      repExprErrs_seq_nil known is]
    simp only [List.mem_append]
    exact ⟨fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x), fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩⟩
termination_by is => sizeOf is
end

-- A rule has no repetition error exactly when no repeated expression of
-- it can match the empty string.
theorem repetitionErrors_nil (known : List String) (r : Rule) :
    repetitionErrors known r = [] ↔ ∀ a ∈ r.alts, ∀ x ∈ repeatedExpr.seq a.items, exprNullable known x = false := by
  simp only [repetitionErrors, List.flatMap_eq_nil_iff]
  exact forall_congr' fun a => imp_congr_right fun _ => repExprErrs_seq_nil known a.items

/-! ### Alternatives -/

theorem bindingErrors_nil (w : Bool) (u : List String) (items : List Item) :
    bindingErrors w u items = [] ↔
      ∀ l n e, (l, some n, e) ∈ items → "_".isPrefixOf n = false ∧ (w = true → hasValue u e = true) := by
  simp only [bindingErrors, List.flatMap_eq_nil_iff, Prod.forall]
  constructor
  · intro h l n e hm
    have := h l (some n) e hm
    by_cases h1 : "_".isPrefixOf n <;> by_cases h2 : w <;> by_cases h3 : hasValue u e <;> simp_all
  · intro h l b e hm
    cases b with
    | none => rfl
    | some n =>
      have := h l n e hm
      by_cases h1 : "_".isPrefixOf n <;> by_cases h2 : w <;> by_cases h3 : hasValue u e <;> simp_all

theorem duplicateErrors_nil (items : List Item) :
    duplicateErrors items = [] ↔ (topBound items).Nodup := by
  have := secondOccurrences_nil (items.filterMap fun (l, b, _) => b.map (·, l))
  rw [duplicateErrors, List.map_eq_nil_iff, this]
  have he : (items.filterMap fun (l, b, _) => b.map (·, l)).map Prod.fst = topBound items := by
    unfold topBound
    rw [List.map_filterMap]
    congr 1
    funext x
    obtain ⟨l, b, e⟩ := x
    cases b <;> rfl
  rw [he]

theorem omissionErrors_nil (u d v k : List String) (r : Rule) (a : Alt) :
    omissionErrors u d v k r a = [] ↔
      a.action.isSome ∨ v.contains r.name ∨ k.contains r.name ∨ (valueRefs.items a.items).any (k.contains ·) ∨
        (countedItems u a.items).length = 1 ∨ omitsUnitAction u r.name a.items ∨ discardsValues d r.name a.items := by
  unfold omissionErrors
  simp only []
  repeat' split
  all_goals (try simp_all)
  all_goals (rename_i h; rcases h with h | h <;> simp [h])

-- The sequences of the groups inside a sequence, at any depth.
def groupSeqs : Expr → List (List Item)
  | .group alts => groupSeqs.alts alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => groupSeqs x
  | .label _ x _ => groupSeqs x
  | _ => []
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega
where
  alts : List (List Item) → List (List Item)
    | [] => []
    | is :: as => is :: groupSeqs.items is ++ groupSeqs.alts as
  termination_by as => sizeOf as
  decreasing_by all_goals simp_wf <;> omega
  items : List Item → List (List Item)
    | [] => []
    | (_, _, e) :: is => groupSeqs e ++ groupSeqs.items is
  termination_by is => sizeOf is
  decreasing_by all_goals simp_wf <;> omega

theorem forall_append {α : Type} {p : α → Prop} {xs ys : List α} :
    (∀ x ∈ xs ++ ys, p x) ↔ (∀ x ∈ xs, p x) ∧ ∀ x ∈ ys, p x := by
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun ⟨h1, h2⟩ x hx => hx.elim (h1 x) (h2 x)⟩

mutual
theorem groupExprErrs_nil (w : Bool) (u : List String) :
    (e : Expr) → (groupExprErrs w u e = [] ↔ ∀ s ∈ groupSeqs e, bindingErrors w u s = [])
  | .group alts => by
    rw [groupExprErrs, groupSeqs]; exact groupExprErrs_alts_nil w u alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => by
    rw [groupExprErrs, groupSeqs]; exact groupExprErrs_nil w u x
  | .label _ x _ => by
    rw [groupExprErrs, groupSeqs]; exact groupExprErrs_nil w u x
  | .lit .. | .cls .. | .any | .ref .. | .pred .. | .template .. => by
    simp [groupExprErrs, groupSeqs]
termination_by e => sizeOf e

theorem groupExprErrs_alts_nil (w : Bool) (u : List String) :
    (as : List (List Item)) →
      (groupExprErrs.alts w u as = [] ↔ ∀ s ∈ groupSeqs.alts as, bindingErrors w u s = [])
  | [] => by simp [groupExprErrs.alts, groupSeqs.alts]
  | is :: as => by
    rw [groupExprErrs.alts, groupSeqs.alts, List.append_eq_nil_iff, List.append_eq_nil_iff,
      groupExprErrs_items_nil w u is, groupExprErrs_alts_nil w u as]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ s hs
      simp only [List.mem_cons, List.mem_append] at hs
      rcases hs with (rfl | hs) | hs
      · exact h1
      · exact h2 s hs
      · exact h3 s hs
    · intro h
      exact ⟨⟨h is (by simp), fun s hs => h s (by simp [hs])⟩, fun s hs => h s (by simp [hs])⟩
termination_by as => sizeOf as

theorem groupExprErrs_items_nil (w : Bool) (u : List String) :
    (is : List Item) →
      (groupExprErrs.items w u is = [] ↔ ∀ s ∈ groupSeqs.items is, bindingErrors w u s = [])
  | [] => by simp [groupExprErrs.items, groupSeqs.items]
  | (l, b, e) :: is => by
    rw [groupExprErrs.items, groupSeqs.items, List.append_eq_nil_iff, groupExprErrs_nil w u e,
      groupExprErrs_items_nil w u is, forall_append]
termination_by is => sizeOf is
end

-- An alternative has no error exactly when the bindings of its sequence
-- and of the sequences of its groups are valid, the bindings of its
-- sequence are distinct, and, with values, its value is that of one
-- element or it has an action or one of the exceptions.
theorem altErrors_nil (w : Bool) (u d v k : List String) (r : Rule) :
    altErrors w u d v k r = [] ↔
      ∀ a ∈ r.alts,
        bindingErrors w u a.items = [] ∧ (topBound a.items).Nodup ∧
        (w = true → omissionErrors u d v k r a = []) ∧
        ∀ s ∈ groupSeqs.items a.items, bindingErrors w u s = [] := by
  simp only [altErrors, List.flatMap_eq_nil_iff, List.append_eq_nil_iff, duplicateErrors_nil,
    groupExprErrs_items_nil]
  apply forall_congr'; intro a; apply imp_congr_right; intro _
  cases w <;> simp [and_assoc]

/-! ### References to bindings -/

theorem bindingReferenceErrors_nil (vars : Loc → String → List (Loc × String)) (r : Rule) :
    bindingReferenceErrors vars r = [] ↔
      ∀ a ∈ r.alts, ∀ kind left l0 code, (kind, left, l0, code) ∈ altCodes a →
        ∀ l n, (l, n) ∈ vars l0 code →
          n ∈ r.params ∨ n ∉ r.alts.flatMap (fun a => boundIn a.items) ∨ n ∈ left := by
  simp only [bindingReferenceErrors, List.flatMap_eq_nil_iff, Prod.forall]
  apply forall_congr'; intro a; apply imp_congr_right; intro _
  apply forall_congr'; intro kind; apply forall_congr'; intro left; apply forall_congr'; intro l0
  apply forall_congr'; intro code; apply imp_congr_right; intro _
  apply forall_congr'; intro l; apply forall_congr'; intro n; apply imp_congr_right; intro _
  by_cases h1 : n ∈ r.params <;> by_cases h2 : n ∈ r.alts.flatMap (fun a => boundIn a.items) <;>
    by_cases h3 : n ∈ left <;> simp [h1, h2, h3]

/-! ### Constructor names -/

theorem misplacedErrors_nil (g : Grammar) (c : Classification) :
    misplacedErrors g c = [] ↔
      ∀ r ∈ g.rules, ∀ a ∈ r.alts, ∀ l n, a.constructor = some (l, n) → misplaced g c r n = none := by
  simp only [misplacedErrors, List.flatMap_eq_nil_iff]
  apply forall_congr'; intro r; apply imp_congr_right; intro _
  apply forall_congr'; intro a; apply imp_congr_right; intro _
  cases a.constructor with
  | none => simp
  | some p =>
    obtain ⟨l, n⟩ := p
    cases misplaced g c r n <;> simp

theorem lowerErrors_nil (g : Grammar) (c : Classification) (isUpper : Char → Bool) :
    lowerErrors g c isUpper = [] ↔
      ∀ r ∈ g.rules, (r.name ∈ c.generated ∨ r.name ∈ c.unknown) →
        ∀ a ∈ r.alts, ∀ l n, a.constructor = some (l, n) → startsUpper isUpper n = true := by
  simp only [lowerErrors, List.flatMap_eq_nil_iff]
  apply forall_congr'; intro r; apply imp_congr_right; intro _
  by_cases h : r.name ∈ c.generated ∨ r.name ∈ c.unknown
  · have hb : (c.generated.contains r.name || c.unknown.contains r.name) = true := by simpa using h
    simp only [hb, ↓reduceIte, List.flatMap_eq_nil_iff, h, true_implies]
    apply forall_congr'; intro a; apply imp_congr_right; intro _
    cases a.constructor with
    | none => simp
    | some p => obtain ⟨l, n⟩ := p; by_cases hn : startsUpper isUpper n <;> simp [hn]
  · have hb : (c.generated.contains r.name || c.unknown.contains r.name) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ↓reduceIte, true_iff]
    exact fun hm => absurd hm h

theorem typeNameErrors_nil (g : Grammar) (c : Classification) :
    typeNameErrors g c = [] ↔ ((knownTypes c).map (·.name)).Nodup := by
  rw [← indexed_take_nodup]
  simp only [typeNameErrors, List.flatMap_eq_nil_iff, Prod.forall]
  apply forall_congr'; intro k; apply forall_congr'; intro d; apply imp_congr_right; intro _
  cases h : (List.filter (fun e => e.name == d.name) (List.take k (knownTypes c))) with
  | nil =>
    simp only [List.filter_eq_nil_iff, beq_iff_eq] at h
    simp only [List.mem_map, not_exists, not_and, true_iff]
    exact fun e he hn => h e he hn
  | cons e es =>
    have he : e ∈ List.filter (fun e => e.name == d.name) (List.take k (knownTypes c)) := by rw [h]; simp
    simp only [List.mem_filter, beq_iff_eq] at he
    simp only [List.cons_ne_nil, false_iff]
    intro hn
    exact hn (List.mem_map.2 ⟨e, he.1, he.2⟩)

theorem insertFirst_keys (seen : List (String × String)) (n v : String) (h : n ∉ seen.map Prod.fst) :
    (insertFirst seen n v).map Prod.fst = seen.map Prod.fst ++ [n] := by
  simp [insertFirst, h]

theorem ownerClash_nil (owners : List (String × String)) (d : DataType) (k : Constructor) :
    ownerClash owners d k = [] ↔ ∀ owner, lookupFirst owners k.name = some owner → owner = d.rule := by
  unfold ownerClash
  cases lookupFirst owners k.name with
  | none => simp
  | some o => by_cases ho : o = d.rule <;> simp [ho]

theorem clashAgain_some {owners seen : List (String × String)} {d : DataType} {k : Constructor} {o : String}
    (h : lookupFirst seen k.name = some o) : clashAgain owners seen d k ≠ [] := by
  unfold clashAgain
  simp only [h]
  split <;> simp

theorem clashAgain_none {owners seen : List (String × String)} {d : DataType} {k : Constructor}
    (h : lookupFirst seen k.name = none) : clashAgain owners seen d k = ownerClash owners d k := by
  unfold clashAgain
  rw [h]

-- The constructors clash exactly when two have the same name, or one has
-- the name of the type of another rule.
theorem clashes_nil (owners : List (String × String)) :
    ∀ (seen : List (String × String)) (cs : List (DataType × Constructor)),
      clashes owners seen cs = [] ↔
        (cs.map (·.2.name)).Nodup ∧
        ∀ x ∈ cs, x.2.name ∉ seen.map Prod.fst ∧ ∀ owner, lookupFirst owners x.2.name = some owner → owner = x.1.rule
  | seen, [] => by simp [clashes]
  | seen, (d, k) :: rest => by
    rw [clashes, List.append_eq_nil_iff]
    cases hs : lookupFirst seen k.name with
    | some owner =>
      have hm : k.name ∈ seen.map Prod.fst := Decidable.byContradiction fun hn => by
        rw [(lookupFirst_none seen k.name).2 hn] at hs; cases hs
      constructor
      · rintro ⟨h, _⟩; exact absurd h (clashAgain_some hs)
      · rintro ⟨_, h⟩; exact absurd hm (h (d, k) (by simp)).1
    | none =>
      have hn := (lookupFirst_none seen k.name).1 hs
      rw [clashAgain_none hs, ownerClash_nil, clashes_nil owners (insertFirst seen k.name d.rule) rest,
        insertFirst_keys seen _ _ hn]
      simp only [List.map_cons, List.nodup_cons, List.forall_mem_cons, List.mem_append,
        List.mem_singleton, not_or]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨?_, h2⟩, ⟨hn, h1⟩, fun x hx => ⟨(h3 x hx).1.1, (h3 x hx).2⟩⟩
        intro hm
        simp only [List.mem_map] at hm
        obtain ⟨x, hx, hxn⟩ := hm
        exact (h3 x hx).1.2 hxn
      · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩, h4⟩
        refine ⟨h3, h2, fun x hx => ⟨⟨(h4 x hx).1, ?_⟩, (h4 x hx).2⟩⟩
        intro he
        exact h1 (List.mem_map.2 ⟨x, hx, he⟩)

theorem constructorErrors_nil (g : Grammar) (c : Classification) (isUpper : Char → Bool) :
    constructorErrors g c isUpper = [] ↔
      misplacedErrors g c = [] ∧ lowerErrors g c isUpper = [] ∧ ((knownTypes c).map (·.name)).Nodup ∧
        ((constructorList c).map (·.2.name)).Nodup ∧
        ∀ x ∈ constructorList c, ∀ owner, lookupFirst (typeOwners c) x.2.name = some owner → owner = x.1.rule := by
  rw [constructorErrors, List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff,
    typeNameErrors_nil, clashes_nil]
  simp [and_assoc]

/-! ### Names in the syntax tree -/

theorem syntaxNameGo_nil (o : Oracle) :
    ∀ (seen : List (String × String)) (rs : List Rule),
      syntaxNameGo o seen rs = [] ↔
        (rs.map (syntaxTypeName o ·.name)).Nodup ∧ ∀ r ∈ rs, syntaxTypeName o r.name ∉ seen.map Prod.fst
  | seen, [] => by simp [syntaxNameGo]
  | seen, r :: rs => by
    rw [syntaxNameGo]
    cases hs : lookupFirst seen (syntaxTypeName o r.name) with
    | some e =>
      have hm : syntaxTypeName o r.name ∈ seen.map Prod.fst := Decidable.byContradiction fun hn => by
        rw [(lookupFirst_none seen _).2 hn] at hs; cases hs
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ h
      exact h r (by simp) hm
    | none =>
      have hn := (lookupFirst_none seen _).1 hs
      simp only
      rw [syntaxNameGo_nil o (seen ++ [(syntaxTypeName o r.name, r.name)]) rs]
      simp only [List.map_cons, List.nodup_cons, List.forall_mem_cons, List.map_append, List.mem_append,
        List.map_cons, List.map_nil, List.mem_singleton, not_or]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, h1⟩, hn, fun x hx => (h2 x hx).1⟩
        intro hm
        simp only [List.mem_map] at hm
        obtain ⟨x, hx, hxn⟩ := hm
        exact (h2 x hx).2 hxn
      · rintro ⟨⟨h1, h2⟩, _, h3⟩
        refine ⟨h2, fun x hx => ⟨h3 x hx, fun he => h1 (List.mem_map.2 ⟨x, hx, he⟩)⟩⟩

-- With %syntax, the rules that have nodes have distinct type names.
theorem syntaxNameErrors_nil (g : Grammar) (o : Oracle) :
    syntaxNameErrors g o = [] ↔
      g.syntaxLoc = none ∨
        ((g.rules.filter (fun r => !((g.tokens ++ g.inline).map Prod.snd).contains r.name)).map
          (syntaxTypeName o ·.name)).Nodup := by
  unfold syntaxNameErrors
  split
  · simp_all
  · rename_i hs
    rw [syntaxNameGo_nil]
    simp [hs]

/-! ### Hygiene -/

theorem lineErrors_nil (f ln : Nat) (line : String) :
    lineErrors f ln line = [] ↔
      (∀ n, definedName line = some n → atColumnOne line = true → reservedName n = false) ∧
        ∀ a ∈ aliases line, a ≠ "PegRt" ∧ a ≠ "PegPrelude" := by
  unfold lineErrors
  rw [List.append_eq_nil_iff]
  apply and_congr
  · cases definedName line with
    | none => simp
    | some n =>
      by_cases h1 : atColumnOne line <;> by_cases h2 : reservedName n <;> simp [h1, h2]
  · simp only [List.flatMap_eq_nil_iff]
    apply forall_congr'; intro a; apply imp_congr_right; intro _
    by_cases h1 : a = "PegRt" <;> by_cases h2 : a = "PegPrelude" <;> simp [h1, h2]

theorem hygieneErrors_nil (v : Loc × String) :
    hygieneErrors v = [] ↔ ∀ ln line, (ln, line) ∈ indexed v.1.line (linesOf v.2) → lineErrors v.1.file ln line = [] := by
  simp [hygieneErrors, List.flatMap_eq_nil_iff]

end PegHs.CheckGroups
