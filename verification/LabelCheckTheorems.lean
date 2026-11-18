import LabelCheckTermination

/-!
What `stripLabels`, `stripLabelsAs` and `labelWarnings` of
packages/peg-grammar/src/Peg/Grammar/Labels.hs do, on the model of
LabelCheckModel (tied to the source by check-label-check.sh), with the total
`labelWarnings` of LabelCheckTermination.

Removing labels (ADR 0029, ADR 0038, ADR 0089):
- `unlabelExpr_stripExpr`, `hasLabel_stripExpr`, `stripExpr_eq_unlabelExpr`:
  `stripExpr` removes exactly the label annotations. "Unchanged" means: after
  erasing every label, the result is the input (`unlabelExpr (stripExpr e) =
  unlabelExpr e`), and no label remains outside the arguments of template
  calls. `stripExpr` does not enter template arguments; on a grammar without
  template calls, which is what `expandTemplates` returns
  (TemplateExpansionWhole), it removes every label.
- `stripLabels_rules`: every rule keeps its name, parameters and other fields,
  every alternative its location and other fields, every item its location
  and binding; only the expressions change, by `stripExpr`.
- `stripLabels_fields`, `recoveryEntries_spec`: `%recover`, `%safe` and
  `%message` become empty, `%expect` and the other fields stay, and the
  entries gain each recovery rule that is not already the start rule or an
  entry, once (ADR 0038). `stripLabelsAs_fields`: the module name changes and
  keeps its location.

The warnings (ADR 0028, ADR 0029, ADR 0087, ADR 0088):
- `sites_labels`: the check judges every label of a rule once, in order.
- `mem_labelWarnings`: a warning is exactly a label whose name is not in
  `%safe` and whose verdict is not `safe`. It is located at the item that
  holds the labelled expression, and its message is `the label NAME may reject
  valid input: where it fails, ...` or `the label NAME cannot be checked: ...`.
  `labelWarnings_eq_nil_iff` states the case of no warning.
- `verdict_ignores_other_labels`, `unlabelGrammar_noLabel`,
  `unlabelFrames_noLabel`, `unlabelGrammar_fields`: each label is judged on
  the grammar and the frames without any label, with %recover, the entries
  and the start rule kept (ADR 0087); so two grammars that differ only in
  labels give a label the same verdict (ADR 0029, ADR 0088).
- `verdict_in_lookahead`, `verdict_unchecked_growing`, `ruleFailed_recovery`,
  `ruleSucceeded_recovery`, `ruleSucceeded_entry`, `succeeded_in_lookahead`:
  the cases of ADR 0028 decided at a step: a failure inside a lookahead is
  an ordinary failure; a label in a growing alternative of a rule in indirect
  or hidden left recursion cannot be checked; a failure or success that leaves
  a recovery rule stops there; the input may end after an entry; a lookahead
  around a label decides the other way.

Rejection (ADR 0097 invariant 2):
- `werror_rejects_iff`, `labels_reject_with_diagnostic`: labels make
  `peg-hs gen` fail only with `--Werror`, and then there is at least one
  warning. check-label-check.sh fixes the source of `generateWithWarnings`
  and of the `--Werror` test in peg-cli.

Premises: those of LabelCheckModel.
-/

namespace PegHs.LabelCheck

/-! ## Labels in expressions -/

mutual
-- Whether a label occurs anywhere in an expression, template arguments included.
def hasLabel : Expr → Bool
  | .label .. => true
  | .group alts => altsHasLabel alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => hasLabel x
  | .template _ _ as _ => listHasLabel as
  | _ => false
termination_by e => sizeOf e

def itemsHasLabel : List Item → Bool
  | [] => false
  | (_, _, e) :: is => hasLabel e || itemsHasLabel is
termination_by is => sizeOf is

def altsHasLabel : List (List Item) → Bool
  | [] => false
  | a :: as => itemsHasLabel a || altsHasLabel as
termination_by as => sizeOf as

def listHasLabel : List Expr → Bool
  | [] => false
  | e :: es => hasLabel e || listHasLabel es
termination_by es => sizeOf es
end

mutual
def hasTemplate : Expr → Bool
  | .template .. => true
  | .group alts => altsHasTemplate alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => hasTemplate x
  | .label _ x _ => hasTemplate x
  | _ => false
termination_by e => sizeOf e

def itemsHasTemplate : List Item → Bool
  | [] => false
  | (_, _, e) :: is => hasTemplate e || itemsHasTemplate is
termination_by is => sizeOf is

def altsHasTemplate : List (List Item) → Bool
  | [] => false
  | a :: as => itemsHasTemplate a || altsHasTemplate as
termination_by as => sizeOf as
end

mutual
theorem hasLabel_unlabelExpr : (e : Expr) → hasLabel (unlabelExpr e) = false
  | .label _ x _ => by rw [unlabelExpr]; exact hasLabel_unlabelExpr x
  | .group alts => by rw [unlabelExpr, hasLabel]; exact altsHasLabel_unlabelAlts alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => by
    rw [unlabelExpr, hasLabel]; exact hasLabel_unlabelExpr x
  | .template _ _ as _ => by rw [unlabelExpr, hasLabel]; exact listHasLabel_unlabelList as
  | .lit .. | .cls .. | .any | .ref .. | .pred .. => by simp [unlabelExpr, hasLabel]
termination_by e => sizeOf e

theorem itemsHasLabel_unlabelItems : (is : List Item) → itemsHasLabel (unlabelItems is) = false
  | [] => by rw [unlabelItems, itemsHasLabel]
  | (_, _, e) :: is => by
    rw [unlabelItems, itemsHasLabel, hasLabel_unlabelExpr e, itemsHasLabel_unlabelItems is]; rfl
termination_by is => sizeOf is

theorem altsHasLabel_unlabelAlts : (as : List (List Item)) → altsHasLabel (unlabelAlts as) = false
  | [] => by rw [unlabelAlts, altsHasLabel]
  | a :: as => by
    rw [unlabelAlts, altsHasLabel, itemsHasLabel_unlabelItems a, altsHasLabel_unlabelAlts as]; rfl
termination_by as => sizeOf as

theorem listHasLabel_unlabelList : (es : List Expr) → listHasLabel (unlabelList es) = false
  | [] => by rw [unlabelList, listHasLabel]
  | e :: es => by
    rw [unlabelList, listHasLabel, hasLabel_unlabelExpr e, listHasLabel_unlabelList es]; rfl
termination_by es => sizeOf es
end

mutual
theorem unlabelExpr_of_noLabel : (e : Expr) → hasLabel e = false → unlabelExpr e = e
  | .label .., h => by simp [hasLabel] at h
  | .group alts, h => by
    rw [hasLabel] at h; rw [unlabelExpr, unlabelAlts_of_noLabel alts h]
  | .star x, h | .plus x, h | .opt x, h | .and x, h | .not x, h | .capture x, h | .discard x, h => by
    rw [hasLabel] at h; rw [unlabelExpr, unlabelExpr_of_noLabel x h]
  | .template _ _ as _, h => by
    rw [hasLabel] at h; rw [unlabelExpr, unlabelList_of_noLabel as h]
  | .lit .., _ | .cls .., _ | .any, _ | .ref .., _ | .pred .., _ => by simp [unlabelExpr]
termination_by e => sizeOf e

theorem unlabelItems_of_noLabel : (is : List Item) → itemsHasLabel is = false → unlabelItems is = is
  | [], _ => by rw [unlabelItems]
  | (_, _, e) :: is, h => by
    rw [itemsHasLabel, Bool.or_eq_false_iff] at h
    rw [unlabelItems, unlabelExpr_of_noLabel e h.1, unlabelItems_of_noLabel is h.2]
termination_by is => sizeOf is

theorem unlabelAlts_of_noLabel : (as : List (List Item)) → altsHasLabel as = false → unlabelAlts as = as
  | [], _ => by rw [unlabelAlts]
  | a :: as, h => by
    rw [altsHasLabel, Bool.or_eq_false_iff] at h
    rw [unlabelAlts, unlabelItems_of_noLabel a h.1, unlabelAlts_of_noLabel as h.2]
termination_by as => sizeOf as

theorem unlabelList_of_noLabel : (es : List Expr) → listHasLabel es = false → unlabelList es = es
  | [], _ => by rw [unlabelList]
  | e :: es, h => by
    rw [listHasLabel, Bool.or_eq_false_iff] at h
    rw [unlabelList, unlabelExpr_of_noLabel e h.1, unlabelList_of_noLabel es h.2]
termination_by es => sizeOf es
end

/-- Erasing labels twice is erasing them once. -/
theorem unlabelExpr_idem (e : Expr) : unlabelExpr (unlabelExpr e) = unlabelExpr e :=
  unlabelExpr_of_noLabel _ (hasLabel_unlabelExpr e)

mutual
/-- After erasing every label, the stripped expression is the expression. -/
theorem unlabelExpr_stripExpr : (e : Expr) → unlabelExpr (stripExpr e) = unlabelExpr e
  | .label _ x _ => by
    rw [stripExpr, unlabelExpr_stripExpr x]
    conv => rhs; rw [unlabelExpr]
  | .group alts => by rw [stripExpr, unlabelExpr, unlabelExpr, unlabelAlts_stripAlts alts]
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => by
    rw [stripExpr, unlabelExpr, unlabelExpr, unlabelExpr_stripExpr x]
  | .template .. | .lit .. | .cls .. | .any | .ref .. | .pred .. => by simp [stripExpr]
termination_by e => sizeOf e

theorem unlabelItems_stripItems : (is : List Item) → unlabelItems (stripItems is) = unlabelItems is
  | [] => by rw [stripItems]
  | (_, _, e) :: is => by
    rw [stripItems, unlabelItems, unlabelItems, unlabelExpr_stripExpr e, unlabelItems_stripItems is]
termination_by is => sizeOf is

theorem unlabelAlts_stripAlts : (as : List (List Item)) → unlabelAlts (stripAlts as) = unlabelAlts as
  | [] => by rw [stripAlts]
  | a :: as => by
    rw [stripAlts, unlabelAlts, unlabelAlts, unlabelItems_stripItems a, unlabelAlts_stripAlts as]
termination_by as => sizeOf as
end

mutual
/-- Without template calls, stripping is erasing every label. -/
theorem stripExpr_eq_unlabelExpr : (e : Expr) → hasTemplate e = false → stripExpr e = unlabelExpr e
  | .label _ x _, h => by
    rw [hasTemplate] at h; rw [stripExpr, unlabelExpr, stripExpr_eq_unlabelExpr x h]
  | .group alts, h => by
    rw [hasTemplate] at h; rw [stripExpr, unlabelExpr, stripAlts_eq_unlabelAlts alts h]
  | .star x, h | .plus x, h | .opt x, h | .and x, h | .not x, h | .capture x, h | .discard x, h => by
    rw [hasTemplate] at h; rw [stripExpr, unlabelExpr, stripExpr_eq_unlabelExpr x h]
  | .template .., h => by simp [hasTemplate] at h
  | .lit .., _ | .cls .., _ | .any, _ | .ref .., _ | .pred .., _ => by simp [stripExpr, unlabelExpr]
termination_by e => sizeOf e

theorem stripItems_eq_unlabelItems : (is : List Item) → itemsHasTemplate is = false →
    stripItems is = unlabelItems is
  | [], _ => by rw [stripItems, unlabelItems]
  | (_, _, e) :: is, h => by
    rw [itemsHasTemplate, Bool.or_eq_false_iff] at h
    rw [stripItems, unlabelItems, stripExpr_eq_unlabelExpr e h.1, stripItems_eq_unlabelItems is h.2]
termination_by is => sizeOf is

theorem stripAlts_eq_unlabelAlts : (as : List (List Item)) → altsHasTemplate as = false →
    stripAlts as = unlabelAlts as
  | [], _ => by rw [stripAlts, unlabelAlts]
  | a :: as, h => by
    rw [altsHasTemplate, Bool.or_eq_false_iff] at h
    rw [stripAlts, unlabelAlts, stripItems_eq_unlabelItems a h.1, stripAlts_eq_unlabelAlts as h.2]
termination_by as => sizeOf as
end

/-- Without template calls, no label is left. -/
theorem hasLabel_stripExpr (e : Expr) (h : hasTemplate e = false) : hasLabel (stripExpr e) = false := by
  rw [stripExpr_eq_unlabelExpr e h]
  exact hasLabel_unlabelExpr e

/-- An expression without labels is not changed. -/
theorem stripExpr_of_noLabel (e : Expr) (h : hasLabel e = false) (ht : hasTemplate e = false) :
    stripExpr e = e := by
  rw [stripExpr_eq_unlabelExpr e ht, unlabelExpr_of_noLabel e h]

theorem stripItems_eq_map : ∀ (is : List Item), stripItems is = is.map (fun i => (i.1, i.2.1, stripExpr i.2.2))
  | [] => by rw [stripItems]; rfl
  | (_, _, e) :: is => by rw [stripItems, stripItems_eq_map is]; rfl

theorem unlabelItems_eq_map : ∀ (is : List Item),
    unlabelItems is = is.map (fun i => (i.1, i.2.1, unlabelExpr i.2.2))
  | [] => by rw [unlabelItems]; rfl
  | (_, _, e) :: is => by rw [unlabelItems, unlabelItems_eq_map is]; rfl

/-! ## stripLabels -/

/-- The rules of the stripped grammar: the same rules, alternatives and items, in the same
order, with the same names, parameters, locations, bindings and other fields; each item's
expression is stripped. -/
theorem stripLabels_rules (g : Grammar) :
    (stripLabels g).rules = g.rules.map (fun r => { r with alts := r.alts.map (fun a =>
      { a with items := a.items.map (fun i => (i.1, i.2.1, stripExpr i.2.2)) }) }) := by
  simp only [stripLabels, stripItems_eq_map]

/-- After erasing the labels, the stripped rules are the rules. -/
theorem stripLabels_unlabel_rules (g : Grammar) :
    (unlabelGrammar (stripLabels g)).rules = (unlabelGrammar g).rules := by
  simp only [unlabelGrammar, stripLabels, List.map_map, Function.comp_def, unlabelItems_stripItems]

/-- The fields of the stripped grammar other than the rules. -/
theorem stripLabels_fields (g : Grammar) :
    (stripLabels g).recovers = [] ∧ (stripLabels g).safe = [] ∧ (stripLabels g).messages = [] ∧
    (stripLabels g).entries = g.entries ++ recoveryEntries g ∧
    (stripLabels g).module = g.module ∧ (stripLabels g).start = g.start ∧
    (stripLabels g).other = g.other := by
  simp [stripLabels]

/-- `stripLabelsAs` is `stripLabels` with the module name replaced, at the same location. -/
theorem stripLabelsAs_fields (m : String) (g : Grammar) :
    stripLabelsAs m g = { stripLabels g with module := (g.module.1, m) } := rfl

theorem recoveryGo_spec : ∀ (seen : List String) (rs : List (Loc × String)),
    (∀ r ∈ recoveryGo seen rs, r ∈ rs ∧ r.2 ∉ seen) ∧
    ((recoveryGo seen rs).map (·.2)).Nodup ∧
    (∀ r ∈ rs, r.2 ∈ seen ∨ r.2 ∈ (recoveryGo seen rs).map (·.2))
  | _, [] => by simp [recoveryGo]
  | seen, r :: rs => by
    rw [recoveryGo]
    split
    · rename_i hr
      obtain ⟨h1, h2, h3⟩ := recoveryGo_spec seen rs
      refine ⟨fun q hq => ⟨List.mem_cons_of_mem _ (h1 q hq).1, (h1 q hq).2⟩, h2, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Or.inl (by simpa using hr)
      · exact h3 q hq
    · rename_i hr
      obtain ⟨h1, h2, h3⟩ := recoveryGo_spec (r.2 :: seen) rs
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨by simp, by simpa using hr⟩
        · have := h1 q hq
          exact ⟨List.mem_cons_of_mem _ this.1, fun h => this.2 (List.mem_cons_of_mem _ h)⟩
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, h2⟩
        intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨q, hq, hqr⟩ := hmem
        exact (h1 q hq).2 (by simp [hqr])
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · right; simp
        · rcases h3 q hq with h | h
          · simp only [List.mem_cons] at h
            rcases h with h | h
            · right; simp [h]
            · exact Or.inl h
          · right; simp only [List.map_cons, List.mem_cons]; exact Or.inr h

/-- The entries that stripLabels adds (ADR 0038): recovery rules, each once, none already the
start rule or an entry, and every recovery rule is then the start rule or an entry. -/
theorem recoveryEntries_spec (g : Grammar) :
    (∀ r ∈ recoveryEntries g, r ∈ g.recovers.map (·.2) ∧ r.2 ∉ startName g :: g.entries.map (·.2)) ∧
    ((recoveryEntries g).map (·.2)).Nodup ∧
    (∀ p ∈ g.recovers, p.2.2 ∈ startName g :: (stripLabels g).entries.map (·.2)) := by
  obtain ⟨h1, h2, h3⟩ := recoveryGo_spec (startName g :: g.entries.map (·.2)) (g.recovers.map (·.2))
  refine ⟨h1, h2, ?_⟩
  intro p hp
  have := h3 p.2 (List.mem_map_of_mem hp)
  simp only [stripLabels, List.map_append, List.mem_cons, List.mem_append] at this ⊢
  rcases this with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## The labels the check judges -/

def siteLabel (s : Site) : Option String :=
  match s.expr with
  | .label _ _ n => some n
  | _ => none

mutual
-- The labels of an expression in the order of the grammar, outside template arguments.
def exprLabels : Expr → List String
  | .label _ x n => n :: exprLabels x
  | .group alts => altsLabels alts
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => exprLabels x
  | _ => []
termination_by e => sizeOf e

def itemsLabels : List Item → List String
  | [] => []
  | (_, _, e) :: is => exprLabels e ++ itemsLabels is
termination_by is => sizeOf is

def altsLabels : List (List Item) → List String
  | [] => []
  | a :: as => itemsLabels a ++ altsLabels as
termination_by as => sizeOf as
end

mutual
theorem exprSites_labels (rn : String) (fs : List Frame) (l : Loc) :
    (e : Expr) → (exprSites rn fs l e).filterMap siteLabel = exprLabels e
  | .label _ x n => by
    rw [exprSites, exprLabels]
    simp [isSite, siteLabel, exprSites_labels rn _ l x]
  | .group gs => by
    rw [exprSites, exprLabels]
    simp only [isSite, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact altSites_labels rn fs _ false 0 gs
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x => by
    rw [exprSites, exprLabels]
    simp only [isSite, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact exprSites_labels rn _ l x
  | .ref .. => by unfold exprSites exprLabels; simp [isSite, siteLabel]
  | .lit .. | .cls .. | .any | .pred .. | .template .. => by unfold exprSites exprLabels; simp [isSite]
termination_by e => sizeOf e

theorem altSites_labels (rn : String) (outer : List Frame) (galts : List (Loc × List Item)) (body : Bool) :
    (k : Nat) → (gs : List (List Item)) → (altSites rn outer galts body k gs).filterMap siteLabel = altsLabels gs
  | _, [] => by rw [altSites, altsLabels]; rfl
  | k, is :: rest => by
    rw [altSites, altsLabels, List.filterMap_append, itemSites_labels rn outer galts body k is 0 is,
      altSites_labels rn outer galts body (k + 1) rest]
termination_by _ gs => sizeOf gs

theorem itemSites_labels (rn : String) (outer : List Frame) (galts : List (Loc × List Item)) (body : Bool)
    (k : Nat) (is : List Item) :
    (j : Nat) → (items : List Item) → (itemSites rn outer galts body k is j items).filterMap siteLabel = itemsLabels items
  | _, [] => by rw [itemSites, itemsLabels]; rfl
  | j, (l, _, e) :: rest => by
    rw [itemSites, itemsLabels, List.filterMap_append, exprSites_labels rn _ l e,
      itemSites_labels rn outer galts body k is (j + 1) rest]
termination_by _ items => sizeOf items
end

/-- The check judges every label of a rule once, in the order of the grammar (labels inside
template arguments, which an expanded grammar does not have, excepted). -/
theorem sites_labels (r : Rule) :
    (sites r).filterMap siteLabel = altsLabels (r.alts.map (·.items)) :=
  altSites_labels _ _ _ _ _ _

/-! ## The warnings -/

/-- The verdict the check gives to the label at a site: on the grammar and the frames without
any label (ADR 0029, ADR 0087). -/
noncomputable def siteVerdict (keyOf : Nat → List Item → String) (g : Grammar) (s : Site) (x : Expr) : Verdict :=
  verdictOf (contextWith keyOf (unlabelGrammar g)) s.rule (unlabelFrames s.frames) (unlabelExpr x)

theorem verdictMessage_spec (name : String) (v : Verdict) (msg : String) :
    verdictMessage name v = some msg ↔
      (∃ why, v = .mayReject why ∧ msg = "the label " ++ name ++ " may reject valid input: where it fails, " ++ why) ∨
      (∃ why, v = .unchecked why ∧ msg = "the label " ++ name ++ " cannot be checked: " ++ why) := by
  cases v <;> simp [verdictMessage, eq_comm]

/-- A warning is a label of the grammar, not named in %safe, whose verdict is not `safe`; it is
located at the item that holds the labelled expression, and its message names the label and
says whether it may reject valid input or cannot be checked. -/
theorem mem_labelWarnings (keyOf : Nat → List Item → String) (g : Grammar) (d : Diagnostic) :
    d ∈ labelWarningsBy keyOf g ↔
      ∃ s ∈ g.rules.flatMap sites, ∃ l x name, s.expr = .label l x name ∧
        name ∉ g.safe.map (·.2) ∧ d.loc = s.loc ∧
        ((∃ why, siteVerdict keyOf g s x = .mayReject why ∧
            d.msg = "the label " ++ name ++ " may reject valid input: where it fails, " ++ why) ∨
         (∃ why, siteVerdict keyOf g s x = .unchecked why ∧
            d.msg = "the label " ++ name ++ " cannot be checked: " ++ why)) := by
  unfold labelWarningsBy labelWarningsWith
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, hd⟩
    refine ⟨s, hs, ?_⟩
    split at hd
    · rename_i l x name hexpr
      split at hd
      · simp at hd
      · rename_i hsafe
        obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hd
        refine ⟨l, x, name, hexpr, by simpa using hsafe, rfl, ?_⟩
        exact (verdictMessage_spec name _ msg).1 hmsg
    · simp at hd
  · rintro ⟨s, hs, l, x, name, hexpr, hsafe, hloc, hv⟩
    refine ⟨s, hs, ?_⟩
    simp only [hexpr]
    have hsafe' : ((g.safe.map (·.2)).contains name) = false := by simpa using hsafe
    simp only [hsafe', Bool.false_eq_true, ↓reduceIte]
    have := (verdictMessage_spec name (siteVerdict keyOf g s x) d.msg).2 hv
    unfold siteVerdict at this
    rw [this]
    cases d
    simp only at hloc
    simp [hloc]

/-- No warning exactly when every label not named in %safe is safe. -/
theorem labelWarnings_eq_nil_iff (keyOf : Nat → List Item → String) (g : Grammar) :
    labelWarningsBy keyOf g = [] ↔
      ∀ s ∈ g.rules.flatMap sites, ∀ l x name, s.expr = .label l x name →
        name ∉ g.safe.map (·.2) → siteVerdict keyOf g s x = .safe := by
  constructor
  · intro h s hs l x name hexpr hsafe
    cases hv : siteVerdict keyOf g s x with
    | safe => rfl
    | mayReject why =>
      have := (mem_labelWarnings keyOf g ⟨s.loc, "the label " ++ name ++ " may reject valid input: where it fails, " ++ why⟩).2
        ⟨s, hs, l, x, name, hexpr, hsafe, rfl, Or.inl ⟨why, hv, rfl⟩⟩
      rw [h] at this; simp at this
    | unchecked why =>
      have := (mem_labelWarnings keyOf g ⟨s.loc, "the label " ++ name ++ " cannot be checked: " ++ why⟩).2
        ⟨s, hs, l, x, name, hexpr, hsafe, rfl, Or.inr ⟨why, hv, rfl⟩⟩
      rw [h] at this; simp at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro d hd
    obtain ⟨s, hs, l, x, name, hexpr, hsafe, _, hv⟩ := (mem_labelWarnings keyOf g d).1 hd
    rw [h s hs l x name hexpr hsafe] at hv
    rcases hv with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> cases h1

/-! ## Other labels do not change the verdict (ADR 0029, ADR 0087, ADR 0088) -/

theorem unlabelGrammar_noLabel (g : Grammar) :
    ∀ r ∈ (unlabelGrammar g).rules, ∀ a ∈ r.alts, ∀ i ∈ a.items, hasLabel i.2.2 = false := by
  intro r hr a ha i hi
  simp only [unlabelGrammar, List.mem_map] at hr
  obtain ⟨r0, _, rfl⟩ := hr
  simp only [List.mem_map] at ha
  obtain ⟨a0, _, rfl⟩ := ha
  simp only [unlabelItems_eq_map, List.mem_map] at hi
  obtain ⟨i0, _, rfl⟩ := hi
  exact hasLabel_unlabelExpr _

/-- The grammar the check analyses keeps %recover, the entries, the start rule, %safe and the
other fields; unlike `stripLabels` it adds no entry (ADR 0087). -/
theorem unlabelGrammar_fields (g : Grammar) :
    (unlabelGrammar g).recovers = g.recovers ∧ (unlabelGrammar g).entries = g.entries ∧
    (unlabelGrammar g).start = g.start ∧ (unlabelGrammar g).safe = g.safe ∧
    (unlabelGrammar g).module = g.module ∧ (unlabelGrammar g).other = g.other ∧
    (unlabelGrammar g).rules.map (·.name) = g.rules.map (·.name) := by
  simp [unlabelGrammar, Function.comp]

/-- The frames of a label lose the frames of the labels around it, and the items they hold lose
their labels. -/
theorem unlabelFrames_noLabel (fs : List Frame) :
    ∀ f ∈ unlabelFrames fs, (match f with
      | .label => False
      | .seq items _ => ∀ i ∈ items, hasLabel i.2.2 = false
      | .alts alts _ _ => ∀ p ∈ alts, ∀ i ∈ p.2, hasLabel i.2.2 = false
      | .star x _ | .plus x _ => hasLabel x = false
      | _ => True) := by
  intro f hf
  simp only [unlabelFrames, List.mem_flatMap] at hf
  obtain ⟨f0, _, hf⟩ := hf
  cases f0 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hf <;> subst hf <;> simp only
  · intro i hi
    rw [unlabelItems_eq_map] at hi
    simp only [List.mem_map] at hi
    obtain ⟨i0, _, rfl⟩ := hi
    exact hasLabel_unlabelExpr _
  · intro p hp i hi
    simp only [List.mem_map] at hp
    obtain ⟨p0, _, rfl⟩ := hp
    rw [unlabelItems_eq_map] at hi
    simp only [List.mem_map] at hi
    obtain ⟨i0, _, rfl⟩ := hi
    exact hasLabel_unlabelExpr _
  · exact hasLabel_unlabelExpr _
  · exact hasLabel_unlabelExpr _

/-- Two grammars that are the same after erasing labels, and labels whose frames and bodies are
the same after erasing labels, get the same verdict: the other labels do not change it. -/
theorem verdict_ignores_other_labels (keyOf : Nat → List Item → String) {g1 g2 : Grammar} {s1 s2 : Site} {x1 x2 : Expr}
    (hg : unlabelGrammar g1 = unlabelGrammar g2) (hr : s1.rule = s2.rule)
    (hf : unlabelFrames s1.frames = unlabelFrames s2.frames) (hx : unlabelExpr x1 = unlabelExpr x2) :
    siteVerdict keyOf g1 s1 x1 = siteVerdict keyOf g2 s2 x2 := by
  unfold siteVerdict
  rw [hg, hr, hf, hx]

/-- Putting a label on an expression does not change the grammar the check analyses. -/
theorem unlabelExpr_label (l : Loc) (x : Expr) (n : String) : unlabelExpr (.label l x n) = unlabelExpr x := by
  rw [unlabelExpr]

/-! ## The cases of ADR 0028 -/

theorem run_one_failed (ctx : Ctx) (rule : String) (fs : List Frame) (k : CharSet) :
    (run ctx 1).failed rule fs ([], 0) k [] =
      failedBody ctx (run ctx 0) rule fs [] 0 k [failedKey ctx rule fs [] 0 k] := by
  simp [run, step, visit, truncate, maxPrefix]

/-- A label in a lookahead is safe: a throw there is a failure of the lookahead's body, as
without the label (ADR 0021, ADR 0028). -/
theorem verdict_in_lookahead {ctx : Ctx} (hp : PassWF ctx.pass) (rule : String) (l : Loc)
    (rest : List Frame) (x : Expr) :
    verdictOf ctx rule (.and l :: rest) x = .safe ∧ verdictOf ctx rule (.not l :: rest) x = .safe := by
  constructor <;> apply verdictFuel_eq hp (n := 1) <;>
    simp [verdictFuel, run_one_failed, failedBody, ret]

/-- A label in a growing alternative of a rule in indirect or hidden left recursion cannot be
checked (ADR 0028). -/
theorem verdict_unchecked_growing {ctx : Ctx} (hp : PassWF ctx.pass) {rule : String}
    {items : List Item} {j : Nat} {alts : List (Loc × List Item)} {i : Nat} {rest : List Frame}
    (hlr : ctx.otherLr.contains rule = true) (hg : ctx.growing rule i = true) (x : Expr) :
    verdictOf ctx rule (.seq items j :: .alts alts i true :: rest) x =
      .unchecked ("it is in a growing alternative of " ++ rule ++
        ", which takes part in indirect or hidden left recursion") := by
  apply verdictFuel_eq hp (n := 1)
  simp only [verdictFuel, run_one_failed, failedBody, hlr, hg, Bool.and_true, ↓reduceIte, ret,
    Option.map_some]

/-- The failure of a recovery rule's body stops there. -/
theorem ruleFailed_recovery (ctx : Ctx) (R : Rec) {rule : String} (h : ctx.recovery.contains rule = true)
    (pre : List Item) (lifts : Nat) (k : CharSet) (V : Visited) :
    ruleFailed ctx R rule pre lifts k V = some (.safe, V) := by
  simp only [ruleFailed, h, ↓reduceIte, ret]

/-- The success of a recovery rule stops there. -/
theorem ruleSucceeded_recovery (ctx : Ctx) (R : Rec) {rule : String} (h : ctx.recovery.contains rule = true)
    (k : CharSet) (V : Visited) : ruleSucceeded ctx R rule k V = some (.safe, V) := by
  simp only [ruleSucceeded, h, ↓reduceIte, ret]

/-- After an entry rule, the input may end: a label whose failure lets an entry succeed with the
end of the input next may reject valid input (ADR 0028, ADR 0038). -/
theorem ruleSucceeded_entry (ctx : Ctx) (R : Rec) {rule : String} (hr : ctx.recovery.contains rule = false)
    (he : ctx.entries.contains rule = true) {k : CharSet} (hk : k.meets endOfInput = true) (V : Visited) :
    ruleSucceeded ctx R rule k V =
      some (.mayReject ("the input can end after the rule " ++ rule ++ ", which is an entry"), V) := by
  simp only [ruleSucceeded, hr, he, hk, Bool.and_self, Bool.false_eq_true, ↓reduceIte, ret]

/-- Where the labelled expression succeeds without the label inside a lookahead, the lookahead
decides the other way (ADR 0028). -/
theorem succeeded_in_lookahead (ctx : Ctx) (R : Rec) (rule : String) (l : Loc) (rest : List Frame)
    (k : CharSet) (V : Visited) :
    succeededBody ctx R rule (.and l :: rest) k V =
      some (.mayReject ("the lookahead at " ++ showLoc l ++ " can match"), V) ∧
    succeededBody ctx R rule (.not l :: rest) k V =
      some (.mayReject ("the lookahead at " ++ showLoc l ++ " can match"), V) := by
  constructor <;> simp [succeededBody, ret]

/-! ## Rejection (ADR 0097 invariant 2) -/

/-- `peg-hs gen` fails on the warnings it receives exactly with `--Werror` and a warning
(packages/peg-cli/app/Command/Gen.hs, fixed by check-label-check.sh). -/
def werrorRejects (werror : Bool) (warnings : List Diagnostic) : Bool := werror && !warnings.isEmpty

theorem werror_rejects_iff (werror : Bool) (warnings : List Diagnostic) :
    werrorRejects werror warnings = true ↔ werror = true ∧ 1 ≤ warnings.length := by
  cases warnings <;> simp [werrorRejects]

/-- Labels make the generation fail only with `--Werror`, and then with at least one
diagnostic; with `--strip-labels` there is no warning and no such failure. -/
theorem labels_reject_with_diagnostic (keyOf : Nat → List Item → String) (g : Grammar) (werror : Bool) :
    (werrorRejects werror (labelWarningsBy keyOf g) = true → 1 ≤ (labelWarningsBy keyOf g).length) ∧
    werrorRejects false (labelWarningsBy keyOf g) = false ∧
    werrorRejects werror [] = false := by
  refine ⟨fun h => ((werror_rejects_iff _ _).1 h).2, by simp [werrorRejects], by simp [werrorRejects]⟩

end PegHs.LabelCheck
