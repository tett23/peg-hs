import PublicGeneration

/-!
The premises of PublicGeneration can be met (ADR 0097): `modelInputs`
builds, from any `Inputs`, inputs whose `Premises` hold
(`modelInputs_premises`), so the theorems that take `Premises` are not
vacuous. PublicPremisesMeta applies them to the two metagrammars.

- `expandRefines`: `modelExpand` is the model itself. It takes the result of
  TemplateExpansionWhole.ExpandTemplates on the template view (which exists
  and is unique, `expandTemplates_whole`) and lifts an expanded grammar back
  to `Grammar` with `lift`, a right inverse of `toTemplate` on the grammars
  whose start directive is that of the input (`toTemplate_lift`). The model
  keeps the start directive (`expandTemplates_start`).

This is a witness, not the Haskell function: the Haskell `expandTemplates`
is tied to the model by the probe that the module header of PublicGeneration
names. `assemble` is translated (AssembleTranslated), and no premise ties it
to its model (AssembleTranslatedProof.assemble_agrees).
-/

namespace PegHs.PublicGeneration

open PegHs.LabelCheck (Loc Expr Item)

/-! ## A right inverse of the template view -/

def unloc (n : Nat) : Loc := ⟨0, 0, n⟩

theorem locNat_unloc (n : Nat) : locNat (unloc n) = n := by
  simp [locNat, unloc]

def unlocated (p : Nat × String) : Loc × String := (unloc p.1, p.2)

theorem located_unlocated (p : Nat × String) : located (unlocated p) = p := by
  simp [located, unlocated, locNat_unloc]

mutual
def exprF : TemplateSubstitution.Expr → Expr
  | .lit t w => .lit t w
  | .charClass w => .cls [] w
  | .any => .any
  | .ref l n args => .ref (unloc l) n (args.map fun a => (unloc 0, a))
  | .group alts => .group (altsF alts)
  | .star x => .star (exprF x)
  | .plus x => .plus (exprF x)
  | .opt x => .opt (exprF x)
  | .and x => .and (exprF x)
  | .not x => .not (exprF x)
  | .capture x => .capture (exprF x)
  | .label l x n => .label (unloc l) (exprF x) n
  | .predicate b c => .pred b (unloc 0, c)
  | .template l n as vs => .template (unloc l) n (listF as) (vs.map fun v => (unloc 0, v))
  | .discard x => .discard (exprF x)

def itemsF : List (Option String × TemplateSubstitution.Expr) → List Item
  | [] => []
  | (b, e) :: is => (unloc 0, b, exprF e) :: itemsF is

def altsF : List (List (Option String × TemplateSubstitution.Expr)) → List (List Item)
  | [] => []
  | a :: as => itemsF a :: altsF as

def listF : List TemplateSubstitution.Expr → List Expr
  | [] => []
  | e :: es => exprF e :: listF es
end

mutual
theorem exprT_exprF : ∀ e, exprT (exprF e) = e
  | .lit t w => by simp [exprF, exprT]
  | .charClass w => by simp [exprF, exprT]
  | .any => by simp [exprF, exprT]
  | .ref l n args => by simp [exprF, exprT, locNat_unloc, Function.comp_def]
  | .group alts => by simp [exprF, exprT, altsT_altsF alts]
  | .star x => by simp [exprF, exprT, exprT_exprF x]
  | .plus x => by simp [exprF, exprT, exprT_exprF x]
  | .opt x => by simp [exprF, exprT, exprT_exprF x]
  | .and x => by simp [exprF, exprT, exprT_exprF x]
  | .not x => by simp [exprF, exprT, exprT_exprF x]
  | .capture x => by simp [exprF, exprT, exprT_exprF x]
  | .label l x n => by simp [exprF, exprT, exprT_exprF x, locNat_unloc]
  | .predicate b c => by simp [exprF, exprT]
  | .template l n as vs => by
    simp [exprF, exprT, listT_listF as, locNat_unloc, Function.comp_def]
  | .discard x => by simp [exprF, exprT, exprT_exprF x]

theorem itemsT_itemsF : ∀ is, itemsT (itemsF is) = is
  | [] => by simp [itemsF, itemsT]
  | (b, e) :: is => by simp [itemsF, itemsT, exprT_exprF e, itemsT_itemsF is]

theorem altsT_altsF : ∀ as, altsT (altsF as) = as
  | [] => by simp [altsF, altsT]
  | a :: as => by simp [altsF, altsT, itemsT_itemsF a, altsT_altsF as]

theorem listT_listF : ∀ es, listT (listF es) = es
  | [] => by simp [listF, listT]
  | e :: es => by simp [listF, listT, exprT_exprF e, listT_listF es]
end

def Rule.lift (r : TemplateExpansionWhole.Rule) : Rule where
  name := r.name
  loc := unloc r.location
  params := r.params
  templateParams := r.templateParams
  type := r.type
  annotation := r.annotation.map unloc
  alts := r.alts.map fun a =>
    { loc := unloc 0, items := itemsF a.items, action := a.action.map fun c => (unloc 0, c),
      constructor := a.constructor.map fun c => (unloc 0, c) }

theorem Rule.toTemplate_lift (r : TemplateExpansionWhole.Rule) : (Rule.lift r).toTemplate = r := by
  simp only [Rule.lift, Rule.toTemplate, List.map_map, Function.comp_def, itemsT_itemsF,
    locNat_unloc, Option.map_map]
  simp

-- `g` supplies the fields that the template view drops, and the start
-- directive, which the view writes as a list of at most one entry.
def lift (g : Grammar) (t : TemplateExpansionWhole.Grammar) : Grammar :=
  { g with
    entries := t.entries.map unlocated
    noMemo := t.nomemo.map unlocated
    syntaxLoc := if t.syntaxMode then some (unloc 0) else none
    tokens := t.tokens.map unlocated
    trivia := t.trivia.map unlocated
    inline := t.inline.map unlocated
    recovers := t.recovers.map fun p => ((unloc 0, ""), unlocated p)
    expects := t.expects.map fun p => (unlocated p, (unloc 0, ""))
    rules := t.rules.map Rule.lift }

theorem toTemplate_lift (g : Grammar) (t : TemplateExpansionWhole.Grammar)
    (start : t.start = (toTemplate g).start) : toTemplate (lift g t) = t := by
  cases t
  simp only [toTemplate] at start
  simp only [toTemplate, lift, List.map_map, Function.comp_def, located_unlocated,
    Rule.toTemplate_lift, start]
  simp only [List.map_id']
  cases (by assumption : Bool) <;> simp

/-! ## The model keeps the start directive -/

theorem expandOnce_start {env : TemplateExpansionWhole.Env} {known : TemplateExpansionWhole.Known}
    {g g' : TemplateExpansionWhole.Grammar} (h : TemplateExpansionWhole.ExpandOnce env known g (.ok g')) :
    g'.start = g.start := by
  cases h with
  | plain => rfl
  | expanded => rfl

theorem go_start {env : TemplateExpansionWhole.Env}
    {classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known}
    {g : TemplateExpansionWhole.Grammar} {k : Nat} {known : TemplateExpansionWhole.Known}
    {r : Except (List TemplateSubstitution.Diagnostic) TemplateExpansionWhole.Grammar}
    (h : TemplateExpansionWhole.Go env classify g k known r) :
    ∀ g', r = .ok g' → g'.start = g.start := by
  induction h with
  | error => intro _ h; cases h
  | stop once _ => intro _ h; cases h; exact expandOnce_start once
  | next _ _ _ ih => exact ih

theorem expandTemplates_start {env : TemplateExpansionWhole.Env}
    {classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known}
    {g g' : TemplateExpansionWhole.Grammar}
    (h : TemplateExpansionWhole.ExpandTemplates env classify g (.ok g')) : g'.start = g.start := by
  cases h with
  | plain => rfl
  | passes _ go => exact go_start go g' rfl

/-! ## Inputs that meet the premises -/

noncomputable def modelResult (env : TemplateExpansionWhole.Env)
    (classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known) (g : Grammar) :
    Except (List TemplateSubstitution.Diagnostic) TemplateExpansionWhole.Grammar :=
  Classical.choose (TemplateExpansionWhole.expandTemplates_whole env classify (toTemplate g)).1

noncomputable def modelExpand (env : TemplateExpansionWhole.Env)
    (classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known)
    (templateDiag : TemplateSubstitution.Diagnostic → String) (g : Grammar) :
    Except Diagnostics Grammar :=
  match modelResult env classify g with
  | .error ds => .error (ds.map templateDiag)
  | .ok t => .ok (lift g t)

noncomputable def modelInputs {T : Type} (s : Inputs T) : Inputs T :=
  { s with expand := modelExpand s.env s.classify s.templateDiag }

theorem modelExpand_refines (env : TemplateExpansionWhole.Env)
    (classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known)
    (templateDiag : TemplateSubstitution.Diagnostic → String) (g : Grammar) :
    ∃ r, TemplateExpansionWhole.ExpandTemplates env classify (toTemplate g) r ∧
      (match r, modelExpand env classify templateDiag g with
        | .error ds, .error es => es = ds.map templateDiag
        | .ok g', .ok h => toTemplate h = g'
        | _, _ => False) := by
  have spec : TemplateExpansionWhole.ExpandTemplates env classify (toTemplate g)
      (modelResult env classify g) :=
    Classical.choose_spec (TemplateExpansionWhole.expandTemplates_whole env classify (toTemplate g)).1
  refine ⟨modelResult env classify g, spec, ?_⟩
  unfold modelExpand
  generalize modelResult env classify g = r at spec ⊢
  cases r with
  | error ds => rfl
  | ok t => exact toTemplate_lift g t (expandTemplates_start spec)

theorem modelInputs_expand {T : Type} (s : Inputs T) :
    (modelInputs s).expand = modelExpand s.env s.classify s.templateDiag := by
  simp only [modelInputs]

theorem modelInputs_env {T : Type} (s : Inputs T) : (modelInputs s).env = s.env := by
  simp only [modelInputs]
theorem modelInputs_classify {T : Type} (s : Inputs T) : (modelInputs s).classify = s.classify := by
  simp only [modelInputs]
theorem modelInputs_templateDiag {T : Type} (s : Inputs T) :
    (modelInputs s).templateDiag = s.templateDiag := by
  simp only [modelInputs]

theorem modelInputs_premises {T : Type} (s : Inputs T) : Premises (modelInputs s) := by
  constructor
  · intro g
    obtain ⟨r, hx, hr⟩ := modelExpand_refines s.env s.classify s.templateDiag g
    rw [modelInputs_env, modelInputs_classify]
    refine ⟨r, hx, ?_⟩
    rw [modelInputs_expand]
    revert hr
    generalize modelExpand s.env s.classify s.templateDiag g = e
    intro hr
    cases r <;> cases e <;> simp only [Refines, modelInputs_templateDiag] at hr ⊢ <;> exact hr

end PegHs.PublicGeneration

#print axioms PegHs.PublicGeneration.toTemplate_lift
#print axioms PegHs.PublicGeneration.expandTemplates_start
#print axioms PegHs.PublicGeneration.modelInputs_premises
