import TemplateBindingsProof

namespace PegHs.TemplateGuardProof
open TemplatesTranslated TemplateSubstitutionBridge TemplateBindingsProof

def pLocated (x : Located String) : TemplateLocation.Location × String := (pLoc x.locOf, x.unLoc)

def pGrammar (g : Grammar) : TemplateExpansionWhole.Grammar where
  rules := g.grammarRules.map pRule
  start := g.grammarStart.toList.map pLocated
  entries := g.grammarEntries.map pLocated
  recovers := g.grammarRecovers.map (fun x => pLocated x.1)
  nomemo := g.grammarNoMemo.map pLocated
  tokens := g.grammarTokens.map pLocated
  trivia := g.grammarTrivia.map pLocated
  inline := g.grammarInline.map pLocated
  expects := g.grammarExpects.map (fun x => pLocated x.1)
  syntaxMode := HsMaybe.isJust g.grammarSyntax

theorem any_congr_mem {α : Type} (xs : List α) (f g : α → Bool)
    (same : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [same x (by simp)]
    congr 1
    exact ih (fun y member => same y (by simp [member]))

theorem callsItems_any (items : List TemplateExpansionWhole.Item) :
    TemplateExpansionWhole.callsTemplateItems items = items.any (fun item => TemplateExpansionWhole.callsTemplateExpr item.2) := by
  induction items with
  | nil => rfl
  | cons i items ih => cases i; simp [TemplateExpansionWhole.callsTemplateItems, ih]

theorem callsAlts_any (alts : List (List TemplateExpansionWhole.Item)) :
    TemplateExpansionWhole.callsTemplateAlts alts = alts.any (fun items => items.any (fun item => TemplateExpansionWhole.callsTemplateExpr item.2)) := by
  induction alts with
  | nil => rfl
  | cons items alts ih => simp [TemplateExpansionWhole.callsTemplateAlts, callsItems_any, ih]

theorem root_adr0097_i2_template_call_expr_refines (e : Expr) :
    callsTemplate.expr_478 e = TemplateExpansionWhole.callsTemplateExpr (pExpr e) := by
  refine (measure (fun x : Expr => sizeOf x)).wf.induction
    (C := fun e => callsTemplate.expr_478 e = TemplateExpansionWhole.callsTemplateExpr (pExpr e)) e ?_
  intro e ih
  cases e <;> simp only [callsTemplate.expr_478, pExpr, TemplateExpansionWhole.callsTemplateExpr]
  all_goals first
    | rfl
    | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
    | skip
  case EGroup alts =>
    simp only [callsAlts_any, pAlts_map, List.any_map, HsList.any]
    apply any_congr_mem
    intro items outer
    simp only [Function.comp_def, pItems_map, List.any_map]
    apply any_congr_mem
    intro item inner
    exact ih item.itemExpr (by
      have a := List.sizeOf_lt_of_mem outer
      have b := List.sizeOf_lt_of_mem inner
      have c := Item.itemExpr_sizeOf item
      change sizeOf item.itemExpr < sizeOf (Expr.EGroup alts)
      simp
      omega)

theorem root_adr0097_i2_template_call_rule_refines (r : Rule) :
    callsTemplate r = TemplateExpansionWhole.callsTemplate (pRule r) := by
  simp only [callsTemplate, TemplateExpansionWhole.callsTemplate, pRule, List.any_map, HsList.any, callsItems_any]
  apply any_congr_mem
  intro alt member
  simp only [Function.comp_def, pAlt, pItems_map, List.any_map]
  apply any_congr_mem
  intro item member
  exact root_adr0097_i2_template_call_expr_refines item.itemExpr

def sourcePlain (g : Grammar) : Bool :=
  HsBase.and (HsBase.not (HsList.any (fun r => HsBase.not (HsList.null r.ruleTemplateParams)) g.grammarRules))
    (HsBase.not (HsList.any callsTemplate g.grammarRules))

theorem root_adr0097_i2_plain_guard_refines (g : Grammar) :
    sourcePlain g = TemplateExpansionWhole.plainGrammar (pGrammar g) := by
  simp only [sourcePlain, TemplateExpansionWhole.plainGrammar, pGrammar, List.any_map, HsList.any, HsBase.and, HsBase.not]
  congr 2
  · apply any_congr_mem
    intro rule member
    simp [TemplateExpansionWhole.isTemplate, pRule, HsList.null]
  · apply any_congr_mem
    intro rule member
    exact root_adr0097_i2_template_call_rule_refines rule

theorem root_adr0097_i2_plain_expansion (fuel : Nat) (g : Grammar)
    (plain : TemplateExpansionWhole.plainGrammar (pGrammar g) = true) : expandTemplates fuel g = .ok g := by
  have source : sourcePlain g = true := by rw [root_adr0097_i2_plain_guard_refines]; exact plain
  rw [expandTemplates]
  unfold sourcePlain at source
  simp only [source, ite_true]

theorem root_adr0097_i2_plain_refines (fuel : Nat) (g : Grammar)
    (env : TemplateExpansionWhole.Env) (classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known)
    (plain : TemplateExpansionWhole.plainGrammar (pGrammar g) = true) :
    expandTemplates fuel g = .ok g ∧
      TemplateExpansionWhole.ExpandTemplates env classify (pGrammar g) (.ok (pGrammar g)) :=
  ⟨root_adr0097_i2_plain_expansion fuel g plain, .plain plain⟩

#print axioms root_adr0097_i2_template_call_expr_refines
#print axioms root_adr0097_i2_template_call_rule_refines
#print axioms root_adr0097_i2_plain_guard_refines
#print axioms root_adr0097_i2_plain_expansion
#print axioms root_adr0097_i2_plain_refines
end PegHs.TemplateGuardProof
