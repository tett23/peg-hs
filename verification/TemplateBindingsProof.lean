import TemplateSubstitutionBridge
import TemplateExpansionWhole

namespace PegHs.TemplateBindingsProof
open TemplatesTranslated TemplateSubstitutionBridge

theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α → List β)
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [same x (by simp)]
    congr 1
    exact ih (fun y member => same y (by simp [member]))

theorem root_adr0097_i2_expr_bindings_refine (e : Expr) :
    expandOnce.exprBinds_204 e = TemplateExpansionWhole.exprBinds (pExpr e) := by
  refine (measure (fun x : Expr => sizeOf x)).wf.induction
    (C := fun e => expandOnce.exprBinds_204 e = TemplateExpansionWhole.exprBinds (pExpr e)) e ?_
  intro e ih
  cases e <;> simp only [expandOnce.exprBinds_204, pExpr, TemplateExpansionWhole.exprBinds,
    exprChildren, HsList.concatMap, List.flatMap_nil, List.flatMap_cons, List.append_nil]
  all_goals first
    | rfl
    | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
    | skip
  case EGroup alts =>
    rw [pAlts_map]
    simp only [List.flatMap_map]
    apply flatMap_congr_mem
    intro items outer
    rw [pItems_map]
    simp only [List.flatMap_map]
    apply flatMap_congr_mem
    intro item inner
    simp only [expandOnce.itemBinds_203, HsList.append]
    rw [ih item.itemExpr (by
      have a := List.sizeOf_lt_of_mem outer
      have b := List.sizeOf_lt_of_mem inner
      have c := Item.itemExpr_sizeOf item
      change sizeOf item.itemExpr < sizeOf (Expr.EGroup alts)
      simp
      omega)]
    cases item with
    | Item l bind e => cases bind <;> rfl
  case ETemplate l n args vals =>
    rw [pArgs_map]
    simp only [List.flatMap_map]
    apply flatMap_congr_mem
    intro arg member
    exact ih arg (by
      have smaller := List.sizeOf_lt_of_mem member
      change sizeOf arg < sizeOf (Expr.ETemplate l n args vals)
      simp
      omega)
theorem root_adr0097_i2_item_bindings_refine (i : Item) :
    expandOnce.itemBinds_203 i = i.itemBind.toList ++ TemplateExpansionWhole.exprBinds (pExpr i.itemExpr) := by
  rw [expandOnce.itemBinds_203, root_adr0097_i2_expr_bindings_refine]
  cases i with
  | Item l bind e => cases bind <;> rfl

theorem root_adr0097_i2_expr_code_refines (e : Expr) :
    exprCode e = TemplateExpansionWhole.exprCode (pExpr e) := by
  refine (measure (fun x : Expr => sizeOf x)).wf.induction
    (C := fun e => exprCode e = TemplateExpansionWhole.exprCode (pExpr e)) e ?_
  intro e ih
  cases e <;> simp only [exprCode, pExpr, TemplateExpansionWhole.exprCode,
    exprChildren, HsList.concatMap, HsList.append, List.flatMap_nil, List.flatMap_cons, List.append_nil]
  all_goals first
    | rfl
    | (apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
    | skip
  case EGroup alts =>
    rw [pAlts_map]
    simp only [List.flatMap_map]
    apply flatMap_congr_mem
    intro items outer
    rw [pItems_map]
    simp only [List.flatMap_map]
    apply flatMap_congr_mem
    intro item inner
    exact ih item.itemExpr (by
      have a := List.sizeOf_lt_of_mem outer
      have b := List.sizeOf_lt_of_mem inner
      have c := Item.itemExpr_sizeOf item
      change sizeOf item.itemExpr < sizeOf (Expr.EGroup alts)
      simp
      omega)
  case ETemplate l n args vals =>
    rw [pArgs_map]
    simp only [List.flatMap_map]
    congr 1
    apply flatMap_congr_mem
    intro arg member
    exact ih arg (by
      have smaller := List.sizeOf_lt_of_mem member
      change sizeOf arg < sizeOf (Expr.ETemplate l n args vals)
      simp
      omega)

def pAlt (a : Alt) : TemplateExpansionWhole.Alt where
  items := pItems a.altItems
  action := a.altAction.map Located.unLoc
  constructor := a.altConstructor.map Located.unLoc

def pRule (r : Rule) : TemplateExpansionWhole.Rule where
  name := r.ruleName
  location := pLoc r.ruleLoc
  params := r.ruleParams.map (fun p => (p.paramName, p.paramType.unLoc))
  templateParams := r.ruleTemplateParams.map (fun p => (p.templateParamName, p.templateParamType))
  type := r.ruleType.unLoc
  alts := r.ruleAlts.map pAlt
  annotation := r.ruleAnnotation.map pLoc

theorem root_adr0097_i2_alt_code_refines (a : Alt) :
    altCode a = TemplateExpansionWhole.altCode (pAlt a) := by
  simp only [altCode, TemplateExpansionWhole.altCode, pAlt, HsList.append, HsList.concatMap,
    pItems_map, List.flatMap_map]
  congr 1
  · cases a.altAction <;> rfl
  · apply flatMap_congr_mem
    intro item member
    exact root_adr0097_i2_expr_code_refines item.itemExpr

theorem root_adr0097_i2_body_names_refine (env : TemplateExpansionWhole.Env)
    (idents : ∀ code, env.idents code = haskellIdents code) (r : Rule) :
    r.ruleParams.map Param.paramName ++ r.ruleAlts.flatMap expandOnce.altNames_202 =
      TemplateExpansionWhole.bodyNames env (pRule r) := by
  simp only [TemplateExpansionWhole.bodyNames, pRule, List.map_map, List.flatMap_map]
  congr 1
  apply flatMap_congr_mem
  intro alt member
  rw [expandOnce.altNames_202, root_adr0097_i2_alt_code_refines]
  simp only [HsList.append, HsList.concatMap, pAlt, pItems_map, List.flatMap_map]
  congr 1
  · apply flatMap_congr_mem
    intro code member
    exact (idents code).symm
  · apply flatMap_congr_mem
    intro item member
    exact root_adr0097_i2_item_bindings_refine item

#print axioms root_adr0097_i2_expr_bindings_refine
#print axioms root_adr0097_i2_item_bindings_refine
#print axioms root_adr0097_i2_expr_code_refines
#print axioms root_adr0097_i2_alt_code_refines
#print axioms root_adr0097_i2_body_names_refine
end PegHs.TemplateBindingsProof
