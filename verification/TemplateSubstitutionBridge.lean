import TemplatesTranslated
import TemplateSubstitution

namespace PegHs.TemplateSubstitutionBridge
open TemplatesTranslated
abbrev MExpr := TemplateSubstitution.Expr

def pLoc (l : Loc) : TemplateSubstitution.Location :=
  ⟨l.locFile.toNat, l.locLine.toNat, l.locColumn.toNat⟩

mutual
def pExpr : Expr → MExpr
  | .ELit v w => .lit v w
  | .EClass _ w => .charClass w
  | .EAny => .any
  | .ERef l n args => .ref (pLoc l) n (args.map Located.unLoc)
  | .EGroup alts => .group (pAlts alts)
  | .EStar e => .star (pExpr e)
  | .EPlus e => .plus (pExpr e)
  | .EOpt e => .opt (pExpr e)
  | .EAnd e => .and (pExpr e)
  | .ENot e => .not (pExpr e)
  | .ECapture e => .capture (pExpr e)
  | .ELabel l e n => .label (pLoc l) (pExpr e) n
  | .EPred b c => .predicate b c.unLoc
  | .ETemplate l n args vals => .template (pLoc l) n (pArgs args) (vals.map Located.unLoc)
  | .EDiscard e => .discard (pExpr e)
termination_by e => sizeOf e

def pItems : List Item → List (Option String × MExpr)
  | [] => []
  | .Item _ b e :: rest => (b, pExpr e) :: pItems rest
termination_by is => sizeOf is

def pAlts : List (List Item) → List (List (Option String × MExpr))
  | [] => []
  | items :: rest => pItems items :: pAlts rest
termination_by alts => sizeOf alts

def pArgs : List Expr → List MExpr
  | [] => []
  | e :: rest => pExpr e :: pArgs rest
termination_by es => sizeOf es
end

def pSub (sub : HsMap String (TemplateParam × Expr)) : TemplateSubstitution.Substitution :=
  fun n => (HsMap.lookup n sub).map fun p =>
    (HsMaybe.isJust p.1.templateParamType, pExpr p.2)

theorem pItems_map (items : List Item) :
    pItems items = items.map (fun i => (i.itemBind, pExpr i.itemExpr)) := by
  induction items with
  | nil => simp [pItems]
  | cons i rest ih => cases i; simp [pItems, Item.itemBind, Item.itemExpr, ih]

theorem pAlts_map (alts : List (List Item)) : pAlts alts = alts.map pItems := by
  induction alts with
  | nil => simp [pAlts]
  | cons items rest ih => simp [pAlts, ih]

theorem pArgs_map (args : List Expr) : pArgs args = args.map pExpr := by
  induction args with
  | nil => simp [pArgs]
  | cons e rest ih => simp [pArgs, ih]

theorem root_adr0097_i2_substitution_refines (e : Expr) :
    ∀ sub, pExpr (substituteAlt.expr_303 sub e) = TemplateSubstitution.substitute (pSub sub) false (pExpr e) ∧
      pExpr (substituteAlt.passed_318 sub e) = TemplateSubstitution.substitute (pSub sub) true (pExpr e) := by
  refine (measure (fun x : Expr => sizeOf x)).wf.induction
    (C := fun e => ∀ sub,
      pExpr (substituteAlt.expr_303 sub e) = TemplateSubstitution.substitute (pSub sub) false (pExpr e) ∧
      pExpr (substituteAlt.passed_318 sub e) = TemplateSubstitution.substitute (pSub sub) true (pExpr e)) e ?_
  intro e ih sub
  have exprPart : pExpr (substituteAlt.expr_303 sub e) =
      TemplateSubstitution.substitute (pSub sub) false (pExpr e) := by
    have step (x : Expr) (smaller : sizeOf x < sizeOf e) := ih x smaller sub
    cases e <;> simp only [substituteAlt.expr_303, pExpr, TemplateSubstitution.substitute]
    all_goals first
      | (congr 1; exact (step _ (by simp <;> omega)).1)
      | skip
    case ERef l n args =>
      cases args with
      | nil =>
        cases found : HsMap.lookup n sub with
        | none => simp [substituteAlt.expr_303, pSub, pExpr, TemplateSubstitution.substitute, found]
        | some pair =>
          rcases pair with ⟨p, arg⟩
          cases flag : HsMaybe.isJust p.templateParamType <;>
            simp [substituteAlt.expr_303, pSub, TemplateSubstitution.substitute, found, flag] <;>
            split <;> simp_all [pExpr]
      | cons arg rest => simp [substituteAlt.expr_303, pExpr, TemplateSubstitution.substitute]
    case EGroup alts =>
      congr 1
      simp only [pAlts_map, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro items itemsIn
      simp only [pItems_map, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro item itemIn
      cases item with
      | Item l b x =>
        simp only [substituteAlt.item_302, Item.itemBind, Item.itemExpr]
        congr 1
        apply (step x ?_).1
        have outer := List.sizeOf_lt_of_mem itemsIn
        have inner := List.sizeOf_lt_of_mem itemIn
        have field : sizeOf x < sizeOf (Item.Item l b x) := by simp <;> omega
        simp
        omega
    case ETemplate l n args vals =>
      congr 1
      simp only [pArgs_map, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro arg argIn
      apply (step arg ?_).2
      have smaller := List.sizeOf_lt_of_mem argIn
      simp
      omega
  refine ⟨exprPart, ?_⟩
  cases e <;> try simpa only [substituteAlt.passed_318, pExpr, TemplateSubstitution.substitute] using exprPart
  case ERef l n args =>
    cases args with
    | nil =>
      cases found : HsMap.lookup n sub with
      | none => simp [substituteAlt.passed_318, substituteAlt.expr_303, pSub, pExpr,
          TemplateSubstitution.substitute, found]
      | some pair =>
        rcases pair with ⟨p, arg⟩
        simp [substituteAlt.passed_318, pSub, pExpr, TemplateSubstitution.substitute, found] <;>
          split <;> simp_all [pExpr]
    | cons arg rest =>
      simpa only [substituteAlt.passed_318, pExpr, TemplateSubstitution.substitute, List.map_cons] using exprPart

theorem root_adr0097_i2_alt_items_refine (sub : HsMap String (TemplateParam × Expr)) (a : Alt) :
    pItems (substituteAlt sub a).altItems =
      TemplateSubstitution.substituteAlt (pSub sub) (pItems a.altItems) := by
  simp only [substituteAlt, Alt.altItems, pItems_map, TemplateSubstitution.substituteAlt,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro item _
  cases item with
  | Item l b e =>
    simp only [substituteAlt.item_302, Item.itemBind, Item.itemExpr]
    exact congrArg (fun x => (b, x)) (root_adr0097_i2_substitution_refines e sub).1

theorem root_adr0097_i2_item_fields_preserved (sub : HsMap String (TemplateParam × Expr)) (i : Item) :
    (substituteAlt.item_302 sub i).itemLoc = i.itemLoc ∧
      (substituteAlt.item_302 sub i).itemBind = i.itemBind := by
  constructor
  · simp [substituteAlt.item_302, Item.itemLoc]
  · simp [substituteAlt.item_302, Item.itemBind]

theorem root_adr0097_i2_alt_fields_preserved (sub : HsMap String (TemplateParam × Expr)) (a : Alt) :
    (substituteAlt sub a).altLoc = a.altLoc ∧
      (substituteAlt sub a).altAction = a.altAction ∧
      (substituteAlt sub a).altConstructor = a.altConstructor := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms PegHs.TemplateSubstitutionBridge.root_adr0097_i2_substitution_refines
#print axioms PegHs.TemplateSubstitutionBridge.root_adr0097_i2_alt_items_refine
#print axioms PegHs.TemplateSubstitutionBridge.root_adr0097_i2_alt_fields_preserved
end PegHs.TemplateSubstitutionBridge
