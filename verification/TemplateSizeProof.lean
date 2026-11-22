import TemplateGuardProof

namespace PegHs.TemplateSizeProof
open TemplatesTranslated TemplateSubstitutionBridge

theorem sumInteger_map_nat {α : Type} (xs : List α) (f : α → Int) (g : α → Nat)
    (same : ∀ x ∈ xs, f x = (g x : Int)) :
    HsList.sumInteger (xs.map f) = ((xs.map g).sum : Int) := by
  rw [HsList.sumInteger_eq_sum]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Int.natCast_add]
    rw [same x (by simp), ih (fun y member => same y (by simp [member]))]

theorem root_adr0097_i2_expr_size_refines (e : Expr) :
    exprSize e = (TemplateExpansionWhole.exprSize (pExpr e) : Int) := by
  refine (measure (fun x : Expr => sizeOf x)).wf.induction
    (C := fun e => exprSize e = (TemplateExpansionWhole.exprSize (pExpr e) : Int)) e ?_
  intro e ih
  cases e <;> simp only [exprSize, pExpr, TemplateExpansionWhole.exprSize,
    HsInt.add, Int.natCast_add]
  all_goals first
    | rfl
    | (congr 1; apply ih; change sizeOf _ < sizeOf _; simp <;> omega)
    | skip
  case EGroup alts =>
    simp only [pAlts_map, List.map_map, Function.comp_def]
    congr 1
    apply sumInteger_map_nat
    intro items outer
    simp only [pItems_map, List.map_map, Function.comp_def]
    apply sumInteger_map_nat
    intro item inner
    exact ih item.itemExpr (by
      have a := List.sizeOf_lt_of_mem outer
      have b := List.sizeOf_lt_of_mem inner
      have c := Item.itemExpr_sizeOf item
      change sizeOf item.itemExpr < sizeOf (Expr.EGroup alts)
      simp
      omega)
  case ETemplate l n args vals =>
    simp only [pArgs_map, List.map_map, Function.comp_def]
    congr 1
    apply sumInteger_map_nat
    intro arg member
    exact ih arg (by
      have smaller := List.sizeOf_lt_of_mem member
      change sizeOf arg < sizeOf (Expr.ETemplate l n args vals)
      simp
      omega)

theorem root_adr0097_i2_argument_size_refines (args : List Expr) :
    HsList.sumInteger (args.map exprSize) =
      (((pArgs args).map TemplateExpansionWhole.exprSize).sum : Int) := by
  simp only [pArgs_map, List.map_map, Function.comp_def]
  apply sumInteger_map_nat
  intro arg member
  exact root_adr0097_i2_expr_size_refines arg

def sizeOfArguments (args : List Expr) : Nat :=
  ((pArgs args).map TemplateExpansionWhole.exprSize).sum

def rejected (depth : Int) (args : List Expr) : Bool :=
  HsBase.or (HsInt.gt depth 64) (HsInt.gt (HsList.sumInteger (args.map exprSize)) 10000)

theorem root_adr0097_i2_limits_refine (depth : Int) (nonnegative : 0 ≤ depth) (args : List Expr) :
    rejected depth args = !TemplateQueue.allowed depth.toNat (sizeOfArguments args) := by
  have sizes : HsList.sumInteger (args.map exprSize) = (sizeOfArguments args : Int) :=
    root_adr0097_i2_argument_size_refines args
  rw [rejected, sizes]
  apply Bool.eq_iff_iff.mpr
  simp only [HsBase.or, HsInt.gt, Bool.or_eq_true, decide_eq_true_eq,
    TemplateQueue.allowed, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

abbrev SourceJob := String × Rule × List Expr × List (String × Located String) × Int × Loc

def withPending (st : St) (pending : List SourceJob) : St :=
  .St st.stInstances pending st.stErrors st.stCount st.stInstanceTypes st.stInstanceNames

def rejectedState (st : St) (t : Rule) (l : Loc) : St :=
  .St st.stInstances []
    (.Diagnostic l (TemplateExpansionWhole.depthMessage (TemplateBindingsProof.pRule t)) :: st.stErrors)
    st.stCount st.stInstanceTypes st.stInstanceNames

theorem root_adr0097_i2_rejected_step (fuel : Nat) (st : St) (pending : List SourceJob)
    (templates : HsMap String Rule) (bodyNames : HsMap String (HsSet String))
    (ruleTypes : HsMap String String) (usedNames : HsSet String)
    (name : String) (t : Rule) (args : List Expr) (captured : List (String × Located String))
    (depth : Int) (l : Loc) (nonnegative : 0 ≤ depth)
    (blocked : TemplateQueue.allowed depth.toNat (sizeOfArguments args) = false) :
    Expand.runExpandFn (expandOnce.drain_245 (fuel + 1) 64 10000 templates bodyNames ruleTypes usedNames)
      (withPending st ((name, t, args, captured, depth, l) :: pending)) =
      Expand.runExpandFn (expandOnce.drain_245 fuel 64 10000 templates bodyNames ruleTypes usedNames)
        (withPending (rejectedState st t l) pending) := by
  have over : rejected depth args = true := by
    rw [root_adr0097_i2_limits_refine depth nonnegative args, blocked]
    rfl
  unfold rejected at over
  have showDepth : HsText.pack (HsInt.«show» 64) = toString (64 : Nat) := by decide
  rw [expandOnce.drain_245]
  cases expandOnce.drain_245 fuel 64 10000 templates bodyNames ruleTypes usedNames with
  | Expand k =>
    simp only [withPending, rejectedState, gets', modify', addError,
      instMonad_gtgteq_Expand, instApplicative_pure_Expand, Expand.runExpandFn,
      St.stPending, St.stInstances, St.stErrors, St.stCount, St.stInstanceTypes, St.stInstanceNames,
      HsList.drop, List.drop, Int.toNat, HsBase.maybe, over, ite_true,
      HsText.append, TemplateExpansionWhole.depthMessage, TemplateBindingsProof.pRule, showDepth, String.append_assoc]

theorem root_adr0097_i2_rejected_singleton (fuel : Nat) (st : St)
    (templates : HsMap String Rule) (bodyNames : HsMap String (HsSet String))
    (ruleTypes : HsMap String String) (usedNames : HsSet String)
    (name : String) (t : Rule) (args : List Expr) (captured : List (String × Located String))
    (depth : Int) (l : Loc) (nonnegative : 0 ≤ depth)
    (blocked : TemplateQueue.allowed depth.toNat (sizeOfArguments args) = false) :
    Expand.runExpandFn (expandOnce.drain_245 (fuel + 2) 64 10000 templates bodyNames ruleTypes usedNames)
      (withPending st [(name, t, args, captured, depth, l)]) =
      ([], rejectedState st t l) := by
  have over : rejected depth args = true := by
    rw [root_adr0097_i2_limits_refine depth nonnegative args, blocked]
    rfl
  unfold rejected at over
  have showDepth : HsText.pack (HsInt.«show» 64) = toString (64 : Nat) := by decide
  simp only [withPending, rejectedState, expandOnce.drain_245, gets', modify', addError,
    instMonad_gtgteq_Expand, instApplicative_pure_Expand, Expand.runExpandFn,
    St.stPending, St.stInstances, St.stErrors, St.stCount, St.stInstanceTypes, St.stInstanceNames,
    HsList.drop, List.drop, Int.toNat, HsBase.maybe, over, ite_true,
    HsText.append, TemplateExpansionWhole.depthMessage, TemplateBindingsProof.pRule, showDepth, String.append_assoc]

theorem root_adr0097_i2_rejected_singleton_diagnostic (fuel : Nat) (st : St)
    (templates : HsMap String Rule) (bodyNames : HsMap String (HsSet String))
    (ruleTypes : HsMap String String) (usedNames : HsSet String)
    (name : String) (t : Rule) (args : List Expr) (captured : List (String × Located String))
    (depth : Int) (l : Loc) (nonnegative : 0 ≤ depth)
    (blocked : TemplateQueue.allowed depth.toNat (sizeOfArguments args) = false) :
    let result := Expand.runExpandFn
      (expandOnce.drain_245 (fuel + 2) 64 10000 templates bodyNames ruleTypes usedNames)
      (withPending st [(name, t, args, captured, depth, l)])
    result.1 = [] ∧ result.2.stErrors ≠ [] ∧ result.2.stPending = [] := by
  dsimp only
  rw [root_adr0097_i2_rejected_singleton fuel st templates bodyNames ruleTypes usedNames
    name t args captured depth l nonnegative blocked]
  simp only [rejectedState, St.stErrors, St.stPending, List.cons_ne_nil,
    ne_eq, not_false_eq_true, and_self]

#print axioms root_adr0097_i2_expr_size_refines
#print axioms root_adr0097_i2_argument_size_refines
#print axioms root_adr0097_i2_limits_refine
#print axioms root_adr0097_i2_rejected_step
#print axioms root_adr0097_i2_rejected_singleton
#print axioms root_adr0097_i2_rejected_singleton_diagnostic
end PegHs.TemplateSizeProof
