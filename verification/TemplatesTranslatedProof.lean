import TemplatesTranslated
import TemplateFreshProof

namespace PegHs.TemplatesTranslatedProof
open TemplatesTranslated

def CountSafe {α : Type} (action : Expand α) : Prop :=
  ∀ st, 0 ≤ St.stCount st → 0 ≤ St.stCount (Expand.runExpandFn action st).2

theorem pure_safe {α : Type} [Inhabited α] (value : α) :
    CountSafe (instApplicative_pure_Expand value) := by
  intro st safe
  exact safe

theorem gets_safe {α : Type} [Inhabited α] (f : St → α) : CountSafe (gets' f) := by
  intro st safe
  exact safe

theorem modify_safe (f : St → St)
    (safe : ∀ st, 0 ≤ St.stCount st → 0 ≤ St.stCount (f st)) : CountSafe (modify' f) := by
  exact safe

theorem default_safe {α : Type} [Inhabited α] : CountSafe (hsUndefined : Expand α) := by
  intro _ _
  change (0 : Int) ≤ 0
  decide

theorem bind_safe {α β : Type} [Inhabited α] [Inhabited β]
    (action : Expand α) (next : α → Expand β)
    (first : CountSafe action) (rest : ∀ value, CountSafe (next value)) :
    CountSafe (instMonad_gtgteq_Expand action next) := by
  cases action with
  | Expand run =>
    intro st safe
    change 0 ≤ St.stCount (Expand.runExpandFn (next (run st).1) (run st).2).2
    exact rest (run st).1 (run st).2 (first st safe)

theorem fmap_safe {α β : Type} [Inhabited α] [Inhabited β]
    (f : α → β) (action : Expand α) (safe : CountSafe action) :
    CountSafe (instFunctor_fmap_Expand f action) := by
  cases action with
  | Expand run =>
    intro st initial
    change 0 ≤ St.stCount (run st).2
    exact safe st initial

theorem ap_safe {α β : Type} [Inhabited α] [Inhabited β]
    (functions : Expand (α → β)) (arguments : Expand α)
    (first : CountSafe functions) (second : CountSafe arguments) :
    CountSafe (instApplicative_ltstargt_Expand functions arguments) := by
  cases functions with
  | Expand runF =>
    cases arguments with
    | Expand runA =>
      intro st initial
      change 0 ≤ St.stCount (runA (runF st).2).2
      exact second (runF st).2 (first st initial)

theorem foldr_safe {α β : Type} (step : α → Expand β → Expand β) (last : Expand β)
    (lastSafe : CountSafe last) (stepSafe : ∀ x rest, CountSafe rest → CountSafe (step x rest))
    (xs : List α) : CountSafe (xs.foldr step last) := by
  induction xs with
  | nil => exact lastSafe
  | cons x xs ih => exact stepSafe x _ ih

theorem addError_safe (d : Diagnostic) : CountSafe (addError d) := by
  intro st safe
  exact safe

theorem traverse_safe {α β : Type} [Inhabited β] (f : α → Expand β)
    (safe : ∀ x, CountSafe (f x)) (xs : List α) :
    CountSafe (xs.foldr (fun x rest =>
      instApplicative_ltstargt_Expand (instFunctor_fmap_Expand List.cons (f x)) rest)
      (instApplicative_pure_Expand [])) := by
  apply foldr_safe _ _ (pure_safe [])
  intro x rest restSafe
  exact ap_safe _ _ (fmap_safe List.cons (f x) (safe x)) restSafe

theorem traverse_unit_safe {α : Type} (f : α → Expand Unit)
    (safe : ∀ x, CountSafe (f x)) (xs : List α) :
    CountSafe (xs.foldr (fun x rest => instMonad_gtgteq_Expand (f x) (fun _ => rest))
      (instApplicative_pure_Expand ())) := by
  apply foldr_safe _ _ (pure_safe ())
  intro x rest restSafe
  exact bind_safe _ _ (safe x) (fun _ => restSafe)

theorem ite_safe {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Expand α) (yesSafe : CountSafe yes) (noSafe : CountSafe no) :
    CountSafe (if condition then yes else no) := by
  split
  · exact yesSafe
  · exact noSafe

theorem option_safe {α β : Type} (value : Option α) (empty : Expand β)
    (present : α → Expand β) (emptySafe : CountSafe empty)
    (presentSafe : ∀ x, CountSafe (present x)) :
    CountSafe (match value with | none => empty | some x => present x) := by
  cases value with
  | none => exact emptySafe
  | some x => exact presentSafe x

theorem root_adr0097_i2_instance_count_delta (fuel : Nat) (usedNames : HsSet String)
    (l : Loc) (depth : Int) (t : Rule) (args : List Expr)
    (tys : List (Option String)) (captured : List (String × Located String)) (st : St) :
    let after := (Expand.runExpandFn
      (expandOnce.instanceOf_221 fuel usedNames l depth t args tys captured) st).2
    St.stCount after = St.stCount st ∨ St.stCount after = St.stCount st + 1 := by
  simp only [expandOnce.instanceOf_221, gets', modify',
    instMonad_gtgteq_Expand, instApplicative_pure_Expand, Expand.runExpandFn]
  split <;> simp [St.stCount, HsInt.add]

theorem instanceOf_safe (fuel : Nat) (usedNames : HsSet String)
    (l : Loc) (depth : Int) (t : Rule) (args : List Expr)
    (tys : List (Option String)) (captured : List (String × Located String)) :
    CountSafe (expandOnce.instanceOf_221 fuel usedNames l depth t args tys captured) := by
  intro st initial
  have delta := root_adr0097_i2_instance_count_delta fuel usedNames l depth t args tys captured st
  dsimp only at delta
  omega

-- Keep the predicate atomic while indexing the conditional simp rules.
attribute [local irreducible] CountSafe
attribute [local simp] pure_safe gets_safe modify_safe default_safe bind_safe fmap_safe
  ap_safe traverse_safe traverse_unit_safe ite_safe option_safe addError_safe instanceOf_safe

theorem argType_safe (ruleTypes : HsMap String String) (l : Loc)
    (argument : TemplateParam × Expr) :
    CountSafe (expandOnce.argType_210 ruleTypes l argument) := by
  rcases argument with ⟨p, e⟩
  cases h : TemplateParam.templateParamType p <;> cases e <;>
    simp [expandOnce.argType_210, h]

attribute [local simp] argType_safe

theorem captures_safe (fuel : Nat) (bodyNames : HsMap String (HsSet String))
    (l : Loc) (caller : Caller) (scope : HsSet String) (t : Rule) (args : List Expr) :
    CountSafe (expandOnce.captures_188 fuel bodyNames l caller scope t args) := by
  unfold expandOnce.captures_188
  dsimp only
  apply bind_safe
  · apply traverse_unit_safe
    intro x
    exact addError_safe _
  · intro _
    apply bind_safe
    · apply traverse_unit_safe
      intro x
      exact addError_safe _
    · intro _
      exact pure_safe _

attribute [local simp] captures_safe

def ExprCountSafe (fuel : Nat) : Prop :=
  ∀ templates bodyNames ruleTypes usedNames caller depth scope e,
    CountSafe (expandOnce.expandExpr_144 fuel templates bodyNames ruleTypes usedNames
      caller depth scope e)

def ItemsCountSafe (fuel : Nat) : Prop :=
  ∀ templates bodyNames ruleTypes usedNames caller depth scope items,
    CountSafe (expandOnce.expandItems_137 fuel templates bodyNames ruleTypes usedNames
      caller depth scope items)

theorem root_adr0097_i2_expansion_count_nonnegative (fuel : Nat) :
    ExprCountSafe fuel ∧ ItemsCountSafe fuel := by
  induction fuel with
  | zero =>
    constructor
    · intro templates bodyNames ruleTypes usedNames caller depth scope e
      unfold expandOnce.expandExpr_144
      exact default_safe
    · intro templates bodyNames ruleTypes usedNames caller depth scope items
      unfold expandOnce.expandItems_137
      exact default_safe
  | succ fuel ih =>
    obtain ⟨exprSafe, itemsSafe⟩ := ih
    dsimp only [ExprCountSafe, ItemsCountSafe] at exprSafe itemsSafe ⊢
    constructor
    · intro templates bodyNames ruleTypes usedNames caller depth scope e
      unfold expandOnce.expandExpr_144
      cases e <;> simp [exprSafe, itemsSafe]
      rename_i l n args vals
      cases found : HsMap.lookup n templates with
      | none => simp
      | some t =>
        apply bind_safe
        · split
          · exact addError_safe _
          · split
            · exact addError_safe _
            · exact pure_safe _
        · intro _
          apply bind_safe
          · apply traverse_safe
            intro e
            exact exprSafe templates bodyNames ruleTypes usedNames caller depth scope e
          · intro expanded
            split
            · simp
            · apply bind_safe
              · exact captures_safe fuel bodyNames l caller scope t expanded
              · intro captured
                apply bind_safe
                · apply traverse_safe
                  intro argument
                  exact argType_safe ruleTypes l argument
                · intro tys
                  apply bind_safe
                  · exact instanceOf_safe fuel usedNames l depth t expanded tys captured
                  · intro _
                    exact pure_safe _
    · intro templates bodyNames ruleTypes usedNames caller depth scope items
      unfold expandOnce.expandItems_137
      cases items <;> simp [exprSafe, itemsSafe]

theorem expr_safe (fuel : Nat) : ExprCountSafe fuel :=
  (root_adr0097_i2_expansion_count_nonnegative fuel).1

theorem items_safe (fuel : Nat) : ItemsCountSafe fuel :=
  (root_adr0097_i2_expansion_count_nonnegative fuel).2

theorem alt_safe (fuel : Nat) (templates : HsMap String Rule)
    (bodyNames : HsMap String (HsSet String)) (ruleTypes : HsMap String String)
    (usedNames : HsSet String) (caller : Caller) (depth : Int) (scope : HsSet String) (a : Alt) :
    CountSafe (expandOnce.expandAlt_133 fuel templates bodyNames ruleTypes usedNames caller depth scope a) := by
  unfold expandOnce.expandAlt_133
  apply bind_safe
  · exact items_safe fuel templates bodyNames ruleTypes usedNames caller depth scope _
  · intro _
    exact pure_safe _

theorem rule_safe (fuel : Nat) (templates : HsMap String Rule)
    (bodyNames : HsMap String (HsSet String)) (ruleTypes : HsMap String String)
    (usedNames : HsSet String) (r : Rule) :
    CountSafe (expandOnce.expandRule_126 fuel templates bodyNames ruleTypes usedNames r) := by
  unfold expandOnce.expandRule_126
  dsimp only
  apply bind_safe
  · apply traverse_safe
    intro a
    exact alt_safe fuel templates bodyNames ruleTypes usedNames _ 0 HsSet.empty a
  · intro _
    exact pure_safe _

theorem root_adr0097_i2_drain_count_nonnegative (fuel : Nat) (maxDepth maxSize : Int)
    (templates : HsMap String Rule) (bodyNames : HsMap String (HsSet String))
    (ruleTypes : HsMap String String) (usedNames : HsSet String) :
    CountSafe (expandOnce.drain_245 fuel maxDepth maxSize templates bodyNames ruleTypes usedNames) := by
  induction fuel with
  | zero =>
    unfold expandOnce.drain_245
    exact default_safe
  | succ fuel ih =>
    unfold expandOnce.drain_245
    apply bind_safe
    · exact gets_safe _
    · intro pending
      cases pending with
      | nil => exact pure_safe _
      | cons next rest =>
        rcases next with ⟨name, t, args, captured, depth, l⟩
        dsimp only
        apply bind_safe
        · apply modify_safe
          intro st safe
          exact safe
        · intro _
          apply bind_safe
          · split
            · simp
            · apply bind_safe
              · apply traverse_safe
                intro a
                exact alt_safe fuel templates bodyNames ruleTypes usedNames _ depth HsSet.empty _
              · intro alts
                apply bind_safe
                · exact gets_safe _
                · intro _
                  exact pure_safe _
          · intro _
            apply bind_safe
            · exact ih
            · intro _
              exact pure_safe _

private theorem eraseDups_nonempty {α : Type} [BEq α] (xs : List α) (nonempty : xs ≠ []) :
    xs.eraseDups ≠ [] := by
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    rw [List.eraseDups_cons]
    intro empty
    cases empty

private theorem eraseDups_reverse_cons_ne_nil {α : Type} [BEq α] (head : α) (tail : List α) :
    (head :: tail).reverse.eraseDups ≠ [] := by
  apply eraseDups_nonempty
  intro empty
  have originalEmpty := List.reverse_eq_nil_iff.mp empty
  cases originalEmpty

theorem root_adr0097_i2_expand_once_error_nonempty (fuel : Nat) (known : HsMap String String)
    (g : Grammar) (diags : List Diagnostic) (result : expandOnce fuel known g = .error diags) :
    diags ≠ [] := by
  unfold expandOnce at result
  dsimp only at result
  split at result
  · simp_all
  · split at result
    · rename_i haveErrors
      rintro rfl
      have emptyErrors := Except.error.inj result
      simp [HsBase.not, HsList.null] at emptyErrors haveErrors
      exact haveErrors emptyErrors
    · split at result
      · rintro rfl
        exact eraseDups_reverse_cons_ne_nil _ _ (Except.error.inj result)
      · cases result

private theorem go_error_nonempty (k : Nat) :
    ∀ fuel, k < fuel → ∀ (g : Grammar) (known : HsMap String String) (diags : List Diagnostic),
      expandTemplates.go_69 fuel g k known = .error diags → diags ≠ [] := by
  induction k with
  | zero =>
    intro fuel enough g known diags result
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold expandTemplates.go_69 at result
      cases pass : expandOnce fuel known g with
      | error errors =>
        have equal : errors = diags := by
          simpa only [pass, HsEither.bind, Except.error.injEq] using result
        subst diags
        exact root_adr0097_i2_expand_once_error_nonempty fuel known g errors pass
      | ok expanded =>
        simp [pass, HsEither.bind, HsBase.or, HsInt.le] at result
  | succ k ih =>
    intro fuel enough g known diags result
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold expandTemplates.go_69 at result
      cases pass : expandOnce fuel known g with
      | error errors =>
        have equal : errors = diags := by
          simpa only [pass, HsEither.bind, Except.error.injEq] using result
        subst diags
        exact root_adr0097_i2_expand_once_error_nonempty fuel known g errors pass
      | ok expanded =>
        simp only [pass, HsEither.bind] at result
        split at result
        · simp_all
        · have nextIndex : HsInt.sub ((k + 1 : Nat) : Int) 1 = (k : Int) := by
            simp only [HsInt.sub]
            omega
          rw [nextIndex] at result
          exact ih fuel (by omega) g _ diags result

theorem root_adr0097_i2_expand_templates_error_nonempty (fuel : Nat) (enough : 9 ≤ fuel)
    (g : Grammar) (diags : List Diagnostic)
    (result : expandTemplates fuel g = .error diags) : diags ≠ [] := by
  unfold expandTemplates at result
  split at result
  · simp_all
  · exact go_error_nonempty 8 fuel (by omega) g HsMap.empty diags result

#print axioms PegHs.TemplatesTranslatedProof.root_adr0097_i2_instance_count_delta
#print axioms PegHs.TemplatesTranslatedProof.instanceOf_safe
#print axioms PegHs.TemplatesTranslatedProof.captures_safe
#print axioms PegHs.TemplatesTranslatedProof.root_adr0097_i2_expansion_count_nonnegative
#print axioms PegHs.TemplatesTranslatedProof.root_adr0097_i2_drain_count_nonnegative
#print axioms PegHs.TemplatesTranslatedProof.root_adr0097_i2_expand_once_error_nonempty
#print axioms PegHs.TemplatesTranslatedProof.root_adr0097_i2_expand_templates_error_nonempty
end PegHs.TemplatesTranslatedProof
