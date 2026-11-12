import RuleRejection

namespace PegHs.RuleRejectionRefs

abbrev Ref := Nat × String × Nat

-- The payloads irrelevant to reference extraction are projected to simple
-- scalars. `group` contains the projected expressions of each Item.
inductive Expr where
  | lit : String → String → Expr
  | charClass : String → Expr
  | any : Expr
  | ref : Nat → String → Nat → Expr
  | group : List (List Expr) → Expr
  | star : Expr → Expr
  | plus : Expr → Expr
  | opt : Expr → Expr
  | and : Expr → Expr
  | not : Expr → Expr
  | capture : Expr → Expr
  | label : Nat → Expr → String → Expr
  | predicate : Bool → String → Expr
  | template : Nat → String → List Expr → Nat → Expr
  | discard : Expr → Expr

-- Direct translation of Check.hs `exprRefs` after Item.itemExpr projection.
def exprRefs : Expr → List Ref
  | .lit _ _ => []
  | .charClass _ => []
  | .any => []
  | .ref location name arity => [(location, name, arity)]
  | .group alts => alts.flatMap (fun items => items.flatMap exprRefs)
  | .star x => exprRefs x
  | .plus x => exprRefs x
  | .opt x => exprRefs x
  | .and x => exprRefs x
  | .not x => exprRefs x
  | .capture x => exprRefs x
  | .label _ x _ => exprRefs x
  | .predicate _ _ => []
  | .template _ _ args _ => args.flatMap exprRefs
  | .discard x => exprRefs x
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega
  · have h := List.sizeOf_lt_of_mem (by assumption)
    omega

def itemsRefs (items : List Expr) : List Ref := items.flatMap exprRefs

-- This relation is independent of the executable list traversal.
inductive HasRef : Expr → Ref → Prop where
  | direct {location name arity} : HasRef (.ref location name arity) (location, name, arity)
  | group {alts items x reference} : items ∈ alts → x ∈ items → HasRef x reference →
      HasRef (.group alts) reference
  | star {x reference} : HasRef x reference → HasRef (.star x) reference
  | plus {x reference} : HasRef x reference → HasRef (.plus x) reference
  | opt {x reference} : HasRef x reference → HasRef (.opt x) reference
  | and {x reference} : HasRef x reference → HasRef (.and x) reference
  | not {x reference} : HasRef x reference → HasRef (.not x) reference
  | capture {x reference} : HasRef x reference → HasRef (.capture x) reference
  | label {location x name reference} : HasRef x reference →
      HasRef (.label location x name) reference
  | template {location name args values x reference} : x ∈ args → HasRef x reference →
      HasRef (.template location name args values) reference
  | discard {x reference} : HasRef x reference → HasRef (.discard x) reference

theorem invariant2_exprRefs_iff (expression : Expr) (reference : Ref) :
    reference ∈ exprRefs expression ↔ HasRef expression reference := by
  induction expression using exprRefs.induct with
  | case1 =>
    constructor
    · intro h; simp [exprRefs] at h
    · intro h; cases h
  | case2 =>
    constructor
    · intro h; simp [exprRefs] at h
    · intro h; cases h
  | case3 =>
    constructor
    · intro h; simp [exprRefs] at h
    · intro h; cases h
  | case4 location name arity =>
    constructor
    · intro h
      simp only [exprRefs, List.mem_singleton] at h
      subst reference
      exact HasRef.direct
    · intro h
      cases h
      simp [exprRefs]
  | case5 alts ih =>
    constructor
    · intro h
      simp only [exprRefs, List.mem_flatMap] at h
      obtain ⟨items, hitems, x, hx, href⟩ := h
      exact HasRef.group hitems hx ((ih items hitems x hx).mp href)
    · intro h
      cases h with
      | group hitems hx href =>
        simp only [exprRefs, List.mem_flatMap]
        exact ⟨_, hitems, _, hx, (ih _ hitems _ hx).mpr href⟩
  | case6 x ih =>
    constructor
    · intro h; exact HasRef.star (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | star hx => simpa [exprRefs] using ih.mpr hx
  | case7 x ih =>
    constructor
    · intro h; exact HasRef.plus (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | plus hx => simpa [exprRefs] using ih.mpr hx
  | case8 x ih =>
    constructor
    · intro h; exact HasRef.opt (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | opt hx => simpa [exprRefs] using ih.mpr hx
  | case9 x ih =>
    constructor
    · intro h; exact HasRef.and (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | and hx => simpa [exprRefs] using ih.mpr hx
  | case10 x ih =>
    constructor
    · intro h; exact HasRef.not (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | not hx => simpa [exprRefs] using ih.mpr hx
  | case11 x ih =>
    constructor
    · intro h; exact HasRef.capture (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | capture hx => simpa [exprRefs] using ih.mpr hx
  | case12 location x name ih =>
    constructor
    · intro h; exact HasRef.label (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | label hx => simpa [exprRefs] using ih.mpr hx
  | case13 =>
    constructor
    · intro h; simp [exprRefs] at h
    · intro h; cases h
  | case14 location name args values ih =>
    constructor
    · intro h
      simp only [exprRefs, List.mem_flatMap] at h
      obtain ⟨x, hx, href⟩ := h
      exact HasRef.template hx ((ih x hx).mp href)
    · intro h
      cases h with
      | template hx href =>
        simp only [exprRefs, List.mem_flatMap]
        exact ⟨_, hx, (ih _ hx).mpr href⟩
  | case15 x ih =>
    constructor
    · intro h; exact HasRef.discard (ih.mp (by simpa [exprRefs] using h))
    · intro h; cases h with | discard hx => simpa [exprRefs] using ih.mpr hx

theorem invariant2_itemsRefs_iff (items : List Expr) (reference : Ref) :
    reference ∈ itemsRefs items ↔ ∃ expression ∈ items, HasRef expression reference := by
  simp [itemsRefs, List.mem_flatMap, invariant2_exprRefs_iff]

def grammarRefs (rules : List (List (List Expr))) : List Ref :=
  rules.flatMap fun alternatives => alternatives.flatMap itemsRefs

theorem invariant2_grammarRefs_iff (rules : List (List (List Expr))) (reference : Ref) :
    reference ∈ grammarRefs rules ↔
      ∃ alternatives ∈ rules, ∃ items ∈ alternatives,
        ∃ expression ∈ items, HasRef expression reference := by
  simp [grammarRefs, List.mem_flatMap, invariant2_itemsRefs_iff]

def withoutArity (references : List Ref) : List (Nat × String) :=
  references.map fun (location, name, _) => (location, name)

theorem invariant2_nestedMissingRefProducesError
    (expression : Expr) (location : Nat) (name : String) (arity : Nat)
    (defined : List String)
    (nested : HasRef expression (location, name, arity))
    (missing : name ∉ defined) :
    RuleRejection.undefinedRef location name ∈
      RuleRejection.undefinedFromRefs (withoutArity (exprRefs expression)) defined := by
  apply RuleRejection.invariant2_missingRefProducesError _ _ location name
  · apply List.mem_map.mpr
    exact ⟨(location, name, arity), (invariant2_exprRefs_iff expression _).mpr nested, rfl⟩
  · exact missing

theorem invariant2_nestedMissingRefVisible {G : Type}
    (parsed g0 g : G)
    (resolve expand : G → Except RuleRejection.Diagnostics G)
    (notes : G → RuleRejection.Diagnostics → RuleRejection.Diagnostics)
    (strip : Option (G → G))
    (warningFor : G → G → RuleRejection.Diagnostics)
    (generate : G → Except RuleRejection.Diagnostics String)
    (expression : Expr) (defined : List String)
    (repetition before after : List RuleRejection.Diagnostic)
    (location : Nat) (name : String) (arity : Nat)
    (hr : resolve parsed = .ok g0) (he : expand g0 = .ok g)
    (hn : ∀ ds, ds ≠ [] → notes g0 ds ≠ [])
    (nested : HasRef expression (location, name, arity))
    (missing : name ∉ defined) :
    ∃ ds, ds ≠ [] ∧
      PegHs.Pipeline.visible
        (PegHs.Pipeline.pipeline (.ok parsed) resolve expand
          (fun _ => RuleRejection.checkRoot
            (RuleRejection.undefinedFromRefs (withoutArity (exprRefs expression)) defined)
            repetition before after)
          notes strip warningFor generate) = .error ds := by
  apply RuleRejection.invariant2_rejectionReachesVisible parsed g0 g resolve expand
    notes strip warningFor generate
    (RuleRejection.undefinedFromRefs (withoutArity (exprRefs expression)) defined)
    repetition before after hr he hn
  exact Or.inl ⟨location, name,
    invariant2_nestedMissingRefProducesError expression location name arity defined nested missing⟩

-- Invariant 2: a deeply nested rule reference is extracted once.
example : (3, "Missing", 0) ∈ exprRefs (.group [[.star (.ref 3 "Missing" 0)]]) := by
  simp [exprRefs]

end PegHs.RuleRejectionRefs

#print axioms PegHs.RuleRejectionRefs.invariant2_exprRefs_iff
#print axioms PegHs.RuleRejectionRefs.invariant2_grammarRefs_iff
#print axioms PegHs.RuleRejectionRefs.invariant2_nestedMissingRefProducesError
#print axioms PegHs.RuleRejectionRefs.invariant2_nestedMissingRefVisible
