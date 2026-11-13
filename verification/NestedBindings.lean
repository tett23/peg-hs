import AssembleValidation

namespace PegHs.AssembleValidation

-- Projection of the recursion in Assemble.nestedItems and nestedExpr.
-- The unary constructors have identical traversal; template arguments have
-- no item of their own. A group contributes each item in alternative order.
inductive BindingTree where
  | leaf
  | unary (child : BindingTree)
  | templateArgs (args : List BindingTree)
  | group (alternatives : List (List BindingTree))
  | item (binder : Option String) (expression : BindingTree)

def BindingTree.names : BindingTree → List String
  | .leaf => []
  | .unary child => child.names
  | .templateArgs args => args.flatMap fun child => child.names
  | .group alternatives => alternatives.flatMap fun items => items.flatMap fun item => item.names
  | .item binder expression => binder.toList ++ expression.names

termination_by tree => sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial
  all_goals have h := List.sizeOf_lt_of_mem (by assumption : _ ∈ alternatives); omega

inductive BindingTree.Binds (name : String) : BindingTree → Prop where
  | here : Binds name (.item (some name) expression)
  | expression : Binds name expr → Binds name (.item binder expr)
  | unary : Binds name child → Binds name (.unary child)
  | argument {children : List BindingTree} : child ∈ children → Binds name child → Binds name (.templateArgs children)
  | grouped {child : BindingTree} : items ∈ groups → child ∈ items → Binds name child → Binds name (.group groups)

theorem invariant2_nested_names_iff (tree : BindingTree) (name : String) :
    name ∈ tree.names ↔ tree.Binds name := by
  constructor
  · intro member
    induction tree using (measure (fun t : BindingTree => sizeOf t)).wf.induction with
    | h tree ih =>
      cases tree with
      | leaf => simp [BindingTree.names] at member
      | unary child => exact .unary (ih child (by change sizeOf _ < sizeOf (BindingTree.unary child); simp +arith) (by simpa [BindingTree.names] using member))
      | item binder expr =>
        rw [BindingTree.names, List.mem_append] at member
        rcases member with bound | nested
        · cases binder with
          | none => contradiction
          | some b => simp at bound; subst b; exact .here
        · exact .expression (ih expr (by change sizeOf _ < sizeOf (BindingTree.item binder expr); simp +arith) nested)
      | templateArgs children =>
        rw [BindingTree.names, List.mem_flatMap] at member
        obtain ⟨child, inside, nested⟩ := member
        exact .argument inside (ih child (by have := List.sizeOf_lt_of_mem inside; change sizeOf child < sizeOf (BindingTree.templateArgs children); simp; omega) nested)
      | group groups =>
        rw [BindingTree.names, List.mem_flatMap] at member
        obtain ⟨items, groupMem, inside⟩ := member
        obtain ⟨child, childMem, nested⟩ := List.mem_flatMap.mp inside
        exact .grouped groupMem childMem (ih child (by
          have := List.sizeOf_lt_of_mem groupMem
          have := List.sizeOf_lt_of_mem childMem
          change sizeOf child < sizeOf (BindingTree.group groups)
          simp; omega) nested)
  · intro occurs
    induction occurs with
    | here => simp [BindingTree.names]
    | expression _ ih => simpa only [BindingTree.names] using List.mem_append_right _ ih
    | unary _ ih => simpa only [BindingTree.names] using ih
    | argument child _ ih => simp only [BindingTree.names]; exact List.mem_flatMap.mpr ⟨_, child, ih⟩
    | grouped group item _ ih => simp only [BindingTree.names]; exact List.mem_flatMap.mpr ⟨_, group, List.mem_flatMap.mpr ⟨_, item, ih⟩⟩

theorem invariant2_nested_binder_reported (tree : BindingTree) (name rule : String)
    (templates : List String) (p : Predicates) (reserved : p.reservedBinder name = true)
    (occurs : tree.Binds name) (tops : List Top)
    (definition : Top.definitionWithBindings rule templates tree.names ∈ tops) :
    ∃ ds, assemble tops p = .error ds ∧ diagnostic ⟨.reservedBinding, name⟩ ∈ ds := by
  have names := (invariant2_nested_names_iff tree name).2 occurs
  have violation : ⟨.reservedBinding, name⟩ ∈ binderViolations tops p := by
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨name, List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, definition, names⟩, reserved⟩, rfl⟩
  have reported : diagnostic ⟨.reservedBinding, name⟩ ∈ errors tops p :=
    List.mem_map.mpr ⟨_, List.mem_append_right _ violation, rfl⟩
  cases h : errors tops p with
  | nil => simp [h] at reported
  | cons d ds => exact ⟨_, by simp [assemble, h], h ▸ reported⟩

-- Flags act from left to right. Reading them from the right gives an
-- independent specification: the last mention of any alias wins.
def extensionFlag (aliases : List String) (option : String) : Option Bool :=
  if option ∈ aliases then some true
  else if option ∈ aliases.map ("No" ++ ·) then some false else none

def extensionEnabled (aliases options : List String) (initial := false) : Bool :=
  options.foldl (fun enabled option => (extensionFlag aliases option).getD enabled) initial

theorem invariant2_extension_last_setting (aliases options : List String) (initial : Bool) :
    extensionEnabled aliases options initial =
      (options.reverse.findSome? (extensionFlag aliases)).getD initial := by
  induction options generalizing initial with
  | nil => rfl
  | cons option rest ih =>
    change extensionEnabled aliases rest ((extensionFlag aliases option).getD initial) = _
    rw [ih, List.reverse_cons, List.findSome?_append]
    cases rest.reverse.findSome? (extensionFlag aliases) <;>
      cases h : extensionFlag aliases option <;> simp [h]

example : extensionEnabled ["RecursiveDo", "DoRec"] ["DoRec", "NoRecursiveDo"] = false := rfl
example : extensionEnabled ["RecursiveDo", "DoRec"] ["NoDoRec", "Arrows", "RecursiveDo"] = true := rfl

def languageOptions (tops : List Top) : List String :=
  (args (directives tops) "language").flatMap AssembleValidationHelpers.splitExports

def binderKeyword (words options : List String) (name : String) : Bool :=
  (name != "_" && words.contains name) ||
    (extensionEnabled ["RecursiveDo", "DoRec"] options && ["mdo", "rec"].contains name) ||
    (extensionEnabled ["Arrows"] options && ["proc", "rec"].contains name)

theorem invariant2_extension_binder_diagnostic (tree : BindingTree) (name rule : String)
    (templates words : List String) (tops : List Top) (p : Predicates)
    (occurs : tree.Binds name) (definition : Top.definitionWithBindings rule templates tree.names ∈ tops)
    (enabled : (name ∈ ["mdo", "rec"] ∧
        (languageOptions tops).reverse.findSome? (extensionFlag ["RecursiveDo", "DoRec"]) = some true) ∨
      (name ∈ ["proc", "rec"] ∧
        (languageOptions tops).reverse.findSome? (extensionFlag ["Arrows"]) = some true)) :
    ∃ ds, assemble tops {p with reservedBinder := binderKeyword words (languageOptions tops)} = .error ds ∧
      diagnostic ⟨.reservedBinding, name⟩ ∈ ds := by
  apply invariant2_nested_binder_reported tree name rule templates _ _ occurs tops definition
  change binderKeyword words (languageOptions tops) name = true
  rcases enabled with ⟨member, flag⟩ | ⟨member, flag⟩ <;>
    simp [binderKeyword, invariant2_extension_last_setting, flag, member]

#print axioms invariant2_extension_binder_diagnostic
#print axioms invariant2_extension_last_setting
#print axioms invariant2_nested_binder_reported
end PegHs.AssembleValidation
