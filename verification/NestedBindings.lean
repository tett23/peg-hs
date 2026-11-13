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

theorem invariant2_nested_binder_reported (tree : BindingTree) (name rule : String)
    (templates : List String) (p : Predicates) (reserved : p.reservedBinder name = true)
    (occurs : tree.Binds name) :
    ∃ ds, assemble [.definitionWithBindings rule templates tree.names] p = .error ds ∧ ds ≠ [] := by
  have member : name ∈ tree.names := by
    induction occurs with
    | here => simp [BindingTree.names]
    | expression _ ih => simpa only [BindingTree.names] using List.mem_append_right _ ih
    | unary _ ih => simpa only [BindingTree.names] using ih
    | argument child _ ih => simp only [BindingTree.names]; exact List.mem_flatMap.mpr ⟨_, child, ih⟩
    | grouped group item _ ih => simp only [BindingTree.names]; exact List.mem_flatMap.mpr ⟨_, group, List.mem_flatMap.mpr ⟨_, item, ih⟩⟩
  apply binder_violation_rejected _ p ⟨.reservedBinding, name⟩
  simp [binderViolations, emit, member, reserved]

#print axioms invariant2_nested_binder_reported
end PegHs.AssembleValidation
