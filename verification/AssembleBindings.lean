-- The model of Peg.Grammar's Expr and Item as far as Assemble's binding
-- collection (nestedItems and nestedExpr) observes them.
--
-- Haskell constructor     model
--   Item _ bind e         item bind e
--   EGroup groups         group groups (each element of a group is an item)
--   EStar, EPlus, EOpt, EAnd, ENot, ECapture, ELabel, EDiscard
--                         unary child
--   ETemplate _ _ args _  templateArgs args
--   ELit, EClass, EAny, ERef, EPred
--                         leaf
--
-- AssembleValidationProbe.hs maps every Haskell Expr to this type with the
-- table above and compares the binder diagnostics of the two sides.
namespace PegHs.AssembleValidation

inductive BindingTree where
  | leaf
  | unary (child : BindingTree)
  | templateArgs (args : List BindingTree)
  | group (alternatives : List (List BindingTree))
  | item (binder : Option String) (expression : BindingTree)
  deriving BEq

-- nestedItems i = i : nestedExpr (itemExpr i), with itemBind read off each
-- item; a group visits its alternatives and items in order.
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

-- An independent description of a binding occurrence: an item node with
-- the binder, reached through the constructors that nestedExpr descends.
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

-- The binders of a definition: concatMap nestedItems over the items of
-- every alternative, keeping the items that have a binder.
def altBinders (alternatives : List (List BindingTree)) : List String :=
  alternatives.flatMap fun items => items.flatMap BindingTree.names

theorem invariant2_alt_binders_iff (alternatives : List (List BindingTree)) (name : String) :
    name ∈ altBinders alternatives ↔
      ∃ items ∈ alternatives, ∃ item ∈ items, item.Binds name := by
  simp only [altBinders, List.mem_flatMap, invariant2_nested_names_iff]

#print axioms invariant2_nested_names_iff
#print axioms invariant2_alt_binders_iff

end PegHs.AssembleValidation
