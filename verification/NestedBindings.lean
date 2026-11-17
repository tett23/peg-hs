import AssembleValidation

-- Binder diagnostics of assemble for each reason that binderError gives:
-- a Haskell reserved word, an extension keyword under its LANGUAGE flag,
-- and a leading Unicode modifier letter. The binding trees, the
-- extractor and binderError are concrete (AssembleBindings,
-- AssemblePredicates).
namespace PegHs.AssembleValidation

theorem invariant2_modifier_binding_rejected (c : Char) (tail : List Char)
    (isModifier : AssembleChars.isModifier c = true) (tops : List Top) (rule : String)
    (templates : List String) (alternatives : List (List BindingTree))
    (definition : Top.definition rule templates alternatives ∈ tops)
    (items : List BindingTree) (alternative : items ∈ alternatives)
    (item : BindingTree) (inside : item ∈ items) (occurs : item.Binds (String.ofList (c :: tail))) :
    ∃ ds, assemble tops = .error ds ∧ ds ≠ [] := by
  obtain ⟨ds, rejected, reported⟩ := invariant2_nested_binder_rejected tops _ rule templates
    alternatives definition items alternative item inside occurs
    (by simp [binderError, startsWithModifier, isModifier])
  exact ⟨ds, rejected, fun empty => by simp [empty] at reported⟩

theorem invariant2_modifier_parameter_rejected (c : Char) (tail : List Char)
    (isModifier : AssembleChars.isModifier c = true) (rule : String)
    (templates params : List String) (tops : List Top)
    (annotation : Top.annotation rule templates params ∈ tops)
    (member : String.ofList (c :: tail) ∈ params) :
    ∃ ds, assemble tops = .error ds ∧ ds ≠ [] := by
  obtain ⟨ds, rejected, reported⟩ := invariant2_parameter_rejected tops _ rule templates params
    annotation member (by simp [binderError, startsWithModifier, isModifier])
  exact ⟨ds, rejected, fun empty => by simp [empty] at reported⟩

theorem invariant2_reserved_word_diagnostic (name rule : String) (templates : List String)
    (alternatives : List (List BindingTree)) (tops : List Top)
    (word : name ∈ grammarReservedWords) (notWildcard : name ≠ "_")
    (definition : Top.definition rule templates alternatives ∈ tops)
    (items : List BindingTree) (alternative : items ∈ alternatives)
    (item : BindingTree) (inside : item ∈ items) (occurs : item.Binds name) :
    ∃ ds, assemble tops = .error ds ∧ diagnostic ⟨.reservedBinding, name⟩ ∈ ds :=
  invariant2_nested_binder_rejected tops name rule templates alternatives definition items
    alternative item inside occurs (reserved_word_binder_error _ _ word notWildcard)

theorem invariant2_extension_binder_diagnostic (name rule : String) (templates : List String)
    (alternatives : List (List BindingTree)) (tops : List Top)
    (definition : Top.definition rule templates alternatives ∈ tops)
    (items : List BindingTree) (alternative : items ∈ alternatives)
    (item : BindingTree) (inside : item ∈ items) (occurs : item.Binds name)
    (enabled : (name ∈ ["mdo", "rec"] ∧
        (languageOptions tops).reverse.findSome? (extensionFlag ["RecursiveDo", "DoRec"]) = some true) ∨
      (name ∈ ["proc", "rec"] ∧
        (languageOptions tops).reverse.findSome? (extensionFlag ["Arrows"]) = some true)) :
    ∃ ds, assemble tops = .error ds ∧ diagnostic ⟨.reservedBinding, name⟩ ∈ ds := by
  apply invariant2_nested_binder_rejected tops name rule templates alternatives definition items
    alternative item inside occurs
  rcases enabled with ⟨member, flag⟩ | ⟨member, flag⟩ <;>
    simp [binderError, binderKeyword, extensionKeyword, recursiveDoEnabled, arrowsEnabled,
      invariant2_extension_last_setting, flag, member]

#print axioms invariant2_modifier_binding_rejected
#print axioms invariant2_modifier_parameter_rejected
#print axioms invariant2_reserved_word_diagnostic
#print axioms invariant2_extension_binder_diagnostic
end PegHs.AssembleValidation
