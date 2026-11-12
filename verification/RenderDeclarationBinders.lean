import RenderDeclarationsGHC

namespace PegHs.RenderDeclarationBinders

-- The grammar parser accepts a textual identifier, but Codegen prints it
-- without quoting in both a function argument and a do statement pattern.
-- `reserved` is the Haskell list checked by Assemble.toParam/assemble; the
-- checker ties its use and the `case` member to the production source.
def reservedBinder (reserved : List String)
    (recursiveDo arrows : Bool) (name : String) : Prop :=
  (name ≠ "_" ∧ name ∈ reserved) ∨
  (recursiveDo = true ∧ name ∈ ["mdo", "rec"]) ∨
  (arrows = true ∧ name ∈ ["proc", "rec"])

def acceptedBinder (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool) (name : String) : Prop :=
  identifier name = true ∧ ¬ reservedBinder reserved recursiveDo arrows name

theorem accepted_is_identifier (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool) (name : String)
    (h : acceptedBinder identifier reserved recursiveDo arrows name) :
    identifier name = true := h.1

theorem accepted_not_reserved (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool) (name : String)
    (h : acceptedBinder identifier reserved recursiveDo arrows name)
    (notWildcard : name ≠ "_") :
    name ∉ reserved := by
  intro member
  exact h.2 (Or.inl ⟨notWildcard, member⟩)

theorem reserved_rejected (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool) (name : String)
    (h : name ∈ reserved) (notWildcard : name ≠ "_") :
    ¬ acceptedBinder identifier reserved recursiveDo arrows name := by
  intro accepted
  exact accepted.2 (Or.inl ⟨notWildcard, h⟩)

theorem case_rejected (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool)
    (h : "case" ∈ reserved) :
    ¬ acceptedBinder identifier reserved recursiveDo arrows "case" := by
  exact reserved_rejected identifier reserved recursiveDo arrows "case" h (by decide)

theorem wildcard_allowed (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool)
    (valid : identifier "_" = true) :
    acceptedBinder identifier reserved recursiveDo arrows "_" := by
  constructor
  · exact valid
  · simp [reservedBinder]

theorem mdo_rejected_with_recursive_do (identifier : String → Bool)
    (reserved : List String) (arrows : Bool) :
    ¬ acceptedBinder identifier reserved true arrows "mdo" := by
  intro accepted
  exact accepted.2 (Or.inr (Or.inl ⟨rfl, by simp⟩))

theorem mdo_allowed_without_recursive_do (identifier : String → Bool)
    (reserved : List String) (valid : identifier "mdo" = true)
    (notReserved : "mdo" ∉ reserved) :
    acceptedBinder identifier reserved false false "mdo" := by
  constructor
  · exact valid
  · simp [reservedBinder, notReserved]

def memoKeyText (name : String) : String :=
  if name == "_" then "()" else name

def memoKeyTypeText (name ty : String) : String :=
  if name == "_" then "()" else ty

theorem wildcard_memo_key : memoKeyText "_" = "()" := by decide
theorem wildcard_memo_key_type (ty : String) :
    memoKeyTypeText "_" ty = "()" := by simp [memoKeyTypeText]
theorem named_memo_key (name : String) (notWildcard : name ≠ "_") :
    memoKeyText name = name := by
  simp [memoKeyText, notWildcard]
theorem named_memo_key_type (name ty : String) (notWildcard : name ≠ "_") :
    memoKeyTypeText name ty = ty := by
  simp [memoKeyTypeText, notWildcard]

-- A binder accepted by the parser is eligible for the VARID premise used
-- by RenderDeclarationsGHC.name_with_arguments. The lexer/category check
-- remains explicit because GHC's Unicode and extension rules are external.
theorem accepted_with_ghc_varid (identifier : String → Bool)
    (reserved : List String) (recursiveDo arrows : Bool)
    (ghcVarId : String → Bool) (name : String)
    (accepted : acceptedBinder identifier reserved recursiveDo arrows name)
    (lexer : ghcVarId name = true) :
    ghcVarId name = true ∧ ¬ reservedBinder reserved recursiveDo arrows name :=
  ⟨lexer, accepted.2⟩

#print axioms accepted_is_identifier
#print axioms accepted_not_reserved
#print axioms reserved_rejected
#print axioms case_rejected
#print axioms wildcard_allowed
#print axioms mdo_rejected_with_recursive_do
#print axioms mdo_allowed_without_recursive_do
#print axioms wildcard_memo_key
#print axioms wildcard_memo_key_type
#print axioms named_memo_key
#print axioms named_memo_key_type
#print axioms accepted_with_ghc_varid

end PegHs.RenderDeclarationBinders
