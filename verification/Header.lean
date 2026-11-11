namespace Peg.Verification

-- The caller supplies the Haskell host's Unicode character predicates.
def identTail (alphaNum : Char → Bool) (c : Char) : Bool :=
  alphaNum c || c == '_' || c == '\''

def modulePart (upper alphaNum : Char → Bool) (part : String) : Bool :=
  match part.toList with
  | [] => false
  | first :: rest => upper first && rest.all (identTail alphaNum)

def moduleName (upper alphaNum : Char → Bool) (name : String) : Bool :=
  (name.splitOn ".").all (modulePart upper alphaNum)

-- These propositions describe a declaration's lexical shape independently of
-- the recognizer's Boolean result.
def PartSyntax (upper alphaNum : Char → Bool) (part : String) : Prop :=
  match part.toList with
  | [] => False
  | first :: rest =>
      upper first = true ∧ ∀ c ∈ rest, identTail alphaNum c = true

def NameSyntax (upper alphaNum : Char → Bool) (name : String) : Prop :=
  ∀ part ∈ name.splitOn ".", PartSyntax upper alphaNum part

inductive HeaderSyntax (upper alphaNum : Char → Bool) : String → Prop where
  | moduleDecl (name : String) (valid : NameSyntax upper alphaNum name) :
      HeaderSyntax upper alphaNum ("module " ++ name ++ "\n")

def checkedHeader (upper alphaNum : Char → Bool) (name : String) : Option String :=
  if moduleName upper alphaNum name then some ("module " ++ name ++ "\n") else none

private theorem part_sound (upper alphaNum : Char → Bool) (part : String)
    (h : modulePart upper alphaNum part = true) :
    PartSyntax upper alphaNum part := by
  unfold modulePart at h
  unfold PartSyntax
  split at h
  · simp at h
  · rename_i first rest
    constructor
    · exact (Bool.and_eq_true_iff.mp h).1
    · exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2

private theorem name_sound (upper alphaNum : Char → Bool) (name : String)
    (h : moduleName upper alphaNum name = true) :
    NameSyntax upper alphaNum name := by
  intro part member
  exact part_sound upper alphaNum part ((List.all_eq_true.mp h) part member)

theorem invariant3_checkedHeader_sound
    (upper alphaNum : Char → Bool) (name code : String)
    (h : checkedHeader upper alphaNum name = some code) :
    HeaderSyntax upper alphaNum code := by
  unfold checkedHeader at h
  split at h
  · rename_i valid
    cases h
    exact HeaderSyntax.moduleDecl name (name_sound upper alphaNum name valid)
  · simp at h

theorem invariant3_invalid_name_rejected
    (upper alphaNum : Char → Bool) (name : String)
    (h : moduleName upper alphaNum name = false) :
    checkedHeader upper alphaNum name = none := by
  simp [checkedHeader, h]

#print axioms invariant3_checkedHeader_sound
#print axioms invariant3_invalid_name_rejected

end Peg.Verification
