import BoundedDecimal
import Pipeline
import AssembleValidationHelpers
import AssemblePredicates
import AssembleBindings
import DirectiveNames

-- The validation half of Peg.Grammar.Assemble.assemble on a model of Top.
--
-- Premises recorded here (also in verification/README.md):
-- * Int is 64 bits: intMax is maxBound :: Int; TabstopProof checks it
--   against the value that ExtractTabstop.hs prints.
-- * Locations, Located wrappers, Param types and the type of an annotation
--   are erased; only names reach the validation.
-- * The predicates are the concrete translations in AssemblePredicates;
--   the binders come from the trees in AssembleBindings.
-- * The wording of diagnostics stays in Haskell; see diagnostic below.
namespace PegHs.AssembleValidation

inductive Top where
  | directive (name arg : String)
  -- TAnnot: rule name, template parameter names, parameter names.
  | annotation (name : String) (templateParams params : List String)
  -- TDef: rule name, template parameter names, the items of each alternative.
  | definition (name : String) (templateNames : List String)
      (alternatives : List (List BindingTree))
  | verbatim
  deriving BEq

def directives (tops : List Top) : List (String × String) := tops.filterMap fun
  | .directive n a => some (n, a)
  | _ => none

def annotations (tops : List Top) : List (String × List String) := tops.filterMap fun
  | .annotation n ps _ => some (n, ps)
  | _ => none

def definitions (tops : List Top) : List (String × List String) := tops.filterMap fun
  | .definition n ps _ => some (n, ps)
  | _ => none

def known : List String :=
  ["module", "start", "entry", "export", "env", "tabstop", "nomemo",
   "language", "syntax", "token", "trivia", "inline", "recover", "safe",
   "deriving", "expect", "message", "import", "library"]

def args (ds : List (String × String)) (name : String) : List String :=
  (ds.filter (fun d => d.1 == name)).map (·.2)

def modulePresent (tops : List Top) : Bool :=
  (directives tops).any fun d => d.1 == "module" || d.1 == "library"

-- maxBound :: Int on a 64-bit target.
def intMax : Nat := 9223372036854775807

-- languageOptions in assemble: the items of every %language, in order.
def languageOptions (tops : List Top) : List String :=
  (args (directives tops) "language").flatMap AssembleValidationHelpers.splitExports

-- The second and later occurrences are the rejection witnesses. Assemble.hs
-- may report only one duplicate directive per name; multiplicity is erased
-- here because the theorem concerns acceptance and nonempty diagnostics.
def repeated [BEq α] : List α → List α := go []
where
  go (seen : List α) : List α → List α
    | [] => []
    | x :: xs => (if seen.contains x then [x] else []) ++ go (x :: seen) xs

inductive Kind where
  | unknownDirective | duplicateDirective | missingArgument | unexpectedArgument
  | libraryConflict | libraryDirective | libraryVerbatim | invalidImportPath
  | duplicateImport | invalidRecover | invalidLanguage | invalidModule
  | invalidExport | invalidDeriving | invalidString | duplicateString
  | invalidSafe | invalidRuleName | invalidTabstop | missingTemplateType
  | orphanAnnotation | duplicateAnnotation | duplicateDefinition | noRules
  | templateMismatch
  | reservedParameter | reservedBinding
  deriving BEq, DecidableEq, Repr

structure Violation where
  kind : Kind
  subject : String
  deriving BEq, DecidableEq

def emit (kind : Kind) (names : List String) : List Violation :=
  names.map (⟨kind, ·⟩)

def stringResults (ds : List (String × String)) (n : String) :
    List (Except String String) :=
  (args ds n).filterMap fun a => if a.isEmpty then none else
    some (AssembleValidationHelpers.stringArg validIdent n a)

def parseFailures (rs : List (Except String String)) : List String := rs.filterMap fun
  | .error e => some e
  | .ok _ => none

def parsedNames (rs : List (Except String String)) : List String := rs.filterMap fun
  | .error _ => none
  | .ok n => some n

def otherViolations (tops : List Top) : List Violation := Id.run do
  let ds := directives tops
  let imports := args ds "import"
  let library := ds.any fun d => d.1 == "library"
  let strings := stringResults ds "expect" ++ stringResults ds "message"
  return (
    emit .unknownDirective ((ds.filter (fun d => !known.contains d.1)).map (·.1)) ++
    emit .duplicateDirective (repeated ((ds.filter (fun d =>
      ["module", "start", "env", "tabstop", "syntax", "deriving", "library"].contains d.1)).map (·.1))) ++
    emit .missingArgument ((ds.filter (fun d => known.contains d.1 &&
      !["syntax", "deriving", "library"].contains d.1 && d.2.isEmpty)).map (·.1)) ++
    emit .unexpectedArgument ((ds.filter (fun d =>
      ["syntax", "library"].contains d.1 && !d.2.isEmpty)).map (·.1)) ++
    (if library && (ds.any fun d => d.1 == "module") then [⟨.libraryConflict, ""⟩] else []) ++
    (if library then emit .libraryDirective ((ds.filter (fun d => known.contains d.1 &&
      !["library", "module"].contains d.1)).map (·.1)) else []) ++
    (if library && tops.any (fun t => match t with | .verbatim => true | _ => false)
      then [⟨.libraryVerbatim, ""⟩] else []) ++
    emit .invalidImportPath (imports.filter (fun x => !x.isEmpty && !DirectiveNames.validImportPath x)) ++
    emit .duplicateImport (repeated (imports.filter DirectiveNames.validImportPath)) ++
    emit .invalidRecover ((args ds "recover").filter fun a =>
      !a.isEmpty && match words a with
        | [lab, rule] => !(validIdent lab && validIdent rule)
        | _ => true) ++
    emit .invalidLanguage (((args ds "language").flatMap AssembleValidationHelpers.splitExports).filter
      (fun x => !DirectiveNames.validExtension x)) ++
    emit .invalidModule ((args ds "module").filter
      (fun x => !x.isEmpty && !validModule x)) ++
    emit .invalidExport (((args ds "export").flatMap AssembleValidationHelpers.splitExports).filter
      (fun x => !validExport (languageOptions tops) x)) ++
    emit .invalidDeriving (((args ds "deriving").flatMap AssembleValidationHelpers.splitExports).filter
      (fun x => !validClass x)) ++
    emit .invalidString (parseFailures strings) ++
    emit .duplicateString (repeated (parsedNames (stringResults ds "expect")) ++
      repeated (parsedNames (stringResults ds "message"))) ++
    emit .invalidSafe ((args ds "safe").filter
      (fun x => !x.isEmpty && !validIdent x)) ++
    emit .invalidRuleName ((ds.filter (fun d =>
      ["start", "entry", "nomemo", "token", "trivia", "inline"].contains d.1 &&
      !d.2.isEmpty && !validIdent d.2)).map (·.1)) ++
    emit .invalidTabstop (match (args ds "tabstop").head? with
      | none => []
      | some x => if (BoundedDecimal.positive intMax x).isNone then [x] else []) ++
    emit .missingTemplateType ((definitions tops).filterMap fun d =>
      if !d.2.isEmpty && !(annotations tops).any (fun a => a.1 == d.1)
      then some d.1 else none) ++
    emit .templateMismatch ((definitions tops).filterMap fun d =>
      match (annotations tops).find? (fun a => a.1 == d.1) with
      | some a => if d.2 != a.2 then some d.1 else none
      | none => none))

def structuralViolations (tops : List Top) : List Violation :=
  let annots := (annotations tops).map (·.1)
  let defs := (definitions tops).map (·.1)
  emit .orphanAnnotation (annots.eraseDups.filter (fun n => !defs.contains n)) ++
  emit .duplicateAnnotation (repeated annots) ++
  emit .duplicateDefinition (repeated defs) ++
  (if defs.isEmpty && modulePresent tops then [⟨.noRules, ""⟩] else [])

-- The parameter names of every annotation, and the binders that
-- concatMap nestedItems finds in every alternative of every definition.
def annotationParams (tops : List Top) : List String := tops.flatMap fun
  | .annotation _ _ params => params
  | _ => []

def definitionBinders (tops : List Top) : List String := tops.flatMap fun
  | .definition _ _ alternatives => altBinders alternatives
  | _ => []

-- binderError in assemble, under the LANGUAGE options of the same file.
def binderViolations (tops : List Top) : List Violation :=
  emit .reservedParameter ((annotationParams tops).filter (binderError (languageOptions tops))) ++
  emit .reservedBinding ((definitionBinders tops).filter (binderError (languageOptions tops)))

def violations (tops : List Top) : List Violation :=
  otherViolations tops ++ structuralViolations tops ++ binderViolations tops

-- The exact wording and locations remain in Haskell. A distinct nonempty
-- diagnostic is constructed for each violation solely for rejection proofs.
def diagnostic (v : Violation) : String := toString (repr v.kind) ++ ":" ++ v.subject

def errors (tops : List Top) : List String :=
  (violations tops).map diagnostic

def assemble (tops : List Top) : Except (List String) Unit :=
  match errors tops with
  | [] => if modulePresent tops then .ok () else .error ["missing %module directive"]
  | es@(_ :: _) => .error es

theorem errors_nonempty_iff_violation (tops : List Top) :
    errors tops ≠ [] ↔ ∃ v, v ∈ violations tops := by
  cases h : violations tops with
  | nil => simp [errors, h]
  | cons v rest =>
    constructor
    · intro _
      exact ⟨v, by simp⟩
    · intro _ eq
      unfold errors at eq
      rw [h] at eq
      simp at eq

theorem assemble_failure_nonempty (tops : List Top)
    (ds : List String) (h : assemble tops = .error ds) : ds ≠ [] := by
  cases he : errors tops with
  | nil =>
    cases hm : modulePresent tops with
    | false =>
      have eq : ds = ["missing %module directive"] := by
        simpa [assemble, he, hm] using h.symm
      simp [eq]
    | true => simp [assemble, he, hm] at h
  | cons d rest =>
    have eq : ds = d :: rest := by simpa [assemble, he] using h.symm
    simp [eq]

theorem assemble_failure_iff_violation_or_missing_module (tops : List Top) :
    (∃ ds, assemble tops = .error ds) ↔
      (∃ v, v ∈ violations tops) ∨ modulePresent tops = false := by
  cases he : errors tops with
  | nil =>
    have hv : ¬∃ v, v ∈ violations tops := by
      intro h
      exact (errors_nonempty_iff_violation tops).2 h he
    cases hm : modulePresent tops <;> simp [assemble, he, hm, hv]
  | cons d rest =>
    have hv : ∃ v, v ∈ violations tops :=
      (errors_nonempty_iff_violation tops).1 (by simp [he])
    simp [assemble, he, hv]

-- The only other outcome: no violation, a module, and acceptance.
theorem assemble_ok_iff (tops : List Top) :
    assemble tops = .ok () ↔ violations tops = [] ∧ modulePresent tops = true := by
  cases he : errors tops with
  | nil =>
    have hv : violations tops = [] := by
      cases h : violations tops with
      | nil => rfl
      | cons v rest => simp [errors, h] at he
    cases hm : modulePresent tops <;> simp [assemble, he, hm, hv]
  | cons d rest =>
    have hv : violations tops ≠ [] := by
      intro h; simp [errors, h] at he
    simp [assemble, he, hv]

theorem structural_violation_rejected (tops : List Top)
    (v : Violation) (h : v ∈ structuralViolations tops) :
    ∃ ds, assemble tops = .error ds ∧ ds ≠ [] := by
  have hv : ∃ x, x ∈ violations tops :=
    ⟨v, by simp [violations, h]⟩
  obtain ⟨ds, hd⟩ := (assemble_failure_iff_violation_or_missing_module tops).2
    (Or.inl hv)
  exact ⟨ds, hd, assemble_failure_nonempty tops ds hd⟩

theorem binder_violation_rejected (tops : List Top)
    (v : Violation) (h : v ∈ binderViolations tops) :
    ∃ ds, assemble tops = .error ds ∧ ds ≠ [] := by
  have hv : ∃ x, x ∈ violations tops :=
    ⟨v, by simp [violations, h]⟩
  obtain ⟨ds, hd⟩ := (assemble_failure_iff_violation_or_missing_module tops).2
    (Or.inl hv)
  exact ⟨ds, hd, assemble_failure_nonempty tops ds hd⟩

theorem mem_emit (k k' : Kind) (n : String) (xs : List String) :
    (⟨k, n⟩ : Violation) ∈ emit k' xs ↔ k = k' ∧ n ∈ xs := by
  unfold emit
  rw [List.mem_map]
  constructor
  · rintro ⟨a, h, eq⟩
    cases eq
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨n, h, rfl⟩

-- The binding diagnostics name exactly the binders that occur in some
-- definition's alternatives and that binderError rejects.
theorem invariant2_reserved_binding_iff (tops : List Top) (name : String) :
    ⟨.reservedBinding, name⟩ ∈ binderViolations tops ↔
      binderError (languageOptions tops) name = true ∧
      ∃ rule templates alternatives, Top.definition rule templates alternatives ∈ tops ∧
        ∃ items ∈ alternatives, ∃ item ∈ items, item.Binds name := by
  have kinds : (⟨.reservedBinding, name⟩ : Violation) ∈ binderViolations tops ↔
      name ∈ (definitionBinders tops).filter (binderError (languageOptions tops)) := by
    unfold binderViolations
    rw [List.mem_append, mem_emit, mem_emit]
    simp
  rw [kinds, List.mem_filter]
  constructor
  · rintro ⟨inside, rejected⟩
    obtain ⟨top, member, names⟩ := List.mem_flatMap.mp inside
    refine ⟨rejected, ?_⟩
    cases top with
    | definition rule templates alternatives =>
      exact ⟨rule, templates, alternatives, member,
        (invariant2_alt_binders_iff alternatives name).1 names⟩
    | directive => simp at names
    | annotation => simp at names
    | verbatim => simp at names
  · rintro ⟨rejected, rule, templates, alternatives, member, occurs⟩
    exact ⟨List.mem_flatMap.mpr ⟨_, member, (invariant2_alt_binders_iff alternatives name).2 occurs⟩,
      rejected⟩

theorem invariant2_reserved_parameter_iff (tops : List Top) (name : String) :
    ⟨.reservedParameter, name⟩ ∈ binderViolations tops ↔
      binderError (languageOptions tops) name = true ∧
      ∃ rule templates params, Top.annotation rule templates params ∈ tops ∧ name ∈ params := by
  have kinds : (⟨.reservedParameter, name⟩ : Violation) ∈ binderViolations tops ↔
      name ∈ (annotationParams tops).filter (binderError (languageOptions tops)) := by
    unfold binderViolations
    rw [List.mem_append, mem_emit, mem_emit]
    simp
  rw [kinds, List.mem_filter]
  constructor
  · rintro ⟨inside, rejected⟩
    obtain ⟨top, member, names⟩ := List.mem_flatMap.mp inside
    refine ⟨rejected, ?_⟩
    cases top with
    | annotation rule templates params => exact ⟨rule, templates, params, member, names⟩
    | directive => simp at names
    | definition => simp at names
    | verbatim => simp at names
  · rintro ⟨rejected, rule, templates, params, member, inside⟩
    exact ⟨List.mem_flatMap.mpr ⟨_, member, inside⟩, rejected⟩

theorem invariant2_nested_binder_rejected (tops : List Top) (name rule : String)
    (templates : List String) (alternatives : List (List BindingTree))
    (definition : Top.definition rule templates alternatives ∈ tops)
    (items : List BindingTree) (alternative : items ∈ alternatives)
    (item : BindingTree) (inside : item ∈ items) (occurs : item.Binds name)
    (rejected : binderError (languageOptions tops) name = true) :
    ∃ ds, assemble tops = .error ds ∧ diagnostic ⟨.reservedBinding, name⟩ ∈ ds := by
  have violation := (invariant2_reserved_binding_iff tops name).2
    ⟨rejected, rule, templates, alternatives, definition, items, alternative, item, inside, occurs⟩
  have reported : diagnostic ⟨.reservedBinding, name⟩ ∈ errors tops :=
    List.mem_map.mpr ⟨_, List.mem_append_right _ violation, rfl⟩
  cases h : errors tops with
  | nil => simp [h] at reported
  | cons d ds => exact ⟨_, by simp [assemble, h], h ▸ reported⟩

theorem invariant2_parameter_rejected (tops : List Top) (name rule : String)
    (templates params : List String) (annotation : Top.annotation rule templates params ∈ tops)
    (member : name ∈ params) (rejected : binderError (languageOptions tops) name = true) :
    ∃ ds, assemble tops = .error ds ∧ diagnostic ⟨.reservedParameter, name⟩ ∈ ds := by
  have violation := (invariant2_reserved_parameter_iff tops name).2
    ⟨rejected, rule, templates, params, annotation, member⟩
  have reported : diagnostic ⟨.reservedParameter, name⟩ ∈ errors tops :=
    List.mem_map.mpr ⟨_, List.mem_append_right _ violation, rfl⟩
  cases h : errors tops with
  | nil => simp [h] at reported
  | cons d ds => exact ⟨_, by simp [assemble, h], h ▸ reported⟩

theorem reserved_word_binder_error (options : List String) (name : String)
    (word : name ∈ grammarReservedWords) (notWildcard : name ≠ "_") :
    binderError options name = true := by
  simp [binderError, binderKeyword, word, notWildcard]

theorem reserved_parameter_rejected :
    ∃ ds, assemble [.directive "module" "M",
      .annotation "P" [] ["case"], .definition "P" [] [[]]] = .error ds ∧ ds ≠ [] := by
  apply binder_violation_rejected _ ⟨.reservedParameter, "case"⟩
  exact (invariant2_reserved_parameter_iff _ _).2
    ⟨reserved_word_binder_error _ _ (by decide) (by decide), "P", [], ["case"], by simp, by simp⟩

theorem reserved_binding_rejected :
    ∃ ds, assemble [.directive "module" "M",
      .definition "S" [] [[.item (some "case") .leaf]]] = .error ds ∧ ds ≠ [] := by
  apply binder_violation_rejected _ ⟨.reservedBinding, "case"⟩
  exact (invariant2_reserved_binding_iff _ _).2
    ⟨reserved_word_binder_error _ _ (by decide) (by decide), "S", [],
      [[.item (some "case") .leaf]], by simp, [.item (some "case") .leaf], by simp,
      .item (some "case") .leaf, by simp, .here⟩

-- A binder inside a repeated group, as in the probe's nested location case.
theorem nested_forall_binding_rejected :
    ∃ ds, assemble [.directive "module" "M",
      .definition "S" [] [[.item none (.unary (.group [[], [.item (some "forall") .leaf]]))]]] =
      .error ds ∧ diagnostic ⟨.reservedBinding, "forall"⟩ ∈ ds := by
  apply invariant2_nested_binder_rejected _ "forall" "S" []
    [[.item none (.unary (.group [[], [.item (some "forall") .leaf]]))]] (by simp)
    [.item none (.unary (.group [[], [.item (some "forall") .leaf]]))] (by simp)
    (.item none (.unary (.group [[], [.item (some "forall") .leaf]]))) (by simp)
  · exact .expression (.unary (.grouped (child := .item (some "forall") .leaf)
      (items := [.item (some "forall") .leaf]) (by simp) (by simp) .here))
  · exact reserved_word_binder_error _ _ (by decide) (by decide)

-- U+02B0 MODIFIER LETTER SMALL H cannot start a binder.
theorem modifier_binding_rejected :
    ∃ ds, assemble [.directive "module" "M",
      .definition "S" [] [[.item (some "ʰ") .leaf]]] =
      .error ds ∧ diagnostic ⟨.reservedBinding, "ʰ"⟩ ∈ ds := by
  apply invariant2_nested_binder_rejected _ "ʰ" "S" [] [[.item (some "ʰ") .leaf]] (by simp)
    [.item (some "ʰ") .leaf] (by simp) (.item (some "ʰ") .leaf) (by simp) .here
  have : AssembleChars.isModifier 'ʰ' = true := by decide
  simp [binderError, startsWithModifier, this]

-- mdo is a binder keyword only after RecursiveDo or DoRec is enabled.
theorem mdo_binding_rejected_under_recursive_do :
    ∃ ds, assemble [.directive "module" "M", .directive "language" "RecursiveDo",
      .definition "S" [] [[.item (some "mdo") .leaf]]] =
      .error ds ∧ diagnostic ⟨.reservedBinding, "mdo"⟩ ∈ ds := by
  apply invariant2_nested_binder_rejected _ "mdo" "S" [] [[.item (some "mdo") .leaf]] (by simp)
    [.item (some "mdo") .leaf] (by simp) (.item (some "mdo") .leaf) (by simp) .here
  decide +kernel

theorem duplicate_definition_rejected :
    ∃ ds, assemble [.directive "module" "M", .definition "S" [] [[]], .definition "S" [] [[]]]
      = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ ⟨.duplicateDefinition, "S"⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem orphan_annotation_rejected :
    ∃ ds, assemble [.directive "module" "M", .annotation "S" [] []]
      = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ ⟨.orphanAnnotation, "S"⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem duplicate_annotation_rejected :
    ∃ ds, assemble [.directive "module" "M", .annotation "S" [] [],
      .annotation "S" [] [], .definition "S" [] [[]]]
      = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ ⟨.duplicateAnnotation, "S"⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem no_rules_rejected :
    ∃ ds, assemble [.directive "module" "M"] = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ ⟨.noRules, ""⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem missing_module_rejected :
    ∃ ds, assemble [.definition "S" [] [[]]] = .error ds ∧ ds ≠ [] := by
  have hm : modulePresent [.definition "S" [] [[]]] = false := by decide
  obtain ⟨ds, hd⟩ := (assemble_failure_iff_violation_or_missing_module _).2
    (Or.inr hm)
  exact ⟨ds, hd, assemble_failure_nonempty _ ds hd⟩

-- The concrete predicates accept ordinary and Unicode names, so the
-- rejection theorems are not vacuous.
theorem small_grammar_accepted :
    assemble [.directive "module" "Δ.Ω'", .directive "export" "S, T(..), (+), module X",
      .directive "language" "RecursiveDo", .directive "deriving" "GHC.Generics.Generic",
      .directive "recover" "lab S", .annotation "S" [] ["x"],
      .definition "S" [] [[.item (some "漢") .leaf, .item (some "_") .leaf]]] = .ok () :=
  (assemble_ok_iff _).2 (by decide +kernel)

def parseGrammar (parseTops : Except (List String) (List Top)) : Except (List String) Unit :=
  match parseTops with
  | .error ds => .error ds
  | .ok tops => assemble tops

theorem public_assemble_failure (tops : List Top)
    (ds : List String) (ha : assemble tops = .error ds)
    (resolve expand : Unit → Except (List String) Unit)
    (check : Unit → Except (List String) Unit)
    (notes : Unit → List String → List String)
    (strip : Option (Unit → Unit)) (warningFor : Unit → Unit → List String)
    (generate : Unit → Except (List String) String) :
    PegHs.Pipeline.visible (PegHs.Pipeline.pipeline
      (parseGrammar (.ok tops)) resolve expand check notes strip warningFor generate) =
      .error ds ∧ ds ≠ [] := by
  have hp : parseGrammar (.ok tops) = .error ds := by
    rw [parseGrammar]
    exact ha
  constructor
  · rw [hp]
    exact PegHs.Pipeline.invariant2_parseFailure ds resolve expand check notes strip
      warningFor generate
  · exact assemble_failure_nonempty tops ds ha

#print axioms PegHs.AssembleValidation.assemble_failure_iff_violation_or_missing_module
#print axioms PegHs.AssembleValidation.assemble_ok_iff
#print axioms PegHs.AssembleValidation.invariant2_reserved_binding_iff
#print axioms PegHs.AssembleValidation.invariant2_reserved_parameter_iff
#print axioms PegHs.AssembleValidation.reserved_parameter_rejected
#print axioms PegHs.AssembleValidation.reserved_binding_rejected
#print axioms PegHs.AssembleValidation.nested_forall_binding_rejected
#print axioms PegHs.AssembleValidation.modifier_binding_rejected
#print axioms PegHs.AssembleValidation.mdo_binding_rejected_under_recursive_do
#print axioms PegHs.AssembleValidation.small_grammar_accepted
#print axioms PegHs.AssembleValidation.public_assemble_failure

end PegHs.AssembleValidation
