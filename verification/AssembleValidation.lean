import Pipeline
import AssembleValidationHelpers
import DirectiveNames

namespace PegHs.AssembleValidation

inductive Top where
  | directive (name arg : String)
  | annotation (name : String) (templateParams : List String)
  | annotationWithParams (name : String) (templateParams params : List String)
  | definition (name : String) (templateNames : List String)
  | definitionWithBindings (name : String) (templateNames bindings : List String)
  | verbatim
  deriving BEq

def directives (tops : List Top) : List (String × String) := tops.filterMap fun
  | .directive n a => some (n, a)
  | _ => none

def annotations (tops : List Top) : List (String × List String) := tops.filterMap fun
  | .annotation n ps => some (n, ps)
  | .annotationWithParams n ps _ => some (n, ps)
  | _ => none

def definitions (tops : List Top) : List (String × List String) := tops.filterMap fun
  | .definition n ps => some (n, ps)
  | .definitionWithBindings n ps _ => some (n, ps)
  | _ => none

def known : List String :=
  ["module", "start", "entry", "export", "env", "tabstop", "nomemo",
   "language", "syntax", "token", "trivia", "inline", "recover", "safe",
   "deriving", "expect", "message", "import", "library"]

def args (ds : List (String × String)) (name : String) : List String :=
  (ds.filter (fun d => d.1 == name)).map (·.2)

def modulePresent (tops : List Top) : Bool :=
  (directives tops).any fun d => d.1 == "module" || d.1 == "library"

-- Haskell's finite predicate/splitter functions are pinned by the checker.
-- No diagnostic list is supplied by the caller.
structure Predicates where
  validIdent : String → Bool
  validModule : String → Bool
  validExport : String → Bool
  validClass : String → Bool
  isDigit : Char → Bool
  words : String → List String
  reservedBinder : String → Bool

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

def stringResults (p : Predicates) (ds : List (String × String)) (n : String) :
    List (Except String String) :=
  (args ds n).filterMap fun a => if a.isEmpty then none else
    some (AssembleValidationHelpers.stringArg p.validIdent n a)

def parseFailures (rs : List (Except String String)) : List String := rs.filterMap fun
  | .error e => some e
  | .ok _ => none

def parsedNames (rs : List (Except String String)) : List String := rs.filterMap fun
  | .error _ => none
  | .ok n => some n

def otherViolations (tops : List Top) (p : Predicates) : List Violation := Id.run do
  let ds := directives tops
  let imports := args ds "import"
  let library := ds.any fun d => d.1 == "library"
  let strings := stringResults p ds "expect" ++ stringResults p ds "message"
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
      !a.isEmpty && match p.words a with
        | [lab, rule] => !(p.validIdent lab && p.validIdent rule)
        | _ => true) ++
    emit .invalidLanguage (((args ds "language").flatMap AssembleValidationHelpers.splitExports).filter
      (fun x => !DirectiveNames.validExtension x)) ++
    emit .invalidModule ((args ds "module").filter
      (fun x => !x.isEmpty && !p.validModule x)) ++
    emit .invalidExport (((args ds "export").flatMap AssembleValidationHelpers.splitExports).filter
      (fun x => !p.validExport x)) ++
    emit .invalidDeriving (((args ds "deriving").flatMap AssembleValidationHelpers.splitExports).filter
      (fun x => !p.validClass x)) ++
    emit .invalidString (parseFailures strings) ++
    emit .duplicateString (repeated (parsedNames (stringResults p ds "expect")) ++
      repeated (parsedNames (stringResults p ds "message"))) ++
    emit .invalidSafe ((args ds "safe").filter
      (fun x => !x.isEmpty && !p.validIdent x)) ++
    emit .invalidRuleName ((ds.filter (fun d =>
      ["start", "entry", "nomemo", "token", "trivia", "inline"].contains d.1 &&
      !d.2.isEmpty && !p.validIdent d.2)).map (·.1)) ++
    emit .invalidTabstop (match (args ds "tabstop").head? with
      | none => []
      | some x => if x.isEmpty || !(x.toList.all p.isDigit) ||
          x.toList.all (· == '0') then [x] else []) ++
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

-- The model's input projects TAnnot.params and all recursively nested TDef
-- item bindings. A general extractor for this projection is not yet proved.
-- Haskell's binderKeyword predicate is pinned by the checker and probed.
def binderViolations (tops : List Top) (p : Predicates) : List Violation :=
  emit .reservedParameter ((tops.flatMap fun
    | .annotationWithParams _ _ params => params
    | _ => []).filter p.reservedBinder) ++
  emit .reservedBinding ((tops.flatMap fun
    | .definitionWithBindings _ _ bindings => bindings
    | _ => []).filter p.reservedBinder)

def violations (tops : List Top) (p : Predicates) : List Violation :=
  otherViolations tops p ++ structuralViolations tops ++ binderViolations tops p

-- The exact wording and locations remain in Haskell. A distinct nonempty
-- diagnostic is constructed for each violation solely for rejection proofs.
def diagnostic (v : Violation) : String := toString (repr v.kind) ++ ":" ++ v.subject

def errors (tops : List Top) (p : Predicates) : List String :=
  (violations tops p).map diagnostic

def assemble (tops : List Top) (p : Predicates) : Except (List String) Unit :=
  match errors tops p with
  | [] => if modulePresent tops then .ok () else .error ["missing %module directive"]
  | es@(_ :: _) => .error es

theorem errors_nonempty_iff_violation (tops : List Top) (p : Predicates) :
    errors tops p ≠ [] ↔ ∃ v, v ∈ violations tops p := by
  cases h : violations tops p with
  | nil => simp [errors, h]
  | cons v rest =>
    constructor
    · intro _
      exact ⟨v, by simp⟩
    · intro _ eq
      unfold errors at eq
      rw [h] at eq
      simp at eq

theorem assemble_failure_nonempty (tops : List Top) (p : Predicates)
    (ds : List String) (h : assemble tops p = .error ds) : ds ≠ [] := by
  cases he : errors tops p with
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

theorem assemble_failure_iff_violation_or_missing_module (tops : List Top)
    (p : Predicates) :
    (∃ ds, assemble tops p = .error ds) ↔
      (∃ v, v ∈ violations tops p) ∨ modulePresent tops = false := by
  cases he : errors tops p with
  | nil =>
    have hv : ¬∃ v, v ∈ violations tops p := by
      intro h
      exact (errors_nonempty_iff_violation tops p).2 h he
    cases hm : modulePresent tops <;> simp [assemble, he, hm, hv]
  | cons d rest =>
    have hv : ∃ v, v ∈ violations tops p :=
      (errors_nonempty_iff_violation tops p).1 (by simp [he])
    simp [assemble, he, hv]

theorem structural_violation_rejected (tops : List Top) (p : Predicates)
    (v : Violation) (h : v ∈ structuralViolations tops) :
    ∃ ds, assemble tops p = .error ds ∧ ds ≠ [] := by
  have hv : ∃ x, x ∈ violations tops p :=
    ⟨v, by simp [violations, h]⟩
  obtain ⟨ds, hd⟩ := (assemble_failure_iff_violation_or_missing_module tops p).2
    (Or.inl hv)
  exact ⟨ds, hd, assemble_failure_nonempty tops p ds hd⟩

theorem binder_violation_rejected (tops : List Top) (p : Predicates)
    (v : Violation) (h : v ∈ binderViolations tops p) :
    ∃ ds, assemble tops p = .error ds ∧ ds ≠ [] := by
  have hv : ∃ x, x ∈ violations tops p :=
    ⟨v, by simp [violations, h]⟩
  obtain ⟨ds, hd⟩ := (assemble_failure_iff_violation_or_missing_module tops p).2
    (Or.inl hv)
  exact ⟨ds, hd, assemble_failure_nonempty tops p ds hd⟩

theorem reserved_parameter_rejected (p : Predicates)
    (h : p.reservedBinder "case" = true) :
    ∃ ds, assemble [.directive "module" "M",
      .annotationWithParams "P" [] ["case"], .definition "P" []]
      p = .error ds ∧ ds ≠ [] := by
  apply binder_violation_rejected _ p ⟨.reservedParameter, "case"⟩
  simp [binderViolations, h, emit]

theorem reserved_binding_rejected (p : Predicates)
    (h : p.reservedBinder "case" = true) :
    ∃ ds, assemble [.directive "module" "M",
      .definitionWithBindings "S" [] ["case"]]
      p = .error ds ∧ ds ≠ [] := by
  apply binder_violation_rejected _ p ⟨.reservedBinding, "case"⟩
  simp [binderViolations, h, emit]

theorem duplicate_definition_rejected (p : Predicates) :
    ∃ ds, assemble [.directive "module" "M", .definition "S" [], .definition "S" []]
      p = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ p ⟨.duplicateDefinition, "S"⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem orphan_annotation_rejected (p : Predicates) :
    ∃ ds, assemble [.directive "module" "M", .annotation "S" []]
      p = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ p ⟨.orphanAnnotation, "S"⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem duplicate_annotation_rejected (p : Predicates) :
    ∃ ds, assemble [.directive "module" "M", .annotation "S" [],
      .annotation "S" [], .definition "S" []]
      p = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ p ⟨.duplicateAnnotation, "S"⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem no_rules_rejected (p : Predicates) :
    ∃ ds, assemble [.directive "module" "M"] p = .error ds ∧ ds ≠ [] := by
  apply structural_violation_rejected _ p ⟨.noRules, ""⟩
  simp [structuralViolations, definitions, annotations, repeated, repeated.go,
    emit, modulePresent, directives]

theorem missing_module_rejected (p : Predicates) :
    ∃ ds, assemble [.definition "S" []] p = .error ds ∧ ds ≠ [] := by
  have hm : modulePresent [.definition "S" []] = false := by decide
  obtain ⟨ds, hd⟩ := (assemble_failure_iff_violation_or_missing_module _ p).2
    (Or.inr hm)
  exact ⟨ds, hd, assemble_failure_nonempty _ p ds hd⟩

def parseGrammar (parseTops : Except (List String) (List Top))
    (p : Predicates) : Except (List String) Unit :=
  match parseTops with
  | .error ds => .error ds
  | .ok tops => assemble tops p

theorem public_assemble_failure (tops : List Top) (p : Predicates)
    (ds : List String) (ha : assemble tops p = .error ds)
    (resolve expand : Unit → Except (List String) Unit)
    (check : Unit → Except (List String) Unit)
    (notes : Unit → List String → List String)
    (strip : Option (Unit → Unit)) (warningFor : Unit → Unit → List String)
    (generate : Unit → Except (List String) String) :
    PegHs.Pipeline.visible (PegHs.Pipeline.pipeline
      (parseGrammar (.ok tops) p) resolve expand check notes strip warningFor generate) =
      .error ds ∧ ds ≠ [] := by
  have hp : parseGrammar (.ok tops) p = .error ds := by
    rw [parseGrammar]
    exact ha
  constructor
  · rw [hp]
    exact PegHs.Pipeline.invariant2_parseFailure ds resolve expand check notes strip
      warningFor generate
  · exact assemble_failure_nonempty tops p ds ha

#print axioms PegHs.AssembleValidation.assemble_failure_iff_violation_or_missing_module
#print axioms PegHs.AssembleValidation.reserved_parameter_rejected
#print axioms PegHs.AssembleValidation.reserved_binding_rejected
#print axioms PegHs.AssembleValidation.public_assemble_failure

end PegHs.AssembleValidation
