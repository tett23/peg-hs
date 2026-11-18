import PublicPremises
import CertifiedPublicFiles

/-!
Concrete `Inputs` whose `Premises` hold, applied to the two metagrammars
(ADR 0097): with `metaInputs`, `parse` accepts Peg.hpeg and PegSyntax.hpeg
(`metaInputs_peg`, `metaInputs_syntax`), so the public theorems that take
`Premises metaInputs` have instances on both files.

`baseInputs` fixes every unmodelled function to a constant; `metaInputs` is
`modelInputs baseInputs` (PublicPremises), whose `expand` is the template
expansion model and whose `assemblyErrors` are the errors of the
AssembleValidation model. The derivation of each file is the certificate of
CertifiedPublicFiles (`invariant1_public_peg`, and
`invariant1_public_syntax_as_peg` for PegSyntax.hpeg, which parseTops reads
with the Peg grammar; CheckItemSources ties that source to the file).
-/

namespace PegHs.PublicGeneration

open PegHs.LabelCheck (Loc)

def loc0 : Loc := ⟨0, 0, 0⟩

def emptyGrammar (m : Loc × String) : Grammar where
  module := m
  library := none
  imports := []
  start := none
  entries := []
  noMemo := []
  languages := []
  syntaxLoc := none
  tokens := []
  trivia := []
  inline := []
  recovers := []
  safe := []
  expects := []
  messages := []
  verbatim := []
  rules := []

def baseInputs : Inputs Unit where
  value _ _ := ()
  failure _ := "parse error"
  assemblyErrors _ := []
  moduleName _ := some (loc0, "M")
  build _ m := emptyGrammar m
  missingModule := "missing %module directive"
  diagLoc _ := loc0
  view _ := [.directive "module" "M", .definition "S" [] []]
  libraryRoot := ""
  directiveNames _ := []
  libraryText _ := none
  hasLibraryDirective _ := false
  inFile _ d := d
  relocate _ r := r
  noSuchFile _ p := p
  notALibrary _ p := p
  refs _ := []
  duplicate r := r.name
  expand g := .ok g
  env := ⟨fun _ => [], fun _ _ => ""⟩
  classify _ := []
  templateDiag _ := "template"
  note _ d := d
  oracle _ := ⟨⟨[], [], [], []⟩, fun _ _ => [], fun _ => false, id⟩
  diag d := d.msg
  strip := none
  source := []
  output := []
  upper _ := true
  alphaNum _ := true
  missing _ _ := []
  render _ _ _ := ""
  shown := ""

noncomputable def metaInputs : Inputs Unit := modelInputs baseInputs

theorem metaInputs_premises : Premises metaInputs := modelInputs_premises baseInputs

theorem module_view_accepted :
    AssembleValidation.assemble [.directive "module" "M", .definition "S" [] []] = .ok () := by rfl

-- A file that parseTops accepts is parsed by `parse metaInputs`.
theorem metaInputs_parse (input : List Char)
    (accepted : MetaExecution.parseFile false (String.ofList input) (fun _ => "") = .ok ()) :
    ∃ g, parse metaInputs input = .ok g := by
  rw [MetaExecution.invariant1_parseFile_entry] at accepted
  obtain ⟨env, result⟩ := (FileEntry.invariant1_public_entry
    (MetaExecution.recognizeFile false (String.ofList input).toList).property _).mp accepted
  rw [String.toList_ofList] at result
  obtain ⟨ts, hts⟩ := (FileTops.invariant1_parsesTo_iff metaInputs.value input).mpr ⟨env, result⟩
  have errors : metaInputs.assemblyErrors ts = [] := by
    simp only [metaInputs, modelInputs_assemblyErrors, checkedErrors]
    simp only [baseInputs, module_view_accepted]
  have name : metaInputs.moduleName ts = some (loc0, "M") := by
    simp only [metaInputs, modelInputs]
    rfl
  exact ⟨_, (invariant1_parse_iff metaInputs input _).mpr ⟨ts, _, hts, errors, name, rfl⟩⟩

theorem metaInputs_peg :
    Premises metaInputs ∧ ∃ g, parse metaInputs MetaPieces.Peg.source = .ok g :=
  ⟨metaInputs_premises, metaInputs_parse _ (MetaExecution.invariant1_public_peg _)⟩

theorem metaInputs_syntax :
    Premises metaInputs ∧ ∃ g, parse metaInputs MetaPieces.SyntaxAsPeg.source = .ok g :=
  ⟨metaInputs_premises, metaInputs_parse _ (MetaExecution.invariant1_public_syntax_as_peg _)⟩

end PegHs.PublicGeneration

#print axioms PegHs.PublicGeneration.metaInputs_peg
#print axioms PegHs.PublicGeneration.metaInputs_syntax
