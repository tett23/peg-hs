import FileTops
import SelfHostedRuntime
import PublicEntryProof
import AssembleValidation
import AssembleTranslatedProof
import ImportResolution
import TemplateExpansionWhole
import TemplateQueue
import LabelCheckTheorems
import CheckGroupsTheorems
import InnerGeneration
import RenderFinalize

/-!
The public entries of peg-codegen, `generateWithWarnings` and `generate`
(packages/peg-codegen/src/Peg/Codegen.hs), with the stages of the earlier
modules in place of the abstract arguments of Pipeline.pipeline and
InnerGeneration.innerGenerate (ADR 0097 invariants 1 to 3).

`Grammar` is the grammar that the stages pass on. Its expressions, items and
locations are those of LabelCheckModel, which CheckGroupsModel also uses, and
its fields are the fields that one of the stage models reads or writes. Each
stage model reads a view of it:
- `toLabel` is the grammar of LabelCheckModel (`labelWarnings`,
  `stripLabelsAs`), and `stripAs` is `stripLabelsAs` on `Grammar`
  (`toLabel_stripAs`);
- `toCheck` is the grammar of CheckGroupsModel (`check`);
- `toTemplate` is the grammar of TemplateExpansionWhole, with a location
  `Loc f l c` written `l * 100000 + c` as in its probe;
- ImportResolution takes the rules of `Grammar` as its rules, and `resolve`
  puts the merged rules back into the root grammar
  (`Right root {grammarRules = ...}`).

The stages, in the order of Codegen's `generateWithWarnings`:
- `parse`: `parseGrammar src = parseTops src >>= assemble`, the checked
  translation of PublicParsing (TranslatedEntry, translate-public-entry.awk)
  applied to the start result of the File rule run on the translated runtime
  (`SelfHostedRuntime.runtimeStart`), and the translation of `assemble` from
  GHC's syntax tree (AssembleTranslated, TranslateHaskell.hs).
  `invariant1_runtimeStart_eq` shows that the start result is the
  `startTops` of FileTops for the derivation's reply;
- `resolve`: ImportResolution.resolve, with `lookupLibrary` reading each
  library with the same `tops` and `assembleTops` as `parse` and with
  `libraryErrors` (Import.libraryErrors);
- `Inputs.expand`: `expandTemplates` (see the premises);
- `checkStage`: CheckGroups.check;
- `notes`: TemplateQueue.templateNotes;
- `stripAs` and `warningFor`: LabelCheck.stripLabelsAs and labelWarnings;
- `inner`: InnerGeneration.innerGenerate with InnerGeneration's file-name and
  module-name guards, the same expand, check and notes, `selectMarker`
  (Pragmas) for `freshRestoreMarker`, and RenderFinalize.finalize.

check-pipeline.sh, check-inner-generation.sh, check-assemble-validation.sh,
check-public-parsing.sh and check-import-resolution.sh fix the Haskell that
joins the stages; check-public-generation.sh fixes `generateFromSource`,
the `Generation` record that `generateWithWarnings` returns and
Import.libraryErrors.

Theorems:
- `invariant2_generateWithWarnings`, `invariant2_generate`,
  `invariant2_generateFromSource`: a rejection carries at least one
  diagnostic, and every input gives a diagnostic list or a module text.
- `invariant2_check_rejects_public`, `invariant2_group_error_public`,
  `invariant2_undefined_reference_public`: when `check` rejects the expanded
  grammar (an error of one of its groups, such as a reference to an
  undefined rule), the public entry returns at least one diagnostic and no
  module text.
- `invariant1_generateWithWarnings`: a module text implies that parseTops
  derived the whole input (FileTops.ParsesTo), that the translated assemble
  accepted its items, and that the assemble model accepts their view
  (AssembleTranslatedProof.assemble_agrees); `invariant1_parse_iff` is the
  stage itself.
- `invariant3_generateWithWarnings_text`: a module text is
  `finalize shown marker (render g a marker)` for the expanded, checked
  target grammar, with the marker that selectMarker picks from the first
  render; the target has no template, no template call and no reference to
  a template (TemplateExpansionWhole.Accepted), and `check` accepts it.
  PublicGenerationGHC carries this text to GHC's module grammar.

Premises (the fields of `Inputs` and `Premises`, not proved here):
- `Premises.expandRefines`: the Haskell `expandTemplates` on `Grammar`
  refines the model on the view: on the template view of a grammar, the
  model's result (`ExpandTemplates`, which exists and is unique) is the view
  of the Haskell result, and a rejection's diagnostics are the model's,
  rendered. TemplateExpansionWholeProbe compares the two on parsed grammars.
  The fields of `Grammar` that the view drops are not constrained.
- Unmodelled functions, taken as parameters: the diagnostic texts
  (`Inputs.failure`, `Inputs.diag`, `Inputs.templateDiag`,
  `Inputs.diagText`), the view of the grammar that the translated `assemble`
  builds (`Inputs.grammar`), the Haskell `Top` items of the parsed items
  (`Inputs.items`), the functions of resolveImports that ImportResolution takes as
  inputs, `classify` (`oracle`, `classify`), `undefinedExports` (`missing`),
  `render` and the value of each top item (`value`). Pipeline models
  `[Diagnostic]` as a list of strings, so the stage models' diagnostics are
  rendered by `diag`, `templateDiag` and `diagText`. public-hypotheses.allow lists each
  with the reason that permits it; PublicHypotheses.lean reads them from the
  types of the public theorems.
- The premises of the stage modules that these theorems use. The premises of
  ImportResolution about the libraries are proved here
  (`lookupLibrary_parse_nonempty`, `lookupLibrary_assemble_nonempty`).

PublicPremises shows that `Premises` can be met (`modelInputs_premises`), and
PublicPremisesMeta applies it to Peg.hpeg and PegSyntax.hpeg.
-/

namespace PegHs.PublicGeneration

open PegHs.LabelCheck (Loc Expr Item)

abbrev Diagnostics := PegHs.Pipeline.Diagnostics

/-! ## The grammar between the stages -/

structure Alt where
  loc : Loc
  items : List Item
  action : Option (Loc × String)
  constructor : Option (Loc × String)

structure Rule where
  name : String
  loc : Loc
  params : List (String × String)
  templateParams : List (String × Option String)
  type : String
  annotation : Option Loc
  alts : List Alt

structure Grammar where
  module : Loc × String
  library : Option Loc
  imports : List (Loc × String)
  start : Option (Loc × String)
  entries : List (Loc × String)
  noMemo : List (Loc × String)
  languages : List (Loc × String)
  syntaxLoc : Option Loc
  tokens : List (Loc × String)
  trivia : List (Loc × String)
  inline : List (Loc × String)
  recovers : List ((Loc × String) × (Loc × String))
  safe : List (Loc × String)
  expects : List ((Loc × String) × (Loc × String))
  messages : List ((Loc × String) × (Loc × String))
  verbatim : List (Loc × String)
  rules : List Rule

/-! ## The views of the stage models -/

def Alt.toLabel (a : Alt) : LabelCheck.Alt := ⟨a.loc, a.items, []⟩

def Rule.toLabel (r : Rule) : LabelCheck.Rule :=
  ⟨r.name, r.params.map (·.1), r.alts.map Alt.toLabel, []⟩

def toLabel (g : Grammar) : LabelCheck.Grammar :=
  ⟨g.module, g.start, g.entries, g.recovers, g.safe, g.messages, g.rules.map Rule.toLabel, []⟩

def Alt.toCheck (a : Alt) : CheckGroups.Alt := ⟨a.loc, a.items, a.action, a.constructor⟩

def Rule.toCheck (r : Rule) : CheckGroups.Rule :=
  ⟨r.name, r.loc, r.params.map (·.1), r.templateParams.length, r.annotation,
    r.alts.map Alt.toCheck⟩

def toCheck (g : Grammar) : CheckGroups.Grammar where
  library := g.library
  start := g.start
  entries := g.entries
  noMemo := g.noMemo
  languages := g.languages
  syntaxLoc := g.syntaxLoc
  tokens := g.tokens
  trivia := g.trivia
  inline := g.inline
  recovers := g.recovers
  safe := g.safe
  expects := g.expects
  messages := g.messages
  verbatim := g.verbatim
  rules := g.rules.map Rule.toCheck

-- The location of TemplateExpansionWhole, as its probe writes `Loc f l c`.
def locNat (l : Loc) : Nat := l.line * 100000 + l.col

def located (p : Loc × String) : Nat × String := (locNat p.1, p.2)

mutual
def exprT : Expr → TemplateSubstitution.Expr
  | .lit t w => .lit t w
  | .cls _ w => .charClass w
  | .any => .any
  | .ref l n args => .ref (locNat l) n (args.map (·.2))
  | .group alts => .group (altsT alts)
  | .star x => .star (exprT x)
  | .plus x => .plus (exprT x)
  | .opt x => .opt (exprT x)
  | .and x => .and (exprT x)
  | .not x => .not (exprT x)
  | .capture x => .capture (exprT x)
  | .label l x n => .label (locNat l) (exprT x) n
  | .pred b c => .predicate b c.2
  | .template l n as vs => .template (locNat l) n (listT as) (vs.map (·.2))
  | .discard x => .discard (exprT x)
termination_by e => sizeOf e

def itemsT : List Item → List (Option String × TemplateSubstitution.Expr)
  | [] => []
  | (_, b, e) :: is => (b, exprT e) :: itemsT is
termination_by is => sizeOf is

def altsT : List (List Item) → List (List (Option String × TemplateSubstitution.Expr))
  | [] => []
  | a :: as => itemsT a :: altsT as
termination_by as => sizeOf as

def listT : List Expr → List TemplateSubstitution.Expr
  | [] => []
  | e :: es => exprT e :: listT es
termination_by es => sizeOf es
end

def Rule.toTemplate (r : Rule) : TemplateExpansionWhole.Rule where
  name := r.name
  location := locNat r.loc
  params := r.params
  templateParams := r.templateParams
  type := r.type
  alts := r.alts.map fun a => { items := itemsT a.items, action := a.action.map (·.2) }

def toTemplate (g : Grammar) : TemplateExpansionWhole.Grammar where
  rules := g.rules.map Rule.toTemplate
  start := g.start.toList.map located
  entries := g.entries.map located
  recovers := g.recovers.map (fun p => located p.2)
  nomemo := g.noMemo.map located
  tokens := g.tokens.map located
  trivia := g.trivia.map located
  inline := g.inline.map located
  expects := g.expects.map (fun p => located p.1)
  syntaxMode := g.syntaxLoc.isSome

/-! ## stripLabelsAs on the grammar -/

def stripAs (m : String) (g : Grammar) : Grammar :=
  { g with
    module := (g.module.1, m)
    recovers := []
    safe := []
    messages := []
    entries := g.entries ++ LabelCheck.recoveryEntries (toLabel g)
    rules := g.rules.map fun r =>
      { r with alts := r.alts.map fun a => { a with items := LabelCheck.stripItems a.items } } }

theorem toLabel_stripAs (m : String) (g : Grammar) :
    toLabel (stripAs m g) = LabelCheck.stripLabelsAs m (toLabel g) := by
  simp [toLabel, stripAs, LabelCheck.stripLabelsAs, LabelCheck.stripLabels, Rule.toLabel,
    Alt.toLabel, Function.comp_def]

/-! ## The inputs of the stages -/

-- The order of `diagLoc`: the derived `Ord` of `Loc` (file, line, column).
def locGt (a b : Loc) : Bool :=
  decide (a.file > b.file ∨ (a.file = b.file ∧ (a.line > b.line ∨
    (a.line = b.line ∧ a.col > b.col))))

structure Inputs (T : Type) where
  -- parseTops: the value of each top item and the text of a failure.
  value : FileTops.Kind → Nat → T
  failure : PublicParsing.Failure → String
  -- assemble (translated): the Haskell `Top` items of the parsed items, the
  -- text of a diagnostic, the view of the grammar it builds, and the
  -- location of a diagnostic text (resolveImports sorts by it).
  items : List T → List AssembleTranslated.Top
  diagText : AssembleTranslated.Diagnostic → String
  grammar : AssembleTranslated.Grammar → Grammar
  diagLoc : String → Loc
  -- resolveImports (ImportResolution's inputs). A library is read by
  -- `lookupLibrary` below from its text, `lookup p texts`.
  libraryRoot : String
  directiveNames : Grammar → List String
  libraryText : String → Option (List Char)
  hasLibraryDirective : List T → Bool
  inFile : Nat → String → String
  relocate : Nat → Rule → Rule
  noSuchFile : Loc → String → String
  notALibrary : Loc → String → String
  refs : Rule → List String
  duplicate : Rule → String
  -- expandTemplates and templateNotes.
  expand : Grammar → Except Diagnostics Grammar
  env : TemplateExpansionWhole.Env
  classify : TemplateExpansionWhole.Grammar → TemplateExpansionWhole.Known
  templateDiag : TemplateSubstitution.Diagnostic → String
  note : Grammar → String → String
  -- check and labelWarnings.
  oracle : Grammar → CheckGroups.Oracle
  diag : LabelCheck.Diagnostic → String
  -- The options of generate and the functions after check.
  strip : Option String
  source : List Nat
  output : List Nat
  upper : Char → Bool
  alphaNum : Char → Bool
  missing : Grammar → CheckGroups.Analysis → List String
  render : Grammar → CheckGroups.Analysis → String → String
  shown : String

variable {T : Type}

/-! ## The stages -/

-- assemble on the parsed items: the translation of `Assemble.hs`.
def assembleTops (s : Inputs T) (t : List T) : Except Diagnostics Grammar :=
  match AssembleTranslated.assemble (s.items t) with
  | .ok g => .ok (s.grammar g)
  | .error ds => .error (ds.map s.diagText)

noncomputable def parse (s : Inputs T) (input : List Char) : Except Diagnostics Grammar :=
  PublicParsing.translatedGrammar input.utf8Encode.size
    (SelfHostedRuntime.runtimeStart s.value input) s.failure (assembleTops s)

-- The view of the items that AssembleValidation reads.
def view (s : Inputs T) (ts : List T) : List AssembleValidation.Top :=
  AssembleTranslatedProof.view (s.items ts)

-- `(<=)` on `diagLoc`, the order of resolveImports' `sortOn diagLoc`, with the derived
-- order of `Loc` (check-public-generation.sh fixes it).
def locationLE (s : Inputs T) (a b : String) : Bool := !locGt (s.diagLoc a) (s.diagLoc b)

-- parseTops and assemble, the two halves of `parse`
-- (`parse s input = (tops s input).bind (assembleTops s)`, `parse_tops`).
noncomputable def tops (s : Inputs T) (input : List Char) : Except Diagnostics (List T) :=
  PublicParsing.translatedPublic s.failure (PublicParsing.translatedRuntime input.utf8Encode.size
    (SelfHostedRuntime.runtimeStart s.value input))

theorem assembleTops_ok_iff (s : Inputs T) (t : List T) (g : Grammar) :
    assembleTops s t = .ok g ↔ ∃ tg, AssembleTranslated.assemble (s.items t) = .ok tg ∧ s.grammar tg = g := by
  unfold assembleTops
  split <;> simp_all

theorem parse_tops (s : Inputs T) (input : List Char) :
    parse s input = (tops s input).bind (assembleTops s) := rfl

def checkStage (s : Inputs T) (g : Grammar) : Except Diagnostics CheckGroups.Analysis :=
  match CheckGroups.check (toCheck g) (s.oracle g) with
  | .error ds => .error (ds.map s.diag)
  | .ok a => .ok a

def notes (s : Inputs T) (g0 : Grammar) : Diagnostics → Diagnostics :=
  TemplateQueue.templateNotes (s.note g0)

-- Import.libraryErrors: `templateNotes g (either id checkLibrary (expandTemplates g))`.
def libraryErrors (s : Inputs T) (g : Grammar) : Diagnostics :=
  notes s g (match s.expand g with
    | .error ds => ds
    | .ok h => (CheckGroups.checkLibrary (toCheck h) (s.oracle h)).map s.diag)

-- The local `library i (Located l p)` of resolveImports before it relocates
-- anything: `lookup p texts`, parseTops, the `%library` check, assemble and
-- libraryErrors.
noncomputable def lookupLibrary (s : Inputs T) (p : String) : ImportResolution.Library String Rule :=
  match s.libraryText p with
  | none => .noText
  | some text =>
    match tops s text with
    | .error ds => .parseError ds
    | .ok ts =>
      if s.hasLibraryDirective ts then
        match assembleTops s ts with
        | .error ds => .assemblyError ds
        | .ok g => .assembled (libraryErrors s g) g.rules
      else .notLibrary

noncomputable def resolve (s : Inputs T) (g : Grammar) : Except Diagnostics Grammar :=
  match ImportResolution.resolve g.library.isSome s.libraryRoot g.rules (s.directiveNames g)
      g.imports (lookupLibrary s) s.inFile s.relocate s.noSuchFile s.notALibrary (locationLE s)
      Rule.name (fun r => r.loc.file) s.refs s.duplicate with
  | .error ds => .error ds
  | .ok rs => .ok { g with rules := rs }

noncomputable def warningFor (s : Inputs T) (g0 g : Grammar) : Diagnostics :=
  notes s g0 ((LabelCheck.labelWarnings (toLabel g)).map s.diag)

def finalizeStage (s : Inputs T) (marker text : String) : String :=
  RenderFinalize.finalize s.shown marker text

-- Codegen.generate opts g0.
def inner (s : Inputs T) (g0 : Grammar) : Except Diagnostics String :=
  InnerGeneration.innerGenerate (InnerGeneration.fileNameBad s.source s.output)
    (InnerGeneration.moduleNameValid s.upper s.alphaNum g0.module.2) g0.module.2 g0
    s.expand (checkStage s) (notes s) s.missing s.render Peg.Verification.selectMarker
    (finalizeStage s)

-- The grammar that generateWithWarnings generates: `maybe g (`stripLabelsAs` g) strip`.
def target (s : Inputs T) (g : Grammar) : Grammar :=
  match s.strip.map stripAs with
  | none => g
  | some change => change g

-- Codegen.generateWithWarnings opts strip libraries src.
noncomputable def generateWithWarnings (s : Inputs T) (input : List Char) :
    Except Diagnostics (Pipeline.Generation Grammar) :=
  Pipeline.pipeline (parse s input) (resolve s) s.expand
    (fun g => (checkStage s g).map (fun _ => ())) (notes s) (s.strip.map stripAs)
    (warningFor s) (inner s)

-- What the CLI writes: the diagnostics, or the module after
-- `generationModule` is evaluated.
noncomputable def publicModule (s : Inputs T) (input : List Char) : Except Diagnostics String :=
  Pipeline.visible (generateWithWarnings s input)

-- Codegen.generateFromSource opts src: no library, no strip, no warning.
noncomputable def generateFromSource (s : Inputs T) (input : List Char) : Except Diagnostics String :=
  ((parse s input).bind (resolve s)).bind (inner s)

/-! ## Premises -/

-- The relation of the model's result to the result on `Grammar`.
def Refines (s : Inputs T) :
    Except (List TemplateSubstitution.Diagnostic) TemplateExpansionWhole.Grammar →
      Except Diagnostics Grammar → Prop
  | .error ds, .error es => es = ds.map s.templateDiag
  | .ok g', .ok h => toTemplate h = g'
  | _, _ => False

structure Premises (s : Inputs T) : Prop where
  expandRefines : ∀ g, ∃ r, TemplateExpansionWhole.ExpandTemplates s.env s.classify (toTemplate g) r ∧
    Refines s r (s.expand g)

/-! ## Each stage: a rejection carries a diagnostic -/

theorem parse_error_nonempty (s : Inputs T) (input : List Char) (ds : Diagnostics)
    (h : parse s input = .error ds) : ds ≠ [] := by
  unfold parse PublicParsing.translatedGrammar at h
  rw [SelfHostedRuntime.invariant1_runtimeStart_eq] at h
  cases hr : PublicParsing.translatedRuntime input.utf8Encode.size
      (FileTops.startTops s.value input (MetaExecution.recognizeFile false input).val) with
  | error e =>
    rw [hr] at h
    simp [PublicParsing.translatedPublic, Except.bind] at h
    rw [← h]
    simp
  | ok t =>
    rw [hr] at h
    simp only [PublicParsing.translatedPublic, Except.bind] at h
    unfold assembleTops at h
    split at h
    · cases h
    · rename_i es he
      cases h
      have := AssembleTranslatedProof.assemble_error_nonempty _ es he
      simpa using this

theorem tops_error_nonempty (s : Inputs T) (input : List Char) (ds : Diagnostics)
    (h : tops s input = .error ds) : ds ≠ [] := by
  unfold tops at h
  rw [SelfHostedRuntime.invariant1_runtimeStart_eq] at h
  cases hr : PublicParsing.translatedRuntime input.utf8Encode.size
      (FileTops.startTops s.value input (MetaExecution.recognizeFile false input).val) with
  | error e =>
    rw [hr] at h
    simp [PublicParsing.translatedPublic] at h
    rw [← h]
    simp
  | ok t =>
    rw [hr] at h
    simp [PublicParsing.translatedPublic] at h

theorem assembleTops_error_nonempty (s : Inputs T) (t : List T) (ds : Diagnostics)
    (h : assembleTops s t = .error ds) : ds ≠ [] := by
  unfold assembleTops at h
  split at h
  · cases h
  · rename_i es he
    cases h
    have := AssembleTranslatedProof.assemble_error_nonempty _ es he
    simpa using this

-- The premises of ImportResolution about the libraries hold: a library that
-- parseTops or assemble rejects carries a diagnostic.
theorem lookupLibrary_parse_nonempty (s : Inputs T) (p : String) (ds : Diagnostics)
    (h : lookupLibrary s p = .parseError ds) : ds ≠ [] := by
  unfold lookupLibrary at h
  split at h
  · cases h
  · split at h
    · cases h; exact tops_error_nonempty s _ _ (by assumption)
    · split at h
      · split at h <;> cases h
      · cases h

theorem lookupLibrary_assemble_nonempty (s : Inputs T) (p : String) (ds : Diagnostics)
    (h : lookupLibrary s p = .assemblyError ds) : ds ≠ [] := by
  unfold lookupLibrary at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h; exact assembleTops_error_nonempty s _ _ (by assumption)
        · cases h
      · cases h

theorem resolve_error_nonempty (s : Inputs T) (g : Grammar) (ds : Diagnostics)
    (h : resolve s g = .error ds) : ds ≠ [] := by
  unfold resolve at h
  split at h
  · rename_i es he
    cases h
    exact ImportResolution.invariant2_resolve_error_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (lookupLibrary_parse_nonempty s) (lookupLibrary_assemble_nonempty s) _ he
  · cases h

theorem expand_error_nonempty (s : Inputs T) (p : Premises s) (g : Grammar) (ds : Diagnostics)
    (h : s.expand g = .error ds) : ds ≠ [] := by
  obtain ⟨r, hx, hr⟩ := p.expandRefines g
  rw [h] at hr
  cases r with
  | error tds =>
    have nonempty := (TemplateExpansionWhole.expandTemplates_whole s.env s.classify (toTemplate g)).2.2.1
      tds hx
    simp only [Refines] at hr
    rw [hr]
    simpa using nonempty
  | ok _ => simp [Refines] at hr

theorem expand_ok_accepted (s : Inputs T) (p : Premises s) (g h : Grammar)
    (ok : s.expand g = .ok h) :
    TemplateExpansionWhole.ExpandTemplates s.env s.classify (toTemplate g) (.ok (toTemplate h)) ∧
      TemplateExpansionWhole.Accepted (toTemplate g) (toTemplate h) := by
  obtain ⟨r, hx, hr⟩ := p.expandRefines g
  rw [ok] at hr
  cases r with
  | error _ => simp [Refines] at hr
  | ok g' =>
    simp only [Refines] at hr
    rw [hr]
    exact ⟨hx, (TemplateExpansionWhole.expandTemplates_whole s.env s.classify (toTemplate g)).2.2.2
      g' hx⟩

theorem check_error_nonempty (s : Inputs T) (g : Grammar) (ds : Diagnostics)
    (h : checkStage s g = .error ds) : ds ≠ [] := by
  unfold checkStage at h
  split at h
  · rename_i es he
    cases h
    simpa using CheckGroups.check_error_ne_nil _ _ he
  · cases h

theorem check_ok_iff (s : Inputs T) (g : Grammar) :
    (∃ a, checkStage s g = .ok a) ↔ ∃ a, CheckGroups.check (toCheck g) (s.oracle g) = .ok a := by
  unfold checkStage
  cases CheckGroups.check (toCheck g) (s.oracle g) <;> simp

theorem notes_nonempty (s : Inputs T) (g : Grammar) (ds : Diagnostics) (h : ds ≠ []) :
    notes s g ds ≠ [] :=
  TemplateQueue.invariant2_templateNotes_nonempty _ ds h

/-! ## Invariant 2 at the public entries -/

-- Codegen.generate: a diagnostic list with at least one diagnostic, or a text.
theorem invariant2_generate (s : Inputs T) (p : Premises s) (g : Grammar) :
    (∃ ds, ds ≠ [] ∧ inner s g = .error ds) ∨ (∃ code, inner s g = .ok code) :=
  InnerGeneration.diagnosticOrModule _ _ _ g s.expand (checkStage s) (notes s) s.missing s.render _ _
    (expand_error_nonempty s p g) (check_error_nonempty s) (notes_nonempty s g)

theorem inner_error_nonempty (s : Inputs T) (p : Premises s) (g : Grammar) (ds : Diagnostics)
    (h : inner s g = .error ds) : ds ≠ [] :=
  InnerGeneration.failureNonempty _ _ _ g s.expand (checkStage s) (notes s) s.missing s.render _ _
    (expand_error_nonempty s p g) (check_error_nonempty s) (notes_nonempty s g) ds h

-- Codegen.generateWithWarnings, with `generationModule` evaluated.
theorem invariant2_generateWithWarnings (s : Inputs T) (p : Premises s) (input : List Char) :
    (∃ ds, ds ≠ [] ∧ publicModule s input = .error ds) ∨
      (∃ code, publicModule s input = .ok code) :=
  Pipeline.invariant2_diagnosticOrModule (parse s input) (resolve s) s.expand
    (fun g => (checkStage s g).map (fun _ => ())) (notes s) (s.strip.map stripAs)
    (warningFor s) (inner s)
    (parse_error_nonempty s input) (resolve_error_nonempty s) (expand_error_nonempty s p)
    (fun g ds h => check_error_nonempty s g ds (by
      cases hc : checkStage s g <;> simp [hc, Except.map] at h ⊢; exact h))
    (fun g ds h => notes_nonempty s g ds h) (inner_error_nonempty s p)

theorem invariant2_generateFromSource (s : Inputs T) (p : Premises s) (input : List Char) :
    (∃ ds, ds ≠ [] ∧ generateFromSource s input = .error ds) ∨
      (∃ code, generateFromSource s input = .ok code) := by
  unfold generateFromSource
  cases hp : parse s input with
  | error ds => exact Or.inl ⟨ds, parse_error_nonempty s input ds hp, rfl⟩
  | ok g =>
    cases hr : resolve s g with
    | error ds =>
      exact Or.inl ⟨ds, resolve_error_nonempty s g ds hr, by simp only [Except.bind, hr]⟩
    | ok r =>
      simp only [Except.bind, hr]
      rcases invariant2_generate s p r with ⟨ds, ne, h⟩ | ⟨code, h⟩
      · exact Or.inl ⟨ds, ne, h⟩
      · exact Or.inr ⟨code, h⟩

/-! ## Invariant 2 at the public entry: the rejections of `check` -/

-- When `check` rejects the expanded grammar, the public entry returns at
-- least one diagnostic and no module text.
theorem invariant2_check_rejects_public (s : Inputs T) (input : List Char) (parsed g0 g : Grammar)
    (es : List LabelCheck.Diagnostic) (hp : parse s input = .ok parsed) (hr : resolve s parsed = .ok g0)
    (he : s.expand g0 = .ok g) (hc : CheckGroups.check (toCheck g) (s.oracle g) = .error es) :
    ∃ ds, ds ≠ [] ∧ publicModule s input = .error ds ∧ ¬ ∃ code, publicModule s input = .ok code := by
  have hcs : (fun g => (checkStage s g).map (fun _ => ())) g = .error (es.map s.diag) := by
    simp [checkStage, hc, Except.map]
  have failed := Pipeline.invariant2_checkFailure parsed g0 g (es.map s.diag) (resolve s) s.expand
    (fun g => (checkStage s g).map (fun _ => ())) (notes s) (s.strip.map stripAs) (warningFor s)
    (inner s) hr he hcs
  have visible : publicModule s input = .error (notes s g0 (es.map s.diag)) := by
    unfold publicModule generateWithWarnings
    rw [hp]
    exact failed
  refine ⟨_, notes_nonempty s g0 _ ?_, visible, ?_⟩
  · simpa using CheckGroups.check_error_ne_nil _ _ hc
  · rintro ⟨code, hcode⟩
    rw [visible] at hcode
    cases hcode

-- An error of one of the fifteen groups of `check` (CheckGroups.check_rejects)
-- reaches the public entry.
theorem invariant2_group_error_public (s : Inputs T) (input : List Char) (parsed g0 g : Grammar)
    (hp : parse s input = .ok parsed) (hr : resolve s parsed = .ok g0) (he : s.expand g0 = .ok g)
    {fr : CheckGroups.Rule} {rs : List CheckGroups.Rule} (hl : (toCheck g).library = none)
    (hrules : (toCheck g).rules = fr :: rs) {G : List LabelCheck.Diagnostic}
    (hG : G ∈ CheckGroups.groups (toCheck g) fr (s.oracle g)) {d : LabelCheck.Diagnostic} (hd : d ∈ G) :
    ∃ ds, ds ≠ [] ∧ publicModule s input = .error ds ∧ ¬ ∃ code, publicModule s input = .ok code := by
  obtain ⟨es, hc, _⟩ := CheckGroups.check_rejects (toCheck g) (s.oracle g) hl hrules hG hd
  exact invariant2_check_rejects_public s input parsed g0 g es hp hr he hc

-- A reference to an undefined rule in the expanded grammar (the first group,
-- `undefinedErrors`) reaches the public entry.
theorem invariant2_undefined_reference_public (s : Inputs T) (input : List Char)
    (parsed g0 g : Grammar) (hp : parse s input = .ok parsed) (hr : resolve s parsed = .ok g0)
    (he : s.expand g0 = .ok g) (hl : g.library = none) (hrules : g.rules ≠ [])
    {l : Loc} {n : String} {k : Nat} (href : (l, n, k) ∈ CheckGroups.refs (toCheck g))
    (hundefined : n ∉ CheckGroups.ruleNames (toCheck g)) :
    ∃ ds, ds ≠ [] ∧ publicModule s input = .error ds ∧ ¬ ∃ code, publicModule s input = .ok code := by
  obtain ⟨fr, rs, hfr⟩ : ∃ fr rs, (toCheck g).rules = fr :: rs := by
    cases hg : g.rules with
    | nil => exact absurd hg hrules
    | cons r rs => exact ⟨r.toCheck, rs.map Rule.toCheck, by simp [toCheck, hg]⟩
  have nonempty : CheckGroups.undefinedErrors (toCheck g) ≠ [] := by
    intro empty
    exact hundefined ((CheckGroups.undefinedErrors_nil _).mp empty |>.1 l n k href)
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact invariant2_group_error_public s input parsed g0 g hp hr he (by simp [toCheck, hl]) hfr
    (G := CheckGroups.undefinedErrors (toCheck g)) (by simp [CheckGroups.groups]) hd

/-! ## Invariant 1 at the public entry -/

-- parseGrammar succeeds exactly when parseTops derives the whole input and
-- assemble accepts its items.
theorem invariant1_parse_iff (s : Inputs T) (input : List Char) (g : Grammar) :
    parse s input = .ok g ↔
      ∃ ts tg, FileTops.ParsesTo s.value input ts ∧
        AssembleTranslated.assemble (s.items ts) = .ok tg ∧ s.grammar tg = g := by
  unfold parse
  rw [SelfHostedRuntime.invariant1_runtimeStart_eq, PublicParsing.invariant1_translated_grammar]
  simp only [assembleTops_ok_iff]
  have entry (ts : List T) :
      FileTops.startTops s.value input (MetaExecution.recognizeFile false input).val =
          .ok input.utf8Encode.size ts ↔ FileTops.ParsesTo s.value input ts := by
    rw [← PublicParsing.invariant1_parseTops_iff _ _ s.failure]
    exact FileTops.invariant1_parseTops_value s.value (MetaExecution.recognizeFile false input).property
      s.failure ts
  simp only [entry]
  constructor
  · rintro ⟨ts, hts, tg, ha, hg⟩
    exact ⟨ts, tg, hts, ha, hg⟩
  · rintro ⟨ts, tg, hts, ha, hg⟩
    exact ⟨ts, hts, tg, ha, hg⟩

theorem invariant1_generateWithWarnings (s : Inputs T) (input : List Char)
    (code : String) (success : publicModule s input = .ok code) :
    ∃ ts tg, FileTops.ParsesTo s.value input ts ∧
      AssembleTranslated.assemble (s.items ts) = .ok tg ∧
      AssembleValidation.assemble (s.view ts) = .ok () := by
  unfold publicModule generateWithWarnings at success
  obtain ⟨parsed, _, _, hp, _⟩ := (Pipeline.invariant3_visible_success_iff ..).mp success
  obtain ⟨ts, tg, hts, ha, _⟩ := (invariant1_parse_iff s input parsed).mp hp
  exact ⟨ts, tg, hts, ha, AssembleTranslatedProof.assemble_agrees _ tg ha⟩

-- No derivation of the whole input: one diagnostic and no module.
theorem invariant1_no_derivation (s : Inputs T) (input : List Char)
    (none : ¬ ∃ ts, FileTops.ParsesTo s.value input ts) :
    ∃ ds, ds ≠ [] ∧ publicModule s input = .error ds := by
  cases hp : parse s input with
  | ok g =>
    obtain ⟨ts, _, hts, _⟩ := (invariant1_parse_iff s input g).mp hp
    exact absurd ⟨ts, hts⟩ none
  | error ds =>
    refine ⟨ds, parse_error_nonempty s input ds hp, ?_⟩
    unfold publicModule generateWithWarnings
    rw [hp]
    exact Pipeline.invariant2_parseFailure ..

/-! ## Invariant 3 at the public entry: the text -/

theorem invariant3_generateWithWarnings_text (s : Inputs T) (p : Premises s) (input : List Char)
    (code : String) (success : publicModule s input = .ok code) :
    ∃ parsed resolved g final a,
      parse s input = .ok parsed ∧ resolve s parsed = .ok resolved ∧
      s.expand resolved = .ok g ∧ (∃ a0, checkStage s g = .ok a0) ∧
      InnerGeneration.fileNameBad s.source s.output = false ∧
      InnerGeneration.ModuleNameSyntax s.upper s.alphaNum
        (target s g).module.2 ∧
      s.expand (target s g) = .ok final ∧
      TemplateExpansionWhole.Accepted (toTemplate (target s g)) (toTemplate final) ∧
      CheckGroups.check (toCheck final) (s.oracle final) = .ok a ∧
      s.missing final a = [] ∧
      code = RenderFinalize.finalize s.shown
        (Peg.Verification.selectMarker (s.render final a ""))
        (s.render final a (Peg.Verification.selectMarker (s.render final a ""))) := by
  unfold publicModule generateWithWarnings inner at success
  obtain ⟨pp, r, g, hp, hr, he, hc, bad, valid, final, a, hf, hca, hm, hcode⟩ :=
    (InnerGeneration.invariant3_public_render_iff ..).mp success
  have hca' : CheckGroups.check (toCheck final) (s.oracle final) = .ok a := by
    unfold checkStage at hca
    split at hca
    · cases hca
    · rename_i a' h'; cases hca; exact h'
  cases hs : s.strip with
  | none =>
    simp only [hs, Option.map_none] at valid hf
    simp only [target, hs, Option.map_none]
    exact ⟨pp, r, g, final, a, hp, hr, he, hc, bad,
      (InnerGeneration.moduleNameValid_iff _ _ _).mp valid, hf, (expand_ok_accepted s p _ _ hf).2,
      hca', hm, hcode⟩
  | some m =>
    simp only [hs, Option.map_some] at valid hf
    simp only [target, hs, Option.map_some]
    exact ⟨pp, r, g, final, a, hp, hr, he, hc, bad,
      (InnerGeneration.moduleNameValid_iff _ _ _).mp valid, hf, (expand_ok_accepted s p _ _ hf).2,
      hca', hm, hcode⟩

end PegHs.PublicGeneration

#print axioms PegHs.PublicGeneration.toLabel_stripAs
#print axioms PegHs.PublicGeneration.invariant2_generate
#print axioms PegHs.PublicGeneration.invariant2_generateWithWarnings
#print axioms PegHs.PublicGeneration.invariant2_generateFromSource
#print axioms PegHs.PublicGeneration.invariant1_parse_iff
#print axioms PegHs.PublicGeneration.invariant1_generateWithWarnings
#print axioms PegHs.PublicGeneration.invariant1_no_derivation
#print axioms PegHs.PublicGeneration.invariant3_generateWithWarnings_text
#print axioms PegHs.PublicGeneration.invariant2_check_rejects_public
#print axioms PegHs.PublicGeneration.invariant2_group_error_public
#print axioms PegHs.PublicGeneration.invariant2_undefined_reference_public
#print axioms PegHs.PublicGeneration.lookupLibrary_parse_nonempty
#print axioms PegHs.PublicGeneration.lookupLibrary_assemble_nonempty
