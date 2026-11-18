import Lean
import CallOrder
import CallTables
import RecursiveEval
import ConcreteTerminal
import TerminalCursor
import Utf8Terminals
import ConcreteTerminalBody
import LabeledConcreteBody
import ConcreteTables
import MetagrammarPredicates
import PredicateBindings
import Guard
import LineIndex
import SemanticPredicates
import EnvironmentEval
import CaptureWindow
import EnvironmentFuel
import EnvironmentDerivation
import EnvironmentActual
import MetaExecution
import VerbatimRule
import PrefixReplay
import WindowReplay
import WindowReads
import FastWindow
import MemoRecognition
import MemoTrace
import MemoTables
import MemoMetaNoLR
import EnvProjection
import EnvProjectionPredicate
import MemoKeyTransfer
import EnvRunCongruence
import MetaEnvCompatible
import MemoKeyEnvironment
import NoArgInputReads
import ItemWindow
import InitialWhitespaceCall
import FileTopItems
import FileEnd
import FileItemChain
import FileEntry
import TotalFile
import FileTops
import RuntimeChoiceProof
import StrictSpaceChar
import StrictInlineSpace
import DirectiveCommentProof
import DirectiveSuccess
import DirectiveAssembly
import SimpleEscapeProof
import DirectiveDecode
import DirectiveSourceDiagnostic
import DirectiveHex
import DirectiveStringDiagnostic
import TabstopProof
import BoundedDecimal
import DirectiveDuplicates
import DirectiveArityProof
import DirectiveFailure
import StrictWhitespaceScan
import PublicParsing
import PublicEntryProof
import FileExamples
import ConcreteFileCertificates
import EnvironmentDepth
import CapturedPredicates
import GhcPredicates
import ParameterPredicates
import EscapePredicates
import ExpressionDepth
import Parsing
import Header
import Whitespace
import TemplateExpansion
import TemplateExpansionFresh
import TemplateExpansionWhole
import TemplateSubstitution
import TemplateQueue
import Lexical
import Nullable
import Reachable
import Literal
import Signatures
import File
import Consumption
import FileTrees
import Pipeline
import RenderExpression
import AssembleValidation
import AssemblePredicates
import AssembleBindings
import NestedBindings
import ImportResolution
import LabelPropagation
import LabelCheckTheorems
import HsPrelude
import LabelsTranslated
import LabelsTranslatedProof
import CheckGroupsTheorems
import InnerGeneration
import InnerUnicode
import Pragmas
import RuleRejection
import RuleRejectionRefs
import RuleRejectionRepeat
import RuleRejectionNullable
import CertifiedPublicFiles
import DirectiveSequence
import EnvProjectionTests
import ExtractedSignatures
import HaskellDerivation
import ItemSourceSplit
import LayoutDerivation
import RenderComposition
import RenderFinalize
import RenderFinalizeModule
import PublicGeneration
import SelfHostedRuntime
import ScopedEnv
import SelfHostedMemo
import RuntimeForms
import PublicGenerationGHC
import RenderPrinting
import RenderDeclarationBinders
import RenderDeclarationsGHC
import RenderExpressionBoundary
import RenderExpressionGHC
import RenderExpressionLexer
import RenderModuleGHC
import RenderModuleNames
import RenderPrimitiveChoice
import RenderPrimitiveDo
import RenderPrimitiveDoGHC
import RenderPrimitiveStatement
import RenderRuleBodyGHC
import StrictCharMemo
import StrictIdentifierMemo
import StrictParameterGuards
import StrictWhitespaceLexical
import StrictWhitespaceMemo
import TraceChunks
import Verbatim47Data
import TranslatedRuntimeCore
import RuntimeCoreProof
import VerbatimChunks
import VerbatimItem47
import VerbatimValue
import DerivationPeg
import DerivationPegSyntax
import DerivationExtensions
import CommittedModuleDerivations

namespace PegHs.RecursiveEval

-- The two tables are extracted from Peg.hpeg and PegSyntax.hpeg by
-- ExtractCallOrder.hs during verification/check.sh.
def actualMetaRules (syntaxMode : Bool) : Nat → CallOrder.Body :=
  if syntaxMode then Meta2.rules else Meta1.rules

theorem invariant1_actual_meta_total (syntaxMode : Bool) (token : Nat → Option Nat)
    (rule remaining : Nat) :
    ∃ fuel result,
      runFuel (actualMetaRules syntaxMode) token fuel
        (actualMetaRules syntaxMode rule) remaining = some result := by
  cases syntaxMode with
  | false =>
      simpa [actualMetaRules] using
        (invariant1_rule_executable (token := token) Meta1.invariant1_checked (remaining, rule))
  | true =>
      simpa [actualMetaRules] using
        (invariant1_rule_executable (token := token) Meta2.invariant1_checked (remaining, rule))

#print axioms invariant1_actual_meta_total

end PegHs.RecursiveEval

namespace PegHs.ConcreteTerminalBody

-- Both extracted metagrammars terminate on every concrete character input.
theorem invariant1_actual_concrete_total (syntaxMode : Bool)
    (input : List Char) (rule : Nat) :
    ∃ fuel result,
      (if syntaxMode then MetaTerminal2.runConcrete input fuel rule
       else MetaTerminal1.runConcrete input fuel rule) = some result := by
  cases syntaxMode with
  | false => simpa using MetaTerminal1.invariant1_runConcrete_total input rule
  | true => simpa using MetaTerminal2.invariant1_runConcrete_total input rule

#print axioms invariant1_actual_concrete_total

theorem invariant1_actual_labeled_total (syntaxMode : Bool)
    (oracle : Nat → Nat → Bool) (input : List Char) (rule : Nat) :
    ∃ fuel result,
      (if syntaxMode then MetaTerminal2.runLabeled oracle input fuel rule
       else MetaTerminal1.runLabeled oracle input fuel rule) = some result := by
  cases syntaxMode with
  | false => simpa using MetaTerminal1.invariant1_runLabeled_total oracle input rule
  | true => simpa using MetaTerminal2.invariant1_runLabeled_total oracle input rule

#print axioms invariant1_actual_labeled_total

end PegHs.ConcreteTerminalBody

-- Every theorem of each listed module, and every theorem of this file, may use
-- only the standard axioms. check-audit-coverage.sh compares this list with
-- the modules that contain theorems. Keep one module per line between the
-- markers.
def auditedModules : List Lean.Name := [
  -- audited modules begin
  `AssembleBindings,
  `AssemblePredicates,
  `AssembleValidation,
  `AssembleValidationHelpers,
  `BoundedDecimal,
  `CallOrder,
  `CallTables,
  `CaptureWindow,
  `CapturedPredicates,
  `CertifiedPublicFiles,
  `CheckGroupsModel,
  `CheckGroupsReach,
  `CheckGroupsTheorems,
  `CommittedModuleDerivations,
  `ConcreteFileCertificates,
  `ConcreteTables,
  `ConcreteTerminal,
  `ConcreteTerminalBody,
  `Consumption,
  `DerivationExtensions,
  `DerivationPeg,
  `DerivationPegSyntax,
  `DirectiveArgument,
  `DirectiveArityProof,
  `DirectiveAssembly,
  `DirectiveCommentProof,
  `DirectiveDecode,
  `DirectiveDuplicates,
  `DirectiveFailure,
  `DirectiveHex,
  `DirectiveNames,
  `DirectiveSequence,
  `DirectiveSourceDiagnostic,
  `DirectiveStringDiagnostic,
  `DirectiveSuccess,
  `EnvProjection,
  `EnvProjectionPredicate,
  `EnvProjectionTests,
  `EnvRunCongruence,
  `EnvironmentActual,
  `EnvironmentDepth,
  `EnvironmentDerivation,
  `EnvironmentEval,
  `EnvironmentFuel,
  `EscapePredicates,
  `ExpressionDepth,
  `ExtractedSignatures,
  `FastWindow,
  `File,
  `FileEnd,
  `FileEntry,
  `FileExamples,
  `FileItemChain,
  `FileTopItems,
  `FileTops,
  `FileTrees,
  `GhcPredicates,
  `Guard,
  `HaskellDerivation,
  `Header,
  `HsPrelude,
  `ImportResolution,
  `InitialWhitespace,
  `InitialWhitespaceCall,
  `InnerGeneration,
  `InnerUnicode,
  `ItemSourceSplit,
  `ItemWindow,
  `LabelCheckCharSet,
  `LabelCheckModel,
  `LabelCheckTermination,
  `LabelCheckTheorems,
  `LabelPropagation,
  `LabelsTranslated,
  `LabelsTranslatedProof,
  `LabeledConcreteBody,
  `LayoutDerivation,
  `Lexical,
  `LineIndex,
  `Literal,
  `MemoKeyEnvironment,
  `MemoKeyTransfer,
  `MemoMetaNoLR,
  `MemoRecognition,
  `MemoTables,
  `MemoTrace,
  `MetaEnvCompatible,
  `MetaExecution,
  `MetagrammarPredicates,
  `NestedBindings,
  `NoArgInputReads,
  `Nullable,
  `ParameterPredicates,
  `Parsing,
  `Pipeline,
  `Pragmas,
  `PredicateBindings,
  `PrefixReplay,
  `PublicEntryProof,
  `PublicGeneration,
  `PublicGenerationGHC,
  `PublicParsing,
  `Reachable,
  `RecursiveEval,
  `RenderComposition,
  `RenderDeclarationBinders,
  `RenderDeclarationsGHC,
  `RenderExpression,
  `RenderExpressionBoundary,
  `RenderExpressionGHC,
  `RenderExpressionLexer,
  `RenderFinalize,
  `RenderFinalizeModule,
  `RenderModuleGHC,
  `RenderModuleNames,
  `RenderPrimitiveChoice,
  `RenderPrinting,
  `RenderPrimitiveDo,
  `RenderPrimitiveDoGHC,
  `RenderPrimitiveStatement,
  `RenderRuleBodyGHC,
  `RuleRejection,
  `RuleRejectionNullable,
  `RuleRejectionRefs,
  `RuleRejectionRepeat,
  `RuntimeChoiceProof,
  `RuntimeCoreProof,
  `RuntimeForms,
  `ScopedEnv,
  `SelfHostedFileProof,
  `SelfHostedMemo,
  `SelfHostedRuntime,
  `SemanticPredicates,
  `Signatures,
  `SimpleEscapeProof,
  `StrictCharMemo,
  `StrictComment,
  `StrictDirective,
  `StrictIdentifier,
  `StrictIdentifierMemo,
  `StrictInlineSpace,
  `StrictParameterGuards,
  `StrictSpaceChar,
  `StrictWhitespace,
  `StrictWhitespaceLexical,
  `StrictWhitespaceMemo,
  `StrictWhitespaceScan,
  `TabstopProof,
  `TemplateExpansion,
  `TemplateExpansionFresh,
  `TemplateExpansionWhole,
  `TemplateQueue,
  `TemplateSubstitution,
  `TerminalCursor,
  `TotalFile,
  `TraceChunks,
  `TranslatedArity,
  `TranslatedEscapes,
  `TranslatedRuntimeCore,
  `TranslatedTabstop,
  `Utf8Terminals,
  `Verbatim47Data,
  `VerbatimChunks,
  `VerbatimItem47,
  `VerbatimRule,
  `VerbatimScan,
  `VerbatimValue,
  `Whitespace,
  `WindowReads,
  `WindowReplay
  -- audited modules end
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut owners : Std.HashMap Nat Name := {}
  let mut counts : Std.HashMap Name Nat := {}
  for moduleName in auditedModules do
    let some idx := env.getModuleIdx? moduleName | throwError "missing module {moduleName}"
    owners := owners.insert idx.toNat moduleName
    counts := counts.insert moduleName 0
  let generated := [`TranslatedEscapes, `TranslatedArity, `TranslatedTabstop, `TranslatedRuntimeCore, `LabelsTranslated]
  let mut own := 0
  for (name, info) in env.constants.toList do
    -- Declarations of this file have no module index.
    let owner? := (env.getModuleIdxFor? name).map (owners[·.toNat]?)
    let some owner := owner?.getD (some `Audit) | continue
    if info.isAxiom then throwError "unexpected axiom declaration {name}"
    if !info.isTheorem && !(generated.contains owner && info.isDefinition) then continue
    if owner == `Audit then own := own + 1
    else counts := counts.insert owner (counts.getD owner 0 + 1)
    let axioms ← collectAxioms name
    logInfo m!"{name}: {axioms}"
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} depends on unexpected axiom {ax}"
  for moduleName in auditedModules do
    if counts.getD moduleName 0 == 0 then throwError "no audited declarations in {moduleName}"
  if own == 0 then throwError "no audited declarations in Audit"
