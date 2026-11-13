import RenderModuleGHC
import RenderExpressionLexer
import RenderModuleNames
import RenderDeclarationsGHC

namespace PegHs.RenderComposition

open CFG GHCGrammar RenderModuleGHC

-- A chunk is a single element of Codegen.render's intercalated list.
-- Its token annotation excludes tokens introduced by previous chunks.
structure Chunk where
  source : String
  tokens : List Symbol

def renderTail (separator first : String) (chunks : List Chunk) : String :=
  chunks.foldl (fun acc chunk => acc ++ separator ++ chunk.source) first

def tokenTail (first : List Symbol) (chunks : List Chunk) : List Symbol :=
  chunks.foldl (fun acc chunk => acc ++ chunk.tokens) first

theorem renderTail_append (separator first : String) (left right : List Chunk) :
    renderTail separator first (left ++ right) =
      renderTail separator (renderTail separator first left) right := by
  simp [renderTail, List.foldl_append]

theorem tokenTail_append (first : List Symbol) (left right : List Chunk) :
    tokenTail first (left ++ right) =
      tokenTail (tokenTail first left) right := by
  simp [tokenTail, List.foldl_append]

theorem renderTail_intercalate (separator first : String) (chunks : List Chunk) :
    renderTail separator first chunks =
      String.intercalate separator (first :: chunks.map Chunk.source) := by
  simpa [renderTail, List.foldl_map] using
    (RenderExpressionLexer.intercalate_cons separator first
      (chunks.map Chunk.source)).symm

-- GHC inserts virtual layout tokens according to the entire preceding input.
-- A step therefore checks the lexer on the full prefix after adding a chunk.
-- This is a local, independently checkable obligation, not an assumption that
-- the final module's token sequence is already correct.
inductive Trace (lex : String → List Symbol) (separator : String) :
    String → List Symbol → List Chunk → String → List Symbol → Prop where
  | done (source : String) (tokens : List Symbol) :
      Trace lex separator source tokens [] source tokens
  | next {source finalSource : String} {tokens finalTokens : List Symbol}
      {chunk : Chunk} {rest : List Chunk}
      (step : lex (source ++ separator ++ chunk.source) = tokens ++ chunk.tokens)
      (tail : Trace lex separator (source ++ separator ++ chunk.source)
        (tokens ++ chunk.tokens) rest finalSource finalTokens) :
      Trace lex separator source tokens (chunk :: rest) finalSource finalTokens

theorem trace_sound {lex : String → List Symbol} {separator first finalSource : String}
    {firstTokens finalTokens : List Symbol} {chunks : List Chunk}
    (initial : lex first = firstTokens)
    (trace : Trace lex separator first firstTokens chunks finalSource finalTokens) :
    finalSource = renderTail separator first chunks ∧
    finalTokens = tokenTail firstTokens chunks ∧
    lex finalSource = finalTokens := by
  induction trace with
  | done source tokens => exact ⟨rfl, rfl, initial⟩
  | @next source finalSource tokens finalTokens chunk rest step tail ih =>
    obtain ⟨hSource, hTokens, hLex⟩ := ih step
    exact ⟨by simpa [renderTail] using hSource,
      by simpa [tokenTail] using hTokens, hLex⟩

theorem trace_append {lex : String → List Symbol} {separator first middle last : String}
    {firstTokens middleTokens lastTokens : List Symbol}
    {beforeChunks afterChunks : List Chunk}
    (left : Trace lex separator first firstTokens beforeChunks middle middleTokens)
    (right : Trace lex separator middle middleTokens afterChunks last lastTokens) :
    Trace lex separator first firstTokens (beforeChunks ++ afterChunks) last lastTokens := by
  induction left with
  | done _ _ => simpa using right
  | next step tail ih =>
    simpa using Trace.next step (ih right)

-- The CFG theorem is valid for arbitrary export, import and declaration lists.
-- The two remaining premises are observable lexer trace obligations: the
-- prefix trace and its token annotations must match those CFG fragments.
theorem generated_module
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (name : List Symbol) (usesPegPrelude importsPrelude : Bool)
    (exports verbatimImports decls : List (List Symbol))
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : ∀ item ∈ exports, Derives productions [.nonterminal 47] item)
    (verbatim_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (decls_ok : ∀ item ∈ decls, Derives productions [.nonterminal 78] item)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ name ++ exportWord exports ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude ++ verbatimImports).foldl
          semiAppend [] ++ decls.foldl semiAppend [])) :
    lex finalSource = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 0] finalTokens := by
  have hLex := (trace_sound initial trace).2.2
  constructor
  · exact hLex
  · rw [tokens_match]
    apply parse_module_source
    exact generated_with_imports name usesPegPrelude importsPrelude exports
      verbatimImports decls name_ok exports_ok verbatim_ok decls_ok

-- Codegen.ruleDecl contributes a signature and a binding for each emitted
-- rule. Other generated declarations may precede these pairs. The exact
-- ruleDecl rendering is pinned by check-render-declarations-ghc.sh.
structure RuleFragment where
  params : List (List Symbol × Bool)
  result : List Symbol
  body : List Symbol
  types_ok : ∀ p ∈ params, Derives productions [.nonterminal 163] p.1
  result_ok : Derives productions [.nonterminal 163] result
  body_ok : Derives productions [.nonterminal 211] body

def RuleFragment.tokens (r : RuleFragment) :=
  RenderDeclarationsGHC.ruleFromParams r.params r.result r.body

def ruleItems (rules : List RuleFragment) : List (List Symbol) :=
  rules.flatMap fun r => r.tokens.declarations

theorem rule_items_valid (rules : List RuleFragment) :
    ∀ item ∈ ruleItems rules,
      Derives productions [.nonterminal 78] item := by
  intro item member
  obtain ⟨rule, _, inside⟩ := List.mem_flatMap.mp member
  have valid : rule.tokens.Valid := RenderDeclarationsGHC.rule_from_params_valid
    _ _ _ rule.types_ok rule.result_ok rule.body_ok
  obtain ⟨types, result, args, body⟩ := valid
  simp only [RenderDeclarationsGHC.RuleTokens.declarations,
    RenderDeclarationsGHC.generatedPair, List.mem_cons,
    List.mem_nil_iff, or_false] at inside
  rcases inside with rfl | rfl
  · exact RenderDeclarationsGHC.generated_rule_signature _ _ types result
  · exact RenderDeclarationsGHC.binding_named_arguments _ args body

structure EntryFragment where
  resultType : List Symbol
  type_ok : Derives productions [.nonterminal 163] resultType

abbrev CheckedEnvType := Option { ty : List Symbol // Derives productions [.nonterminal 163] ty }

def entryItems (syntaxMode : Bool) (envType : CheckedEnvType) (entries : List EntryFragment) : List (List Symbol) :=
  entries.flatMap fun e => RenderDeclarationsGHC.generatedPair
    (RenderDeclarationsGHC.parameterArrows (envType.toList.map Subtype.val) (RenderDeclarationsGHC.entryTypeWord e.resultType))
    (List.replicate (if envType.isSome then 2 else 1) [.terminal 117]) (RenderDeclarationsGHC.entryBodyWord envType.isSome syntaxMode)

theorem entry_items_valid (syntaxMode : Bool) (envType : CheckedEnvType) (entries : List EntryFragment)
    (item : List Symbol) (member : item ∈ entryItems syntaxMode envType entries) :
    Derives productions [.nonterminal 78] item := by
  obtain ⟨e, _, inside⟩ := List.mem_flatMap.mp member
  simp only [RenderDeclarationsGHC.generatedPair, List.mem_cons,
    List.mem_nil_iff, or_false] at inside
  rcases inside with rfl | rfl
  · apply RenderDeclarationsGHC.generated_rule_signature _ _ _ (RenderDeclarationsGHC.entry_type e.type_ok)
    intro ty member
    obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
    exact checked.property
  · apply RenderDeclarationsGHC.binding_named_arguments _ _ (RenderDeclarationsGHC.entry_body envType.isSome syntaxMode)
    intro arg h
    exact List.eq_of_mem_replicate h ▸ RenderDeclarationsGHC.varid_argument

#print axioms entry_items_valid

-- Entry names all lex as VARID, so only the number retained by keep matters here.
def syntaxEntryItems (syntaxMode : Bool) (envType : CheckedEnvType) (retained : Nat) :=
  let pair := RenderDeclarationsGHC.generatedPair
    (RenderDeclarationsGHC.parameterArrows (envType.toList.map Subtype.val)
      [.terminal 122, .terminal 83, .terminal 122, .terminal 122, .terminal 122])
    (List.replicate (if envType.isSome then 2 else 1) [.terminal 117])
    (RenderDeclarationsGHC.syntaxEntryBodyWord envType.isSome)
  if syntaxMode then (List.replicate retained pair).flatten else []

theorem syntax_entry_items_valid (syntaxMode : Bool) (envType : CheckedEnvType) (retained : Nat)
    (item : List Symbol) (member : item ∈ syntaxEntryItems syntaxMode envType retained) :
    Derives productions [.nonterminal 78] item := by
  cases syntaxMode with
  | false => simp [syntaxEntryItems] at member
  | true =>
    simp only [syntaxEntryItems, ite_true, List.mem_flatten] at member
    obtain ⟨pair, h, inside⟩ := member
    rw [List.eq_of_mem_replicate h] at inside
    simp only [RenderDeclarationsGHC.generatedPair, List.mem_cons, List.mem_nil_iff,
      or_false] at inside
    rcases inside with rfl | rfl
    · exact RenderDeclarationsGHC.syntax_entry_signature envType
    · apply RenderDeclarationsGHC.binding_named_arguments _ _ (RenderDeclarationsGHC.syntax_entry_body _)
      intro arg h
      exact List.eq_of_mem_replicate h ▸ RenderDeclarationsGHC.varid_argument

#print axioms syntax_entry_items_valid

-- The retained list follows the generator's per-entry order. Each binding has
-- its own layout close, supplied by the parser trace.
structure RecoveryEntry extends EntryFragment where
  syntaxTree : Bool
  parserClose : Bool

structure EntryCandidate extends EntryFragment where
  suffix : String
  valueClose : Bool
  syntaxClose : Bool

def selectedValueEntries (keep : String → Bool) (entries : List EntryCandidate) :=
  (entries.filter fun e => keep ("parse" ++ e.suffix)).map EntryCandidate.toEntryFragment

def selectedSyntaxCount (keep : String → Bool) (entries : List EntryCandidate) :=
  (entries.filter fun e => keep ("parseSyntax" ++ e.suffix)).length

def selectRecoveryEntries (recovering syntaxMode : Bool) (keep : String → Bool)
    (entries : List EntryCandidate) : List RecoveryEntry :=
  if recovering then entries.flatMap fun e =>
    (if keep ("parseRecover" ++ e.suffix) then
      [⟨e.toEntryFragment, false, e.valueClose⟩] else []) ++
    (if syntaxMode && keep ("parseSyntaxRecover" ++ e.suffix) then
      [⟨e.toEntryFragment, true, e.syntaxClose⟩] else [])
  else []

open RenderDeclarationsGHC in
def recoveryItems (syntaxMode : Bool) (envType : CheckedEnvType) (entries : List RecoveryEntry) :=
  entries.flatMap fun e => generatedPair
    (parameterArrows (envType.toList.map Subtype.val) (recoverTypeWord e.syntaxTree e.resultType))
    (List.replicate (if envType.isSome then 2 else 1) [.terminal 117])
    (recoverBodyWord envType.isSome syntaxMode e.syntaxTree e.parserClose)

open RenderDeclarationsGHC in
theorem recovery_items_valid (syntaxMode : Bool) (envType : CheckedEnvType)
    (entries : List RecoveryEntry) (item : List Symbol)
    (member : item ∈ recoveryItems syntaxMode envType entries) :
    Derives productions [.nonterminal 78] item := by
  obtain ⟨e, _, inside⟩ := List.mem_flatMap.mp member
  simp only [generatedPair, List.mem_cons, List.mem_nil_iff, or_false] at inside
  rcases inside with rfl | rfl
  · apply generated_rule_signature _ _ _ (recover_entry_type e.syntaxTree e.type_ok)
    intro ty member
    obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
    exact checked.property
  · exact recover_entry_binding envType.isSome syntaxMode e.syntaxTree e.parserClose

#print axioms recovery_items_valid

open RenderDeclarationsGHC

structure DebugSettings where
  enabled : Bool
  noTraditionalRecordSyntax : Bool
  parserClose : DebugEntryKind → Bool

def debugKinds (enabled recovering syntaxMode : Bool) : List DebugEntryKind :=
  if enabled then
    (if recovering then [.recoverValue] ++ (if syntaxMode then [.recoverSyntax] else []) else []) ++
    [.value] ++ (if syntaxMode then [.syntaxTree] else [])
  else []

-- debugNames emits the ordinary entries before the recovering entries.
def debugExportKinds (enabled recovering syntaxMode : Bool) : List DebugEntryKind :=
  if enabled then
    [.value] ++ (if syntaxMode then [.syntaxTree] else []) ++
    (if recovering then [.recoverValue] ++ (if syntaxMode then [.recoverSyntax] else []) else [])
  else []

theorem debug_export_declarations (enabled recovering syntaxMode : Bool) :
    (debugExportKinds enabled recovering syntaxMode).Perm (debugKinds enabled recovering syntaxMode) := by
  cases enabled <;> cases recovering <;> cases syntaxMode <;>
    first | exact List.Perm.refl _ | exact @List.perm_append_comm DebugEntryKind ([_] : List DebugEntryKind) [_]
          | exact @List.perm_append_comm DebugEntryKind ([_, _] : List DebugEntryKind) [_, _]

#print axioms debug_export_declarations

def debugItems (debug : DebugSettings) (recovering syntaxMode : Bool) (env : CheckedEnvType)
    (start : EntryFragment) :=
  (debugKinds debug.enabled recovering syntaxMode).flatMap fun kind =>
    generatedPair (debugTypeWord (env.map Subtype.val) (kind.resultType start.resultType))
      (List.replicate (if env.isSome then 3 else 2) [.terminal 117])
      (kind.body env.isSome syntaxMode debug.noTraditionalRecordSyntax
        [.terminal (if debug.parserClose kind then 0 else 104)])

theorem debug_items_valid (debug : DebugSettings) (recovering syntaxMode : Bool)
    (env : CheckedEnvType) (start : EntryFragment) (item : List Symbol)
    (member : item ∈ debugItems debug recovering syntaxMode env start) :
    Derives productions [.nonterminal 78] item := by
  obtain ⟨kind, _, inside⟩ := List.mem_flatMap.mp member
  have hc : Derives productions [.nonterminal 320]
      [.terminal (if debug.parserClose kind then 0 else 104)] := by
    cases debug.parserClose kind
    · exact Derives.production (pre := []) (post := []) (id := 834)
        (rhs := [.terminal 104]) (by decide) (.refl _)
    · exact Derives.production (pre := []) (post := []) (id := 835)
        (rhs := [.terminal 0]) (by decide) (.refl _)
  exact debug_pair_valid kind env syntaxMode debug.noTraditionalRecordSyntax hc start.type_ok item inside

#print axioms debug_items_valid

def configItems (kept explicitTabstop positional debug : Bool) : List (List Symbol) :=
  if kept then
    [[.terminal 117, .terminal 76, .terminal 122],
     if explicitTabstop then tabstopBindingWord positional else [.terminal 117, .terminal 77, .terminal 121]] ++
    (if positional && (explicitTabstop || debug) then
      [[.terminal 117, .terminal 76, .terminal 122, .terminal 83, .terminal 122, .terminal 83, .terminal 122],
       withTabstopBindingWord] else [])
  else []

theorem config_items_valid (kept explicitTabstop positional debug : Bool) (item : List Symbol)
    (h : item ∈ configItems kept explicitTabstop positional debug) :
    Derives productions [.nonterminal 78] item := by
  cases kept <;> cases explicitTabstop <;> cases positional <;> cases debug <;>
    simp [configItems] at h <;>
    repeat' first | obtain rfl | h := h | subst item | exact config_signature
                  | exact default_config_binding | exact tabstop_config_binding true
                  | exact tabstop_config_binding false | exact with_tabstop_signature
                  | exact with_tabstop_binding

#print axioms config_items_valid

def positionalStoreWord (types : List (List Symbol)) : List Symbol :=
  [.terminal 6, .terminal 118, .terminal 117, .terminal 77, .terminal 118] ++
    (types.map fun ty => [.terminal 107] ++ ty ++ [.terminal 108]).flatten

def storeDeclarations (positional : Bool) (types : List (List Symbol)) : List (List Symbol) :=
  match types with
  | [] => [positionalStoreWord []]
  | first :: rest =>
    if positional then positionalStoreWord types :: storeAccessors 0 types
    else [recordStoreWord first rest]

theorem store_declarations_valid (positional : Bool) (types : List (List Symbol))
    (typed : ∀ ty ∈ types, Derives productions [.nonterminal 163] ty)
    (item : List Symbol) (member : item ∈ storeDeclarations positional types) :
    Derives productions [.nonterminal 78] item := by
  have group (xs : List (List Symbol)) (ok : ∀ ty ∈ xs, Derives productions [.nonterminal 163] ty) :
      Derives productions [.nonterminal 78] (positionalStoreWord xs) := by
    let fields := ConstructorFields.ofParenthesized xs (fun ty h =>
      Derives.production (pre := []) (post := []) (id := 374)
        (rhs := [.nonterminal 163]) (by decide) (ok ty h))
    simpa [positionalStoreWord, fields, ConstructorFields.ofParenthesized, ConstructorFields.word]
      using positional_store_declaration fields
  cases types with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    exact group [] typed
  | cons first rest =>
    cases positional with
    | false =>
      obtain rfl := List.mem_singleton.mp member
      exact record_store_declaration _ _ typed
    | true =>
      rcases List.mem_cons.mp member with rfl | accessor
      · exact group _ typed
      · exact store_accessors_valid _ typed 0 item accessor

#print axioms store_declarations_valid

-- storeDecl (including positional accessors) and newStoreDecl are kept
-- together. The initializer follows the store declarations in both modes.
def storeItems (kept : Bool) (decls : List (List Symbol)) (env : CheckedEnvType)
    (memoised : Nat) : List (List Symbol) :=
  if kept then decls ++ [newStoreSignatureWord (env.map Subtype.val), match memoised with
    | 0 => pureStoreBindingWord env.isSome
    | n + 1 => memoStoreBindingWord env.isSome n]
  else []

theorem store_items_valid (kept : Bool) (decls : List (List Symbol)) (env : CheckedEnvType)
    (memoised : Nat) (decls_ok : ∀ d ∈ decls, Derives productions [.nonterminal 78] d)
    (item : List Symbol) (h : item ∈ storeItems kept decls env memoised) :
    Derives productions [.nonterminal 78] item := by
  cases kept with
  | false => simp [storeItems] at h
  | true =>
    simp only [storeItems, ite_true, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at h
    rcases h with hd | rfl | rfl
    · exact decls_ok _ hd
    · apply new_store_signature
      cases env with
      | none => simp
      | some e => simpa using e.property
    · cases memoised with
      | zero => exact new_store_without_tables _
      | succ n => exact new_store_with_tables _ n

#print axioms store_items_valid

-- The retained syntax declarations, in the order chosen by syntaxDecls.
inductive SyntaxDeclaration where
  | kind
  | names (kinds : Nat)
  | trivia (count : Nat)
  | node
  | cast
  | accessor (shape : SyntaxAccessorKind)

def SyntaxDeclaration.items : SyntaxDeclaration → List (List Symbol)
  | .kind => [[.terminal 117, .terminal 76, .terminal 122],
              [.terminal 117, .terminal 77, .terminal 122, .terminal 131]]
  | .names n => [syntaxQuerySignatureWord false,
      argumentsWord [[.terminal 117]] ++ [.terminal 77] ++ kindNameBody n]
  | .trivia n => [syntaxQuerySignatureWord false,
      argumentsWord [[.terminal 117]] ++ [.terminal 77] ++ ([.terminal 121, .terminal 117] ++ triviaListWord n)]
  | .node => [syntaxNodeNewtypeWord]
  | .cast => [syntaxQuerySignatureWord true,
      argumentsWord [[.terminal 117]] ++ [.terminal 77] ++ syntaxCastBody]
  | .accessor k => [[.terminal 117, .terminal 76, .terminal 118, .terminal 83] ++ syntaxAccessorResult k,
      argumentsWord [[.terminal 107, .terminal 118, .terminal 117, .terminal 108]] ++
        [.terminal 77] ++ syntaxAccessorBody k]

structure SyntaxRule where
  name : String
  isInline : Bool
  isToken : Bool
  accessors : List (String × SyntaxAccessorKind)

structure SyntaxInputs where
  rules : List SyntaxRule
  trivia : List String
  toUpper : Char → Char
  toLower : Char → Char
  isUpper : Char → Bool

private def mapFirst (f : Char → Char) (name : String) : String :=
  match name.toList with
  | [] => name
  | c :: cs => String.ofList (f c :: cs)

def SyntaxInputs.selected (inputs : SyntaxInputs) (keep : String → Bool) : List SyntaxDeclaration :=
  let kinds := inputs.rules.filter fun r => !r.isInline
  let nodes := kinds.filter fun r => !r.isToken
  let upper := mapFirst inputs.toUpper
  let lower := mapFirst inputs.toLower
  (kinds.filter fun r => keep ("syntaxKind" ++ upper r.name)).map (fun _ => .kind) ++
    (if keep "nameOfSyntaxKind" then [.names kinds.length] else []) ++
    (if keep "isTriviaSyntaxKind" then [.trivia inputs.trivia.length] else []) ++
    nodes.flatMap fun r =>
      let ty := RenderModuleNames.generatedTypeName inputs.toUpper inputs.isUpper r.name.toList ++ "Syntax"
      (if keep ty then [.node] else []) ++
      (if keep ("cast" ++ ty) then [.cast] else []) ++
      (r.accessors.filter fun a => keep (lower r.name ++ upper a.1)).map fun a => .accessor a.2

def syntaxItems (enabled : Bool) (decls : List SyntaxDeclaration) :=
  if enabled then decls.flatMap SyntaxDeclaration.items else []

theorem syntax_items_valid (enabled : Bool) (decls : List SyntaxDeclaration) (item : List Symbol)
    (member : item ∈ syntaxItems enabled decls) : Derives productions [.nonterminal 78] item := by
  cases enabled with
  | false => simp [syntaxItems] at member
  | true =>
    obtain ⟨decl, _, h⟩ := List.mem_flatMap.mp member
    cases decl <;> simp only [SyntaxDeclaration.items, List.mem_cons, List.mem_nil_iff, or_false] at h <;>
      repeat' first | obtain rfl | h := h | subst item | exact config_signature | exact syntax_kind_binding
                    | exact syntax_query_signature _ | exact kind_name_binding _ | exact trivia_binding _
                    | exact syntax_node_newtype | exact syntax_cast_binding | exact syntax_accessor_signature _
                    | exact syntax_accessor_binding _

#print axioms syntax_items_valid

theorem generated_module_with_rules
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (qualifiedName syntaxMode : Bool) (usesPegPrelude importsPrelude : Bool)
    (selected : List RenderModuleGHC.GeneratedExport) (dataTypes : Nat)
    (userExports verbatimImports storeFieldTypes : List (List Symbol))
    (envType : CheckedEnvType) (recovering : Bool) (keep : String → Bool)
    (debug : DebugSettings) (start : EntryFragment)
    (candidates : List EntryCandidate) (rules : List RuleFragment)
    (user_ok : ∀ item ∈ userExports, Derives productions [.nonterminal 47] item)
    (verbatim_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (dataDecls : List DataDeclaration) (explicitTabstop : Bool) (memoised : Nat)
    (store_types_ok : ∀ ty ∈ storeFieldTypes, Derives productions [.nonterminal 163] ty)
    (syntaxInputs : SyntaxInputs)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ [.terminal (if qualifiedName then 122 else 118)] ++ exportWord
        (RenderModuleGHC.moduleExports selected dataTypes userExports (debugExportKinds debug.enabled recovering syntaxMode).length) ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude ++ verbatimImports).foldl
          semiAppend [] ++ (dataDecls.map DataDeclaration.word ++ entryItems syntaxMode envType (selectedValueEntries keep candidates) ++
        syntaxEntryItems syntaxMode envType (selectedSyntaxCount keep candidates) ++ recoveryItems syntaxMode envType
          (selectRecoveryEntries recovering syntaxMode keep candidates) ++
        debugItems debug recovering syntaxMode envType start ++ syntaxItems syntaxMode (syntaxInputs.selected keep) ++
        configItems (keep "peg'config") explicitTabstop debug.noTraditionalRecordSyntax debug.enabled ++
        storeItems (keep "peg'newStore") (storeDeclarations debug.noTraditionalRecordSyntax storeFieldTypes) envType memoised ++ ruleItems rules).foldl semiAppend [])) :
    lex finalSource = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 0] finalTokens := by
  have name_ok : Derives productions [.nonterminal 321]
      [.terminal (if qualifiedName then 122 else 118)] := by
    cases qualifiedName
    · exact module_name_simple
    · exact module_name_qualified
  apply generated_module lex first firstTokens chunks finalSource finalTokens _
    usesPegPrelude importsPrelude (RenderModuleGHC.moduleExports selected dataTypes userExports (debugExportKinds debug.enabled recovering syntaxMode).length) verbatimImports
    (dataDecls.map DataDeclaration.word ++ entryItems syntaxMode envType (selectedValueEntries keep candidates) ++
        syntaxEntryItems syntaxMode envType (selectedSyntaxCount keep candidates) ++ recoveryItems syntaxMode envType
          (selectRecoveryEntries recovering syntaxMode keep candidates) ++
        debugItems debug recovering syntaxMode envType start ++ syntaxItems syntaxMode (syntaxInputs.selected keep) ++
        configItems (keep "peg'config") explicitTabstop debug.noTraditionalRecordSyntax debug.enabled ++
        storeItems (keep "peg'newStore") (storeDeclarations debug.noTraditionalRecordSyntax storeFieldTypes) envType memoised ++ ruleItems rules) name_ok
    (RenderModuleGHC.module_exports_valid selected dataTypes userExports (debugExportKinds debug.enabled recovering syntaxMode).length user_ok) verbatim_ok
  · intro item member
    simp only [List.mem_append] at member
    rcases member with (((((((hd | he) | hs) | hc) | hdebug) | hsyntax) | hconfig) | hstore) | hr
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hd
      exact data_declaration_valid d
    · exact entry_items_valid syntaxMode envType _ item he
    · exact syntax_entry_items_valid syntaxMode envType (selectedSyntaxCount keep candidates) item hs
    · exact recovery_items_valid syntaxMode envType _ item hc
    · exact debug_items_valid debug recovering syntaxMode envType start item hdebug
    · exact syntax_items_valid _ _ item hsyntax
    · exact config_items_valid _ _ _ _ item hconfig
    · exact store_items_valid _ _ _ _ (store_declarations_valid _ _ store_types_ok) item hstore
    · exact rule_items_valid rules item hr
  · exact initial
  · exact trace
  · exact tokens_match

#print axioms renderTail_intercalate
#print axioms renderTail_append
#print axioms tokenTail_append
#print axioms trace_sound
#print axioms trace_append
#print axioms generated_module
#print axioms rule_items_valid
#print axioms generated_module_with_rules

end PegHs.RenderComposition
