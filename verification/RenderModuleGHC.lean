import GHCGrammar
import LayoutDerivation

namespace PegHs.RenderModuleGHC

open CFG GHCGrammar

private theorem trans {g : Grammar} {xs ys zs : List Symbol}
    (a : Derives g xs ys) (b : Derives g ys zs) : Derives g xs zs := by
  induction a with
  | refl _ => exact b
  | production rule next ih => exact .production rule (ih b)

private theorem before {g : Grammar} (lead : List Symbol) {xs ys : List Symbol}
    (h : Derives g xs ys) : Derives g (lead ++ xs) (lead ++ ys) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs pre post result rule next ih =>
    have inner : Derives g ((lead ++ pre) ++ rhs ++ post) (lead ++ result) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := lead ++ pre) (post := post) rule inner)

private theorem after {g : Grammar} (tail : List Symbol) {xs ys : List Symbol}
    (h : Derives g xs ys) : Derives g (xs ++ tail) (ys ++ tail) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs pre post result rule next ih =>
    have inner : Derives g (pre ++ rhs ++ (post ++ tail)) (result ++ tail) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := pre) (post := post ++ tail) rule inner)

private theorem beside {g : Grammar} {xs ys us vs : List Symbol}
    (left : Derives g xs ys) (right : Derives g us vs) :
    Derives g (xs ++ us) (ys ++ vs) := by
  exact trans (after us left) (before ys right)

private theorem applyRule {id lhs : Nat} {rhs out : List Symbol} {g : Grammar}
    (rule : g id = some (lhs, rhs)) (children : Derives g rhs out) :
    Derives g [.nonterminal lhs] out := by
  have framed : Derives g ([] ++ rhs ++ []) out := by simpa using children
  simpa using (Derives.production (pre := []) (post := []) rule framed)

private theorem emptyRule {id lhs : Nat} {g : Grammar}
    (rule : g id = some (lhs, [])) : Derives g [.nonterminal lhs] [] := by
  exact applyRule rule (.refl _)

private theorem oneRule {id lhs child : Nat} {g : Grammar} {out : List Symbol}
    (rule : g id = some (lhs, [.nonterminal child]))
    (h : Derives g [.nonterminal child] out) :
    Derives g [.nonterminal lhs] out := by
  exact applyRule rule h

-- The generated module name is a GHC CONID or QCONID token. The header
-- printer's character-level validation is a separate obligation.
theorem module_name_simple :
    Derives productions [.nonterminal 321] [.terminal 118] := by
  have rule : productions 836 = some (321, [.terminal 118]) := by decide
  exact applyRule rule (.refl _)

theorem module_name_qualified :
    Derives productions [.nonterminal 321] [.terminal 122] := by
  have rule : productions 837 = some (321, [.terminal 122]) := by decide
  exact applyRule rule (.refl _)

private theorem export_name {word : List Symbol}
    (qvar_ok : Derives productions [.nonterminal 304] word) :
    Derives productions [.nonterminal 47] word := by
  have r105 : productions 105 = some (54, [.nonterminal 304]) := by decide
  have r103 : productions 103 = some (53, [.nonterminal 54]) := by decide
  have r95 : productions 95 = some (49, []) := by decide
  have r322 : productions 322 = some (140, []) := by decide
  have r92 : productions 92 = some
      (48, [.nonterminal 140, .nonterminal 53, .nonterminal 49]) := by decide
  have r91 : productions 91 = some (47, [.nonterminal 48]) := by decide
  have children := beside (emptyRule r322)
    (beside (oneRule r103 (oneRule r105 qvar_ok)) (emptyRule r95))
  exact oneRule r91 (applyRule r92 (by simpa using children))

theorem export_varid :
    Derives productions [.nonterminal 47] [.terminal 117] := by
  have r775 : productions 775 = some (307, [.terminal 117]) := by decide
  have r773 : productions 773 = some (306, [.nonterminal 307]) := by decide
  have r769 : productions 769 = some (304, [.nonterminal 306]) := by decide
  exact export_name (oneRule r769 (oneRule r773 (applyRule r775 (.refl _))))

theorem export_qvarid :
    Derives productions [.nonterminal 47] [.terminal 121] := by
  have r774 : productions 774 = some (306, [.terminal 121]) := by decide
  have r769 : productions 769 = some (304, [.nonterminal 306]) := by decide
  exact export_name (oneRule r769 (applyRule r774 (.refl _)))

private theorem export_parenthesized_operator {inner : List Symbol}
    (inner_ok : Derives productions [.nonterminal 311] inner) :
    Derives productions [.nonterminal 47]
      ([.terminal 107] ++ inner ++ [.terminal 108]) := by
  have r770 : productions 770 = some
      (304, [.terminal 107, .nonterminal 311, .terminal 108]) := by decide
  have framed := beside (.refl [.terminal 107])
    (beside inner_ok (.refl [.terminal 108]))
  exact export_name (applyRule r770 (by simpa [List.append_assoc] using framed))

theorem export_varsym :
    Derives productions [.nonterminal 47]
      [.terminal 107, .terminal 119, .terminal 108] := by
  have r787 : productions 787 = some (311, [.nonterminal 312]) := by decide
  have r789 : productions 789 = some (312, [.terminal 119]) := by decide
  exact export_parenthesized_operator
    (oneRule r787 (applyRule r789 (.refl _)))

theorem export_minus :
    Derives productions [.nonterminal 47]
      [.terminal 107, .terminal 87, .terminal 108] := by
  have r788 : productions 788 = some (311, [.terminal 87]) := by decide
  exact export_parenthesized_operator (applyRule r788 (.refl _))

theorem export_dot :
    Derives productions [.nonterminal 47]
      [.terminal 107, .terminal 96, .terminal 108] := by
  have r787 : productions 787 = some (311, [.nonterminal 312]) := by decide
  have r790 : productions 790 = some (312, [.nonterminal 314]) := by decide
  have r809 : productions 809 = some (314, [.terminal 96]) := by decide
  exact export_parenthesized_operator
    (oneRule r787 (oneRule r790 (applyRule r809 (.refl _))))

private theorem export_type {word subspec : List Symbol}
    (type_ok : Derives productions [.nonterminal 286] word)
    (subspec_ok : Derives productions [.nonterminal 49] subspec) :
    Derives productions [.nonterminal 47] (word ++ subspec) := by
  have r106 : productions 106 = some (54, [.nonterminal 286]) := by decide
  have r103 : productions 103 = some (53, [.nonterminal 54]) := by decide
  have r322 : productions 322 = some (140, []) := by decide
  have r92 : productions 92 = some
      (48, [.nonterminal 140, .nonterminal 53, .nonterminal 49]) := by decide
  have r91 : productions 91 = some (47, [.nonterminal 48]) := by decide
  have children := beside (emptyRule r322)
    (beside (oneRule r103 (oneRule r106 type_ok)) subspec_ok)
  exact oneRule r91 (applyRule r92 (by simpa using children))

theorem export_colon :
    Derives productions [.nonterminal 47]
      [.terminal 107, .terminal 75, .terminal 108] := by
  have r728 : productions 728 = some
      (286, [.terminal 107, .terminal 75, .terminal 108]) := by decide
  have r95 : productions 95 = some (49, []) := by decide
  simpa using export_type (applyRule r728 (.refl _)) (emptyRule r95)

theorem export_constructor_all :
    Derives productions [.nonterminal 47]
      [.terminal 118, .terminal 107, .terminal 74, .terminal 108] := by
  have r733 : productions 733 = some (289, [.terminal 118]) := by decide
  have r732 : productions 732 = some (288, [.nonterminal 289]) := by decide
  have r725 : productions 725 = some (286, [.nonterminal 288]) := by decide
  have r102 : productions 102 = some (52, [.terminal 74]) := by decide
  have r100 : productions 100 = some (51, [.nonterminal 52]) := by decide
  have r98 : productions 98 = some (50, [.nonterminal 51]) := by decide
  have r96 : productions 96 = some
      (49, [.terminal 107, .nonterminal 50, .terminal 108]) := by decide
  have type_ok := oneRule r725 (oneRule r732 (applyRule r733 (.refl _)))
  have subspec_ok := applyRule r96
    (beside (.refl [.terminal 107])
      (beside (oneRule r98 (oneRule r100 (applyRule r102 (.refl _))))
        (.refl [.terminal 108])))
  simpa using export_type type_ok subspec_ok

-- The printer always emits parentheses around the export list, even when
-- it contains zero items.
theorem exports_empty :
    Derives productions [.nonterminal 44] [.terminal 107, .terminal 108] := by
  have r86 : productions 86 = some (45, []) := by decide
  have r83 : productions 83 = some
      (44, [.terminal 107, .nonterminal 45, .terminal 108]) := by decide
  have inner : Derives productions
      [.terminal 107, .nonterminal 45, .terminal 108]
      [.terminal 107, .terminal 108] := by
    simpa using beside (.refl [.terminal 107])
      (beside (emptyRule r86) (.refl [.terminal 108]))
  exact applyRule r83 inner

def commaAppend (acc item : List Symbol) : List Symbol :=
  acc ++ [.terminal 114] ++ item

theorem exports_nonempty (first : List Symbol) (rest : List (List Symbol))
    (first_ok : Derives productions [.nonterminal 47] first)
    (rest_ok : ∀ item ∈ rest, Derives productions [.nonterminal 47] item) :
    Derives productions [.nonterminal 44]
      ([.terminal 107] ++ rest.foldl commaAppend first ++ [.terminal 108]) := by
  have r90 : productions 90 = some (46, [.nonterminal 47]) := by decide
  have r89 : productions 89 = some
      (46, [.nonterminal 46, .terminal 114, .nonterminal 47]) := by decide
  have r85 : productions 85 = some (45, [.nonterminal 46]) := by decide
  have r83 : productions 83 = some
      (44, [.terminal 107, .nonterminal 45, .terminal 108]) := by decide
  have extend (acc item : List Symbol)
      (acc_ok : Derives productions [.nonterminal 46] acc)
      (item_ok : Derives productions [.nonterminal 47] item) :
      Derives productions [.nonterminal 46] (commaAppend acc item) := by
    have h := beside acc_ok (beside (.refl [.terminal 114]) item_ok)
    simpa [commaAppend, List.append_assoc] using applyRule r89 h
  have fold (acc : List Symbol) (items : List (List Symbol))
      (acc_ok : Derives productions [.nonterminal 46] acc)
      (items_ok : ∀ item ∈ items, Derives productions [.nonterminal 47] item) :
      Derives productions [.nonterminal 46]
        (items.foldl commaAppend acc) := by
    induction items generalizing acc with
    | nil => simpa using acc_ok
    | cons item more ih =>
      have item_ok := items_ok item (by simp)
      have more_ok : ∀ x ∈ more, Derives productions [.nonterminal 47] x := by
        intro x hx
        exact items_ok x (by simp [hx])
      simpa [List.foldl] using
        ih (commaAppend acc item) (extend acc item acc_ok item_ok) more_ok
  have inside := oneRule r85 (fold first rest (oneRule r90 first_ok) rest_ok)
  have framed := beside (.refl [.terminal 107])
    (beside inside (.refl [.terminal 108]))
  simpa [List.append_assoc] using applyRule r83 framed

def exportWord : List (List Symbol) → List Symbol
  | [] => [.terminal 107, .terminal 108]
  | first :: rest => [.terminal 107] ++
      rest.foldl commaAppend first ++ [.terminal 108]

theorem exports_many (items : List (List Symbol))
    (valid : ∀ item ∈ items, Derives productions [.nonterminal 47] item) :
    Derives productions [.nonterminal 44] (exportWord items) := by
  cases items with
  | nil => exact exports_empty
  | cons first rest =>
    have first_ok := valid first (by simp)
    have rest_ok : ∀ item ∈ rest,
        Derives productions [.nonterminal 47] item := by
      intro item member
      exact valid item (by simp [member])
    exact exports_nonempty first rest first_ok rest_ok

def semiAppend (acc item : List Symbol) : List Symbol :=
  acc ++ item ++ [.terminal 113]

theorem import_plain {moduleName : List Symbol}
    (module_ok : Derives productions [.nonterminal 321] moduleName) :
    Derives productions [.nonterminal 59] ([.terminal 12] ++ moduleName) := by
  have r114 : productions 114 = some
      (59, [.terminal 12, .nonterminal 60, .nonterminal 61,
        .nonterminal 63, .nonterminal 62, .nonterminal 321,
        .nonterminal 63, .nonterminal 64, .nonterminal 65]) := by decide
  have r116 : productions 116 = some (60, []) := by decide
  have r118 : productions 118 = some (61, []) := by decide
  have r122 : productions 122 = some (63, []) := by decide
  have r120 : productions 120 = some (62, []) := by decide
  have r124 : productions 124 = some (64, []) := by decide
  have r126 : productions 126 = some (65, []) := by decide
  have children := beside (.refl [.terminal 12])
    (beside (emptyRule r116)
      (beside (emptyRule r118)
        (beside (emptyRule r122)
          (beside (emptyRule r120)
            (beside module_ok
              (beside (emptyRule r122)
                (beside (emptyRule r124) (emptyRule r126))))))))
  simpa [List.append_assoc] using applyRule r114 children

theorem import_qualified_as {moduleName alias : List Symbol}
    (module_ok : Derives productions [.nonterminal 321] moduleName)
    (alias_ok : Derives productions [.nonterminal 321] alias) :
    Derives productions [.nonterminal 59]
      ([.terminal 12, .terminal 22] ++ moduleName ++ [.terminal 3] ++ alias) := by
  have r114 : productions 114 = some
      (59, [.terminal 12, .nonterminal 60, .nonterminal 61,
        .nonterminal 63, .nonterminal 62, .nonterminal 321,
        .nonterminal 63, .nonterminal 64, .nonterminal 65]) := by decide
  have r116 : productions 116 = some (60, []) := by decide
  have r118 : productions 118 = some (61, []) := by decide
  have r121 : productions 121 = some (63, [.terminal 22]) := by decide
  have r122 : productions 122 = some (63, []) := by decide
  have r120 : productions 120 = some (62, []) := by decide
  have r123 : productions 123 = some
      (64, [.terminal 3, .nonterminal 321]) := by decide
  have r126 : productions 126 = some (65, []) := by decide
  have asPart := applyRule r123
    (beside (.refl [.terminal 3]) alias_ok)
  have children := beside (.refl [.terminal 12])
    (beside (emptyRule r116)
      (beside (emptyRule r118)
        (beside (applyRule r121 (.refl _))
          (beside (emptyRule r120)
            (beside module_ok
              (beside (emptyRule r122)
                (beside asPart (emptyRule r126))))))))
  simpa [List.append_assoc] using applyRule r114 children

-- Rule 112 repeats importdecl followed by semis1; rule 113 starts empty.
theorem imports_many (imports : List (List Symbol))
    (valid : ∀ item ∈ imports, Derives productions [.nonterminal 59] item) :
    Derives productions [.nonterminal 58]
      (imports.foldl semiAppend []) := by
  have r112 : productions 112 = some
      (58, [.nonterminal 58, .nonterminal 59, .nonterminal 55]) := by decide
  have r113 : productions 113 = some (58, []) := by decide
  have r108 : productions 108 = some (55, [.terminal 113]) := by decide
  have extend (acc item : List Symbol)
      (acc_ok : Derives productions [.nonterminal 58] acc)
      (item_ok : Derives productions [.nonterminal 59] item) :
      Derives productions [.nonterminal 58] (semiAppend acc item) := by
    have h := beside acc_ok (beside item_ok (applyRule r108 (.refl _)))
    simpa [semiAppend, List.append_assoc] using applyRule r112 h
  have fold (acc : List Symbol) (items : List (List Symbol))
      (acc_ok : Derives productions [.nonterminal 58] acc)
      (items_ok : ∀ item ∈ items, Derives productions [.nonterminal 59] item) :
      Derives productions [.nonterminal 58] (items.foldl semiAppend acc) := by
    induction items generalizing acc with
    | nil => simpa using acc_ok
    | cons item more ih =>
      have item_ok := items_ok item (by simp)
      have more_ok : ∀ x ∈ more, Derives productions [.nonterminal 59] x := by
        intro x hx
        exact items_ok x (by simp [hx])
      simpa [List.foldl] using
        ih (semiAppend acc item) (extend acc item acc_ok item_ok) more_ok
  exact fold [] imports (emptyRule r113) valid

-- Top-level declarations are built the same way, using rules 149-151.
theorem declarations_many (decls : List (List Symbol))
    (valid : ∀ item ∈ decls, Derives productions [.nonterminal 78] item) :
    Derives productions [.nonterminal 76]
      (decls.foldl semiAppend []) := by
  have r149 : productions 149 = some
      (76, [.nonterminal 76, .nonterminal 77, .nonterminal 55]) := by decide
  have r150 : productions 150 = some (76, []) := by decide
  have r151 : productions 151 = some (77, [.nonterminal 78]) := by decide
  have r108 : productions 108 = some (55, [.terminal 113]) := by decide
  have extend (acc item : List Symbol)
      (acc_ok : Derives productions [.nonterminal 76] acc)
      (item_ok : Derives productions [.nonterminal 78] item) :
      Derives productions [.nonterminal 76] (semiAppend acc item) := by
    have h := beside acc_ok
      (beside (oneRule r151 item_ok) (applyRule r108 (.refl _)))
    simpa [semiAppend, List.append_assoc] using applyRule r149 h
  have fold (acc : List Symbol) (items : List (List Symbol))
      (acc_ok : Derives productions [.nonterminal 76] acc)
      (items_ok : ∀ item ∈ items, Derives productions [.nonterminal 78] item) :
      Derives productions [.nonterminal 76] (items.foldl semiAppend acc) := by
    induction items generalizing acc with
    | nil => simpa using acc_ok
    | cons item more ih =>
      have item_ok := items_ok item (by simp)
      have more_ok : ∀ x ∈ more, Derives productions [.nonterminal 78] x := by
        intro x hx
        exact items_ok x (by simp [hx])
      simpa [List.foldl] using
        ih (semiAppend acc item) (extend acc item acc_ok item_ok) more_ok
  exact fold [] decls (emptyRule r150) valid

-- Rule 61 is the actual GHC module production; rules 66, 69, 70 select
-- virtual braces and the import/declaration lists used by the printer.
private theorem module_frame_close {name exports imports decls : List Symbol}
    (closeId closeKind : Nat)
    (closeRule : productions closeId = some (320, [.terminal closeKind]))
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : Derives productions [.nonterminal 44] exports)
    (imports_ok : Derives productions [.nonterminal 58] imports)
    (decls_ok : Derives productions [.nonterminal 76] decls) :
    Derives productions [.nonterminal 32]
      ([.terminal 19] ++ name ++ exports ++ [.terminal 25, .terminal 103] ++
        imports ++ decls ++ [.terminal closeKind]) := by
  have r61 : productions 61 = some
      (32, [.terminal 19, .nonterminal 321, .nonterminal 140,
        .nonterminal 44, .terminal 25, .nonterminal 35]) := by decide
  have r322 : productions 322 = some (140, []) := by decide
  have r66 : productions 66 = some
      (35, [.terminal 103, .nonterminal 37, .nonterminal 320]) := by decide
  have r69 : productions 69 = some (37, [.nonterminal 56, .nonterminal 38]) := by decide
  have r110 : productions 110 = some (56, []) := by decide
  have r70 : productions 70 = some (38, [.nonterminal 58, .nonterminal 76]) := by decide
  have top1 := applyRule r70 (beside imports_ok decls_ok)
  have top := applyRule r69 (beside (emptyRule r110) top1)
  have body := applyRule r66
    (beside (.refl [.terminal 103])
      (beside top (applyRule closeRule (.refl _))))
  have head := beside (.refl [.terminal 19])
    (beside name_ok
      (beside (emptyRule r322)
        (beside exports_ok (beside (.refl [.terminal 25]) body))))
  simpa [List.append_assoc] using applyRule r61 head

theorem module_frame_virtual {name exports imports decls : List Symbol}
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : Derives productions [.nonterminal 44] exports)
    (imports_ok : Derives productions [.nonterminal 58] imports)
    (decls_ok : Derives productions [.nonterminal 76] decls) :
    Derives productions [.nonterminal 32]
      ([.terminal 19] ++ name ++ exports ++ [.terminal 25, .terminal 103] ++
        imports ++ decls ++ [.terminal 104]) := by
  exact module_frame_close 834 104 (by decide)
    name_ok exports_ok imports_ok decls_ok

-- At module EOF GHC's Happy parser uses close -> error (835). The synthetic
-- terminal zero is absent from the lexer callback sequence; eraseLayout
-- projects this raw derivation to the actual source-token word.
theorem module_frame_source {name exports imports decls : List Symbol}
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : Derives productions [.nonterminal 44] exports)
    (imports_ok : Derives productions [.nonterminal 58] imports)
    (decls_ok : Derives productions [.nonterminal 76] decls) :
    Derives (layoutGrammar productions) [.nonterminal 32]
      (sourceSymbols
        ([.terminal 19] ++ name ++ exports ++ [.terminal 25, .terminal 103] ++
          imports ++ decls)) := by
  have raw : Derives productions [.nonterminal 32]
      ([.terminal 19] ++ name ++ exports ++ [.terminal 25, .terminal 103] ++
        imports ++ decls ++ [.terminal 0]) :=
    module_frame_close 835 0 (by decide) name_ok exports_ok imports_ok decls_ok
  have erased := raw.eraseLayout
  simpa [sourceSymbols, List.filter_append, List.append_assoc] using erased

theorem module_frame_source_tokens {name exports imports decls : List Symbol}
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : Derives productions [.nonterminal 44] exports)
    (imports_ok : Derives productions [.nonterminal 58] imports)
    (decls_ok : Derives productions [.nonterminal 76] decls)
    (name_clean : sourceSymbols name = name)
    (exports_clean : sourceSymbols exports = exports)
    (imports_clean : sourceSymbols imports = imports)
    (decls_clean : sourceSymbols decls = decls) :
    Derives (layoutGrammar productions) [.nonterminal 32]
      ([.terminal 19] ++ name ++ exports ++ [.terminal 25, .terminal 103] ++
        imports ++ decls) := by
  have h := module_frame_source name_ok exports_ok imports_ok decls_ok
  simp only [sourceSymbols] at name_clean exports_clean imports_clean decls_clean
  simpa [sourceSymbols, List.filter_append, name_clean, exports_clean,
    imports_clean, decls_clean] using h

theorem generated_lists (name : List Symbol)
    (exports imports decls : List (List Symbol))
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : ∀ item ∈ exports,
      Derives productions [.nonterminal 47] item)
    (imports_ok : ∀ item ∈ imports,
      Derives productions [.nonterminal 59] item)
    (decls_ok : ∀ item ∈ decls,
      Derives productions [.nonterminal 78] item) :
    Derives (layoutGrammar productions) [.nonterminal 32]
      (sourceSymbols
        ([.terminal 19] ++ name ++ exportWord exports ++
          [.terminal 25, .terminal 103] ++
          imports.foldl semiAppend [] ++ decls.foldl semiAppend [])) := by
  exact module_frame_source name_ok (exports_many exports exports_ok)
    (imports_many imports imports_ok) (declarations_many decls decls_ok)

-- The three imports emitted by Codegen.render, in their source order.
-- Imports inside a supplied verbatim block enter separately.
def generatedImports (usesPegPrelude importsPrelude : Bool) : List (List Symbol) :=
  (if usesPegPrelude then [[.terminal 12, .terminal 22, .terminal 118,
    .terminal 3, .terminal 118]] else []) ++
  [[.terminal 12, .terminal 22, .terminal 122, .terminal 3, .terminal 118]] ++
  (if importsPrelude then [] else [[.terminal 12, .terminal 118]])

theorem generated_imports_valid (usesPegPrelude importsPrelude : Bool) :
    ∀ item ∈ generatedImports usesPegPrelude importsPrelude,
      Derives productions [.nonterminal 59] item := by
  have plain := import_plain module_name_simple
  have prelude := import_qualified_as module_name_simple module_name_simple
  have runtime := import_qualified_as module_name_qualified module_name_simple
  cases usesPegPrelude <;> cases importsPrelude <;>
    simp_all [generatedImports]

theorem generated_with_imports (name : List Symbol) (usesPegPrelude importsPrelude : Bool)
    (exports verbatimImports decls : List (List Symbol))
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : ∀ item ∈ exports, Derives productions [.nonterminal 47] item)
    (verbatim_ok : ∀ item ∈ verbatimImports, Derives productions [.nonterminal 59] item)
    (decls_ok : ∀ item ∈ decls, Derives productions [.nonterminal 78] item) :
    Derives (layoutGrammar productions) [.nonterminal 32]
      (sourceSymbols ([.terminal 19] ++ name ++ exportWord exports ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude ++ verbatimImports).foldl semiAppend [] ++
        decls.foldl semiAppend [])) := by
  apply generated_lists _ _ _ _ name_ok exports_ok _ decls_ok
  intro item h
  obtain generated | supplied := List.mem_append.mp h
  · exact generated_imports_valid _ _ _ generated
  · exact verbatim_ok _ supplied

theorem parse_module {tokens : List Symbol}
    (frame : Derives productions [.nonterminal 32] tokens) :
    Derives productions [.nonterminal 0] tokens := by
  have rule : productions 0 = some (0, [.nonterminal 32]) := by decide
  exact oneRule rule frame

#print axioms generated_imports_valid
#print axioms generated_with_imports
#print axioms exports_nonempty
#print axioms export_varid
#print axioms export_qvarid
#print axioms export_varsym
#print axioms export_minus
#print axioms export_dot
#print axioms export_colon
#print axioms export_constructor_all
#print axioms import_plain
#print axioms import_qualified_as
#print axioms imports_many
#print axioms declarations_many
#print axioms module_frame_virtual
#print axioms module_frame_source
#print axioms module_frame_source_tokens
#print axioms generated_lists
#print axioms parse_module

end PegHs.RenderModuleGHC
