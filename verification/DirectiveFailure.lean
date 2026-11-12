import StrictDirective
import StrictWhitespaceScan
import FileItemChain
import PrefixReplay
import FileEntry

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

-- "%{" commits to Verbatim before Directive. For other '%' prefixes with
-- a missing name, TopOne retries Directive and propagates its label.
private theorem bad_item (xs : List Char)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true) :
    Derives (context false ('%' :: xs)) (.call 1 1) (xs.length + 1) {} (.throwLabel xs.length "ident" (some "expected an identifier")) := by
  let input := '%' :: xs
  let ctx := context false input
  let n := xs.length + 1
  let err := Reply.throwLabel xs.length "ident" (some "expected an identifier")
  have lit : ctx.terms 8 = some (.lit ['%', '{']) := rfl
  have oracle := invariant1_oracle_suffix (.lit ['%', '{']) [] input
  have mismatch : matchTerm (.lit ['%', '{']) input = none := by
    cases xs with
    | nil => rfl
    | cons c cs =>
      have ne : '{' ≠ c := by intro eq; subst c; exact notBlock rfl
      simp [input, matchTerm, matchLiteral, ne]
  simp only [List.nil_append, mismatch, Option.map_none] at oracle
  have first : runFuel ctx 1 (.terminal 8) n {} = some .fail := by
    have src : ctx.input = input := rfl
    change terminalOracle _ input n = none at oracle
    simp only [runFuel, lit, src, oracle]
  have block : Derives ctx (ctx.rules 11) n {} .fail := .seqCarryFail (invariant1_runFuel_sound first)
  have attempted : Derives ctx (.call 4 11) n {} .fail :=
    Derives.call (callee := {}) (by rfl) block
  have directive : Derives ctx (ctx.rules 12) n {} err :=
    invariant2_directive_missing_name [] xs {} bad
  have labelled : Derives ctx (.call 5 12) n {} err :=
    Derives.call (callee := {}) (by rfl) directive
  have one : Derives ctx (ctx.rules 2) n {} err :=
    .altRetry attempted (.altLeft labelled (by simp [err]))
  have oneCall : Derives ctx (.call 2 2) n {} err :=
    Derives.call (callee := {}) (by rfl) one
  have item : Derives ctx (ctx.rules 1) n {} err := .seqCarryThrow oneCall
  exact Derives.call (callee := {}) (by rfl) item

theorem invariant2_missing_directive_after_items (pre xs : List Char) (ends : List Nat)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true)
    (items : let input := pre ++ '%' :: xs
      ItemStepsTo (context false input) (xs.length + 1) (afterWhitespace input).length ends) :
    FileResult false (pre ++ '%' :: xs) (.throwLabel xs.length "ident" (some "expected an identifier")) := by
  let input := pre ++ '%' :: xs
  let ctx := context false input
  have failure := bad_item xs notBlock bad
  have src : (context false ('%' :: xs)).input = '%' :: xs := rfl
  have full := invariant1_prepend_derivation pre failure (by rw [src]; exact Nat.le_refl _)
  have same : {context false ('%' :: xs) with input := pre ++ (context false ('%' :: xs)).input} = ctx := rfl
  rw [same] at full
  have scan : Derives ctx (ctx.rules 4) input.length {} (.ok (afterWhitespace input).length {}) :=
    invariant1_strict_whitespace_scan [] input {}
  have leading : Derives ctx (.call 0 4) input.length {} (.ok (afterWhitespace input).length {}) :=
    Derives.call (callee := {}) (by rfl) scan
  exact Derives.seqOk leading (.seqCarryThrow (.star (invariant2_steps_to_throw _ _ _ ends items full)))

theorem invariant2_missing_directive_file (xs : List Char)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true) :
    FileResult false ('%' :: xs) (.throwLabel xs.length "ident" (some "expected an identifier")) := by
  apply invariant2_missing_directive_after_items [] xs [] notBlock bad
  change (afterWhitespace ('%' :: xs)).length = xs.length + 1
  have ordinary : GhcPredicates.space '%' = false := by decide +kernel
  simp [afterWhitespace, ordinary]

theorem invariant2_missing_directive_diagnostic (xs : List Char)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true)
    (reply : Reply) (result : FileResult false ('%' :: xs) reply)
    (format : PublicParsing.Failure → String) :
    PublicParsing.translatedPublic format (PublicParsing.translatedRuntime
      ('%' :: xs).utf8Encode.size (FileEntry.start ('%' :: xs) reply)) =
      .error [format (.labelled "ident" (some "expected an identifier"))] := by
  obtain ⟨_, _, unique⟩ := invariant1_file_result false ('%' :: xs)
  have same := (unique _ result).trans (unique _ (invariant2_missing_directive_file xs notBlock bad)).symm
  subst reply
  rfl

theorem invariant2_missing_directive_no_module {G : Type} (xs : List Char)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true)
    (reply : Reply) (result : FileResult false ('%' :: xs) reply)
    (format : PublicParsing.Failure → String)
    (assemble : Unit → Except Pipeline.Diagnostics G) (resolve expand : G → Except Pipeline.Diagnostics G)
    (check : G → Except Pipeline.Diagnostics Unit) (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics)
    (strip : Option (G → G)) (warnings : G → G → Pipeline.Diagnostics)
    (generate : G → Except Pipeline.Diagnostics String) :
    let parsed := PublicParsing.translatedPublic format (PublicParsing.translatedRuntime
      ('%' :: xs).utf8Encode.size (FileEntry.start ('%' :: xs) reply))
    Pipeline.visible (Pipeline.pipeline (parsed.bind assemble) resolve expand check notes strip warnings generate) =
      .error [format (.labelled "ident" (some "expected an identifier"))] := by
  dsimp only
  rw [invariant2_missing_directive_diagnostic xs notBlock bad reply result format]
  rfl

theorem invariant2_after_items_diagnostic (pre xs : List Char) (ends : List Nat)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true)
    (items : let input := pre ++ '%' :: xs
      ItemStepsTo (context false input) (xs.length + 1) (afterWhitespace input).length ends)
    (reply : Reply) (result : FileResult false (pre ++ '%' :: xs) reply)
    (format : PublicParsing.Failure → String) :
    let input := pre ++ '%' :: xs
    PublicParsing.translatedPublic format (PublicParsing.translatedRuntime input.utf8Encode.size
      (FileEntry.start input reply)) = .error [format (.labelled "ident" (some "expected an identifier"))] := by
  obtain ⟨_, _, unique⟩ := invariant1_file_result false (pre ++ '%' :: xs)
  have failed := invariant2_missing_directive_after_items pre xs ends notBlock bad items
  have eq := (unique _ result).trans (unique _ failed).symm
  subst reply
  rfl

-- A comment and a complete rule precede the malformed third line.
set_option maxRecDepth 20000 in
theorem invariant2_missing_directive_third_line :
    FileResult false "# lead\nS <- .\n%42\n".toList
      (.throwLabel 3 "ident" (some "expected an identifier")) := by
  apply invariant2_missing_directive_after_items "# lead\nS <- .\n".toList "42\n".toList [4]
    (by decide) (by decide +kernel)
  refine ⟨?_, by decide +kernel, rfl⟩
  apply invariant1_runFuel_sound (fuel := 256)
  decide +kernel

#print axioms invariant2_missing_directive_no_module
#print axioms invariant2_missing_directive_diagnostic
end PegHs.MetaExecution
