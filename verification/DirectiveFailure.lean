import StrictDirective
import StrictWhitespace
import FileEntry

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

-- "%{" commits to Verbatim before Directive. For other '%' prefixes with
-- a missing name, TopOne retries Directive and propagates its label.
theorem invariant2_missing_directive_file (xs : List Char)
    (notBlock : xs.head? ≠ some '{')
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true) :
    FileResult false ('%' :: xs) (.throwLabel xs.length "ident" (some "expected an identifier")) := by
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
  have itemCall : Derives ctx (.call 1 1) n {} err :=
    Derives.call (callee := {}) (by rfl) item
  have ws : Derives ctx (ctx.rules 4) n {} (.ok n {}) :=
    invariant1_strict_ws_stop [] '%' xs {} (by decide +kernel) (by decide)
  have leading : Derives ctx (.call 0 4) n {} (.ok n {}) :=
    Derives.call (callee := {}) (by rfl) ws
  exact Derives.seqOk leading (.seqCarryThrow (.star (.loopThrow itemCall)))

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

#print axioms invariant2_missing_directive_no_module
#print axioms invariant2_missing_directive_diagnostic
end PegHs.MetaExecution
