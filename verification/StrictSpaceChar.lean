import SelfHostedFileProof
import TerminalCursor

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

-- The generated binding shadows any earlier c. The predicate reads exactly
-- the character consumed at the cursor, even after a nonempty prefix.
theorem invariant1_strict_space_char (pre : List Char) (c : Char) (tail : List Char) (env : Env) :
    let input := pre ++ c :: tail
    let cleared := {env with resultDepth := 0}
    let captured := (cleared.put "c" [c]).putDepth "c" 0
    runFuel (context false input) 5 translatedStrictSpaceChar (c :: tail).length env =
      some (if GhcPredicates.space c then .ok tail.length captured else .fail) := by
  dsimp only
  let ctx := context false (pre ++ c :: tail)
  let cleared := {env with resultDepth := 0}
  let captured := (cleared.put "c" [c]).putDepth "c" 0
  have term : ctx.terms 1 = some .any := rfl
  have input : ctx.input = pre ++ c :: tail := rfl
  have step : terminalOracle .any ctx.input (c :: tail).length = some tail.length := by
    rw [input, invariant1_oracle_suffix]; rfl
  have matched : matchedText ctx.input (c :: tail).length tail.length = [c] := by
    simp [matchedText, input]
  have site : ctx.sites 0 = some (.space, true) := by
    change (context false []).sites 0 = _
    decide +kernel
  have pred : SemanticPredicates.eval ctx.classes .space (ctx.predicateEnv 0 captured) =
      GhcPredicates.space c := by
    change SemanticPredicates.eval GhcPredicates.classes .space
      (match ctx.sites 0 with
       | some (k, _) => PredicateBindings.predicateEnv k captured
       | none => {captured := [], depth := captured.depth}) = _
    rw [site]
    simp [SemanticPredicates.eval, PredicateBindings.predicateEnv, PredicateBindings.captureName,
      captured, Env.putDepth, Env.put, Env.lookup, GhcPredicates.classes]
  change runFuel ctx 5 translatedStrictSpaceChar (c :: tail).length env = _
  simp only [translatedStrictSpaceChar, runFuel, term, step,
    show tail.length < (c :: tail).length from Nat.lt_succ_self _, ite_true, matched, site]
  change (if SemanticPredicates.eval ctx.classes .space (ctx.predicateEnv 0 captured) == true
    then some (Reply.ok tail.length {captured with resultDepth := 0}) else some Reply.fail) = _
  rw [pred]
  cases GhcPredicates.space c <;> rfl

theorem invariant1_strict_space_char_eof (input : List Char) (env : Env) :
    runFuel (context false input) 5 translatedStrictSpaceChar 0 env = some .fail := by
  let ctx := context false input
  have term : ctx.terms 1 = some .any := rfl
  have source : ctx.input = input := rfl
  have eof : terminalOracle .any ctx.input 0 = none := by
    rw [source]
    simpa [matchTerm] using invariant1_oracle_suffix .any input []
  change runFuel ctx 5 translatedStrictSpaceChar 0 env = _
  simp only [translatedStrictSpaceChar, runFuel, term, eof]

#print axioms invariant1_strict_space_char
#print axioms invariant1_strict_space_char_eof
end PegHs.MetaExecution
