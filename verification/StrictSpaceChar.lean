import SelfHostedFileProof
import TerminalCursor

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

inductive CharRule where
  | space | identStart | identChar

def CharRule.body : CharRule → Body
  | .space => translatedStrictSpaceChar
  | .identStart => translatedStrictIdentStart
  | .identChar => translatedStrictIdentChar

private def CharRule.site : CharRule → Nat
  | .space => 0 | .identStart => 1 | .identChar => 2

private def CharRule.terminal : CharRule → Nat
  | .space => 1 | .identStart => 6 | .identChar => 7

private def CharRule.kind : CharRule → SemanticPredicates.Kind
  | .space => .space | .identStart => .identStart | .identChar => .identChar

def CharRule.accepts (rule : CharRule) (c : Char) : Bool :=
  match rule with
  | .space => GhcPredicates.space c
  | .identStart => GhcPredicates.alpha c || c == '_'
  | .identChar => GhcPredicates.alnum c || c == '_' || c == '\''

private theorem CharRule.shape (rule : CharRule) :
    rule.body = .seq (.bind rule.site "c" (.capture (.terminal rule.terminal))) (.predicate rule.site) := by
  cases rule <;> rfl

-- The generated binding shadows any earlier c. The predicate reads exactly
-- the character consumed at the cursor, even after a nonempty prefix.
theorem invariant1_strict_char (rule : CharRule) (pre : List Char) (c : Char) (tail : List Char) (env : Env) :
    let input := pre ++ c :: tail
    let cleared := {env with resultDepth := 0}
    let captured := (cleared.put "c" [c]).putDepth "c" 0
    runFuel (context false input) 5 rule.body (c :: tail).length env =
      some (if rule.accepts c then .ok tail.length captured else .fail) := by
  dsimp only
  let ctx := context false (pre ++ c :: tail)
  let cleared := {env with resultDepth := 0}
  let captured := (cleared.put "c" [c]).putDepth "c" 0
  have term : ctx.terms rule.terminal = some .any := by cases rule <;> rfl
  have input : ctx.input = pre ++ c :: tail := rfl
  have step : terminalOracle .any ctx.input (c :: tail).length = some tail.length := by
    rw [input, invariant1_oracle_suffix]; rfl
  have matched : matchedText ctx.input (c :: tail).length tail.length = [c] := by
    simp [matchedText, input]
  have site : ctx.sites rule.site = some (rule.kind, true) := by
    change (context false []).sites rule.site = _
    cases rule <;> decide +kernel
  have pred : SemanticPredicates.eval ctx.classes rule.kind (ctx.predicateEnv rule.site captured) =
      rule.accepts c := by
    change SemanticPredicates.eval GhcPredicates.classes rule.kind
      (match ctx.sites rule.site with
       | some (k, _) => PredicateBindings.predicateEnv k captured
       | none => {captured := [], depth := captured.depth}) = _
    rw [site]
    cases rule <;> simp [CharRule.kind, CharRule.accepts, SemanticPredicates.eval, PredicateBindings.predicateEnv, PredicateBindings.captureName,
      captured, Env.putDepth, Env.put, Env.lookup, GhcPredicates.classes]
  change runFuel ctx 5 rule.body (c :: tail).length env = _
  simp only [rule.shape, runFuel, term, step,
    show tail.length < (c :: tail).length from Nat.lt_succ_self _, ite_true, matched, site]
  change (if SemanticPredicates.eval ctx.classes rule.kind (ctx.predicateEnv rule.site captured) == true
    then some (Reply.ok tail.length {captured with resultDepth := 0}) else some Reply.fail) = _
  rw [pred]
  cases rule.accepts c <;> rfl

theorem invariant1_strict_char_eof (rule : CharRule) (input : List Char) (env : Env) :
    runFuel (context false input) 5 rule.body 0 env = some .fail := by
  let ctx := context false input
  have term : ctx.terms rule.terminal = some .any := by cases rule <;> rfl
  have source : ctx.input = input := rfl
  have eof : terminalOracle .any ctx.input 0 = none := by
    rw [source]
    simpa [matchTerm] using invariant1_oracle_suffix .any input []
  change runFuel ctx 5 rule.body 0 env = _
  simp only [rule.shape, runFuel, term, eof]

-- The generated binding shadows any earlier c. The predicate reads exactly
-- the character consumed at the cursor, even after a nonempty prefix.
theorem invariant1_strict_space_char (pre : List Char) (c : Char) (tail : List Char) (env : Env) :
    let input := pre ++ c :: tail
    let cleared := {env with resultDepth := 0}
    let captured := (cleared.put "c" [c]).putDepth "c" 0
    runFuel (context false input) 5 translatedStrictSpaceChar (c :: tail).length env =
      some (if GhcPredicates.space c then .ok tail.length captured else .fail) := invariant1_strict_char .space pre c tail env

theorem invariant1_strict_space_char_eof (input : List Char) (env : Env) :
    runFuel (context false input) 5 translatedStrictSpaceChar 0 env = some .fail := invariant1_strict_char_eof .space input env

#print axioms invariant1_strict_char
#print axioms invariant1_strict_char_eof
end PegHs.MetaExecution
