import StrictWhitespaceScan
import StrictDirective
import StrictInlineSpace
import StrictComment
import StrictWhitespace
import FileEnd

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

-- The name, horizontal separator, and raw argument each consume their own prefix.
theorem invariant1_directive_call (pre : List Char) (c : Char) (cs : List Char) (env : Env)
    (start : CharRule.identStart.accepts c = true) :
    let afterName := cs.dropWhile CharRule.identChar.accepts
    let arg := afterName.dropWhile PegVerification.isInlineSpace
    let rest := arg.dropWhile (· != '\n')
    Derives (context false (pre ++ '%' :: c :: cs)) (.call 5 12) (cs.length + 2) env
      (.ok rest.length {env with resultDepth := 0}) := by
  let input := pre ++ '%' :: c :: cs
  let ctx := context false input
  let n := cs.length + 2
  let cleared := {env with resultDepth := 0}
  let afterName := cs.dropWhile CharRule.identChar.accepts
  let arg := afterName.dropWhile PegVerification.isInlineSpace
  let rest := arg.dropWhile (· != '\n')
  let loc := (cleared.put "l" (matchedText input n n)).putDepth "l" 0
  let named := (loc.put "n" (matchedText input (cs.length + 1) afterName.length)).putDepth "n" 0
  let argLoc := (named.put "al" (matchedText input arg.length arg.length)).putDepth "al" 0
  let result := (argLoc.put "raw" (matchedText input arg.length rest.length)).putDepth "raw" 0
  have here : Derives ctx (ctx.rules 3) n env (.ok n cleared) := .eps
  have hereCall : Derives ctx (.call 12 3) n env (.ok n cleared) :=
    Derives.call (callee := env) (by rfl) here
  have location : Derives ctx (.bind 5 "l" (.call 12 3)) n env (.ok n loc) := Derives.bind hereCall
  have literal : ctx.terms 12 = some (.lit ['%']) := rfl
  have src : ctx.input = input := rfl
  have oracle := invariant1_oracle_suffix (.lit ['%']) pre ('%' :: c :: cs)
  simp [matchTerm, matchLiteral] at oracle
  have percent : runFuel ctx 1 (.terminal 12) n loc = some (.ok (cs.length + 1) loc) := by
    simp [runFuel, literal, src, input, n, oracle, loc, Env.putDepth, Env.put, cleared]
  have identifier := invariant1_strict_identifier (pre ++ ['%']) (c :: cs) loc
  have split : (pre ++ ['%']) ++ c :: cs = input := by simp [input]
  rw [split] at identifier
  simp only [start, ite_true] at identifier
  have nameBody : Derives ctx (ctx.rules 8) (cs.length + 1) loc (.ok afterName.length loc) := identifier
  have nameCall : Derives ctx (.call 13 8) (cs.length + 1) loc (.ok afterName.length loc) :=
    Derives.call (callee := loc) (by rfl) nameBody
  have boundName := Derives.bind (site := 6) (name := "n") (Derives.label
    (name := "ident") (msg := some "expected an identifier") nameCall)
  let beforeSpace := (pre ++ ['%', c]) ++ cs.takeWhile CharRule.identChar.accepts
  have splitSpace : beforeSpace ++ afterName = input := by
    simp [beforeSpace, afterName, input, List.append_assoc]
  have spaces := invariant1_strict_inline_space beforeSpace afterName named
  rw [splitSpace] at spaces
  have spaceBody : Derives ctx (ctx.rules 7) afterName.length named (.ok arg.length named) := spaces
  have spaceCall : Derives ctx (.call 14 7) afterName.length named (.ok arg.length named) :=
    Derives.call (callee := named) (by rfl) spaceBody
  have argHere : Derives ctx (ctx.rules 3) arg.length named (.ok arg.length named) := .eps
  have argHereCall : Derives ctx (.call 15 3) arg.length named (.ok arg.length named) :=
    Derives.call (callee := named) (by rfl) argHere
  have boundArgLoc := Derives.bind (site := 7) (name := "al") argHereCall
  let beforeArg := beforeSpace ++ afterName.takeWhile PegVerification.isInlineSpace
  have splitArg : beforeArg ++ arg = input := by simpa [beforeArg, arg, List.append_assoc] using splitSpace
  have raw := invariant1_directive_argument_scan beforeArg arg argLoc
  rw [splitArg] at raw
  have boundRaw := Derives.bind (site := 8) (name := "raw") raw
  have directive : Derives ctx (ctx.rules 12) n env (.ok rest.length result) :=
    .seqOk location (.seqOk (invariant1_runFuel_sound percent) (.seqOk boundName (.seqOk spaceCall
      (.seqOk boundArgLoc boundRaw))))
  exact Derives.call (callee := env) (by rfl) directive

theorem invariant1_directive_top_item (pre : List Char) (c : Char) (cs : List Char)
    (start : CharRule.identStart.accepts c = true) :
    let rest := ((cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      |>.dropWhile (· != '\n'))
    Derives (context false (pre ++ '%' :: c :: cs)) (.call 1 1) (cs.length + 2) {}
      (.ok (afterWhitespace rest).length {}) := by
  let input := pre ++ '%' :: c :: cs
  let ctx := context false input
  let n := cs.length + 2
  let names := cs.dropWhile CharRule.identChar.accepts
  let raw := names.dropWhile PegVerification.isInlineSpace
  let rest := raw.dropWhile (· != '\n')
  have directive := invariant1_directive_call pre c cs {} start
  have ne : '{' ≠ c := by
    intro same
    subst c
    have bad : CharRule.identStart.accepts '{' = false := by decide +kernel
    simp [bad] at start
  have literal : ctx.terms 8 = some (.lit ['%', '{']) := rfl
  have src : ctx.input = input := rfl
  have oracle := invariant1_oracle_suffix (.lit ['%', '{']) pre ('%' :: c :: cs)
  simp [matchTerm, matchLiteral, ne] at oracle
  have fail : runFuel ctx 1 (.terminal 8) n {} = some .fail := by
    simp [runFuel, literal, src, input, n, oracle]
  have verbatim : Derives ctx (ctx.rules 11) n {} .fail := .seqCarryFail (invariant1_runFuel_sound fail)
  have first : Derives ctx (.call 4 11) n {} .fail := Derives.call (callee := {}) (by rfl) verbatim
  have one : Derives ctx (ctx.rules 2) n {} (.ok rest.length {}) :=
    .altRetry first (.altLeft directive (by intro h; cases h))
  have oneCall : Derives ctx (.call 2 2) n {} (.ok rest.length {}) := Derives.call (callee := {}) (by rfl) one
  let before := pre ++ ['%', c] ++ cs.takeWhile CharRule.identChar.accepts ++
    names.takeWhile PegVerification.isInlineSpace ++ raw.takeWhile (· != '\n')
  have split : before ++ rest = input := by simp [before, rest, raw, names, input, List.append_assoc]
  have scanned := invariant1_strict_whitespace_scan before rest {}
  rw [split] at scanned
  have wsCall : Derives ctx (.call 3 4) rest.length {} (.ok (afterWhitespace rest).length {}) :=
    Derives.call (rule := 4) (callee := {}) (by rfl) scanned
  have item : Derives ctx (ctx.rules 1) n {} (.ok (afterWhitespace rest).length {}) := .seqOk oneCall wsCall
  exact Derives.call (callee := {}) (by rfl) item

-- For a single directive the raw argument may extend all the way to EOF.
theorem invariant1_single_directive_file (c : Char) (cs : List Char)
    (start : CharRule.identStart.accepts c = true)
    (endOfArg : ((cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      |>.dropWhile (· != '\n')) = []) :
    FileResult false ('%' :: c :: cs) (.ok 0 {}) := by
  let input := '%' :: c :: cs
  let ctx := context false input
  let n := cs.length + 2
  have itemCall := invariant1_directive_top_item [] c cs start
  dsimp only at itemCall
  rw [endOfArg] at itemCall
  have leading : Derives ctx (ctx.rules 4) n {} (.ok n {}) :=
    invariant1_strict_ws_stop [] '%' (c :: cs) {} (by decide +kernel) (by decide)
  have firstWs : Derives ctx (.call 0 4) n {} (.ok n {}) := Derives.call (callee := {}) (by rfl) leading
  exact invariant1_file_from_top_items false input firstWs
    (.next (by simpa [afterWhitespace] using itemCall) (by dsimp [n]; omega) (invariant1_top_items_end false input {}))
    (invariant1_eof_terminal _ _)

#print axioms invariant1_single_directive_file
#print axioms invariant1_directive_call
end PegHs.MetaExecution
