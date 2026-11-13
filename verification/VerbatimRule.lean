import VerbatimScan

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

private def afterCapture (input xs : List Char) (env : Env) : Env :=
  let cleared := {env with resultDepth := 0}
  let loc := (cleared.put "l" (matchedText input xs.length xs.length)).putDepth "l" 0
  (loc.put "b" (matchedText input xs.length (verbatimRest xs).length)).putDepth "b" 0

private theorem beforeClose (mode : Bool) (pre xs : List Char) (env : Env) (r : Reply)
    (last : let input := pre ++ '%' :: '{' :: xs
      Derives (context mode input)
        (.label "verbatim" (some "unterminated %{ block") (.terminal (if mode then 12 else 11)))
        (verbatimRest xs).length (afterCapture input xs env) r) :
    let input := pre ++ '%' :: '{' :: xs
    Derives (context mode input) ((context mode input).rules 11) (xs.length + 2) env r := by
  dsimp only at last ⊢
  let input := pre ++ '%' :: '{' :: xs
  let ctx := context mode input
  let cleared := {env with resultDepth := 0}
  let loc := (cleared.put "l" (matchedText input xs.length xs.length)).putDepth "l" 0
  have src : ctx.input = input := by cases mode <;> rfl
  have openTerm : ctx.terms (if mode then 9 else 8) = some (.lit ['%', '{']) := by cases mode <;> rfl
  have oracle := invariant1_oracle_suffix (.lit ['%', '{']) pre ('%' :: '{' :: xs)
  simp [matchTerm, matchLiteral] at oracle
  have opening : runFuel ctx 1 (.terminal (if mode then 9 else 8)) (xs.length + 2) env =
      some (.ok xs.length cleared) := by
    simp [runFuel, openTerm, src, input, oracle, cleared, show xs.length < xs.length + 2 by omega]
  have here : ctx.rules 3 = .eps := by cases mode <;> rfl
  have entered : ctx.hooks.enterCall 11 cleared = some cleared := by cases mode <;> rfl
  have pos : Derives ctx (ctx.rules 3) xs.length cleared (.ok xs.length cleared) := by
    rw [here]; exact .eps
  have atPos : Derives ctx (.call 11 3) xs.length cleared (.ok xs.length cleared) := by
    have h := Derives.call entered pos
    cases mode <;> exact h
  have boundLoc : Derives ctx (.bind 3 "l" (.call 11 3)) xs.length cleared (.ok xs.length loc) := by
    have h := Derives.bind (site := 3) (name := "l") atPos
    cases mode <;> exact h
  have scanned := invariant1_verbatim_scan mode (pre ++ ['%', '{']) xs loc
  have same : (pre ++ ['%', '{']) ++ xs = input := by simp [input]
  rw [same] at scanned
  have boundText : Derives ctx (.bind 4 "b" (.capture (.star (verbatimChar mode)))) xs.length loc
      (.ok (verbatimRest xs).length (afterCapture input xs env)) := by
    have h := Derives.bind (site := 4) (name := "b") (Derives.capture scanned)
    cases mode <;> exact h
  rw [invariant1_verbatim_rule_shape]
  exact .seqOk (invariant1_runFuel_sound opening) (.seqOk boundLoc (.seqOk boundText last))

theorem invariant2_unterminated_verbatim (mode : Bool) (pre xs : List Char) (env : Env)
    (missing : verbatimRest xs = []) :
    let input := pre ++ '%' :: '{' :: xs
    Derives (context mode input) ((context mode input).rules 11) (xs.length + 2) env
      (.throwLabel 0 "verbatim" (some "unterminated %{ block")) := by
  apply beforeClose
  dsimp only
  rw [missing]
  apply Derives.label (r := .fail)
  apply Derives.terminalFail
  right
  exact ⟨.lit ['}', '%'], by cases mode <;> rfl, by simp⟩

private theorem rest_suffix (xs : List Char) : ∃ consumed, xs = consumed ++ verbatimRest xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    cases h : verbatimEnd (c :: cs) with
    | true => exact ⟨[], by simp [verbatimRest, h]⟩
    | false =>
      obtain ⟨consumed, eq⟩ := ih
      exact ⟨c :: consumed, by simpa [verbatimRest, h] using congrArg (List.cons c) eq⟩

-- The generated action reads b from the capture environment. Recover the
-- original source as that exact capture followed by the unconsumed suffix.
theorem invariant1_verbatim_capture_split (pre xs : List Char) (env : Env) :
    let captured := (afterCapture (pre ++ '%' :: '{' :: xs) xs env).lookup "b"
    xs = captured ++ verbatimRest xs := by
  obtain ⟨body, split⟩ := rest_suffix xs
  have lengths := congrArg List.length split
  simp only [List.length_append] at lengths
  have width : xs.length - (verbatimRest xs).length = body.length := by omega
  have capture : matchedText (pre ++ '%' :: '{' :: xs) xs.length (verbatimRest xs).length = body := by
    unfold matchedText
    simp only [List.length_append, List.length_cons, width]
    rw [show pre.length + (xs.length + 1 + 1) - xs.length = pre.length + 2 by omega]
    rw [List.drop_append]
    simp only [List.drop_of_length_le (show pre.length ≤ pre.length + 2 by omega), List.nil_append,
      Nat.add_sub_cancel_left]
    change xs.take body.length = body
    conv => lhs; rw [split]
    simp
  simpa [afterCapture, Env.lookup, Env.putDepth, Env.put, capture] using split

-- A certificate may check an isolated block ending in }% once and replay it
-- with any following grammar text without traversing the following input.
theorem invariant1_verbatim_rest_append (xs tail extra : List Char)
    (closed : verbatimRest xs = '}' :: '%' :: tail) :
    verbatimRest (xs ++ extra) = ('}' :: '%' :: tail) ++ extra := by
  induction xs with
  | nil => contradiction
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp [verbatimRest, verbatimEnd] at closed
    | cons d ds =>
      have same : verbatimEnd ((c :: d :: ds) ++ extra) = verbatimEnd (c :: d :: ds) := rfl
      cases h : verbatimEnd (c :: d :: ds) with
      | true =>
        simp only [verbatimRest, h, ite_true] at closed
        change verbatimRest (c :: ((d :: ds) ++ extra)) = _
        rw [verbatimRest]
        change (if verbatimEnd ((c :: d :: ds) ++ extra) then _ else _) = _
        rw [same, h]
        exact congrArg (· ++ extra) closed
      | false =>
        rw [verbatimRest] at closed
        simp only [h, Bool.false_eq_true, ite_false] at closed
        change verbatimRest (c :: ((d :: ds) ++ extra)) = _
        rw [verbatimRest]
        change (if verbatimEnd ((c :: d :: ds) ++ extra) then _ else _) = _
        rw [same, h]
        exact ih closed

-- A successful call returns to its caller without leaking the two local captures.
theorem invariant1_closed_verbatim_call (mode : Bool) (pre xs tail : List Char) (env : Env)
    (closed : verbatimRest xs = '}' :: '%' :: tail) :
    let input := pre ++ '%' :: '{' :: xs
    Derives (context mode input) (.call 4 11) (xs.length + 2) env
      (.ok tail.length {env with resultDepth := 0}) := by
  let input := pre ++ '%' :: '{' :: xs
  let ctx := context mode input
  let captured := afterCapture input xs env
  have found : ctx.terms (if mode then 12 else 11) = some (.lit ['}', '%']) := by cases mode <;> rfl
  obtain ⟨consumed, eq⟩ := rest_suffix xs
  rw [closed] at eq
  have src : ctx.input = ((pre ++ ['%', '{']) ++ consumed) ++ ('}' :: '%' :: tail) := by
    have source : ctx.input = input := by cases mode <;> rfl
    rw [source]; unfold input; rw [eq]; simp
  have oracle := invariant1_oracle_at_cursor (term := .lit ['}', '%']) src
    (remaining := ('}' :: '%' :: tail).length) rfl
  simp [matchTerm, matchLiteral] at oracle
  have ending : runFuel ctx 1 (.terminal (if mode then 12 else 11)) (verbatimRest xs).length captured =
      some (.ok tail.length {captured with resultDepth := 0}) := by
    simp [closed, runFuel, found, oracle, show tail.length < tail.length + 1 + 1 by omega]
  have done := beforeClose mode pre xs env _ (Derives.label
    (name := "verbatim") (msg := some "unterminated %{ block") (invariant1_runFuel_sound ending))
  have entered : ctx.hooks.enterCall 4 env = some env := by cases mode <;> rfl
  have called := Derives.call (rule := 11) entered done
  cases mode <;> exact called

theorem invariant1_verbatim_top_item (mode : Bool) (pre xs tail : List Char) (rest : Nat)
    (closed : verbatimRest xs = '}' :: '%' :: tail)
    (ws : Derives (context mode (pre ++ '%' :: '{' :: xs)) (.call 3 4) tail.length {} (.ok rest {})) :
    Derives (context mode (pre ++ '%' :: '{' :: xs)) (.call 1 1) (xs.length + 2) {} (.ok rest {}) := by
  let ctx := context mode (pre ++ '%' :: '{' :: xs)
  have verb := invariant1_closed_verbatim_call mode pre xs tail {} closed
  have shape : ctx.rules 2 = .alt (.call 4 11) (.alt (.call 5 12) (.call 6 13)) := by cases mode <;> rfl
  have child : Derives ctx (ctx.rules 2) (xs.length + 2) {} (.ok tail.length {}) := by
    rw [shape]; exact .altLeft verb (by intro h; cases h)
  have top : Derives ctx (.call 2 2) (xs.length + 2) {} (.ok tail.length {}) := by
    have entered : ctx.hooks.enterCall 2 {} = some {} := by cases mode <;> rfl
    have h := Derives.call entered child
    cases mode <;> exact h
  have item : Derives ctx (ctx.rules 1) (xs.length + 2) {} (.ok rest {}) := by
    cases mode with
    | false => exact .seqOk top ws
    | true =>
      have any : ctx.terms 1 = some .any := rfl
      have src : ctx.input = pre ++ '%' :: '{' :: xs := rfl
      have oracle := invariant1_oracle_suffix .any pre ('%' :: '{' :: xs)
      simp [matchTerm] at oracle
      have seen : runFuel ctx 1 (.terminal 1) (xs.length + 2) {} = some (.ok (xs.length + 1) {}) := by
        simp [runFuel, any, src, oracle]
      exact .seqOk (.ahead (invariant1_runFuel_sound seen)) (.seqOk (.label top) ws)
  have entered : ctx.hooks.enterCall 1 {} = some {} := by cases mode <;> rfl
  have h := Derives.call entered item
  cases mode <;> exact h

#print axioms invariant1_verbatim_top_item
#print axioms invariant1_closed_verbatim_call
#print axioms invariant2_unterminated_verbatim
end PegHs.MetaExecution
