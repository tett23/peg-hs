import RenderPrimitiveStatement

/-
Codegen.exprCodeU's printing as total Lean functions, and a lexer bridge from
the printed text to GHC terminal IDs (ADR 0097 invariant 3).

`PExpr` is the printing tree of exprCodeU for the expressions without user
code: `.`, a rule reference without arguments, a literal, a character class,
the ten wrappers (`*`, `+`, `?` with and without a value, `&`, `!`, `$`,
`~`), and a group whose alternatives are do blocks of item statements ending
in `PegPrelude.pure ()` or `PegPrelude.pure v`. `render` is its text, as
exprCodeU, wrap, doBlock, itemStmt and passThroughOf print it, with
Literal.encodeLiteral for `hsString` and Literal.encodeEndpoint for `showT`
on a character. The choices that need the grammar's analysis (`many` or
`skipMany`, which statement form an item gets, the fresh names) are fields of
the tree; check-render-printing.sh builds the tree from the real Env and
compares `render` with exprCodeU's text.

`lexModel` is a total lexer for the characters that `render` prints:
identifiers and qualified identifiers, the reserved ids `do` and `_`, the
reserved op `<-`, string and character literals, and the special characters
`( ) [ ] , ; { }`. Its classes follow GHC 9.10.3's Lexer.x; a word it does not
know (another reserved word of reservedWordsFM, an operator other than `<-`,
an unterminated literal) gives `none`, so the model never claims a token GHC
would not give.

Theorems:
- `printed_lexes`: `lexModel (render e) = some (tokens e)` for every
  tree whose names are valid. This replaces, for these expressions, the
  lexer equations that RenderExpressionGHC.bridge_wrap, bridge_choice and
  bridge_do take as premises: the printer's token word is now computed.
- `printed_derives`: `tokens e` derives from GHC Parser.y's `exp`
  (nonterminal 211), and from `texp` (229), the argument position.
- `printed_ghc`: GHC's lexer, wherever it agrees with `lexModel` on the
  printed text, gives a word that derives from `exp`.
- `render_wrap`, `render_group`: `render` is RenderExpression.renderWrap,
  renderChoice and renderDo, the string models that check-render-expression.sh
  pins to Codegen.hs.

Premises left explicit in the theorems:
- `valid` (`valid e = true`): rule names consist of ASCII `idTail`
  characters (RenderExpression.RuleTail with RenderExpressionLexer's ASCII
  classes), and bound names are varids outside GHC's reserved words. The
  checker also accepts rule names with other Unicode letters; the model's
  lexer does not read them, and check-render-printing.sh leaves those texts
  out.
- `agrees` (printed_ghc): GHC's lexer on the printed expression gives the
  model's word. This is the lexer bridge. It is about the text after
  Codegen.finalize (RenderFinalizeModule): the printed expressions here hold
  no user code and so no restore marker, every line break they print is
  followed by ten spaces, and check-render-printing.sh finds each printed text
  unchanged in the finalized module that peg-hs gen writes. The same script
  compares `lexModel` with the terminal IDs that GHC 9.10.3's lexer passes to
  the parser, for every printed expression of the repository's grammars.
-/

namespace PegHs.RenderPrinting

open CFG GHCGrammar

/-! ## The model lexer -/

-- Characters that end an identifier: layout whitespace and GHC's special
-- characters (Lexer.x `$special`) that the printer uses.
def isBreak (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '(' || c == ')' || c == '[' || c == ']' ||
    c == ',' || c == ';' || c == '{' || c == '}'

def breakToken (c : Char) : List (Option Symbol) :=
  if c == '(' then [some (.terminal 107)]
  else if c == ')' then [some (.terminal 108)]
  else if c == '[' then [some (.terminal 105)]
  else if c == ']' then [some (.terminal 106)]
  else if c == ',' then [some (.terminal 114)]
  else if c == ';' then [some (.terminal 113)]
  else if c == '{' then [some (.terminal 101)]
  else if c == '}' then [some (.terminal 102)]
  else []

-- reservedWordsFM of GHC 9.10.3's Lexer.x (check-render-printing.sh compares
-- the list). Each of them lexes as its own token, never as ITvarid.
def reservedWords : List String :=
  ["_", "as", "case", "cases", "class", "data", "default", "deriving", "do",
   "else", "hiding", "if", "import", "in", "infix", "infixl", "infixr",
   "instance", "let", "module", "newtype", "of", "qualified", "then", "type",
   "where", "forall", "mdo", "family", "role", "pattern", "static", "stock",
   "anyclass", "via", "group", "by", "using", "foreign", "export", "label",
   "dynamic", "safe", "interruptible", "unsafe", "stdcall", "ccall", "capi",
   "prim", "javascript", "unit", "dependency", "signature", "rec", "proc"]

def varChars : List Char → Bool
  | [] => false
  | c :: cs => RenderExpressionLexer.asciiLower c && cs.all RenderExpressionLexer.idTail

def conChars : List Char → Bool
  | [] => false
  | c :: cs => RenderExpressionLexer.asciiUpper c && cs.all RenderExpressionLexer.idTail

def reserved (w : List Char) : Bool := reservedWords.any (·.toList == w)

def plainVar (w : List Char) : Bool := varChars w && !reserved w

def splitQualified : List Char → List Char → Option (List Char × List Char)
  | _, [] => none
  | acc, c :: cs => if c == '.' then some (acc.reverse, cs) else splitQualified (c :: acc) cs

-- One module component: Lexer.x's (@conid \.) @varid.
def qualifiedVar (w : List Char) : Bool :=
  match splitQualified [] w with
  | none => false
  | some (m, v) => conChars m && plainVar v

-- The token of a word of non-break characters.
def wordToken (w : List Char) : Option Symbol :=
  if w == ['d', 'o'] then some (.terminal 125)
  else if w == ['_'] then some (.terminal 2)
  else if w == ['<', '-'] then some (.terminal 82)
  else if plainVar w then some (.terminal 117)
  else if qualifiedVar w then some (.terminal 121)
  else none

inductive Mode where
  | word (acc : List Char)  -- the current word, reversed
  | str | strEsc | chr | chrEsc
  deriving DecidableEq, Repr

def flush : List Char → List (Option Symbol)
  | [] => []
  | acc => [wordToken acc.reverse]

def step : Mode → Char → List (Option Symbol) × Mode
  | .word acc, c =>
    if isBreak c then (flush acc ++ breakToken c, .word [])
    else if acc = [] ∧ c = '"' then ([], .str)
    else if acc = [] ∧ c = '\'' then ([], .chr)
    else ([], .word (c :: acc))
  | .str, c =>
    if c = '\\' then ([], .strEsc)
    else if c = '"' then ([some (.terminal 130)], .word [])
    else ([], .str)
  | .strEsc, _ => ([], .str)
  | .chr, c =>
    if c = '\\' then ([], .chrEsc)
    else if c = '\'' then ([some (.terminal 129)], .word [])
    else ([], .chr)
  | .chrEsc, _ => ([], .chr)

def run (m : Mode) : List Char → List (Option Symbol) × Mode
  | [] => ([], m)
  | c :: cs =>
    let first := step m c
    let rest := run first.2 cs
    (first.1 ++ rest.1, rest.2)

def finish : Mode → List (Option Symbol)
  | .word acc => flush acc
  | _ => [none]

def lexChars (cs : List Char) : List (Option Symbol) :=
  let r := run (.word []) cs
  r.1 ++ finish r.2

def lexModel (s : String) : Option (List Symbol) :=
  (lexChars s.toList).mapM id

theorem run_append (m : Mode) (s t : List Char) :
    run m (s ++ t) =
      ((run m s).1 ++ (run (run m s).2 t).1, (run (run m s).2 t).2) := by
  induction s generalizing m with
  | nil => simp [run]
  | cons c cs ih => simp [run, ih, List.append_assoc]

theorem mapM_some (xs : List Symbol) : xs.mapM some = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-! ## Closed texts

A text is closed with a token word when lexing it from the start of a word
gives that word once the last identifier is flushed. A break character after
it flushes that identifier, so closed texts compose at breaks. -/

def Closed (s : String) (ts : List Symbol) : Prop :=
  ∃ pre w, run (.word []) s.toList = (pre, .word w) ∧ pre ++ flush w = ts.map some

-- The text ends between tokens: nothing is pending.
abbrev Clean (s : String) (ts : List Symbol) : Prop :=
  run (.word []) s.toList = (ts.map some, .word [])

theorem Clean.closed {s : String} {ts : List Symbol} (h : Clean s ts) : Closed s ts :=
  ⟨ts.map some, [], h, by simp [flush]⟩

theorem Closed.lex {s : String} {ts : List Symbol} (h : Closed s ts) :
    lexModel s = some ts := by
  obtain ⟨pre, w, hrun, htok⟩ := h
  simp [lexModel, lexChars, hrun, finish, htok]
  exact mapM_some ts

theorem step_break (acc : List Char) (c : Char) (hc : isBreak c = true) :
    step (.word acc) c = (flush acc ++ breakToken c, .word []) := by
  simp [step, hc]

theorem Closed.append_break {s u : String} {ts us : List Symbol} {c : Char}
    (left : Closed s ts) (hc : isBreak c = true) (right : Closed (String.singleton c ++ u) us) :
    Closed (s ++ String.singleton c ++ u) (ts ++ us) := by
  obtain ⟨pre, w, hrun, htok⟩ := left
  obtain ⟨pre', w', hrun', htok'⟩ := right
  refine ⟨pre ++ flush w ++ pre', w', ?_, ?_⟩
  · have hr' : run (.word []) (c :: u.toList) = (pre', .word w') := by simpa using hrun'
    have tail : run (.word w) (c :: u.toList) = (flush w ++ pre', .word w') := by
      have e0 := hr'
      simp only [run, step_break _ _ hc] at e0 ⊢
      simp only [flush, List.nil_append] at e0
      obtain ⟨e1, e2⟩ := Prod.mk.inj e0
      rw [← e1, e2]
      simp [List.append_assoc]
    have split : (s ++ String.singleton c ++ u).toList = s.toList ++ (c :: u.toList) := by
      simp [String.toList_append]
    rw [split, run_append, hrun]
    simp only [tail, List.append_assoc]
  · rw [List.map_append, ← htok, ← htok']
    simp [List.append_assoc]

theorem Clean.append {s u : String} {ts us : List Symbol}
    (left : Clean s ts) (right : Closed u us) : Closed (s ++ u) (ts ++ us) := by
  obtain ⟨pre, w, hrun, htok⟩ := right
  refine ⟨ts.map some ++ pre, w, ?_, ?_⟩
  · rw [String.toList_append, run_append, left]
    simp [hrun]
  · simp [List.append_assoc, htok]

theorem Clean.append_clean {s u : String} {ts us : List Symbol}
    (left : Clean s ts) (right : Clean u us) : Clean (s ++ u) (ts ++ us) := by
  unfold Clean at *
  rw [String.toList_append, run_append, left]
  simp [right]

def StartsBreak (u : String) : Prop :=
  ∃ c cs, u.toList = c :: cs ∧ isBreak c = true

theorem StartsBreak.append {u : String} (v : String) (h : StartsBreak u) :
    StartsBreak (u ++ v) := by
  obtain ⟨c, cs, hu, hc⟩ := h
  exact ⟨c, cs ++ v.toList, by simp [String.toList_append, hu], hc⟩

theorem Closed.append {s u : String} {ts us : List Symbol}
    (left : Closed s ts) (hu : StartsBreak u) (right : Closed u us) :
    Closed (s ++ u) (ts ++ us) := by
  obtain ⟨c, cs, hlist, hc⟩ := hu
  have eq : u = String.singleton c ++ String.ofList cs := by
    apply String.toList_injective
    simp [String.toList_append, hlist]
  rw [eq] at right ⊢
  have joined := Closed.append_break left hc right
  rwa [String.append_assoc] at joined

/-! ## Identifiers -/

theorem run_word (acc cs : List Char) (hne : acc ≠ [])
    (h : ∀ c ∈ cs, isBreak c = false) :
    run (.word acc) cs = ([], .word (cs.reverse ++ acc)) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    have hc : isBreak c = false := h c (by simp)
    have rest : ∀ x ∈ cs, isBreak x = false := fun x hx => h x (by simp [hx])
    simp [run, step, hc, hne, ih (c :: acc) (by simp) rest]

theorem closed_word {s : String} {c : Char} {cs : List Char} {t : Symbol}
    (hs : s.toList = c :: cs) (hc : isBreak c = false) (hq : c ≠ '"') (ha : c ≠ '\'')
    (hrest : ∀ x ∈ cs, isBreak x = false) (tok : wordToken (c :: cs) = some t) :
    Closed s [t] := by
  refine ⟨[], cs.reverse ++ [c], ?_, ?_⟩
  · rw [hs]
    simp [run, step, hc, hq, ha, run_word [c] cs (by simp) hrest]
  · simp [flush, tok]

theorem idTail_not_break {c : Char} (h : RenderExpressionLexer.idTail c = true) :
    isBreak c = false := by
  have small : c.toNat < 128 := by
    simp [RenderExpressionLexer.idTail, RenderExpressionLexer.asciiLower,
      RenderExpressionLexer.asciiUpper, RenderExpressionLexer.asciiDigit] at h
    rcases h with (((⟨_, h⟩ | rfl) | ⟨_, h⟩) | ⟨_, h⟩) | rfl <;> first | omega | decide
  have ascii : ∀ n : Fin 128, RenderExpressionLexer.idTail (Char.ofNat n.val) = true →
      isBreak (Char.ofNat n.val) = false := by decide
  simpa using ascii ⟨c.toNat, small⟩ (by simpa using h)

theorem varChars_head {c : Char} {cs : List Char} (h : varChars (c :: cs) = true) :
    isBreak c = false ∧ c ≠ '"' ∧ c ≠ '\'' ∧ ∀ x ∈ cs, isBreak x = false := by
  simp only [varChars, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨lower, tail⟩ := h
  have lowTail : RenderExpressionLexer.idTail c = true := by
    simp [RenderExpressionLexer.idTail, lower]
  refine ⟨idTail_not_break lowTail, ?_, ?_, fun x hx => idTail_not_break (tail x hx)⟩
  · intro eq; subst eq; simp [RenderExpressionLexer.asciiLower] at lower
  · intro eq; subst eq; simp [RenderExpressionLexer.asciiLower] at lower

theorem plainVar_token {w : List Char} (h : plainVar w = true) :
    wordToken w = some (.terminal 117) := by
  have notDo : w ≠ ['d', 'o'] := by
    intro eq; subst eq; revert h; decide
  have notWild : w ≠ ['_'] := by
    intro eq; subst eq; revert h; decide
  have notArrow : w ≠ ['<', '-'] := by
    intro eq; subst eq; revert h; decide
  simp [wordToken, notDo, notWild, notArrow, h]

theorem closed_var {s : String} (h : plainVar s.toList = true) :
    Closed s [.terminal 117] := by
  cases hs : s.toList with
  | nil => rw [hs] at h; simp [plainVar, varChars] at h
  | cons c cs =>
    rw [hs] at h
    have hv : varChars (c :: cs) = true := by
      simp only [plainVar, Bool.and_eq_true] at h; exact h.1
    obtain ⟨hb, hq, ha, hrest⟩ := varChars_head hv
    exact closed_word hs hb hq ha hrest (plainVar_token h)

theorem reserved_no_apostrophe {w : List Char} (h : '\'' ∈ w) : reserved w = false := by
  have none : ∀ r ∈ reservedWords, '\'' ∉ r.toList := by decide
  cases hr : reserved w with
  | false => rfl
  | true =>
    simp only [reserved, List.any_eq_true, beq_iff_eq] at hr
    obtain ⟨r, mem, eq⟩ := hr
    exact absurd (eq ▸ h) (none r mem)

theorem varChars_varId (s : String) :
    varChars s.toList = RenderExpressionLexer.varId s := by
  simp only [RenderExpressionLexer.varId]
  cases s.toList <;> rfl

theorem rule_plainVar (name : String)
    (valid : ∀ c ∈ name.toList, RenderExpressionLexer.idTail c = true) :
    plainVar (Peg.Verification.RenderExpression.renderRule name).toList = true := by
  have v := RenderExpressionLexer.rule_name_ascii name valid
  have hv : varChars (Peg.Verification.RenderExpression.renderRule name).toList = true := by
    rw [varChars_varId]; exact v
  have ap : '\'' ∈ (Peg.Verification.RenderExpression.renderRule name).toList := by
    simp [Peg.Verification.RenderExpression.renderRule, String.toList_append]
  simp [plainVar, hv, reserved_no_apostrophe ap]

/-! ## Literals -/

theorem run_str_plain (xs : List Char) (h : ∀ x ∈ xs, x ≠ '\\' ∧ x ≠ '"') :
    run .str xs = ([], .str) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x (by simp)
    simp [run, step, h1, h2, ih (fun y hy => h y (by simp [hy]))]

theorem run_chr_plain (xs : List Char) (h : ∀ x ∈ xs, x ≠ '\\' ∧ x ≠ '\'') :
    run .chr xs = ([], .chr) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x (by simp)
    simp [run, step, h1, h2, ih (fun y hy => h y (by simp [hy]))]

theorem digits_plain (n : Nat) :
    ∀ x ∈ n.repr.toList, x ≠ '\\' ∧ x ≠ '"' ∧ x ≠ '\'' := by
  intro x member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10)
    (show x ∈ Nat.toDigits 10 n from by simpa [Nat.repr] using member)
  refine ⟨?_, ?_, ?_⟩ <;> (intro eq; subst eq; revert digit; decide)

theorem repr_nonempty (n : Nat) : ∃ d ds, n.repr.toList = d :: ds := by
  cases h : n.repr.toList with
  | nil =>
    simp [Nat.repr] at h
  | cons d ds => exact ⟨d, ds, rfl⟩

theorem encodeChar_high (c : Char) (high : 127 < c.toNat) :
    Peg.Verification.encodeChar c = "\\" ++ c.toNat.repr := by
  have hn : (c == '\n') = false := by
    simp only [beq_eq_false_iff_ne]; intro e; subst e; revert high; decide
  have ht : (c == '\t') = false := by
    simp only [beq_eq_false_iff_ne]; intro e; subst e; revert high; decide
  unfold Peg.Verification.encodeChar
  split
  next h => exfalso; have e := beq_iff_eq.mp h; subst e; revert high; decide
  next =>
    split
    next h => exfalso; have e := beq_iff_eq.mp h; subst e; revert high; decide
    next => simp [hn, ht]

theorem run_str_encodeChar (c : Char) :
    run .str (Peg.Verification.encodeChar c).toList = ([], .str) := by
  by_cases high : 127 < c.toNat
  · obtain ⟨d, ds, hd⟩ := repr_nonempty c.toNat
    have plain := digits_plain c.toNat
    rw [hd] at plain
    have hds : ∀ x ∈ ds, x ≠ '\\' ∧ x ≠ '"' := fun x hx =>
      ⟨(plain x (by simp [hx])).1, (plain x (by simp [hx])).2.1⟩
    rw [encodeChar_high c high]
    simp [String.toList_append, hd, run, step, run_str_plain ds hds]
  · have ascii : ∀ n : Fin 128,
        run .str (Peg.Verification.encodeChar (Char.ofNat n.val)).toList = ([], .str) := by
      decide
    simpa using ascii ⟨c.toNat, by omega⟩

theorem run_str_body (cs : List Char) :
    run .str (Peg.Verification.encodeBody cs).toList = ([], .str) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    unfold Peg.Verification.encodeBody
    split
    · simp [String.toList_append, run_append, run_str_encodeChar, ih, run, step]
    · simp [String.toList_append, run_append, run_str_encodeChar, ih]

theorem clean_literal (s : String) :
    Clean (Peg.Verification.encodeLiteral s) [.terminal 130] := by
  unfold Clean Peg.Verification.encodeLiteral
  simp [String.toList_append, run_append, run, step, isBreak, run_str_body]

theorem clean_endpoint (c : Char) :
    Clean (Peg.Verification.encodeEndpoint c) [.terminal 129] := by
  unfold Clean
  by_cases high : 127 < c.toNat
  · obtain ⟨d, ds, hd⟩ := repr_nonempty c.toNat
    have plain := digits_plain c.toNat
    rw [hd] at plain
    have hds : ∀ x ∈ ds, x ≠ '\\' ∧ x ≠ '\'' := fun x hx =>
      ⟨(plain x (by simp [hx])).1, (plain x (by simp [hx])).2.2⟩
    have h39 : c.toNat ≠ 39 := by omega
    have hq : (c == '"') = false := by
      simp only [beq_eq_false_iff_ne]; intro e; subst e; revert high; decide
    simp [Peg.Verification.encodeEndpoint, encodeChar_high c high, h39, hq,
      String.toList_append, hd, run_append, run, step, isBreak, run_chr_plain ds hds]
  · have ascii : ∀ n : Fin 128,
        run (.word []) (Peg.Verification.encodeEndpoint (Char.ofNat n.val)).toList =
          ([some (.terminal 129)], .word []) := by
      decide
    simpa using ascii ⟨c.toNat, by omega⟩

/-! ## The printing tree of exprCodeU -/

inductive Wrapper where
  | many | skipMany | many1 | skipMany1 | optional | skipOptional
  | andP | notP | capture | voidP
  deriving DecidableEq, Repr

def Wrapper.name : Wrapper → String
  | .many => "PegRt.many"
  | .skipMany => "PegRt.skipMany"
  | .many1 => "PegRt.many1"
  | .skipMany1 => "PegRt.skipMany1"
  | .optional => "PegRt.optional"
  | .skipOptional => "PegRt.skipOptional"
  | .andP => "PegRt.andP"
  | .notP => "PegRt.notP"
  | .capture => "PegRt.capture"
  | .voidP => "PegRt.voidP"

-- The last statement of a group's alternative.
inductive Final where
  | unit
  | var (name : String)
  deriving DecidableEq, Repr

mutual
inductive PExpr where
  | any
  | ref (name : String)
  | lit (value source : String)
  | cls (ranges : List (Char × Char)) (source : String)
  | wrap (f : Wrapper) (inner : PExpr)
  | group (first : Alt) (rest : Alts)
  deriving Repr

-- The alternatives after the first.
inductive Alts where
  | nil
  | cons (alt : Alt) (rest : Alts)
  deriving Repr

-- The statements of a do block, ending in its final statement.
inductive Alt where
  | last (final : Final)
  | cons (stmt : Stmt) (rest : Alt)
  deriving Repr

inductive Stmt where
  | expr (e : PExpr)
  | bind (name : String) (e : PExpr)
  | discard (e : PExpr)
  deriving Repr
end

def Final.text : Final → String
  | .unit => "PegPrelude.pure ()"
  | .var v => "PegPrelude.pure " ++ v

def rangeText (r : Char × Char) : String :=
  "(" ++ Peg.Verification.encodeEndpoint r.1 ++ ", " ++
    Peg.Verification.encodeEndpoint r.2 ++ ")"

def doOpen : String := "do { "
def stmtSep : String := "\n          ; "
def doClose : String := "\n          }"

mutual
def render : PExpr → String
  | .any => "PegRt.anyChar"
  | .ref n => "peg'rule'" ++ n
  | .lit v s => "PegRt.lit " ++ Peg.Verification.encodeLiteral v ++ " " ++
      Peg.Verification.encodeLiteral s
  | .cls rs s => "PegRt.cls [" ++ String.intercalate ", " (rs.map rangeText) ++ "] " ++
      Peg.Verification.encodeLiteral s
  | .wrap f e => f.name ++ " (" ++ render e ++ ")"
  | .group a as => "PegRt.choice [" ++ (doOpen ++ renderBody a ++ doClose) ++
      renderAlts as ++ "]"

def renderAlts : Alts → String
  | .nil => ""
  | .cons a r => ", " ++ (doOpen ++ renderBody a ++ doClose) ++ renderAlts r

def renderBody : Alt → String
  | .last f => f.text
  | .cons st r => renderStmt st ++ stmtSep ++ renderBody r

def renderStmt : Stmt → String
  | .expr e => render e
  | .bind v e => v ++ " <- " ++ render e
  | .discard e => "_ <- " ++ render e
end

def renderAlt (a : Alt) : String := doOpen ++ renderBody a ++ doClose

/-! ## The token word of the printed text -/

@[simp] abbrev t (n : Nat) : Symbol := .terminal n

def rangePair : List Symbol := [t 107, t 129, t 114, t 129, t 108]

def rangeTokens : List (Char × Char) → List Symbol
  | [] => []
  | _ :: rest => rest.foldl (fun acc _ => RenderExpressionGHC.commaAppend acc rangePair) rangePair

def Final.tokens : Final → List Symbol
  | .unit => [t 121, t 107, t 108]
  | .var _ => [t 121, t 117]

mutual
def tokens : PExpr → List Symbol
  | .any => [t 121]
  | .ref _ => [t 117]
  | .lit _ _ => [t 121, t 130, t 130]
  | .cls rs _ => [t 121, t 105] ++ rangeTokens rs ++ [t 106, t 130]
  | .wrap _ e => [t 121, t 107] ++ tokens e ++ [t 108]
  | .group a as => [t 121, t 105] ++ ([t 125, t 101] ++ bodyTokens a ++ [t 102]) ++
      altsTokens as ++ [t 106]

def altsTokens : Alts → List Symbol
  | .nil => []
  | .cons a r => [t 114] ++ ([t 125, t 101] ++ bodyTokens a ++ [t 102]) ++ altsTokens r

def bodyTokens : Alt → List Symbol
  | .last f => f.tokens
  | .cons st r => stmtTokens st ++ [t 113] ++ bodyTokens r

def stmtTokens : Stmt → List Symbol
  | .expr e => tokens e
  | .bind _ e => [t 117, t 82] ++ tokens e
  | .discard e => [t 2, t 82] ++ tokens e
end

def blockTokens (a : Alt) : List Symbol := [t 125, t 101] ++ bodyTokens a ++ [t 102]

/-! ## Valid names -/

def Final.valid : Final → Bool
  | .unit => true
  | .var v => plainVar v.toList

mutual
def valid : PExpr → Bool
  | .any => true
  | .ref n => n.toList.all RenderExpressionLexer.idTail
  | .lit _ _ => true
  | .cls _ _ => true
  | .wrap _ e => valid e
  | .group a as => validBody a && validAlts as

def validAlts : Alts → Bool
  | .nil => true
  | .cons a r => validBody a && validAlts r

def validBody : Alt → Bool
  | .last f => f.valid
  | .cons st r => validStmt st && validBody r

def validStmt : Stmt → Bool
  | .expr e => valid e
  | .bind v e => plainVar v.toList && valid e
  | .discard e => valid e
end

/-! ## The printed text lexes as its token word -/

def closedB (s : String) (ts : List Symbol) : Bool :=
  match run (.word []) s.toList with
  | (pre, .word w) => pre ++ flush w == ts.map some
  | _ => false

theorem closedB_sound {s : String} {ts : List Symbol} (h : closedB s ts = true) :
    Closed s ts := by
  unfold closedB at h
  split at h
  next pre w hrun => exact ⟨pre, w, hrun, by simpa using h⟩
  next => contradiction

def startsBreakB (u : String) : Bool :=
  match u.toList with
  | c :: _ => isBreak c
  | [] => false

theorem startsBreakB_sound {u : String} (h : startsBreakB u = true) : StartsBreak u := by
  unfold startsBreakB at h
  split at h
  next c cs hu => exact ⟨c, cs, hu, h⟩
  next => contradiction

theorem wrapper_closed (f : Wrapper) : Closed f.name [t 121] := by
  cases f <;> exact closedB_sound (by decide)

theorem final_closed (f : Final) (h : f.valid = true) : Closed f.text f.tokens := by
  cases f with
  | unit => exact closedB_sound (by decide)
  | var v =>
    have hv : plainVar v.toList = true := by simpa [Final.valid] using h
    have pure : Clean "PegPrelude.pure " [t 121] := by decide
    simpa [Final.text, Final.tokens] using pure.append (closed_var hv)

theorem range_clean (r : Char × Char) : Clean (rangeText r) rangePair := by
  have h := ((((show Clean "(" [t 107] by decide).append_clean (clean_endpoint r.1)).append_clean
    (show Clean ", " [t 114] by decide)).append_clean (clean_endpoint r.2)).append_clean
    (show Clean ")" [t 108] by decide)
  simpa [rangeText, rangePair, String.append_assoc] using h

theorem ranges_clean (rs : List (Char × Char)) :
    Clean (String.intercalate ", " (rs.map rangeText)) (rangeTokens rs) := by
  cases rs with
  | nil => decide
  | cons r rest =>
    have fold (items : List (Char × Char)) (accS : String) (accT : List Symbol)
        (acc : Clean accS accT) :
        Clean ((items.map rangeText).foldl (fun a item => a ++ ", " ++ item) accS)
          (items.foldl (fun a _ => RenderExpressionGHC.commaAppend a rangePair) accT) := by
      induction items generalizing accS accT with
      | nil => simpa using acc
      | cons x xs ih =>
        apply ih
        have h := (acc.append_clean (show Clean ", " [t 114] by decide)).append_clean
          (range_clean x)
        simpa [RenderExpressionGHC.commaAppend, List.append_assoc, t] using h
    rw [List.map_cons, RenderExpressionLexer.intercalate_cons]
    exact fold rest _ _ (range_clean r)

theorem lit_closed (v s : String) : Closed (render (.lit v s)) (tokens (.lit v s)) := by
  have h := (((show Clean "PegRt.lit " [t 121] by decide).append_clean (clean_literal v)).append_clean
    (show Clean " " [] by decide)).append_clean (clean_literal s)
  simpa [render, tokens, String.append_assoc] using h.closed

theorem cls_closed (rs : List (Char × Char)) (s : String) :
    Closed (render (.cls rs s)) (tokens (.cls rs s)) := by
  have h := (((show Clean "PegRt.cls [" [t 121, t 105] by decide).append_clean
    (ranges_clean rs)).append_clean (show Clean "] " [t 106] by decide)).append_clean
    (clean_literal s)
  simpa [render, tokens, String.append_assoc, List.append_assoc] using h.closed

theorem alts_starts (as : Alts) : StartsBreak (renderAlts as ++ "]") := by
  cases as with
  | nil => exact startsBreakB_sound (by decide)
  | cons a r =>
    simp only [renderAlts, String.append_assoc]
    exact StartsBreak.append _ (startsBreakB_sound (by decide))

theorem block_closed {a : Alt} (body : Closed (renderBody a) (bodyTokens a)) :
    Closed (doOpen ++ (renderBody a ++ doClose)) (blockTokens a) := by
  have close : Closed (renderBody a ++ doClose) (bodyTokens a ++ [t 102]) :=
    body.append (startsBreakB_sound (by decide)) (closedB_sound (by decide))
  have h := (show Clean doOpen [t 125, t 101] by decide).append close
  simpa [blockTokens, List.append_assoc] using h

mutual
theorem render_closed : (e : PExpr) → valid e = true → Closed (render e) (tokens e)
  | .any, _ => closedB_sound (by decide)
  | .ref n, h => by
    have hn : ∀ c ∈ n.toList, RenderExpressionLexer.idTail c = true := by
      simpa [valid] using h
    simpa [render, tokens, Peg.Verification.RenderExpression.renderRule] using
      closed_var (rule_plainVar n hn)
  | .lit v s, _ => lit_closed v s
  | .cls rs s, _ => cls_closed rs s
  | .wrap f e, h => by
    have he : valid e = true := by simpa [valid] using h
    have inner : Closed (render e ++ ")") (tokens e ++ [t 108]) :=
      (render_closed e he).append (startsBreakB_sound (by decide)) (closedB_sound (by decide))
    have paren := (show Clean " (" [t 107] by decide).append inner
    have whole := (wrapper_closed f).append
      (StartsBreak.append _ (startsBreakB_sound (by decide))) paren
    have e1 : render (.wrap f e) = f.name ++ (" (" ++ (render e ++ ")")) := by
      simp [render, String.append_assoc]
    have e2 : tokens (.wrap f e) = [t 121] ++ ([t 107] ++ (tokens e ++ [t 108])) := by
      simp [tokens]
    rw [e1, e2]
    exact whole
  | .group a as, h => by
    have ha : validBody a = true ∧ validAlts as = true := by simpa [valid] using h
    have block := block_closed (body_closed a ha.1)
    have rest := block.append (alts_starts as) (alts_closed as ha.2)
    have whole := (show Clean "PegRt.choice [" [t 121, t 105] by decide).append rest
    have e1 : render (.group a as) =
        "PegRt.choice [" ++ ((doOpen ++ (renderBody a ++ doClose)) ++ (renderAlts as ++ "]")) := by
      simp [render, String.append_assoc]
    have e2 : tokens (.group a as) =
        [t 121, t 105] ++ (blockTokens a ++ (altsTokens as ++ [t 106])) := by
      simp [tokens, blockTokens, List.append_assoc]
    rw [e1, e2]
    exact whole

theorem alts_closed : (as : Alts) → validAlts as = true →
    Closed (renderAlts as ++ "]") (altsTokens as ++ [t 106])
  | .nil, _ => closedB_sound (by decide)
  | .cons a r, h => by
    have ha : validBody a = true ∧ validAlts r = true := by simpa [validAlts] using h
    have block := block_closed (body_closed a ha.1)
    have rest := block.append (alts_starts r) (alts_closed r ha.2)
    have whole := (show Clean ", " [t 114] by decide).append rest
    have e1 : renderAlts (.cons a r) ++ "]" =
        ", " ++ ((doOpen ++ (renderBody a ++ doClose)) ++ (renderAlts r ++ "]")) := by
      simp [renderAlts, String.append_assoc]
    have e2 : altsTokens (.cons a r) ++ [t 106] =
        [t 114] ++ (blockTokens a ++ (altsTokens r ++ [t 106])) := by
      simp [altsTokens, blockTokens, List.append_assoc]
    rw [e1, e2]
    exact whole

theorem body_closed : (a : Alt) → validBody a = true → Closed (renderBody a) (bodyTokens a)
  | .last f, h => by
    simpa [renderBody, bodyTokens] using final_closed f (by simpa [validBody] using h)
  | .cons st r, h => by
    have hs : validStmt st = true ∧ validBody r = true := by simpa [validBody] using h
    have rest := (show Clean stmtSep [t 113] by decide).append (body_closed r hs.2)
    have whole := (stmt_closed st hs.1).append
      (StartsBreak.append _ (startsBreakB_sound (by decide))) rest
    have e1 : renderBody (.cons st r) = renderStmt st ++ (stmtSep ++ renderBody r) := by
      simp [renderBody, String.append_assoc]
    have e2 : bodyTokens (.cons st r) = stmtTokens st ++ ([t 113] ++ bodyTokens r) := by
      simp [bodyTokens, List.append_assoc]
    rw [e1, e2]
    exact whole

theorem stmt_closed : (st : Stmt) → validStmt st = true → Closed (renderStmt st) (stmtTokens st)
  | .expr e, h => by
    simpa [renderStmt, stmtTokens] using render_closed e (by simpa [validStmt] using h)
  | .bind v e, h => by
    have hv : plainVar v.toList = true ∧ valid e = true := by simpa [validStmt] using h
    have spaced := (show Clean " " [] by decide).append (render_closed e hv.2)
    have arrow := (closedB_sound (by decide) : Closed " <-" [t 82]).append
      (StartsBreak.append _ (startsBreakB_sound (by decide) : StartsBreak " ")) spaced
    have whole := (closed_var hv.1).append (StartsBreak.append _ (startsBreakB_sound (by decide)))
      arrow
    have e1 : renderStmt (.bind v e) = v ++ (" <-" ++ (" " ++ render e)) := by
      simp only [renderStmt, String.append_assoc]
      congr 1
    have e2 : stmtTokens (.bind v e) = [t 117] ++ ([t 82] ++ ([] ++ tokens e)) := by
      simp [stmtTokens]
    rw [e1, e2]
    exact whole
  | .discard e, h => by
    have he : valid e = true := by simpa [validStmt] using h
    have spaced := (show Clean " " [] by decide).append (render_closed e he)
    have arrow := (closedB_sound (by decide) : Closed " <-" [t 82]).append
      (StartsBreak.append _ (startsBreakB_sound (by decide) : StartsBreak " ")) spaced
    have whole := (closedB_sound (by decide) : Closed "_" [t 2]).append
      (StartsBreak.append _ (startsBreakB_sound (by decide))) arrow
    have e1 : renderStmt (.discard e) = "_" ++ (" <-" ++ (" " ++ render e)) := by
      simp only [renderStmt]
      rw [← String.append_assoc, ← String.append_assoc]
      rfl
    have e2 : stmtTokens (.discard e) = [t 2] ++ ([t 82] ++ ([] ++ tokens e)) := by
      simp [stmtTokens]
    rw [e1, e2]
    exact whole
end

theorem printed_lexes (e : PExpr) (h : valid e = true) : lexModel (render e) = some (tokens e) :=
  (render_closed e h).lex

/-! ## The token word derives in GHC 9.10.3's grammar -/

private theorem trans {xs ys zs : List Symbol}
    (first : Derives productions xs ys) (second : Derives productions ys zs) :
    Derives productions xs zs := by
  induction first with
  | refl _ => exact second
  | production rule next ih => exact .production rule (ih second)

private theorem derives_pre (pre : List Symbol) {xs ys : List Symbol}
    (h : Derives productions xs ys) : Derives productions (pre ++ xs) (pre ++ ys) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs left right result rule next ih =>
    have next' : Derives productions ((pre ++ left) ++ rhs ++ right) (pre ++ result) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := pre ++ left) (post := right) rule next')

private theorem derives_post (post : List Symbol) {xs ys : List Symbol}
    (h : Derives productions xs ys) : Derives productions (xs ++ post) (ys ++ post) := by
  induction h with
  | refl _ => exact .refl _
  | @production id lhs rhs left right result rule next ih =>
    have next' : Derives productions (left ++ rhs ++ (right ++ post)) (result ++ post) := by
      simpa [List.append_assoc] using ih
    simpa [List.append_assoc] using
      (Derives.production (pre := left) (post := right ++ post) rule next')

private theorem one {id lhs child : Nat} {out : List Symbol}
    (rule : productions id = some (lhs, [.nonterminal child]))
    (valid : Derives productions [.nonterminal child] out) :
    Derives productions [.nonterminal lhs] out := by
  simpa using (Derives.production (pre := []) (post := []) rule valid)

-- Parser.y 596: texp -> exp.
theorem exp_to_texp {body : List Symbol}
    (h : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 229] body :=
  one (id := 596) (by decide) h

-- Parser.y 661, 658: qual -> exp, stmt -> qual.
theorem exp_statement {body : List Symbol}
    (h : Derives productions [.nonterminal 211] body) :
    Derives productions [.nonterminal 257] body :=
  one (id := 658) (child := 258) (by decide) (one (id := 661) (lhs := 258) (by decide) h)

-- Parser.y 818: literal -> CHAR, lifted to aexp as string_argument lifts STRING.
theorem char_argument : Derives productions [.nonterminal 229] [t 129] := by
  have literal : Derives productions [.nonterminal 319] [.terminal 129] :=
    Derives.production (pre := []) (post := []) (id := 818) (rhs := [.terminal 129])
      (by decide) (.refl _)
  exact RenderExpressionGHC.aexp_to_texp (one (id := 551) (by decide)
    (one (id := 554) (lhs := 219) (by decide) (one (id := 559) (lhs := 220) (by decide) literal)))

theorem range_pair_texp : Derives productions [.nonterminal 229] rangePair := by
  have h := RenderExpressionGHC.aexp_to_texp
    (RenderDeclarationsGHC.pair_argument char_argument char_argument)
  simpa [rangePair, List.append_assoc] using h

-- Parser.y 709, 694, 556: sysdcon_nolist -> '[' ']' as an aexp.
theorem empty_list : Derives productions [.nonterminal 218] [t 105, t 106] := by
  have nil : Derives productions [.nonterminal 280] [.terminal 105, .terminal 106] :=
    Derives.production (pre := []) (post := []) (id := 709) (rhs := [.terminal 105, .terminal 106])
      (by decide) (.refl _)
  exact one (id := 551) (by decide) (one (id := 554) (lhs := 219) (by decide)
    (one (id := 556) (lhs := 220) (by decide) (one (id := 694) (lhs := 274) (by decide) nil)))

theorem class_function (rs : List (Char × Char)) :
    Derives productions [.nonterminal 217] ([t 121, t 105] ++ rangeTokens rs ++ [t 106]) := by
  match rs with
  | [] => simpa [rangeTokens] using RenderExpressionGHC.application RenderExpressionGHC.qualified_function empty_list
  | [_] => simpa [rangeTokens] using RenderExpressionGHC.choice_singleton range_pair_texp
  | _ :: _ :: rest =>
    have h := RenderExpressionGHC.choice_many rangePair rangePair (rest.map fun _ => rangePair)
      range_pair_texp range_pair_texp (by
        intro item mem
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp mem
        exact range_pair_texp)
    simpa [rangeTokens, List.foldl_map] using h

-- Parser.y 616 builds the first two list items; 615 adds each further one.
theorem lexps_pair {left right : List Symbol}
    (hl : Derives productions [.nonterminal 229] left)
    (hr : Derives productions [.nonterminal 229] right) :
    Derives productions [.nonterminal 234] (left ++ [t 114] ++ right) := by
  have r616 : productions 616 = some
      (234, [.nonterminal 229, .terminal 114, .nonterminal 229]) := by decide
  have first := derives_post [.terminal 114, .nonterminal 229] hl
  have second := derives_pre (left ++ [.terminal 114]) hr
  have assembled : Derives productions
      [.nonterminal 229, .terminal 114, .nonterminal 229] (left ++ [t 114] ++ right) := by
    have first' : Derives productions
        [.nonterminal 229, .terminal 114, .nonterminal 229]
        (left ++ [.terminal 114] ++ [.nonterminal 229]) := by
      simpa [List.append_assoc] using first
    exact trans first' second
  simpa using (Derives.production (pre := []) (post := []) r616 assembled)

theorem final_statement (f : Final) :
    Derives productions [.nonterminal 257] f.tokens := by
  cases f with
  | unit => simpa [Final.tokens] using RenderPrimitiveStatement.pure_unit_statement
  | var v =>
    simpa [Final.tokens] using
      RenderPrimitiveStatement.pure_value_statement RenderDeclarationsGHC.varid_argument

mutual
theorem expr_derives : (e : PExpr) → valid e = true →
    Derives productions [.nonterminal 211] (tokens e)
  | .any, _ => by
    simpa [tokens] using RenderExpressionGHC.fexp_to_exp RenderExpressionGHC.qualified_function
  | .ref _, _ => by
    simpa [tokens] using RenderExpressionGHC.fexp_to_exp
      (one (id := 536) (by decide) RenderDeclarationsGHC.varid_argument)
  | .lit _ _, _ => by
    simpa [tokens] using RenderExpressionGHC.fexp_to_exp (RenderExpressionGHC.application
      (RenderExpressionGHC.application RenderExpressionGHC.qualified_function
        RenderExpressionGHC.string_argument) RenderExpressionGHC.string_argument)
  | .cls rs _, _ => by
    simpa [tokens, List.append_assoc] using RenderExpressionGHC.fexp_to_exp
      (RenderExpressionGHC.application (class_function rs) RenderExpressionGHC.string_argument)
  | .wrap _ e, h => by
    have he : valid e = true := by simpa [valid] using h
    simpa [tokens, List.append_assoc] using RenderExpressionGHC.fexp_to_exp
      (RenderExpressionGHC.application_parenthesized RenderExpressionGHC.qualified_function
        (exp_to_texp (expr_derives e he)))
  | .group a .nil, h => by
    have ha : validBody a = true := by simpa [valid, validAlts] using h
    have block := RenderExpressionGHC.aexp_to_texp
      (RenderExpressionGHC.do_block (body_derives a ha))
    have items : Derives productions [.nonterminal 233]
        ([t 125, t 101] ++ bodyTokens a ++ [t 102]) :=
      one (id := 608) (by decide) block
    simpa [tokens, altsTokens, List.append_assoc] using
      RenderExpressionGHC.fexp_to_exp (RenderExpressionGHC.choice items)
  | .group a (.cons b r), h => by
    have hv : validBody a = true ∧ (validBody b = true ∧ validAlts r = true) := by
      simpa [valid, validAlts] using h
    have blockA := RenderExpressionGHC.aexp_to_texp
      (RenderExpressionGHC.do_block (body_derives a hv.1))
    have blockB := RenderExpressionGHC.aexp_to_texp
      (RenderExpressionGHC.do_block (body_derives b hv.2.1))
    have list := alts_after _ (lexps_pair blockA blockB) r hv.2.2
    have items := one (id := 609) (lhs := 233) (by decide) list
    simpa [tokens, altsTokens, List.append_assoc] using
      RenderExpressionGHC.fexp_to_exp (RenderExpressionGHC.choice items)

theorem alts_after (acc : List Symbol) (hacc : Derives productions [.nonterminal 234] acc) :
    (as : Alts) → validAlts as = true →
    Derives productions [.nonterminal 234] (acc ++ altsTokens as)
  | .nil, _ => by simpa [altsTokens] using hacc
  | .cons b r, h => by
    have hv : validBody b = true ∧ validAlts r = true := by simpa [validAlts] using h
    have block := RenderExpressionGHC.aexp_to_texp
      (RenderExpressionGHC.do_block (body_derives b hv.1))
    have next := RenderExpressionGHC.lexps_extend hacc block
    have rest := alts_after _ next r hv.2
    simpa [altsTokens, RenderExpressionGHC.commaAppend, List.append_assoc] using rest

theorem body_derives : (a : Alt) → validBody a = true →
    Derives productions [.nonterminal 254] (bodyTokens a)
  | .last f, _ => by
    simpa [bodyTokens] using RenderExpressionGHC.statement_one (final_statement f)
  | .cons st r, h => by
    have hv : validStmt st = true ∧ validBody r = true := by simpa [validBody] using h
    simpa [bodyTokens] using
      body_after _ (RenderExpressionGHC.statement_one (stmt_derives st hv.1)) r hv.2

theorem body_after (acc : List Symbol) (hacc : Derives productions [.nonterminal 254] acc) :
    (a : Alt) → validBody a = true →
    Derives productions [.nonterminal 254] (acc ++ [t 113] ++ bodyTokens a)
  | .last f, _ => by
    simpa [bodyTokens] using RenderExpressionGHC.statement_cons hacc (final_statement f)
  | .cons st r, h => by
    have hv : validStmt st = true ∧ validBody r = true := by simpa [validBody] using h
    have next := RenderExpressionGHC.statement_cons hacc (stmt_derives st hv.1)
    simpa [bodyTokens, List.append_assoc] using body_after _ next r hv.2

theorem stmt_derives : (st : Stmt) → validStmt st = true →
    Derives productions [.nonterminal 257] (stmtTokens st)
  | .expr e, h => by
    simpa [stmtTokens] using exp_statement (expr_derives e (by simpa [validStmt] using h))
  | .bind _ e, h => by
    have hv : valid e = true := by
      simp only [validStmt, Bool.and_eq_true] at h
      exact h.2
    simpa [stmtTokens] using
      RenderPrimitiveStatement.named_binding_statement (expr_derives e hv)
  | .discard e, h => by
    simpa [stmtTokens] using RenderPrimitiveStatement.wildcard_binding_statement
      (expr_derives e (by simpa [validStmt] using h))
end

theorem printed_derives (e : PExpr) (h : valid e = true) :
    Derives productions [.nonterminal 211] (tokens e) ∧
    Derives productions [.nonterminal 229] (tokens e) :=
  ⟨expr_derives e h, exp_to_texp (expr_derives e h)⟩

-- The lexer bridge: where GHC's lexer agrees with the model on the printed
-- text, its word is the printer's token word and derives from `exp`.
theorem printed_ghc (lex : String → List Symbol) (e : PExpr) (h : valid e = true)
    (agrees : lexModel (render e) = some (lex (render e))) :
    lex (render e) = tokens e ∧ Derives productions [.nonterminal 211] (lex (render e)) := by
  have same : lex (render e) = tokens e :=
    (Option.some.inj (agrees.symm.trans (printed_lexes e h)))
  exact ⟨same, same ▸ expr_derives e h⟩

/-! ## The tree's text is the string models of RenderExpression -/

def Alt.texts : Alt → List String
  | .last f => [f.text]
  | .cons st r => renderStmt st :: r.texts

def Alts.toList : Alts → List Alt
  | .nil => []
  | .cons a r => a :: r.toList

theorem Alt.texts_cons (a : Alt) : ∃ x xs, a.texts = x :: xs := by
  cases a with
  | last f => exact ⟨_, _, rfl⟩
  | cons st r => exact ⟨_, _, rfl⟩

theorem renderBody_intercalate : (a : Alt) →
    renderBody a = String.intercalate stmtSep a.texts
  | .last f => by simp [renderBody, Alt.texts]
  | .cons st r => by
    obtain ⟨x, xs, hx⟩ := r.texts_cons
    have ih := renderBody_intercalate r
    rw [hx] at ih
    simp only [renderBody, Alt.texts, hx, String.intercalate_cons_cons, ih]

theorem renderAlt_do (a : Alt) :
    renderAlt a = Peg.Verification.RenderExpression.renderDo a.texts := by
  simp [renderAlt, Peg.Verification.RenderExpression.renderDo, renderBody_intercalate,
    doOpen, doClose, stmtSep, String.append_assoc]

theorem intercalate_alts : (as : Alts) → (x : String) →
    String.intercalate ", " (x :: as.toList.map renderAlt) = x ++ renderAlts as
  | .nil, x => by simp [Alts.toList, renderAlts]
  | .cons b r, x => by
    have ih := intercalate_alts r (renderAlt b)
    simp only [Alts.toList, List.map_cons, String.intercalate_cons_cons] at ih ⊢
    rw [ih]
    simp [renderAlts, renderAlt, String.append_assoc]

-- exprCodeU's wrappers: RenderExpression.renderWrap.
theorem render_wrap (f : Wrapper) (e : PExpr) :
    render (.wrap f e) = Peg.Verification.RenderExpression.renderWrap f.name (render e) := by
  simp [render, Peg.Verification.RenderExpression.renderWrap]

-- exprCodeU's groups: RenderExpression.renderChoice of renderDo blocks.
theorem render_group (a : Alt) (as : Alts) :
    render (.group a as) = Peg.Verification.RenderExpression.renderChoice
      ((a :: as.toList).map fun alt => Peg.Verification.RenderExpression.renderDo alt.texts) := by
  have h := intercalate_alts as (renderAlt a)
  have same : (a :: as.toList).map (fun alt => Peg.Verification.RenderExpression.renderDo alt.texts) =
      renderAlt a :: as.toList.map renderAlt := by
    simp [renderAlt_do]
  rw [same, Peg.Verification.RenderExpression.renderChoice, h]
  simp [render, renderAlt, String.append_assoc]

end PegHs.RenderPrinting
