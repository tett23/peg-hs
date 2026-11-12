import Lexical

namespace PegVerification

-- GHC Data.Char.isSpace on Unicode scalar values (checked exhaustively by
-- check-whitespace.sh). This table is a semantic boundary, not a Lean axiom.
def ghcSpaceChars : List Char :=
  ([9, 10, 11, 12, 13, 32, 160, 0x1680] ++
    (List.range 11).map (0x2000 + ·) ++ [0x202f, 0x205f, 0x3000]).map Char.ofNat

def ghcIsSpace (c : Char) : Bool := ghcSpaceChars.contains c

-- Compile a finite character class using the existing PEG operators.
def oneOfChars : List Char → Expr
  | [] => .predicate false
  | c :: cs => .choice (.char c) (oneOfChars cs)

def spaceCharRun (space : Char → Bool) : List Char → Result
  | [] => .error none
  | c :: cs => if space c then .ok cs else .error none

theorem invariant1_oneOfChars (chars xs : List Char) :
    run (oneOfChars chars) xs = spaceCharRun chars.contains xs := by
  induction chars with
  | nil => cases xs <;> rfl
  | cons c chars ih =>
    cases xs with
    | nil => simpa [oneOfChars, run, spaceCharRun] using ih
    | cons x xs =>
      by_cases h : x = c
      · subst x
        simp [oneOfChars, run, spaceCharRun]
      · simpa [oneOfChars, run, h, spaceCharRun, List.contains_cons, Ne.symm h] using ih

def wsChoiceRun (space : Char → Bool) (xs : List Char) : Result :=
  match spaceCharRun space xs with
  | .ok ys => .ok ys
  | .error none => run comment xs
  | .error (some name) => .error (some name)

def wsStep (space : Char → Bool) : List Char → Result
  | [] => .error none
  | c :: cs =>
      if space c then .ok cs
      else if c == '#' then .ok (cs.dropWhile beforeNewline)
      else .error none

theorem invariant1_ws_choice (space : Char → Bool) (xs : List Char) :
    wsChoiceRun space xs = wsStep space xs := by
  cases xs with
  | nil => simp [wsChoiceRun, spaceCharRun, wsStep, comment, run, Except.bind]
  | cons c cs =>
      by_cases sc : space c = true
      · simp [wsChoiceRun, spaceCharRun, wsStep, sc]
      · by_cases hash : c = '#'
        · subst c
          simp [wsChoiceRun, spaceCharRun, wsStep, sc, invariant1_comment]
        · simp [wsChoiceRun, spaceCharRun, wsStep, sc, hash,
                invariant1_comment_no_marker c cs hash]

def wsRun (space : Char → Bool) (xs : List Char) : Result :=
  repeatRun (wsChoiceRun space) (xs.length + 1) xs

-- Independent structural specification of the input remainder.
def wsDrop (space : Char → Bool) : Nat → List Char → List Char
  | 0, xs => xs
  | _ + 1, [] => []
  | fuel + 1, c :: cs =>
      if space c then wsDrop space fuel cs
      else if c == '#' then wsDrop space fuel (cs.dropWhile beforeNewline)
      else c :: cs

theorem invariant1_ws_fuel (space : Char → Bool) :
    ∀ fuel xs, xs.length < fuel →
      repeatRun (wsChoiceRun space) fuel xs = .ok (wsDrop space fuel xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs impossible
      omega
  | succ fuel ih =>
      intro xs enough
      simp only [repeatRun, invariant1_ws_choice]
      cases xs with
      | nil => simp [wsStep, wsDrop]
      | cons c cs =>
          by_cases sc : space c = true
          · have remaining : cs.length < fuel := by simp at enough; omega
            simpa [repeatRun, wsStep, wsDrop, sc] using ih cs remaining
          · by_cases hash : c = '#'
            · subst c
              have le : (cs.dropWhile beforeNewline).length ≤ cs.length :=
                (List.dropWhile_suffix beforeNewline).length_le
              have remaining : (cs.dropWhile beforeNewline).length < fuel := by
                simp at enough
                omega
              have progress : (cs.dropWhile beforeNewline).length < cs.length + 1 := by omega
              simpa [wsStep, wsDrop, sc, progress] using
                ih (cs.dropWhile beforeNewline) remaining
            · simp [wsStep, wsDrop, sc, hash]

theorem invariant1_ws (space : Char → Bool) (xs : List Char) :
    wsRun space xs = .ok (wsDrop space (xs.length + 1) xs) :=
  invariant1_ws_fuel space (xs.length + 1) xs (by omega)

theorem invariant1_ws_suffix (space : Char → Bool) :
    ∀ fuel xs, (wsDrop space fuel xs).IsSuffix xs := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs
      exact ⟨[], by simp [wsDrop]⟩
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil => exact ⟨[], by simp [wsDrop]⟩
      | cons c cs =>
          by_cases sc : space c = true
          · obtain ⟨pre, eq⟩ := ih cs
            exact ⟨c :: pre, by simpa [wsDrop, sc] using
              (congrArg (List.cons c) eq)⟩
          · by_cases hash : c = '#'
            · subst c
              obtain ⟨pre, eq⟩ := ih (cs.dropWhile beforeNewline)
              obtain ⟨head, headEq⟩ := List.dropWhile_suffix (l := cs) beforeNewline
              exact ⟨'#' :: (head ++ pre), by
                simp [wsDrop, sc, List.append_assoc, eq, headEq]⟩
            · exact ⟨[], by simp [wsDrop, sc, hash]⟩

-- The exact predicate used by the grammar is supplied to the universal theorem.
theorem invariant1_ghc_ws (xs : List Char) :
    wsRun ghcIsSpace xs = .ok (wsDrop ghcIsSpace (xs.length + 1) xs) :=
  invariant1_ws ghcIsSpace xs

def whitespaceExpr := Expr.many (.choice (oneOfChars ghcSpaceChars) comment)

theorem invariant1_ws_expr (xs : List Char) :
    run whitespaceExpr xs = .ok (wsDrop ghcIsSpace (xs.length+1) xs) := by
  have body : run (.choice (oneOfChars ghcSpaceChars) comment) = wsChoiceRun ghcIsSpace := by
    funext input
    simp only [run, invariant1_oneOfChars, wsChoiceRun]
    rfl
  change repeatRun (run (.choice (oneOfChars ghcSpaceChars) comment)) _ _ = _
  rw [body]
  exact invariant1_ghc_ws xs

-- Empty, whitespace, comment, newline, and non-whitespace boundaries.
example : wsRun ghcIsSpace [] = .ok [] := by rfl
example : wsRun ghcIsSpace [' ', '\t', 'x'] = .ok ['x'] := by rfl
example : wsRun ghcIsSpace ['#', 'x', '\n', 'z'] = .ok ['z'] := by rfl
example : wsRun ghcIsSpace ['\n', 'z'] = .ok ['z'] := by rfl
example : wsRun ghcIsSpace ['x'] = .ok ['x'] := by rfl

#print axioms invariant1_ws_choice
#print axioms invariant1_ws
#print axioms invariant1_ws_suffix
#print axioms invariant1_ghc_ws

end PegVerification
