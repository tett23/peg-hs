import Parsing

namespace PegVerification.File

abbrev Rule := List Char → Result

def finish : Rule
  | [] => .ok []
  | _ :: _ => .error (some "top")

def fileRun (ws item : Rule) (src : List Char) : Result := do
  let xs ← ws src
  let tail ← repeatRun item (xs.length + 1) xs
  finish tail

-- A derivation reaches EOF by taking successful steps on strictly shorter remainders.
-- It has no fuel and cannot terminate with an unparsed suffix.
inductive Items (itemRel : List Char → List Char → Prop) : List Char → Prop where
  | endOfFile : Items itemRel []
  | next {xs ys} : itemRel xs ys → ys.length < xs.length → Items itemRel ys → Items itemRel xs

private theorem items_cons_iff {itemRel} {x : Char} {xs} :
    Items itemRel (x :: xs) ↔ ∃ ys, itemRel (x :: xs) ys ∧ ys.length < (x :: xs).length ∧ Items itemRel ys := by
  constructor
  · intro h
    cases h with
    | next found shorter rest => exact ⟨_, found, shorter, rest⟩
  · rintro ⟨ys, found, shorter, rest⟩
    exact .next found shorter rest

private theorem repeat_iff (item : Rule) (itemRel : List Char → List Char → Prop)
    (hitem : ∀ xs ys, item xs = .ok ys ↔ itemRel xs ys)
    (empty : item [] = .error none) (fuel : Nat) (xs : List Char) (enough : xs.length < fuel) :
    (repeatRun item fuel xs).bind finish = .ok [] ↔ Items itemRel xs := by
  induction fuel generalizing xs with
  | zero => omega
  | succ n ih =>
    cases xs with
    | nil => simp [repeatRun, empty, Except.bind, finish, Items.endOfFile]
    | cons x xs =>
      rw [items_cons_iff]
      simp only [← hitem]
      cases h : item (x :: xs) with
      | error err =>
        cases err <;> simp [repeatRun, h, Except.bind, finish]
      | ok ys =>
        by_cases smaller : ys.length < xs.length + 1
        · simp only [List.length_cons] at enough
          have bound : ys.length < n := by omega
          simpa [repeatRun, h, smaller] using ih ys bound
        · simp [repeatRun, h, smaller, Except.bind, finish]

theorem invariant1_file_iff (ws item : Rule) (space itemRel : List Char → List Char → Prop)
    (hws : ∀ xs ys, ws xs = .ok ys ↔ space xs ys)
    (hitem : ∀ xs ys, item xs = .ok ys ↔ itemRel xs ys)
    (empty : item [] = .error none) (src : List Char) :
    fileRun ws item src = .ok [] ↔ ∃ xs, space src xs ∧ Items itemRel xs := by
  simp only [← hws]
  cases h : ws src with
  | error e => simp [fileRun, h, Bind.bind, Except.bind]
  | ok xs =>
    simpa [fileRun, h, Bind.bind, Except.bind] using
      repeat_iff item itemRel hitem empty (xs.length + 1) xs (by omega)

-- The PEG operator tree of the File production in both metagrammars.
def fileExpr (ws item : Expr) : Expr :=
  .seq ws (.seq (.many item) (.label "top" (.notAhead .any)))

theorem invariant1_file_expr (ws item : Expr) (src : List Char) :
    run (fileExpr ws item) src = fileRun (run ws) (run item) src := by
  have eof : run (.label "top" (.notAhead .any)) = finish := by
    funext xs
    cases xs <;> rfl
  change (run ws src).bind (fun xs => (repeatRun (run item) (xs.length + 1) xs).bind
    (run (.label "top" (.notAhead .any)))) = _
  rw [eof]
  rfl

theorem invariant1_file_derivation (ws item : Expr) (src : List Char)
    (empty : run item [] = .error none) :
    run (fileExpr ws item) src = .ok [] ↔
      ∃ xs, Eval ws src (.ok xs) ∧ Items (fun a b => Eval item a (.ok b)) xs := by
  rw [invariant1_file_expr]
  apply invariant1_file_iff _ _ _ _ _ _ empty
  · intro xs ys
    exact (invariant1_core_iff _ _ _).symm
  · intro xs ys
    exact (invariant1_core_iff _ _ _).symm

-- The file matches zero items; a nonempty suffix that is not an item fails.
example : fileRun Except.ok (fun _ => .error none) [] = .ok [] := by rfl
example : fileRun Except.ok (fun _ => .error none) ['?'] = .error (some "top") := by rfl
example : run (fileExpr (.many (.char ' ')) (.char 'a')) [' ', 'a', 'a'] = .ok [] := by rfl
example : run (fileExpr (.many (.char ' ')) (.char 'a')) ['a', '?'] = .error (some "top") := by rfl
example : fileRun Except.ok (fun _ => .error (some "item")) ['a'] = .error (some "item") := by rfl

end PegVerification.File
