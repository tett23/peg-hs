import AssembleValidationHelpers

namespace PegHs.DirectiveArgument
open AssembleValidationHelpers (stripSpace)

-- The offset version follows outside/inside in directiveComment. The
-- independent split version constructs the argument one character at a time.
def offset : Bool → Nat → List Char → Nat
  | _, n, [] => n
  | false, n, '#' :: _ => n
  | true, n, '\\' :: _ :: tail => offset true (n + 2) tail
  | quoted, n, c :: tail => offset (if c == '"' then !quoted else quoted) (n + 1) tail

private def prepend (chars : List Char) (parts : List Char × List Char) :=
  (chars ++ parts.1, parts.2)

def splitQuoted : Bool → List Char → List Char × List Char
  | _, [] => ([], [])
  | false, '#' :: cs => ([], '#' :: cs)
  | true, '\\' :: c :: cs => prepend ['\\', c] (splitQuoted true cs)
  | quoted, c :: cs => prepend [c] (splitQuoted (if c == '"' then !quoted else quoted) cs)

private theorem split_spec (q : Bool) (n : Nat) (xs : List Char) :
    let parts := splitQuoted q xs
    offset q n xs = n + parts.1.length ∧ parts.1 ++ parts.2 = xs ∧
      (parts.2 = [] ∨ parts.2.head? = some '#') := by
  fun_induction offset q n xs <;> simp_all [splitQuoted, prepend] <;> omega

def comment (name : String) (xs : List Char) : List Char × List Char :=
  if name == "env" then (xs, [])
  else if ["expect", "message"].contains name then
    let i := offset false 0 xs
    (xs.take i, xs.drop i)
  else (xs.takeWhile (· != '#'), xs.dropWhile (· != '#'))

theorem invariant2_quoted_split (xs : List Char) :
    (xs.take (offset false 0 xs), xs.drop (offset false 0 xs)) = splitQuoted false xs := by
  obtain ⟨count, pieces, _⟩ := split_spec false 0 xs
  simp only [Nat.zero_add] at count
  rw [count]
  have join (a b : List Char) (h : a ++ b = xs) :
      (xs.take a.length, xs.drop a.length) = (a,b) := by subst xs; simp
  exact join _ _ pieces

theorem invariant2_argument_preserves_line (name : String) (xs : List Char) :
    (comment name xs).1 ++ (comment name xs).2 = xs := by
  unfold comment
  split
  · simp
  · split
    · exact List.take_append_drop ..
    · exact List.takeWhile_append_dropWhile

def argument (name : String) (raw : List Char) := stripSpace (comment name raw).1

#print axioms invariant2_quoted_split
#print axioms invariant2_argument_preserves_line
end PegHs.DirectiveArgument
