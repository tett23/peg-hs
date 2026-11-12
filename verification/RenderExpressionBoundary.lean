import Pragmas

namespace PegHs.RenderExpressionBoundary

open Peg.Verification

-- The tail of a line comment is consumed up to, but not including, a newline.
-- This models precisely the boundary relevant to a following generated ')'.
def afterLineComment (chars : List Char) : List Char :=
  chars.dropWhile (· != '\n')

theorem comment_stops_at_newline (tail after : List Char)
    (noNewline : '\n' ∉ tail) :
    afterLineComment (tail ++ '\n' :: after) = '\n' :: after := by
  induction tail with
  | nil => simp [afterLineComment]
  | cons c rest ih =>
    have notNl : c ≠ '\n' := by
      intro eq
      exact noNewline (by simp [eq])
    have restNoNl : '\n' ∉ rest := by
      intro member
      exact noNewline (by simp [member])
    simpa [afterLineComment, notNl] using ih restNoNl

-- The production fragment always puts a newline between the user body and
-- its restore marker, then another newline before the generated continuation.
theorem fragment_frame_boundary (marker : String) (line col : Nat)
    (path body : String) :
    renderFragment marker line col path body =
      ("\n" ++ renderLine line path ++ "\n " ++ renderColumn col) ++
        body ++ "\n" ++ marker ++ "\n    " := by
  simp [renderFragment, String.append_assoc]

theorem comment_cannot_consume_continuation
    (tail : List Char) (noNewline : '\n' ∉ tail)
    (marker continuation : String) :
    afterLineComment
      (tail ++ ('\n' :: (marker ++ "\n    " ++ continuation).toList)) =
      ('\n' :: (marker ++ "\n    " ++ continuation).toList) := by
  exact comment_stops_at_newline tail _ noNewline

#print axioms comment_stops_at_newline
#print axioms fragment_frame_boundary
#print axioms comment_cannot_consume_continuation

end PegHs.RenderExpressionBoundary
