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

-- Input is the stripped annotation passed to the named-type renderer.
def protectTypeComment (ty : String) : String :=
  if ty.contains "--" then ty ++ "\n    " else ty

theorem named_type_comment_boundary (lead tail : String) :
    protectTypeComment (lead ++ "--" ++ tail) =
      lead ++ "--" ++ tail ++ "\n    " := by
  have found : (lead ++ "--" ++ tail).contains "--" := by
    apply String.contains_string_iff.mpr
    exact ⟨lead.toList, tail.toList, by simp [String.toList_append, List.append_assoc]⟩
  simp [protectTypeComment, found]

-- Removing the comment opener and the preceding type leaves the scanner
-- at the comment body. Generated punctuation survives the scan unchanged.
theorem named_type_comment_scan (lead tail continuation : String)
    (singleLine : '\n' ∉ tail.toList) :
    afterLineComment
      (((protectTypeComment (lead ++ "--" ++ tail) ++ continuation).toList).drop
        (lead ++ "--").toList.length) = '\n' :: ("    " ++ continuation).toList := by
  rw [named_type_comment_boundary]
  generalize lead ++ "--" = opener
  simp only [String.toList_append, List.append_assoc, List.drop_left]
  exact comment_stops_at_newline _ _ singleLine

#print axioms named_type_comment_scan
#print axioms named_type_comment_boundary
#print axioms comment_stops_at_newline
#print axioms fragment_frame_boundary
#print axioms comment_cannot_consume_continuation

end PegHs.RenderExpressionBoundary
