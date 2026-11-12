import ItemWindow

namespace PegHs.MetaExecution

theorem invariant1_source_window (source : List Char) (start width : Nat) :
    source = source.take start ++
      ((source.drop start).take width ++ source.drop (start + width)) := by
  calc
    source = source.take start ++ source.drop start :=
      (List.take_append_drop start source).symm
    _ = source.take start ++
        ((source.drop start).take width ++ (source.drop start).drop width) := by
      rw [List.take_append_drop width (source.drop start)]
    _ = source.take start ++
        ((source.drop start).take width ++ source.drop (start + width)) := by
      rw [List.drop_drop]

-- The verified parser window can be reused as the source of its consumed
-- piece. Only the short overlap with the next piece must be checked.
theorem invariant1_window_from_overlap (window following : List Char)
    (consumed : Nat) (within : consumed ≤ window.length)
    (overlap : following.take (window.length - consumed) = window.drop consumed) :
    (window.take consumed ++ following).take window.length = window := by
  have split := List.take_append_drop consumed window
  have prefixLen : (window.take consumed).length = consumed := by
    simp [List.length_take, Nat.min_eq_left within]
  rw [List.take_append]
  rw [List.take_of_length_le (by omega : (window.take consumed).length ≤ window.length)]
  rw [prefixLen, overlap]
  exact split

theorem invariant1_window_from_parts (piece lookahead following : List Char)
    (overlap : following.take lookahead.length = lookahead) :
    (piece ++ following).take (piece ++ lookahead).length = piece ++ lookahead := by
  rw [List.length_append, List.take_append]
  rw [List.take_of_length_le (by omega : piece.length ≤ piece.length + lookahead.length)]
  simpa only [Nat.add_sub_cancel_left] using congrArg (piece ++ ·) overlap

end PegHs.MetaExecution
