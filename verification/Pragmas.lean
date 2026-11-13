import Literal

namespace Peg.Verification

-- A fragment body is user-supplied Haskell. This grammar covers the generated
-- wrapper only; it treats the body as opaque text.
inductive LinePragmaSyntax : String → Prop where
  | line (n : Nat) (path : String) (pathSyntax : LiteralSyntax path) :
      LinePragmaSyntax ("{-# LINE " ++ toString n ++ " " ++ path ++ " #-}")

inductive ColumnPragmaSyntax : String → Prop where
  | column (n : Nat) :
      ColumnPragmaSyntax ("{-# COLUMN " ++ toString n ++ " #-}")

def renderLine (line : Nat) (path : String) : String :=
  "{-# LINE " ++ toString line ++ " " ++ encodeLiteral path ++ " #-}"

def renderColumn (column : Nat) : String :=
  "{-# COLUMN " ++ toString column ++ " #-}"

def exampleMarker : String := "{-# PEG'RESTORE_ #-}"

def markerCandidate (n : Nat) : String :=
  "{-# PEG'RESTORE_" ++ String.ofList (List.replicate n 'x') ++ " #-}"

theorem markerCandidate_injective : Function.Injective markerCandidate := by
  intro left right equal
  have lengths := congrArg String.length equal
  simp [markerCandidate, String.length_append] at lengths
  omega

private theorem markerCandidates_nodup (indices : List Nat)
    (distinct : indices.Nodup) : (indices.map markerCandidate).Nodup := by
  induction indices with
  | nil => simp
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at *
      constructor
      · intro member
        obtain ⟨other, inRest, equal⟩ := List.mem_map.mp member
        exact distinct.1 ((markerCandidate_injective equal.symm) ▸ inRest)
      · exact ih distinct.2

theorem invariant3_candidate_exists (occupied : List String) :
    ∃ n < occupied.length + 1, markerCandidate n ∉ occupied := by
  classical
  by_cases someFresh : ∃ n < occupied.length + 1, markerCandidate n ∉ occupied
  · exact someFresh
  exfalso
  have allOccupied : (List.range (occupied.length + 1)).map markerCandidate ⊆ occupied := by
    intro marker member
    obtain ⟨n, inRange, equal⟩ := List.mem_map.mp member
    subst marker
    by_cases present : markerCandidate n ∈ occupied
    · exact present
    · exact False.elim (someFresh ⟨n, List.mem_range.mp inRange, present⟩)
  have atMost := List.Nodup.length_le_of_subset
    (markerCandidates_nodup _ List.nodup_range) allOccupied
  simp at atMost
  omega

inductive FragmentFrameSyntax (marker : String) : String → Prop where
  | frame (line col : String) (body : String)
      (lineSyntax : LinePragmaSyntax line)
      (colSyntax : ColumnPragmaSyntax col) :
      FragmentFrameSyntax marker
        ("\n" ++ line ++ "\n " ++ col ++ body ++ "\n" ++ marker ++ "\n    ")

def renderFragment (marker : String) (line col : Nat) (path body : String) : String :=
  "\n" ++ renderLine line path ++ "\n " ++ renderColumn col ++ body ++
    "\n" ++ marker ++ "\n    "

theorem invariant3_fragment_marker_slot (before after path body : String) (line col n : Nat) :
    ∃ left right : List (List Char), ∀ marker ∈ ["", markerCandidate n],
      (before ++ renderFragment marker line col path body ++ after).toList.splitOn '\n' =
        left ++ [marker.toList] ++ right := by
  let head := before ++ "\n" ++ renderLine line path ++ "\n " ++ renderColumn col ++ body
  let tail := "    " ++ after
  refine ⟨head.toList.splitOn '\n', tail.toList.splitOn '\n', ?_⟩
  intro marker member
  have noLF : '\n' ∉ marker.toList := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> simp [markerCandidate, String.toList_append]
  have parts : (before ++ renderFragment marker line col path body ++ after).toList =
      head.toList ++ '\n' :: (marker.toList ++ '\n' :: tail.toList) := by
    simp [renderFragment, head, tail, String.toList_append, List.append_assoc]
  rw [parts, List.splitOn_append_cons_self, List.splitOn_append_cons_self,
    List.splitOn_eq_singleton noLF, List.append_assoc]

#print axioms invariant3_fragment_marker_slot

-- Each adjacent pair of chunks encloses one generated restore line.
def renderRestoreSlots (marker : String) : List String → String
  | [] => ""
  | [last] => last
  | first :: second :: rest =>
    first ++ "\n" ++ marker ++ "\n" ++ renderRestoreSlots marker (second :: rest)

def restoreLineSlots : List String → List (Option (List Char))
  | [] => [some []]
  | [last] => (last.toList.splitOn '\n').map some
  | first :: second :: rest =>
    (first.toList.splitOn '\n').map some ++ none :: restoreLineSlots (second :: rest)

theorem invariant3_multiple_restore_slots (chunks : List String) (marker : String)
    (singleLine : '\n' ∉ marker.toList) :
    (renderRestoreSlots marker chunks).toList.splitOn '\n' =
      (restoreLineSlots chunks).map (fun slot => slot.getD marker.toList) := by
  induction chunks using renderRestoreSlots.induct with
  | case1 => rfl
  | case2 last => simp [renderRestoreSlots, restoreLineSlots, List.map_map, Function.comp_def]
  | case3 first second rest ih =>
    have chars : (renderRestoreSlots marker (first :: second :: rest)).toList =
        first.toList ++ '\n' :: (marker.toList ++ '\n' ::
          (renderRestoreSlots marker (second :: rest)).toList) := by
      simp [renderRestoreSlots, String.toList_append, List.append_assoc]
    rw [chars, List.splitOn_append_cons_self, List.splitOn_append_cons_self,
      List.splitOn_eq_singleton singleLine, ih]
    simp [restoreLineSlots, List.map_map, Function.comp_def]

#print axioms invariant3_multiple_restore_slots

def finalizeLine (marker : String) (line : Nat) (path input : String) : String :=
  if input == marker then renderLine (line + 1) path else input

def firstUnused (occupied : List String) : List String → Option String
  | [] => none
  | candidate :: rest =>
      if candidate ∈ occupied then firstUnused occupied rest else some candidate

theorem invariant3_first_unused_fresh (occupied candidates : List String)
    (marker : String) (found : firstUnused occupied candidates = some marker) :
    marker ∉ occupied := by
  induction candidates with
  | nil => simp [firstUnused] at found
  | cons candidate rest ih =>
      by_cases used : candidate ∈ occupied
      · simp [firstUnused, used] at found
        exact ih found
      · simp [firstUnused, used] at found
        simpa [found] using used

private theorem firstUnused_member (occupied candidates : List String)
    (marker : String) (found : firstUnused occupied candidates = some marker) :
    marker ∈ candidates := by
  induction candidates with
  | nil => simp [firstUnused] at found
  | cons candidate rest ih =>
      by_cases used : candidate ∈ occupied
      · simp [firstUnused, used] at found
        exact List.mem_cons_of_mem _ (ih found)
      · simp [firstUnused, used] at found
        exact List.mem_cons.mpr (Or.inl found.symm)

private theorem firstUnused_complete (occupied candidates : List String)
    (available : ∃ marker ∈ candidates, marker ∉ occupied) :
    ∃ marker, firstUnused occupied candidates = some marker := by
  induction candidates with
  | nil =>
      obtain ⟨_, member, _⟩ := available
      simp at member
  | cons candidate rest ih =>
      by_cases used : candidate ∈ occupied
      · obtain ⟨marker, member, absent⟩ := available
        have inRest : marker ∈ rest := by
          rcases List.mem_cons.mp member with equal | tail
          · exact False.elim (absent (equal ▸ used))
          · exact tail
        obtain ⟨selected, found⟩ := ih ⟨marker, inRest, absent⟩
        exact ⟨selected, by simpa [firstUnused, used] using found⟩
      · exact ⟨candidate, by simp [firstUnused, used]⟩

theorem invariant3_finite_marker_selection (occupied : List String) :
    ∃ marker,
      firstUnused occupied ((List.range (occupied.length + 1)).map markerCandidate) = some marker ∧
      marker ∉ occupied := by
  obtain ⟨n, bound, absent⟩ := invariant3_candidate_exists occupied
  have member : markerCandidate n ∈
      (List.range (occupied.length + 1)).map markerCandidate := by
    apply List.mem_map.mpr
    exact ⟨n, List.mem_range.mpr bound, rfl⟩
  obtain ⟨marker, found⟩ := firstUnused_complete occupied _ ⟨markerCandidate n, member, absent⟩
  exact ⟨marker, found, invariant3_first_unused_fresh occupied _ marker found⟩

theorem invariant3_line_sound (line : Nat) (path : String) :
    LinePragmaSyntax (renderLine line path) := by
  exact LinePragmaSyntax.line line (encodeLiteral path)
    (invariant3_literal_sound path)

theorem invariant3_column_sound (col : Nat) :
    ColumnPragmaSyntax (renderColumn col) := by
  exact ColumnPragmaSyntax.column col

theorem invariant3_fragment_frame_sound (marker : String) (line col : Nat) (path body : String) :
    FragmentFrameSyntax marker (renderFragment marker line col path body) := by
  exact FragmentFrameSyntax.frame (renderLine line path) (renderColumn col) body
    (invariant3_line_sound line path)
    (invariant3_column_sound col)

theorem invariant3_restore_line_sound (marker : String) (line : Nat) (path : String) :
    LinePragmaSyntax (finalizeLine marker line path marker) := by
  simpa [finalizeLine] using invariant3_line_sound (line + 1) path

theorem invariant3_finalize_other_line (marker : String) (line : Nat) (path input : String)
    (different : input ≠ marker) :
    finalizeLine marker line path input = input := by
  simp [finalizeLine, different]

theorem invariant3_user_line_unchanged (marker : String) (line : Nat)
    (path : String) (userLines : List String)
    (fresh : marker ∉ userLines) :
    userLines.map (finalizeLine marker line path) = userLines := by
  induction userLines with
  | nil => rfl
  | cons userLine rest ih =>
      have different : userLine ≠ marker := by
        intro equal
        apply fresh
        simp [equal]
      have restFresh : marker ∉ rest := by
        intro member
        apply fresh
        simp [member]
      simp [invariant3_finalize_other_line marker line path userLine different, ih restFresh]

theorem invariant3_selected_user_lines_unchanged
    (occupied userLines : List String) (marker path : String) (line : Nat)
    (found : firstUnused occupied
      ((List.range (occupied.length + 1)).map markerCandidate) = some marker)
    (covered : ∀ userLine ∈ userLines,
      (∃ n, userLine = markerCandidate n) → userLine ∈ occupied) :
    userLines.map (finalizeLine marker line path) = userLines := by
  apply invariant3_user_line_unchanged marker line path userLines
  intro member
  have selected : marker ∈ (List.range (occupied.length + 1)).map markerCandidate :=
    firstUnused_member occupied _ marker found
  obtain ⟨n, _, equals⟩ := List.mem_map.mp selected
  exact invariant3_first_unused_fresh occupied _ marker found
    (covered marker member ⟨n, equals.symm⟩)

-- zipWith fix [1..] (T.lines t), with one-based physical line numbers.
def finalizeLines (marker path : String) (lines : List String) : List String :=
  lines.zipIdx.map fun (line, index) => finalizeLine marker (index + 1) path line

-- Data.Text.lines drops exactly the final empty field of a terminated input.
def textLines (source : String) : List String :=
  let fields := (source.toList.splitOn '\n').map String.ofList
  match fields.reverse with
  | "" :: rest => rest.reverse
  | _ => fields

def textUnlines : List String → String
  | [] => ""
  | line :: rest => line ++ "\n" ++ textUnlines rest

def finalizeText (marker path source : String) : String :=
  textUnlines (finalizeLines marker path (textLines source))

theorem textLines_unlines (lines : List String)
    (clean : ∀ line ∈ lines, '\n' ∉ line.toList) : textLines (textUnlines lines) = lines := by
  have fields : ((textUnlines lines).toList.splitOn '\n').map String.ofList = lines ++ [""] := by
    induction lines with
    | nil => rfl
    | cons line rest ih =>
      have chars : (textUnlines (line :: rest)).toList =
          line.toList ++ '\n' :: (textUnlines rest).toList := by
        simp [textUnlines, String.toList_append, List.append_assoc]
      rw [chars, List.splitOn_append_cons_self, List.splitOn_eq_singleton (clean line (by simp))]
      simp [ih (fun x h => clean x (by simp [h]))]
  simp [textLines, fields]

#print axioms textLines_unlines

theorem invariant3_finalize_lines_at (marker path : String) (lines : List String)
    (i : Nat) (inside : i < lines.length) :
    (finalizeLines marker path lines)[i]? =
      some (if lines[i] = marker then renderLine (i + 2) path else lines[i]) := by
  simp [finalizeLines, inside, finalizeLine]

theorem invariant3_finalize_preserves_original_lines (original : List String) :
    let occupied := original.filter fun line => "{-# PEG'RESTORE_".toList.isPrefixOf line.toList
    ∃ marker, firstUnused occupied ((List.range (occupied.length + 1)).map markerCandidate) = some marker ∧
      ∀ (path : String) (rendered : List String) (i : Nat) (hi : i < rendered.length),
        rendered[i] ∈ original → (finalizeLines marker path rendered)[i]? = some rendered[i] := by
  dsimp only
  let occupied := original.filter fun line => "{-# PEG'RESTORE_".toList.isPrefixOf line.toList
  obtain ⟨marker, found, fresh⟩ := invariant3_finite_marker_selection occupied
  refine ⟨marker, found, ?_⟩
  intro path rendered i hi member
  rw [invariant3_finalize_lines_at marker path rendered i hi]
  have differs : rendered[i] ≠ marker := by
    intro eq
    apply fresh
    obtain ⟨n, _, hc⟩ := List.mem_map.mp (firstUnused_member occupied _ marker found)
    apply List.mem_filter.mpr
    refine ⟨eq ▸ member, ?_⟩
    rw [← hc]
    simp [markerCandidate, String.toList_append]
  simp [differs]

#print axioms invariant3_finalize_preserves_original_lines
#print axioms invariant3_finalize_lines_at

#print axioms invariant3_line_sound
#print axioms invariant3_column_sound
#print axioms invariant3_fragment_frame_sound
#print axioms invariant3_restore_line_sound
#print axioms invariant3_finalize_other_line
#print axioms invariant3_user_line_unchanged
#print axioms invariant3_first_unused_fresh
#print axioms invariant3_selected_user_lines_unchanged
#print axioms invariant3_finite_marker_selection

end Peg.Verification
