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

def restoreMarker : String := "{-# PEG'RESTORE #-}"

inductive FragmentFrameSyntax : String → Prop where
  | frame (line col : String) (body : String)
      (lineSyntax : LinePragmaSyntax line)
      (colSyntax : ColumnPragmaSyntax col) :
      FragmentFrameSyntax
        ("\n" ++ line ++ "\n " ++ col ++ body ++ "\n" ++ restoreMarker ++ "\n    ")

def renderFragment (line col : Nat) (path body : String) : String :=
  "\n" ++ renderLine line path ++ "\n " ++ renderColumn col ++ body ++
    "\n" ++ restoreMarker ++ "\n    "

def finalizeLine (line : Nat) (path input : String) : String :=
  if input == restoreMarker then renderLine (line + 1) path else input

theorem invariant3_line_sound (line : Nat) (path : String)
    (allowed : ∀ c ∈ path.toList, Allowed c) :
    LinePragmaSyntax (renderLine line path) := by
  exact LinePragmaSyntax.line line (encodeLiteral path)
    (invariant3_literal_sound path allowed)

theorem invariant3_column_sound (col : Nat) :
    ColumnPragmaSyntax (renderColumn col) := by
  exact ColumnPragmaSyntax.column col

theorem invariant3_fragment_frame_sound (line col : Nat) (path body : String)
    (allowed : ∀ c ∈ path.toList, Allowed c) :
    FragmentFrameSyntax (renderFragment line col path body) := by
  exact FragmentFrameSyntax.frame (renderLine line path) (renderColumn col) body
    (invariant3_line_sound line path allowed)
    (invariant3_column_sound col)

theorem invariant3_restore_line_sound (line : Nat) (path : String)
    (allowed : ∀ c ∈ path.toList, Allowed c) :
    LinePragmaSyntax (finalizeLine line path restoreMarker) := by
  simpa [finalizeLine] using invariant3_line_sound (line + 1) path allowed

theorem invariant3_finalize_other_line (line : Nat) (path input : String)
    (different : input ≠ restoreMarker) :
    finalizeLine line path input = input := by
  simp [finalizeLine, different]

#print axioms invariant3_line_sound
#print axioms invariant3_column_sound
#print axioms invariant3_fragment_frame_sound
#print axioms invariant3_restore_line_sound
#print axioms invariant3_finalize_other_line

end Peg.Verification
