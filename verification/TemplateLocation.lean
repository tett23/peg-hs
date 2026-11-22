import Std

namespace PegHs.TemplateLocation

structure Location where
  file : Nat
  line : Nat
  col : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

-- Numeric locations in the small model fixtures denote column-only values.
instance (n : Nat) : OfNat Location n := ⟨⟨0, 0, n⟩⟩

instance : ToString Location where
  toString l := s!"{l.file}:{l.line}:{l.col}"

theorem root_adr0097_i2_location_eq_iff (a b : Location) :
    a = b ↔ a.file = b.file ∧ a.line = b.line ∧ a.col = b.col := by
  cases a
  cases b
  simp

end PegHs.TemplateLocation
