import TranslatedDirectiveComment

namespace PegHs.DirectiveArgument

theorem invariant2_translated_comment_offset (q : Bool) (n : Nat) (xs : List Char) :
    translatedOffset q n xs = offset q n xs := by
  unfold translatedOffset
  fun_induction scanWith (fun n k : Nat => n + k) q n xs <;> simp_all [offset]

theorem invariant2_translated_comment_split (xs : List Char) :
    (xs.take (translatedOffset false 0 xs), xs.drop (translatedOffset false 0 xs)) = splitQuoted false xs := by
  rw [invariant2_translated_comment_offset]
  exact invariant2_quoted_split xs

-- none records the first overflow and is carried through all subsequent steps.
def checkedAdvance (limit : Nat) (n : Option Nat) (k : Nat) : Option Nat := do
  let pos ← n
  if pos + k ≤ limit then some (pos + k) else none

theorem invariant2_checked_offset (limit : Nat) (q : Bool) (n : Nat) (xs : List Char)
    (fits : n + xs.length ≤ limit) :
    scanWith (checkedAdvance limit) q (some n) xs = some (translatedOffset q n xs) := by
  unfold translatedOffset
  fun_induction scanWith (fun n k : Nat => n + k) q n xs <;>
    (try simp only [List.length_cons] at fits) <;>
    simp [scanWith, checkedAdvance, *] <;>
    split <;> first | omega | (apply_assumption; omega)

theorem invariant2_ghc_offset_fits (xs : List Char) (fits : xs.length ≤ ghcIntMax) :
    scanWith (checkedAdvance ghcIntMax) false (some 0) xs = some (offset false 0 xs) := by
  rw [invariant2_checked_offset _ _ _ _ (by simpa using fits), invariant2_translated_comment_offset]

theorem invariant2_text_offset_fits (xs : List Char) (bytes : xs.utf8Encode.size ≤ ghcIntMax) :
    scanWith (checkedAdvance ghcIntMax) false (some 0) xs = some (offset false 0 xs) := by
  apply invariant2_ghc_offset_fits
  apply Nat.le_trans _ bytes
  clear bytes
  induction xs with
  | nil => simp
  | cons c cs ih =>
    rw [show c :: cs = [c] ++ cs from rfl, List.utf8Encode_append, ByteArray.size_append]
    have positive := c.utf8Size_pos
    simp [List.utf8Encode_singleton]
    omega

example : scanWith (checkedAdvance 2) true (some 0) ['\\', '"'] = some 2 := by decide
example : scanWith (checkedAdvance 1) true (some 0) ['\\', '"'] = none := by decide

#print axioms invariant2_text_offset_fits
#print axioms invariant2_ghc_offset_fits
#print axioms invariant2_translated_comment_split
end PegHs.DirectiveArgument
