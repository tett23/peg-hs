import TranslatedDirectiveComment

namespace PegHs.DirectiveArgument

theorem invariant2_translated_comment_offset (q : Bool) (n : Nat) (xs : List Char) :
    translatedOffset q n xs = offset q n xs := by
  fun_induction translatedOffset q n xs <;> simp_all [offset]

theorem invariant2_translated_comment_split (xs : List Char) :
    (xs.take (translatedOffset false 0 xs), xs.drop (translatedOffset false 0 xs)) = splitQuoted false xs := by
  rw [invariant2_translated_comment_offset]
  exact invariant2_quoted_split xs

#print axioms invariant2_translated_comment_split
end PegHs.DirectiveArgument
