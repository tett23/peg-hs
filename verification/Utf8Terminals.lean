import ConcreteTerminal

namespace PegHs.Utf8Terminals
open PegHs.ConcreteTerminal

-- Operate on the bytes remaining at a scalar boundary. Successful literals
-- consume their exact byte sequence; singleton decoding consumes one scalar.
inductive ByteStep : Terminal → ByteArray → ByteArray → Prop where
  | lit (chars : List Char) (rest : ByteArray) :
      ByteStep (.lit chars) (chars.utf8Encode ++ rest) rest
  | cls {ranges c} (rest : ByteArray)
      (member : ∃ lo hi, (lo, hi) ∈ ranges ∧ lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat) :
      ByteStep (.cls ranges) ([c].utf8Encode ++ rest) rest
  | any (c : Char) (rest : ByteArray) :
      ByteStep .any ([c].utf8Encode ++ rest) rest

private theorem encoded_split {xs before after : List Char}
    (h : xs.utf8Encode = before.utf8Encode ++ after.utf8Encode) : xs = before ++ after := by
  have decoded := congrArg ByteArray.utf8Decode? h
  simpa [← List.utf8Encode_append] using decoded

theorem invariant1_byte_step {term xs tail} :
    matchTerm term xs = some tail ↔ ByteStep term xs.utf8Encode tail.utf8Encode := by
  rw [invariant1_matchTerm_iff]
  constructor
  · intro h
    cases h with
    | lit chars rest => simpa [List.utf8Encode_append] using ByteStep.lit chars tail.utf8Encode
    | @cls rs c rest mem =>
      simpa [← List.utf8Encode_append] using ByteStep.cls (c := c) tail.utf8Encode mem
    | any c rest => simpa [← List.utf8Encode_append] using ByteStep.any c tail.utf8Encode
  · intro h
    generalize hsrc : xs.utf8Encode = source at h
    generalize htail : tail.utf8Encode = rest at h
    cases h with
    | lit chars _ =>
      subst rest
      rw [encoded_split hsrc]
      exact .lit _ _
    | @cls rs c _ mem =>
      subst rest
      rw [encoded_split hsrc]
      exact .cls mem
    | any c _ =>
      subst rest
      rw [encoded_split hsrc]
      exact .any _ _

noncomputable def byteOffset (input : List Char) (pos : Nat) := (input.take pos).utf8Encode.size

theorem invariant1_byte_offset (before chars rest : List Char) :
    byteOffset (before ++ chars ++ rest) (before.length + chars.length) =
      before.utf8Encode.size + chars.utf8Encode.size := by
  rw [← List.length_append]
  unfold byteOffset
  rw [List.take_left, List.utf8Encode_append, ByteArray.size_append]

theorem invariant1_iter (c : Char) (rest : List Char) :
    (c :: rest).utf8Encode.utf8DecodeChar? 0 = some c := by
  simp

theorem invariant1_byte_literal_prefix (pattern source : List Char) :
    (∃ tail : ByteArray, pattern.utf8Encode ++ tail = source.utf8Encode) ↔
      ∃ tail, matchTerm (.lit pattern) source = some tail := by
  constructor
  · rintro ⟨bytes, h⟩
    obtain ⟨tail, eq⟩ := List.isPrefix_of_utf8Encode_append_eq_utf8Encode bytes h
    exact ⟨tail, (invariant1_matchTerm_iff _ _ _).mpr (eq ▸ Matches.lit pattern tail)⟩
  · rintro ⟨tail, h⟩
    have step := (invariant1_matchTerm_iff _ _ _).mp h
    cases step
    exact ⟨tail.utf8Encode, (List.utf8Encode_append ..).symm⟩

-- Byte slicing at the two parser positions recovers exactly the bound text
-- used by semantic predicates, including empty captures and multibyte scalars.
theorem invariant1_capture_bytes (before captured after : List Char) :
    (before ++ captured ++ after).utf8Encode.extract before.utf8Encode.size
      (before.utf8Encode.size + captured.utf8Encode.size) = captured.utf8Encode := by
  rw [List.append_assoc, List.utf8Encode_append, List.utf8Encode_append]
  simpa only [Nat.add_zero] using (ByteArray.extract_append_size_add (a := before.utf8Encode) (b := captured.utf8Encode ++ after.utf8Encode) (i := 0) (j := captured.utf8Encode.size)).trans (ByteArray.extract_append_eq_left rfl)

theorem invariant1_capture_value (before captured after : List Char) :
    ((before ++ captured ++ after).utf8Encode.extract before.utf8Encode.size
      (before.utf8Encode.size + captured.utf8Encode.size)).utf8Decode? = some captured.toArray := by
  rw [invariant1_capture_bytes, List.utf8Decode?_utf8Encode]

end PegHs.Utf8Terminals
