import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma offset_add_i_lt_n {n count offset : Nat} {i : Fin count} 
    (h : offset + count ≤ n) : offset + i.val < n := by
  have h_i_lt : i.val < count := i.isLt
  linarith

/-- Interpret a buffer as a 1-dimensional array.
    Takes a buffer (represented as a Vector of bytes), the count of elements to read,
    and an offset (starting position in bytes) to create a Vector of the specified type.
    This models numpy.frombuffer which interprets raw bytes as typed array elements. -/
def frombuffer {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  Id.pure (Vector.ofFn fun i => buffer.get ⟨offset + i.val, by
    have h_i_lt : i.val < count := i.isLt
    sorry⟩)

/-- Specification: frombuffer interprets raw bytes from a buffer as a typed array.
    The function reads 'count' elements starting from 'offset' bytes into the buffer.
    The result is a Vector containing the selected bytes in the same order
    as they appear in the buffer. Key properties:
    1. Buffer must have sufficient bytes for the requested elements
    2. Offset must be within buffer bounds when count > 0
    3. Elements are read sequentially from the buffer starting at offset
    4. The result preserves the sequential order of elements in the buffer
    5. Each output element corresponds to exactly one input buffer byte -/
theorem frombuffer_spec {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat)
    (h_bounds : offset + count ≤ n) (h_offset : offset < n ∨ count = 0) :
    ⦃⌜offset + count ≤ n ∧ (offset < n ∨ count = 0)⌝⦄
    frombuffer buffer count offset
    ⦃⇓result => ⌜∀ i : Fin count, result.get i = buffer.get ⟨offset + i.val, offset_add_i_lt_n h_bounds⟩⌝⦄ := by
  unfold frombuffer
  apply spec_pure
  constructor
  · exact ⟨h_bounds, h_offset⟩
  · intro i
    simp [Vector.get_ofFn]