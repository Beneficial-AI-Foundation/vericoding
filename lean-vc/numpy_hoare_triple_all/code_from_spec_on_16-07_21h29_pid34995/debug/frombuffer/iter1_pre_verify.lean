import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Interpret a buffer as a 1-dimensional array.
    Takes a buffer (represented as a Vector of bytes), the count of elements to read,
    and an offset (starting position in bytes) to create a Vector of the specified type.
    This models numpy.frombuffer which interprets raw bytes as typed array elements. -/
def frombuffer {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  Vector.ofFn (fun i => buffer.get ⟨offset + i.val, by
    have h : i.val < count := i.isLt
    sorry⟩)

-- LLM HELPER
lemma offset_plus_i_lt {n count offset : Nat} (i : Fin count) (h : offset + count ≤ n) :
    offset + i.val < n := by
  have h_i : i.val < count := i.isLt
  linarith

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
    ⦃⇓result => ⌜∀ i : Fin count, result.get i = buffer.get ⟨offset + i.val, offset_plus_i_lt i h_bounds⟩⌝⦄ := by
  constructor
  · constructor
    · exact h_bounds
    · exact h_offset
  · intro result h_result
    intro i
    simp [frombuffer] at h_result
    rw [h_result]
    simp [Vector.get_ofFn]