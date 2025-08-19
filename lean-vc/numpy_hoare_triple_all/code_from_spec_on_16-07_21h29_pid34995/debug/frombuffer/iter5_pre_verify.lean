import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma offset_plus_i_lt {n count offset : Nat} (i : Fin count) (h : offset + count ≤ n) :
    offset + i.val < n := by
  have h_i : i.val < count := i.isLt
  linarith

/-- Interpret a buffer as a 1-dimensional array.
    Takes a buffer (represented as a Vector of bytes), the count of elements to read,
    and an offset (starting position in bytes) to create a Vector of the specified type.
    This models numpy.frombuffer which interprets raw bytes as typed array elements. -/
def frombuffer {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  Vector.ofFn (fun i => buffer.get ⟨offset + i.val, by
    have h : i.val < count := i.isLt
    have h_offset : offset ≤ n := by
      cases' count with
      | zero => simp
      | succ c => 
        have : offset + count ≤ n := by
          have : 0 < count := Nat.succ_pos c
          have : i.val < count := i.isLt
          have : offset + i.val < n := by
            cases' Nat.lt_or_eq_of_le (Nat.le_add_right offset count) with
            | inl h1 => exact Nat.lt_of_lt_of_le h1 (by assumption)
            | inr h1 => exact Nat.lt_of_le_of_lt (Nat.le_add_right offset i.val) (by
              rw [← h1]; exact Nat.add_lt_add_left h offset)
          exact Nat.le_of_succ_le_succ (Nat.succ_le_of_lt this)
        exact Nat.le_of_add_le_add_right this
    exact Nat.add_lt_of_lt_sub' (Nat.lt_of_succ_le (Nat.succ_le_of_lt h))⟩)

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
  apply Triple.pure
  exact ⟨h_bounds, h_offset⟩
  intro i
  simp [frombuffer]
  rw [Vector.get_ofFn]
  congr
  ext
  simp