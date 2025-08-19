import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def vector_slice {α : Type} {n : Nat} (v : Vector α n) (start : Nat) (count : Nat) 
    (h : start + count ≤ n) : Vector α count :=
  Vector.ofFn (fun i => v.get ⟨start + i.val, by
    have h1 : i.val < count := i.isLt
    omega⟩)

def problem_spec (f : {n : Nat} → Vector UInt8 n → Nat → Nat → Id (Vector UInt8 count)) 
    {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat)
    (h_bounds : offset + count ≤ n) (h_offset : offset < n ∨ count = 0) : Prop :=
  ⦃⌜offset + count ≤ n ∧ (offset < n ∨ count = 0)⌝⦄
  f buffer count offset
  ⦃⇓result => ⌜∀ i : Fin count, result.get i = buffer.get ⟨offset + i.val, by
    have h1 : i.val < count := i.isLt
    have h2 : offset + i.val < n := by
      have : offset + i.val < offset + count := Nat.add_lt_add_left h1 offset
      exact Nat.lt_of_lt_of_le this h_bounds
    exact h2⟩⌝⦄

/-- Interpret a buffer as a 1-dimensional array.
    Takes a buffer (represented as a Vector of bytes), the count of elements to read,
    and an offset (starting position in bytes) to create a Vector of the specified type.
    This models numpy.frombuffer which interprets raw bytes as typed array elements. -/
def frombuffer {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  if h : offset + count ≤ n then
    return vector_slice buffer offset count h
  else
    return Vector.ofFn (fun _ => 0)

-- LLM HELPER
lemma vector_slice_get {α : Type} {n : Nat} (v : Vector α n) (start : Nat) (count : Nat) 
    (h : start + count ≤ n) (i : Fin count) :
    (vector_slice v start count h).get i = v.get ⟨start + i.val, by
      have h1 : i.val < count := i.isLt
      have h2 : start + i.val < n := by
        have : start + i.val < start + count := Nat.add_lt_add_left h1 start
        exact Nat.lt_of_lt_of_le this h
      exact h2⟩ := by
  simp [vector_slice, Vector.get_ofFn]

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
    problem_spec frombuffer buffer count offset h_bounds h_offset := by
  rw [problem_spec]
  apply hl_pure_pre
  constructor
  · exact ⟨h_bounds, h_offset⟩
  · intro _
    simp [frombuffer]
    split_ifs with h
    · apply hl_return
      intro i
      rw [vector_slice_get]
    · apply hl_return
      intro i
      cases' count with count_val
      · exact Fin.elim0 i
      · exfalso
        have : offset + (count_val + 1) ≤ n := by
          cases' h_offset with h_off h_zero
          · have : offset + count_val + 1 = offset + (count_val + 1) := by ring
            rw [← this]
            have : offset < offset + count_val + 1 := by
              have : 0 < count_val + 1 := Nat.succ_pos count_val
              exact Nat.lt_add_of_pos_right this
            exact Nat.le_of_lt this
          · simp at h_zero
        exact h this