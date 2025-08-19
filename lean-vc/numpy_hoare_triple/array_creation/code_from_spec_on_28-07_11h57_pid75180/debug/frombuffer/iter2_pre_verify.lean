import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def vector_slice {α : Type} {n : Nat} (v : Vector α n) (start : Nat) (count : Nat) 
    (h : start + count ≤ n) : Vector α count :=
  Vector.ofFn (fun i => v.get ⟨start + i.val, by
    have h1 : i.val < count := i.isLt
    omega⟩)

/-- Interpret a buffer as a 1-dimensional array.
    Takes a buffer (represented as a Vector of bytes), the count of elements to read,
    and an offset (starting position in bytes) to create a Vector of the specified type.
    This models numpy.frombuffer which interprets raw bytes as typed array elements. -/
def frombuffer {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  if h : offset + count ≤ n then
    pure (vector_slice buffer offset count h)
  else
    pure (Vector.ofFn (fun _ => 0))

-- LLM HELPER
lemma vector_slice_get {α : Type} {n : Nat} (v : Vector α n) (start : Nat) (count : Nat) 
    (h : start + count ≤ n) (i : Fin count) :
    (vector_slice v start count h).get i = v.get ⟨start + i.val, by
      have h1 : i.val < count := i.isLt
      omega⟩ := by
  simp [vector_slice, Vector.get_ofFn]

-- LLM HELPER
lemma bounds_helper {n offset count : Nat} (h_bounds : offset + count ≤ n) 
    (h_offset : offset < n ∨ count = 0) (i : Fin count) :
    offset + i.val < n := by
  have h1 : i.val < count := i.isLt
  omega

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
    ⦃⇓result => ⌜∀ i : Fin count, result.get i = buffer.get ⟨offset + i.val, bounds_helper h_bounds h_offset i⟩⌝⦄ := by
  apply hl_pure_pre
  constructor
  · exact ⟨h_bounds, h_offset⟩
  · intro _
    simp [frombuffer]
    split_ifs with h
    · apply hl_return
      intro i
      rw [vector_slice_get]
      congr
      ext
      simp
    · apply hl_return
      intro i
      simp [Vector.get_ofFn]
      have : count = 0 := by
        by_contra h_ne
        have : 0 < count := Nat.pos_of_ne_zero h_ne
        have ⟨j⟩ := Fin.exists_iff.mpr this
        exact absurd (bounds_helper h_bounds h_offset j) (not_lt.mpr (le_of_not_gt (mt (fun h_le => by omega) h)))
      simp [this] at i
      exact i.elim0