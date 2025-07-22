import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Split an array into multiple sub-arrays of equal size.

    This simplified version of numpy.split handles the case where we split
    a 1D array into N equal parts. The array size must be divisible by N.

    For simplicity, we return a list of vectors rather than a vector of vectors.
-/
def numpy_split {n k : Nat} (arr : Vector Float (k * n)) (sections : Nat)
    (h : sections = k) : Id (List (Vector Float n)) :=
  Id.pure (List.range k |>.map fun i => 
    Vector.ofFn fun j => arr.get ⟨i * n + j.val, by
      have h1 : i < k := List.mem_range.mp (List.get_mem _ _ _)
      have h2 : j.val < n := j.isLt
      calc i * n + j.val
        < i * n + n := Nat.add_lt_add_left h2 _
        _ = (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    ⟩)

-- LLM HELPER
lemma list_range_map_length {α : Type*} {k : Nat} (f : Nat → α) :
  (List.range k |>.map f).length = k := by
  rw [List.length_map, List.length_range]

-- LLM HELPER
lemma list_range_get_mem {k : Nat} (i : Fin k) :
  ∃ sub ∈ (List.range k |>.map fun j => Vector.ofFn fun idx => 
    (Vector.mk (List.replicate (k * 1) (0 : Float))).get ⟨j * 1 + idx.val, by
      have h1 : j < k := List.mem_range.mp (List.get_mem _ _ _)
      have h2 : idx.val < 1 := idx.isLt
      calc j * 1 + idx.val
        < j * 1 + 1 := Nat.add_lt_add_left h2 _
        _ = (j + 1) * 1 := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * 1 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    ⟩),
  True := by
  use Vector.ofFn fun idx => 
    (Vector.mk (List.replicate (k * 1) (0 : Float))).get ⟨i.val * 1 + idx.val, by
      have h1 : i.val < k := i.isLt
      have h2 : idx.val < 1 := idx.isLt
      calc i.val * 1 + idx.val
        < i.val * 1 + 1 := Nat.add_lt_add_left h2 _
        _ = (i.val + 1) * 1 := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * 1 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    ⟩
  simp [List.mem_map]
  use i.val
  constructor
  · exact List.mem_range.mpr i.isLt
  · trivial

/-- Specification: numpy_split divides array into equal-sized sub-arrays.

    When splitting an array of size k*n into k sections, each sub-array
    has exactly n elements. The i-th sub-array contains elements from
    positions i*n to (i+1)*n-1 of the original array.
-/
theorem numpy_split_spec {n k : Nat} (arr : Vector Float (k * n))
    (h : k > 0) :
    ⦃⌜k > 0⌝⦄
    numpy_split arr k rfl
    ⦃⇓result => ⌜result.length = k ∧
                ∀ i : Fin k, ∃ sub ∈ result,
                  ∀ j : Fin n, sub.get j = arr.get ⟨i.val * n + j.val, by
                    have h1 : i.val < k := i.isLt
                    have h2 : j.val < n := j.isLt
                    calc i.val * n + j.val
                      < i.val * n + n := Nat.add_lt_add_left h2 _
                      _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
                      _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
                  ⟩⌝⦄ := by
  unfold numpy_split
  simp
  constructor
  · exact list_range_map_length _
  · intro i
    use Vector.ofFn fun j => arr.get ⟨i.val * n + j.val, by
      have h1 : i.val < k := i.isLt
      have h2 : j.val < n := j.isLt
      calc i.val * n + j.val
        < i.val * n + n := Nat.add_lt_add_left h2 _
        _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    ⟩
    constructor
    · simp [List.mem_map]
      use i.val
      constructor
      · exact List.mem_range.mpr i.isLt
      · rfl
    · intro j
      simp [Vector.get_ofFn]