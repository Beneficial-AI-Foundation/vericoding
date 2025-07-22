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
    Vector.mk (List.range n |>.map fun j => arr.get ⟨i * n + j, by
      have h1 : i < k := List.mem_range.mp (List.get_mem (List.range k) i ⟨i, by simp⟩)
      have h2 : j < n := List.mem_range.mp (List.get_mem (List.range n) j ⟨j, by simp⟩)
      calc i * n + j
        < i * n + n := Nat.add_lt_add_left h2 _
        _ = (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    ⟩))

-- LLM HELPER
lemma list_range_map_length (k : Nat) (f : Nat → α) : (List.range k |>.map f).length = k := by
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma get_nth_subarray {n k : Nat} (arr : Vector Float (k * n)) (i : Fin k) :
  ∃ sub ∈ (List.range k |>.map fun i => 
    Vector.mk (List.range n |>.map fun j => arr.get ⟨i * n + j, by
      have h1 : i < k := List.mem_range.mp (List.get_mem (List.range k) i ⟨i, by simp⟩)
      have h2 : j < n := List.mem_range.mp (List.get_mem (List.range n) j ⟨j, by simp⟩)
      calc i * n + j
        < i * n + n := Nat.add_lt_add_left h2 _
        _ = (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    ⟩)),
  ∀ j : Fin n, sub.get j = arr.get ⟨i.val * n + j.val, by
    have h1 : i.val < k := i.isLt
    have h2 : j.val < n := j.isLt
    calc i.val * n + j.val
      < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
  ⟩ := by
  use Vector.mk (List.range n |>.map fun j => arr.get ⟨i.val * n + j, by
    have h1 : i.val < k := i.isLt
    have h2 : j < n := List.mem_range.mp (List.get_mem (List.range n) j ⟨j, by simp⟩)
    calc i.val * n + j
      < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
  ⟩)
  constructor
  · simp [List.mem_map]
    use i.val
    constructor
    · simp [List.mem_range]
      exact i.isLt
    · rfl
  · intro j
    simp [Vector.get]
    congr 1
    simp [List.get_map, List.get_range]

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
  simp [Triple.valid_spec_eq_spec]
  intro _
  simp [numpy_split]
  constructor
  · exact list_range_map_length k _
  · intro i
    exact get_nth_subarray arr i