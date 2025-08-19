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
lemma list_range_length (k : Nat) : (List.range k).length = k := by
  simp [List.length_range]

-- LLM HELPER
lemma list_get_range (k : Nat) (i : Fin (List.range k).length) : 
  (List.range k).get i = i.val := by
  simp [List.get_range]

-- LLM HELPER
lemma list_mem_map_iff {α β : Type*} (f : α → β) (l : List α) (b : β) :
  b ∈ l.map f ↔ ∃ a ∈ l, f a = b := by
  simp [List.mem_map]

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
  apply triple_pure
  constructor
  · simp [numpy_split, List.length_map, List.length_range]
  · intro i
    simp [numpy_split, list_mem_map_iff, List.mem_range]
    use i.val, i.isLt
    ext j
    simp [Vector.get_ofFn]