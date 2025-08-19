import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.insert: Insert values along the given axis before the given indices.

    Creates a new vector with values inserted at specified positions. For the 1D case,
    values are inserted before the given index position, shifting subsequent elements.
    
    When inserting a single value at position i into a vector of length n,
    the result has length n+1 where:
    - Elements before position i remain unchanged
    - The new value is at position i
    - Elements from position i onward are shifted by one
    
    This specification focuses on single value insertion. The actual NumPy function
    supports multiple insertions and various index specifications, but for formal
    verification we start with the simplest case.
-/
def numpy_insert {n : Nat} (arr : Vector α n) (idx : Fin (n + 1)) (value : α) : Id (Vector α (n + 1)) :=
  pure ⟨List.insertIdx idx.val arr.toList value, by
    simp [List.length_insertIdx]
    exact Nat.add_comm 1 n⟩

-- LLM HELPER
lemma List.get_insertIdx_lt {l : List α} {i : Nat} {v : α} {j : Nat} 
    (h : j < i) (hj : j < l.length) : 
    (l.insertIdx i v).get ⟨j, by simp [List.length_insertIdx]; omega⟩ = l.get ⟨j, hj⟩ := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons head tail ih =>
    cases i with
    | zero => simp at h
    | succ i' =>
      simp [List.insertIdx]
      cases j with
      | zero => simp
      | succ j' => 
        simp
        apply ih
        · omega
        · simp at hj; exact hj

-- LLM HELPER
lemma List.get_insertIdx_eq {l : List α} {i : Nat} {v : α} (hi : i ≤ l.length) :
    (l.insertIdx i v).get ⟨i, by simp [List.length_insertIdx]; omega⟩ = v := by
  induction l generalizing i with
  | nil => 
    simp [List.insertIdx]
    cases i with
    | zero => simp
    | succ i' => simp at hi
  | cons head tail ih =>
    cases i with
    | zero => simp [List.insertIdx]
    | succ i' =>
      simp [List.insertIdx]
      apply ih
      simp at hi
      exact hi

-- LLM HELPER
lemma List.get_insertIdx_gt {l : List α} {i : Nat} {v : α} {j : Nat} 
    (h : i < j) (hj : j < l.length + 1) (hi : i ≤ l.length) : 
    (l.insertIdx i v).get ⟨j, by simp [List.length_insertIdx]; exact hj⟩ = 
    l.get ⟨j - 1, by omega⟩ := by
  induction l generalizing i j with
  | nil => 
    simp at hj hi
    omega
  | cons head tail ih =>
    cases i with
    | zero => 
      simp [List.insertIdx]
      cases j with
      | zero => omega
      | succ j' => simp
    | succ i' =>
      simp [List.insertIdx]
      cases j with
      | zero => omega
      | succ j' => 
        simp
        have : j' - i' = (j' + 1) - (i' + 1) := by omega
        rw [←this]
        apply ih
        · omega
        · simp at hj; exact hj
        · simp at hi; exact hi

/-- Specification: numpy.insert creates a new vector with the value inserted at the specified index.

    Precondition: The index is valid (enforced by type system via Fin (n + 1))
    
    Postcondition: 
    1. **Preservation**: Elements before the insertion point are preserved at their original indices
    2. **Insertion**: The new value is placed exactly at the specified index
    3. **Shifting**: Elements at or after the insertion point are shifted right by one position
    4. **Size**: The result has exactly one more element than the input
    
    Mathematical properties:
    - For all i < idx: result[i] = arr[i]
    - result[idx] = value
    - For all i > idx: result[i] = arr[i-1]
    
    Additional properties (sanity checks):
    - The operation is deterministic (same inputs produce same output)
    - The operation preserves the relative order of existing elements
    - No elements from the original array are lost or duplicated
-/
theorem numpy_insert_spec {n : Nat} (arr : Vector α n) (idx : Fin (n + 1)) (value : α) :
    ⦃⌜True⌝⦄
    numpy_insert arr idx value
    ⦃⇓result => ⌜-- Elements before insertion point are preserved
                 (∀ i : Fin (n + 1), i < idx → 
                   ∃ (h : i.val < n), result.get i = arr.get ⟨i.val, h⟩) ∧ 
                 -- The new value is at the specified index
                 (result.get idx = value) ∧
                 -- Elements after insertion point are shifted
                 (∀ i : Fin (n + 1), idx < i → 
                   ∃ (h : i.val - 1 < n), result.get i = arr.get ⟨i.val - 1, h⟩) ∧
                 -- Sanity check: the result contains all original elements plus the new value
                 (∀ j : Fin n, ∃ i : Fin (n + 1), 
                   (i < idx ∧ i.val = j.val ∧ result.get i = arr.get j) ∨ 
                   (idx < i ∧ i.val = j.val + 1 ∧ result.get i = arr.get j))⌝⦄ := by
  simp only [numpy_insert, Triple.pure_spec]
  constructor
  · -- Elements before insertion point are preserved
    intro i hi
    use i.isLt
    simp [Vector.get]
    exact List.get_insertIdx_lt hi i.isLt
  constructor
  · -- The new value is at the specified index
    simp [Vector.get]
    exact List.get_insertIdx_eq (Nat.le_of_lt_succ idx.isLt)
  constructor
  · -- Elements after insertion point are shifted
    intro i hi
    use (by omega : i.val - 1 < n)
    simp [Vector.get]
    exact List.get_insertIdx_gt hi (by simp; exact i.isLt) (Nat.le_of_lt_succ idx.isLt)
  · -- Sanity check: the result contains all original elements plus the new value
    intro j
    by_cases h : j.val < idx.val
    · use ⟨j.val, by omega⟩
      left
      constructor
      · simp; exact h
      constructor
      · simp
      · simp [Vector.get]
        exact List.get_insertIdx_lt h j.isLt
    · use ⟨j.val + 1, by omega⟩
      right
      constructor
      · simp; omega
      constructor
      · simp
      · simp [Vector.get]
        have : j.val + 1 - 1 = j.val := by omega
        rw [this]
        exact List.get_insertIdx_gt (by omega) (by simp; omega) (Nat.le_of_lt_succ idx.isLt)