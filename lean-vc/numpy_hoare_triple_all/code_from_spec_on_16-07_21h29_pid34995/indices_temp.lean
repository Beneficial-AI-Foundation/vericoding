import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def make_index_vector (n : Nat) : Vector Nat n :=
  Vector.range n

/-- Generate indices for a 1D grid of given size.
    Returns a 2D array where the first dimension has size 1 and contains 
    the indices [0, 1, 2, ..., n-1] -/
def indices (n : Nat) : Id (Vector (Vector Nat n) 1) :=
  pure (Vector.singleton (make_index_vector n))

/-- Specification: indices generates a grid of index values
    This comprehensive specification captures:
    1. The output has the correct shape: (1, n) for 1D case
    2. The single row contains exactly the indices [0, 1, 2, ..., n-1]
    3. Each position i contains the value i
    4. The indices are in ascending order
    5. The result covers all valid indices for the given dimension
-/
theorem indices_spec (n : Nat) :
    ⦃⌜True⌝⦄
    indices n
    ⦃⇓grid => ⌜grid.size = 1 ∧ 
              (∀ i : Fin n, (grid.get ⟨0, by simp⟩).get i = i.val) ∧
              (∀ i j : Fin n, i < j → (grid.get ⟨0, by simp⟩).get i < (grid.get ⟨0, by simp⟩).get j)⌝⦄ := by
  simp [indices, make_index_vector]
  apply pure_post
  simp [Vector.singleton]
  constructor
  · rfl
  constructor
  · intro i
    simp [Vector.singleton, Vector.range, Vector.get_range]
  · intro i j h
    simp [Vector.singleton, Vector.range, Vector.get_range]
    exact Fin.val_lt_of_lt h