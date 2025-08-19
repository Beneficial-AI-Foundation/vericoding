import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def sort_indices_aux (a : Vector Float n) : Vector (Fin n) n :=
  let pairs := Vector.map (fun i => (a.get i, i)) (Vector.range n)
  let sorted_pairs := Vector.sort_by (fun p => p.1) pairs
  Vector.map (fun p => p.2) sorted_pairs

-- LLM HELPER
lemma vector_get_some {α : Type*} (v : Vector α n) (i : Fin n) : 
  v[i]? = some (v.get i) := by
  simp [Vector.get?_eq_some]

-- LLM HELPER
lemma option_le_some_iff {a b : Float} : 
  some a ≤ some b ↔ a ≤ b := by
  simp [Option.le_def]

/-- numpy.argsort: Returns the indices that would sort an array.

    Returns an array of indices that would sort the input array in ascending order.
    These indices can be used to reorder the original array into sorted order.

    This function performs an indirect sort, returning indices rather than values.
-/
def numpy_argsort (a : Vector Float n) : Id (Vector (Fin n) n) :=
  pure (sort_indices_aux a)

/-- Specification: numpy.argsort returns indices that sort the array.

    Precondition: True
    Postcondition: Using the returned indices produces a sorted array
-/
theorem numpy_argsort_spec (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_argsort a
    ⦃⇓indices => ⌜∀ i j : Fin n, i < j → a[indices.get i]? ≤ a[indices.get j]?⌝⦄ := by
  unfold numpy_argsort
  simp [Triple.pure_spec]
  intro i j hij
  rw [vector_get_some, vector_get_some, option_le_some_iff]
  unfold sort_indices_aux
  -- The proof follows from the correctness of Vector.sort_by
  -- which maintains the sorting property on the paired elements
  apply Vector.sort_by_sorted
  exact hij