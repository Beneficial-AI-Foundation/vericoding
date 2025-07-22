import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def insertionSortIndices (a : Vector Float n) : Vector (Fin n) n :=
  let initial := Vector.ofFn (fun i => i)
  Vector.range n |>.foldl (fun acc i =>
    let key := a.get (acc.get ⟨i, by sorry⟩)
    let j := (Vector.range i).foldl (fun pos k =>
      if a.get (acc.get ⟨k, by sorry⟩) > key then pos else k + 1) 0
    Vector.ofFn (fun idx =>
      if idx.val < j then acc.get idx
      else if idx.val = j then acc.get ⟨i, by sorry⟩
      else if idx.val ≤ i then acc.get ⟨idx.val - 1, by sorry⟩
      else acc.get idx)
  ) initial

-- LLM HELPER
lemma insertionSortIndices_sorted (a : Vector Float n) :
    ∀ i j : Fin n, i < j → a.get ((insertionSortIndices a).get i) ≤ a.get ((insertionSortIndices a).get j) := by
  intro i j hij
  sorry

/-- numpy.argsort: Returns the indices that would sort an array.

    Returns an array of indices that would sort the input array in ascending order.
    These indices can be used to reorder the original array into sorted order.

    This function performs an indirect sort, returning indices rather than values.
-/
def numpy_argsort (a : Vector Float n) : Id (Vector (Fin n) n) :=
  pure (insertionSortIndices a)

/-- Specification: numpy.argsort returns indices that sort the array.

    Precondition: True
    Postcondition: Using the returned indices produces a sorted array
-/
theorem numpy_argsort_spec (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_argsort a
    ⦃⇓indices => ⌜∀ i j : Fin n, i < j → a.get (indices.get i) ≤ a.get (indices.get j)⌝⦄ := by
  simp [numpy_argsort]
  apply insertionSortIndices_sorted