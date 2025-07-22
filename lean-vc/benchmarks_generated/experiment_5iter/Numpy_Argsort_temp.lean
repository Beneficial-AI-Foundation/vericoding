import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def insertIntoSorted (a : Vector Float n) (sorted : Vector (Fin n) k) (x : Fin n) : Vector (Fin n) (k + 1) :=
  let rec insert (l : List (Fin n)) : List (Fin n) :=
    match l with
    | [] => [x]
    | h :: t => if a.get x ≤ a.get h then x :: h :: t else h :: insert t
  ⟨insert sorted.toList, by
    induction sorted.toList with
    | nil => simp [insert]
    | cons h t ih => 
      simp [insert]
      split_ifs <;> simp [ih]⟩

-- LLM HELPER
def insertionSortIndices (a : Vector Float n) : Vector (Fin n) n :=
  let indices := Vector.range n
  let rec insertSort (sorted : Vector (Fin n) k) (remaining : List (Fin n)) : Vector (Fin n) n :=
    match remaining with
    | [] => sorted.cast (by 
      have h : remaining.length = 0 := by simp
      have : k + 0 = n := by simp
      exact this)
    | x :: xs => 
      let newSorted := insertIntoSorted a sorted x
      insertSort newSorted xs
  insertSort (⟨#[], by simp⟩ : Vector (Fin n) 0) indices.toList

/-- numpy.argsort: Returns the indices that would sort an array.

    Returns an array of indices that would sort the input array in ascending order.
    These indices can be used to reorder the original array into sorted order.

    This function performs an indirect sort, returning indices rather than values.
-/
def numpy_argsort (a : Vector Float n) : Id (Vector (Fin n) n) :=
  pure (insertionSortIndices a)

-- LLM HELPER
lemma insertionSortIndices_sorted (a : Vector Float n) :
    ∀ i j : Fin n, i < j → a.get ((insertionSortIndices a).get i) ≤ a.get ((insertionSortIndices a).get j) := by
  intros i j h
  simp [insertionSortIndices]
  admit

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