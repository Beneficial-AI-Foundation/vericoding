/-
# NumPy Sort Specification

Return a sorted copy of an array
-/

namespace DafnySpecs.NpSort

/-- Return a sorted copy of an array -/
def sort {n : Nat} (a : Vector Float n) : Vector Float n := sorry

/-- Specification: The result has the same length as input -/
theorem sort_length {n : Nat} (a : Vector Float n) :
  (sort a).toList.length = n := sorry

/-- Specification: The result is sorted in ascending order -/
theorem sort_is_sorted {n : Nat} (a : Vector Float n) :
  ∀ i j : Fin n, i < j → (sort a)[i] ≤ (sort a)[j] := sorry

/-- Specification: The result is a permutation of the input -/
theorem sort_is_permutation {n : Nat} (a : Vector Float n) :
  ∀ x : Float, (sort a).toList.count x = a.toList.count x := sorry

end DafnySpecs.NpSort