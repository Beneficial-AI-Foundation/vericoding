/-
# NumPy Argsort Specification

Returns the indices that would sort an array
-/

namespace DafnySpecs.NpArgsort

/-- Returns the indices that would sort an array -/
def argsort {n : Nat} (a : Vector Float n) : Vector (Fin n) n := sorry

/-- Specification: The result has the same length as input -/
theorem argsort_length {n : Nat} (a : Vector Float n) :
  (argsort a).toList.length = n := sorry

/-- Specification: Using the returned indices produces a sorted array -/
theorem argsort_sorts {n : Nat} (a : Vector Float n) :
  ∀ i j : Fin n, i < j → a[(argsort a)[i]] ≤ a[(argsort a)[j]] := sorry

/-- Specification: The result is a permutation of indices -/
theorem argsort_is_permutation {n : Nat} (a : Vector Float n) :
  ∀ i : Fin n, ∃ j : Fin n, (argsort a)[j] = i := sorry

end DafnySpecs.NpArgsort