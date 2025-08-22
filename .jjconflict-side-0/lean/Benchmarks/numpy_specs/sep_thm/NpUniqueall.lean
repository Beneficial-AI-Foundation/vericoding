/-
# NumPy Unique All Specification

Port of np_uniqueall.dfy to Lean 4
-/

namespace DafnySpecs.NpUniqueall

/-- Find unique elements in array -/
def uniqueall {n : Nat} (a : Vector Int n) : Vector Int n := sorry

/-- Specification: Result length is bounded by input -/
theorem uniqueall_length {n : Nat} (a : Vector Int n) :
  let ret := uniqueall a
  ret.toList.length ≤ n := sorry

/-- Specification: All elements in result are unique -/
theorem uniqueall_unique {n : Nat} (a : Vector Int n) :
  let ret := uniqueall a
  ∀ i j : Nat, i < ret.toList.length → j < ret.toList.length → i ≠ j → ret[i]! ≠ ret[j]! := sorry

/-- Specification: All unique elements from input are in result -/
theorem uniqueall_complete {n : Nat} (a : Vector Int n) :
  let ret := uniqueall a
  ∀ i : Fin n, ∃ j : Nat, j < ret.toList.length ∧ ret[j]! = a[i] := sorry

end DafnySpecs.NpUniqueall
