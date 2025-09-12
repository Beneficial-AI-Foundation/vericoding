import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_594_FirstEvenOddDifference",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_594_FirstEvenOddDifference",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Predicate indicating if a number is even -/
def IsEven (n : Int) : Bool :=
  n % 2 = 0

/-- Predicate indicating if a number is odd -/
def IsOdd (n : Int) : Bool :=
  n % 2 ≠ 0

/--
Finds the difference between the first even and first odd number in an array.
Requires:
- Array has at least 2 elements
- Array contains at least one even number
- Array contains at least one odd number
Ensures:
- Returns difference between first even and first odd number found
-/
def FirstEvenOddDifference (a : Array Int) : Int :=
  sorry

/-- Specification for FirstEvenOddDifference -/
theorem FirstEvenOddDifference_spec (a : Array Int) :
  a.size ≥ 2 →
  (∃ i, 0 ≤ i ∧ i < a.size ∧ IsEven (a.get ⟨i⟩)) →
  (∃ i, 0 ≤ i ∧ i < a.size ∧ IsOdd (a.get ⟨i⟩)) →
  ∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size ∧
    IsEven (a.get ⟨i⟩) ∧ IsOdd (a.get ⟨j⟩) ∧
    FirstEvenOddDifference a = a.get ⟨i⟩ - a.get ⟨j⟩ ∧
    (∀ k, 0 ≤ k ∧ k < i → IsOdd (a.get ⟨k⟩)) ∧
    (∀ k, 0 ≤ k ∧ k < j → IsEven (a.get ⟨k⟩)) :=
  sorry

end DafnyBenchmarks