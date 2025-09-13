import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_784_FirstEvenOddIndices",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_784_FirstEvenOddIndices",
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

/-- Predicate indicating if the given index is the first even number in the array -/
def IsFirstEven (evenIndex : Nat) (lst : Array Int) : Prop :=
  0 ≤ evenIndex ∧ evenIndex < lst.size ∧
  IsEven (lst[evenIndex]!) ∧
  (∀ i, 0 ≤ i ∧ i < evenIndex → IsOdd (lst[i]!))

/-- Predicate indicating if the given index is the first odd number in the array -/
def IsFirstOdd (oddIndex : Nat) (lst : Array Int) : Prop :=
  0 ≤ oddIndex ∧ oddIndex < lst.size ∧
  IsOdd (lst[oddIndex]!) ∧
  (∀ i, 0 ≤ i ∧ i < oddIndex → IsEven (lst[i]!))

/--
Finds the indices of first even and odd numbers in an array
Requires:
- Array has at least 2 elements
- Array contains at least one even number
- Array contains at least one odd number
Ensures:
- Returns valid indices within array bounds
- Returns indices of first even and odd numbers
-/
def FirstEvenOddIndices (lst : Array Int) : Nat × Nat := sorry

theorem FirstEvenOddIndices_spec (lst : Array Int) :
  lst.size ≥ 2 →
  (∃ i, 0 ≤ i ∧ i < lst.size ∧ IsEven (lst[i]!)) →
  (∃ i, 0 ≤ i ∧ i < lst.size ∧ IsOdd (lst[i]!)) →
  let (evenIndex, oddIndex) := FirstEvenOddIndices lst
  0 ≤ evenIndex ∧ evenIndex < lst.size ∧
  0 ≤ oddIndex ∧ oddIndex < lst.size ∧
  IsEven (lst[evenIndex]!) ∧ IsFirstEven evenIndex lst ∧
  IsOdd (lst[oddIndex]!) ∧ IsFirstOdd oddIndex lst := sorry

end DafnyBenchmarks
