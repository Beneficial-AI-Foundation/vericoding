import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_784_ProductEvenOdd",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_784_ProductEvenOdd",
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

/-- Predicate indicating if evenIndex is the first even number in the list -/
def IsFirstEven (evenIndex : Nat) (lst : Array Int) : Prop :=
  0 ≤ evenIndex ∧ evenIndex < lst.size ∧
  IsEven (lst[evenIndex]!) ∧
  (∀ i, 0 ≤ i ∧ i < evenIndex → IsOdd (lst[i]!))

/-- Predicate indicating if oddIndex is the first odd number in the list -/
def IsFirstOdd (oddIndex : Nat) (lst : Array Int) : Prop :=
  0 ≤ oddIndex ∧ oddIndex < lst.size ∧
  IsOdd (lst[oddIndex]!) ∧
  (∀ i, 0 ≤ i ∧ i < oddIndex → IsEven (lst[i]!))

/-- Returns indices of first even and odd numbers in list -/
def FirstEvenOddIndices (lst : Array Int) : (Nat × Nat) := sorry

/-- Specification for FirstEvenOddIndices -/
theorem FirstEvenOddIndices_spec (lst : Array Int) :
  lst.size ≥ 2 →
  (∃ i, 0 ≤ i ∧ i < lst.size ∧ IsEven (lst[i]!)) →
  (∃ i, 0 ≤ i ∧ i < lst.size ∧ IsOdd (lst[i]!)) →
  let (evenIndex, oddIndex) := FirstEvenOddIndices lst
  0 ≤ evenIndex ∧ evenIndex < lst.size ∧
  0 ≤ oddIndex ∧ oddIndex < lst.size ∧
  IsEven (lst[evenIndex]!) ∧ IsFirstEven evenIndex lst ∧
  IsOdd (lst[oddIndex]!) ∧ IsFirstOdd oddIndex lst := sorry

/-- Returns product of first even and odd numbers in list -/
def ProductEvenOdd (lst : Array Int) : Int := sorry

/-- Specification for ProductEvenOdd -/
theorem ProductEvenOdd_spec (lst : Array Int) :
  lst.size ≥ 2 →
  (∃ i, 0 ≤ i ∧ i < lst.size ∧ IsEven (lst[i]!)) →
  (∃ i, 0 ≤ i ∧ i < lst.size ∧ IsOdd (lst[i]!)) →
  ∃ i j, 0 ≤ i ∧ i < lst.size ∧ IsEven (lst[i]!) ∧ IsFirstEven i lst ∧
         0 ≤ j ∧ j < lst.size ∧ IsOdd (lst[j]!) ∧ IsFirstOdd j lst ∧
         ProductEvenOdd lst = (lst[i]!) * (lst[j]!) := sorry

end DafnyBenchmarks
