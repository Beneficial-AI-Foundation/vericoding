import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_examples_relativeOrder_FindEvenNumbers",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_examples_relativeOrder_FindEvenNumbers",
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

/-- FindEvenNumbers takes an array of integers and returns an array containing only the even numbers
    while preserving their relative order -/
def FindEvenNumbers (arr : Array Int) : Array Int := sorry

/-- Specification for FindEvenNumbers:
    1. All even numbers from input array are in output array
    2. Output array only contains numbers from input array
    3. Relative ordering is preserved -/
theorem FindEvenNumbers_spec (arr : Array Int) (evenNumbers : Array Int) :
  (evenNumbers = FindEvenNumbers arr) →
  (∀ x, (arr.contains x ∧ IsEven x) → evenNumbers.contains x) ∧
  (∀ x, ¬arr.contains x → ¬evenNumbers.contains x) ∧
  (∀ k l, 0 ≤ k ∧ k < l ∧ l < evenNumbers.size →
    ∃ n m, 0 ≤ n ∧ n < m ∧ m < arr.size ∧ 
    evenNumbers.get k = arr.get n ∧ evenNumbers.get l = arr.get m) := sorry

end DafnyBenchmarks