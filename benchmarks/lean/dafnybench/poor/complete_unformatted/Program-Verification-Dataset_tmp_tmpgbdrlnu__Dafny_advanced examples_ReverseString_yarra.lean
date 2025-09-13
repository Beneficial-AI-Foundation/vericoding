import Std

open Std.Do

/-!
{
  "name": "Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ReverseString_yarra",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_ReverseString_yarra",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Predicate specifying that one array is the reverse of another array.
Both arrays must be non-null and of equal length.
-/
def reversed (arr : Array Char) (outarr : Array Char) : Prop :=
  arr.size = outarr.size ∧
  ∀ k, 0 ≤ k ∧ k ≤ arr.size - 1 →
    outarr[k]! = arr[arr.size - 1 - k]!

/--
Method that returns a reversed copy of the input character array.
Input array must be non-null and non-empty.
Output array will be non-null, same length as input, and reversed.
-/
def yarra (arr : Array Char) : Array Char :=
  sorry

/--
Specification for yarra method
-/
theorem yarra_spec (arr : Array Char) :
  arr.size > 0 →
  let outarr := yarra arr
  outarr.size = arr.size ∧ reversed arr outarr := sorry

end DafnyBenchmarks
