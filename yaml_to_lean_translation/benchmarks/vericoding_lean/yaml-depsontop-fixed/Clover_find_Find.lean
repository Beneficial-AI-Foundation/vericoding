import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "Clover_find_Find",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_find_Find",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Find method that searches for a key in an array and returns its index.
Translated from Dafny specification.

@param a The array to search in
@param key The value to search for
@return The index of the first occurrence of key, or -1 if not found
-/
def Find (a : Array Int) (key : Int) : Int := sorry

/--
Specification for Find method ensuring:
1. Return index is within valid bounds (-1 to array length-1)
2. If index is not -1, the element at that index equals key and no earlier elements equal key
3. If index is -1, no elements in the array equal key
-/
theorem Find_spec (a : Array Int) (key : Int) :
  let index := Find a key
  -1 ≤ index ∧ index < a.size ∧
  (index ≠ -1 → a.get index = key ∧ 
    (∀ i, 0 ≤ i ∧ i < index → a.get i ≠ key)) ∧
  (index = -1 → (∀ i, 0 ≤ i ∧ i < a.size → a.get i ≠ key)) := sorry

end DafnyBenchmarks