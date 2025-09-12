```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_find_Find",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_find_Find",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["Find"]
}
-/

namespace DafnyBenchmarks

/--
Find method that searches for a key in an array.
Returns the index of the first occurrence of key, or negative if not found.

@param a The array to search in
@param key The value to search for
@return The index where key is found, or negative if not found
-/
def Find (a : Array Int) (key : Int) : Int := sorry

/--
Specification for the Find method:
- If result i is non-negative:
  1. i must be less than array length
  2. key must be at position i
  3. i must be smallest position containing key
- If result i is negative:
  - key must not appear anywhere in array
-/
theorem Find_spec (a : Array Int) (key : Int) (i : Int) :
  i = Find a key →
  (0 ≤ i → 
    (i < a.size ∧ 
     a.get i = key ∧
     (∀ k, 0 ≤ k ∧ k < i → a.get k ≠ key))) ∧
  (i < 0 →
    (∀ k, 0 ≤ k ∧ k < a.size → a.get k ≠ key)) := sorry

end DafnyBenchmarks
```