```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Clover_linear_search2_LinearSearch",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_linear_search2_LinearSearch",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["LinearSearch"]
}
-/

namespace DafnyBenchmarks

/--
LinearSearch finds the first occurrence of element e in array a.
Requires that e exists somewhere in the array.
Ensures the returned index contains e and all earlier elements are not e.
-/
def LinearSearch (a : Array Int) (e : Int) : Int := sorry

/--
Specification for LinearSearch:
- Requires e exists somewhere in array a
- Ensures returned index n contains e
- Ensures all elements before n are not equal to e
-/
theorem LinearSearch_spec (a : Array Int) (e : Int) :
  (∃ i, 0 ≤ i ∧ i < a.size ∧ a.get i = e) →
  let n := LinearSearch a e
  (0 ≤ n ∧ n < a.size ∧ a.get n = e) ∧
  (∀ k, 0 ≤ k ∧ k < n → a.get k ≠ e) := sorry

end DafnyBenchmarks
```