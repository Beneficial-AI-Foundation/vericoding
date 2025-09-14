import Std

open Std.Do

/-!
{
  "name": "dafny-duck_tmp_tmplawbgxjo_p4_single",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-duck_tmp_tmplawbgxjo_p4_single",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Merges two arrays of integers into a single array containing all elements.
Input arrays must be non-empty.
-/
def single (x : Array Int) (y : Array Int) : Array Int := sorry

/--
Specification for single method:
- Requires both input arrays to be non-empty
- Ensures output array contains all elements from both input arrays in order
-/
theorem single_spec (x y : Array Int) :
  x.size > 0 ∧ y.size > 0 →
  ∀ (result : Array Int), single x y = result →
    result.size = x.size + y.size ∧
    (∀ i:Fin x.size, i < x.size → result[i]! = x[i]!) ∧
    (∀ i:Fin y.size, i < y.size → result[x.size + i]! = y[i]!) := sorry

end DafnyBenchmarks
