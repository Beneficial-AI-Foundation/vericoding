import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_798_ArraySum",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_798_ArraySum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- 
Recursively sums elements of array up to index n-1.
Requires:
- Array is not null
- 0 ≤ n ≤ array size
-/
def sumTo (a : Array Int) (n : Int) : Int :=
  if n = 0 then 0 
  else sumTo a (n-1) + a.get (n-1)

/--
Returns sum of all elements in array.
Ensures result equals sumTo(a, a.size)
-/
def ArraySum (a : Array Int) : Int := sorry

/-- Specification for ArraySum -/
theorem ArraySum_spec (a : Array Int) :
  ArraySum a = sumTo a a.size := sorry

end DafnyBenchmarks