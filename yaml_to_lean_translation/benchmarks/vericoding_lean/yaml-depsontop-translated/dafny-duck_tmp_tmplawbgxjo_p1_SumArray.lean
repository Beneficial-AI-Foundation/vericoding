```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-duck_tmp_tmplawbgxjo_p1_SumArray",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-duck_tmp_tmplawbgxjo_p1_SumArray",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["Sum"],
  "methods": ["SumArray"]
}
-/

namespace DafnyBenchmarks

/--
Recursively computes the sum of elements in an array.
Given an array of integers, returns their sum.
Example: [1,3,3,2] -> 9
-/
def Sum (xs : Array Int) : Int :=
  if xs.size = 0 then 
    0 
  else
    Sum (xs.extract 0 (xs.size - 1)) + xs.get! (xs.size - 1)

/--
Takes an array of integers and returns their sum.
Ensures the result equals Sum applied to the input array.
-/
def SumArray (xs : Array Int) : Int := sorry

/--
Specification for SumArray ensuring it returns the correct sum
-/
theorem SumArray_spec (xs : Array Int) (s : Int) :
  s = SumArray xs → s = Sum xs := sorry

end DafnyBenchmarks
```