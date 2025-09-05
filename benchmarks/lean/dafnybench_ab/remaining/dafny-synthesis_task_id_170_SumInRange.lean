import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_170_SumInRange",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_170_SumInRange",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Recursively sums elements in array from start index up to but not including end index.
Translated from Dafny function sumTo.
-/
def sumTo (a : Array Int) (start : Int) (end : Int) : Int :=
  if start == end then 
    0
  else
    sumTo a start (end - 1) + a.get (end - 1)

/--
Main method that returns sum of array elements in given range.
Translated from Dafny method SumInRange.
-/
def SumInRange (a : Array Int) (start : Int) (end : Int) : Int := sorry

/--
Specification for SumInRange method.
Ensures the returned sum equals sumTo for the given range.
-/
theorem SumInRange_spec (a : Array Int) (start : Int) (end : Int) :
  start ≥ 0 ∧ start ≤ end ∧ end ≤ a.size →
  SumInRange a start end = sumTo a start end := sorry

end DafnyBenchmarks