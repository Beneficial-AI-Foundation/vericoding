import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_133_SumOfNegatives",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_133_SumOfNegatives",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Recursively sums all negative numbers in an array up to index n.
Translated from Dafny function sumNegativesTo.
-/
def sumNegativesTo (a : Array Int) (n : Int) : Int :=
  if n = 0 then 0 
  else if (a.get (n-1)) < 0 then 
    sumNegativesTo a (n-1) + (a.get (n-1))
  else 
    sumNegativesTo a (n-1)

/--
Main method that returns sum of all negative numbers in array.
Translated from Dafny method SumOfNegatives.
-/
def SumOfNegatives (a : Array Int) : Int := sorry

/--
Specification for SumOfNegatives method.
-/
theorem SumOfNegatives_spec (a : Array Int) :
  SumOfNegatives a = sumNegativesTo a a.size := sorry

end DafnyBenchmarks