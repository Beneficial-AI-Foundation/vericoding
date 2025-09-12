```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems_sumElems",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session5Exercises_ExerciseSumElems_sumElems",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["SumR", "SumL", "SumV"],
  "methods": ["sumElems"]
}
-/

namespace DafnyBenchmarks

/-- Recursive sum function that sums elements from right to left -/
def SumR (s : Array Int) : Int :=
  if s.size = 0 then 0
  else SumR (s.extract 0 (s.size - 1)) + s.get (s.size - 1)

/-- Recursive sum function that sums elements from left to right -/
def SumL (s : Array Int) : Int :=
  if s.size = 0 then 0
  else s.get 0 + SumL (s.extract 1 s.size)

/-- Helper function to sum array elements in range [c,f) -/
def SumV (v : Array Int) (c : Int) (f : Int) : Int :=
  SumR (v.extract c f)

/-- Specification for SumV requiring valid array bounds -/
theorem SumV_spec (v : Array Int) (c f : Int) :
  0 ≤ c ∧ c ≤ f ∧ f ≤ v.size → 
  SumV v c f = SumR (v.extract c f) := sorry

/-- Main method to sum all elements in an array -/
def sumElems (v : Array Int) : Int := sorry

/-- Specification ensuring sumElems returns the sum of all elements -/
theorem sumElems_spec (v : Array Int) :
  sumElems v = SumR v := sorry

end DafnyBenchmarks
```