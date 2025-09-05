import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_588_DifferenceMinMax",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_588_DifferenceMinMax",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Finds the minimum value in an array recursively -/
def Min (a : Array Int) : Int :=
  if a.size = 1 then
    a.get! 0
  else
    let minPrefix := Min (a.extract 0 (a.size - 1))
    if a.get! (a.size - 1) ≤ minPrefix then
      a.get! (a.size - 1)
    else
      Min (a.extract 0 (a.size - 1))

/-- Finds the maximum value in an array recursively -/
def Max (a : Array Int) : Int :=
  if a.size = 1 then
    a.get! 0
  else
    let maxPrefix := Max (a.extract 0 (a.size - 1))
    if a.get! (a.size - 1) ≥ maxPrefix then
      a.get! (a.size - 1)
    else
      Max (a.extract 0 (a.size - 1))

/-- Computes the difference between maximum and minimum values in an array -/
def DifferenceMinMax (a : Array Int) : Int :=
  Max a - Min a

/-- Specification for DifferenceMinMax -/
theorem DifferenceMinMax_spec (a : Array Int) :
  a.size > 0 →
  DifferenceMinMax a = Max a - Min a := sorry

end DafnyBenchmarks