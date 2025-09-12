import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "Dafny_tmp_tmpv_d3qi10_2_min_minArray",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Dafny_tmp_tmpv_d3qi10_2_min_minArray",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Translation of Dafny min function -/
def min (a b : Int) : Int :=
  if a < b then a else b

/-- Specification for min function -/
theorem min_spec (a b : Int) :
  (min a b ≤ a ∧ min a b ≤ b) ∧ 
  (min a b = a ∨ min a b = b) := sorry

/-- Translation of Dafny minFunction (ghost function) -/
def minFunction (a b : Int) : Int :=
  if a < b then a else b

/-- Specification for minFunction -/
theorem minFunction_spec (a b : Int) :
  (minFunction a b ≤ a ∧ minFunction a b ≤ b) ∧
  (minFunction a b = a ∨ minFunction a b = b) := sorry

/-- Translation of Dafny minArray method -/
def minArray (a : Array Int) : Int := sorry

/-- Specification for minArray -/
theorem minArray_spec (a : Array Int) :
  a.size > 0 →
  (∀ k, 0 ≤ k ∧ k < a.size → minArray a ≤ a.get k) ∧
  (∃ k, 0 ≤ k ∧ k < a.size ∧ minArray a = a.get k) := sorry

end DafnyBenchmarks