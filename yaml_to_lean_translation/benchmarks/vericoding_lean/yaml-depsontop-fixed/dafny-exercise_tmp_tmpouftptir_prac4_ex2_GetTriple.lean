import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "dafny-exercise_tmp_tmpouftptir_prac4_ex2_GetTriple",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_prac4_ex2_GetTriple",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Predicate that checks if an array contains three consecutive equal elements
-/
def triple (a : Array Int) : Bool :=
  ∃ i, 0 ≤ i ∧ i < a.size - 2 ∧ a.get i = a.get (i + 1) ∧ a.get (i + 1) = a.get (i + 2)

/--
GetTriple method that finds three consecutive equal elements in an array
Returns the starting index of such a triple if found, or array length if not found
-/
def GetTriple (a : Array Int) : Int := sorry

/--
Main specification for GetTriple method
-/
theorem GetTriple_spec (a : Array Int) :
  let index := GetTriple a
  (0 ≤ index ∧ index < a.size - 2 ∨ index = a.size) ∧
  (index = a.size ↔ ¬(triple a)) ∧
  (0 ≤ index ∧ index < a.size - 2 ↔ triple a) ∧
  (0 ≤ index ∧ index < a.size - 2 →
    a.get index = a.get (index + 1) ∧ a.get (index + 1) = a.get (index + 2)) := sorry

end DafnyBenchmarks