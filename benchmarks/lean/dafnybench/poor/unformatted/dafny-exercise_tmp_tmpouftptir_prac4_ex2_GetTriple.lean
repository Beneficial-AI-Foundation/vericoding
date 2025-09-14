import Std

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
def triple (a : Array Int) : Prop :=
  ∃ i, 0 ≤ i ∧ i < a.size - 2 ∧ a[i]! = a[(i + 1)]! ∧ a[(i + 1)]! = a[(i + 2)]!

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
    a[index.toNat]! = a[(index + 1).toNat]! ∧ a[(index + 1).toNat]! = a[(index + 2).toNat]!) := sorry

end DafnyBenchmarks
