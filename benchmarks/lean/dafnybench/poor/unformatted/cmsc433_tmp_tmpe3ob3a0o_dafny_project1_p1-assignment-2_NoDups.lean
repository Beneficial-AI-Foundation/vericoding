import Std


open Std.Do

/-!
{
  "name": "cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_NoDups",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_NoDups",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
NoDups checks if an array has no duplicate adjacent elements.
Requires the array to be sorted.
Returns true if and only if there are no duplicates.
-/
def NoDups (a : Array Int) : Bool := sorry

/--
Specification for NoDups method:
- Requires array to be sorted (each element ≤ next element)
- Ensures result is true iff no adjacent elements are equal
-/
theorem NoDups_spec (a : Array Int) :
  (∀ j : Int, 0 < j ∧ j < a.size → a[(j-1).toNat]! ≤ a[j.toNat]!) →
  (NoDups a ↔ ∀ j : Int, 1 ≤ j ∧ j < a.size → a[(j-1).toNat]! ≠ a[j.toNat]!) := sorry

end DafnyBenchmarks
