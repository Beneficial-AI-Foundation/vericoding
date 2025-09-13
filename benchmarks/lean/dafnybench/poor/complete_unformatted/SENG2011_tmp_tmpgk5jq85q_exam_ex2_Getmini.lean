import Std

open Std.Do

/-!
{
  "name": "SENG2011_tmp_tmpgk5jq85q_exam_ex2_Getmini",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: SENG2011_tmp_tmpgk5jq85q_exam_ex2_Getmini",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Finds the index of the first minimum element in an array.

@param a The input array of integers
@return mini The index of the first minimum element

Specification:
- Requires array is non-empty
- Ensures mini is a valid index
- Ensures a is the minimum value
- Ensures a is the first minimum value
-/
def Getmini (a : Array Int) : Nat := sorry

/-- Specification for Getmini -/
theorem Getmini_spec (a : Array Int) (mini : Nat) :
  a.size > 0 →
  (mini = Getmini a) →
  (0 ≤ mini ∧ mini < a.size) ∧
  (∀ x, 0 ≤ x ∧ x < a.size → a[mini]! ≤ a[x]!) ∧
  (∀ x, 0 ≤ x ∧ x < mini → a[mini]! < a[x]!) := sorry

end DafnyBenchmarks
