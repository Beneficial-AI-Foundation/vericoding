import Std

open Std.Do

/-!
{
  "name": "Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3_search_findPositionOfIndex_FindPositionOfElement",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_a3_search_findPositionOfIndex_FindPositionOfElement",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Finds position of an element in an array.
Translated from Dafny method FindPositionOfElement.

Parameters:
- a: Array of integers
- Element: Natural number to search for
- n1: Natural number representing array size
- s1: Sequence of integers matching array prefix

Returns:
- Position: Integer position (-1 or ≥ 1)
- Count: Natural number count
-/
def FindPositionOfElement (a : Array Int) (Element : Nat) (n1 : Nat) (s1 : Array Int) :
  Int × Nat := sorry

/--
Specification for FindPositionOfElement method
-/
theorem FindPositionOfElement_spec
  (a : Array Int) (Element : Nat) (n1 : Nat) (s1 : Array Int) :
  (n1 = s1.size ∧ 0 ≤ n1 ∧ n1 ≤ a.size) →
  (∀ i, 0 ≤ i ∧ i < s1.size → a[i]! = s1[i]!) →
  let (Position, Count) := FindPositionOfElement a Element n1 s1
  (Position = -1 ∨ Position ≥ 1) ∧
  (s1.size ≠ 0 ∧ Position ≥ 1 → ∃ i, 0 ≤ i ∧ i < s1.size ∧ s1[i]! = Element) := sorry

end DafnyBenchmarks
