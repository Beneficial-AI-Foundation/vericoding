import Std

open Std.Do

/-!
{
  "name": "dafny-exercise_tmp_tmpouftptir_prac3_ex2_GetEven",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_prac3_ex2_GetEven",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
GetEven modifies an array of natural numbers by incrementing odd numbers by 1.

@param s Array of natural numbers to be modified
-/
def GetEven (s : Array Nat) : Array Nat := sorry

/--
Specification for GetEven:
For each element in the array:
- If the original element was odd, the new element is incremented by 1
- If the original element was even, it remains unchanged
-/
theorem GetEven_spec (s : Array Nat) :
  ∀ i, 0 ≤ i ∧ i < s.size →
    let s' := GetEven s
    if s[i]! % 2 = 1
    then s'[i]! = s[i]! + 1
    else s'[i]! = s[i]! := sorry

end DafnyBenchmarks
