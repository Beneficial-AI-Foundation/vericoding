import Std

open Std.Do

/-!
{
  "name": "dafny-exercise_tmp_tmpouftptir_firstE_firstE",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_firstE_firstE",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Finds the first occurrence of character 'e' in an array.
Returns the index of first 'e' if found, -1 if not found.

@param a The input array of characters to search
@return The index of first 'e' or -1 if not found
-/
def firstE (a : Array Char) : Int := sorry

/--
Specification for firstE method:
If 'e' exists in the array, returns valid index with first 'e'.
If 'e' does not exist, returns -1.
-/
theorem firstE_spec (a : Array Char) :
  let x := firstE a
  (∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = 'e') →
    (0 ≤ x ∧ x < a.size ∧ a[x.toNat]! = 'e' ∧
     ∀ i, 0 ≤ i ∧ i < x → a[i.toNat]! ≠ 'e') ∧
  (¬∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = 'e') →
    x = -1 := sorry

end DafnyBenchmarks
