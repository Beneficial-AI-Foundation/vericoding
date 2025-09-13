import Std

open Std.Do

/-!
{
  "name": "dafny-language-server_tmp_tmpkir0kenl_Test_comp_Arrays_LinearSearch",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-language-server_tmp_tmpkir0kenl_Test_comp_Arrays_LinearSearch",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Prints an array. Implementation omitted.
-/
def PrintArray (a : Array α) : Unit := sorry

/--
Type alias for lowercase characters
-/
def lowercase := Char

/--
Creates a diagonal matrix with given dimensions and values.
-/
def DiagMatrix (rows : Int) (cols : Int) (zero : α) (one : α) : Array (Array α) :=
  sorry

/--
Prints a 2D matrix. Implementation omitted.
-/
def PrintMatrix (m : Array (Array α)) : Unit := sorry

/--
Linear search in an array. Returns index of key if found, or array length if not found.
-/
def LinearSearch (a : Array Int) (key : Int) : Nat := sorry

/--
Specification for LinearSearch:
- Returns valid index or array length
- If index returned, element at that index equals key
-/
theorem LinearSearch_spec (a : Array Int) (key : Int) :
  let n := LinearSearch a key
  n ≤ a.size ∧ (n = a.size ∨ (a.get ⟨n⟩) = key) := sorry

end DafnyBenchmarks