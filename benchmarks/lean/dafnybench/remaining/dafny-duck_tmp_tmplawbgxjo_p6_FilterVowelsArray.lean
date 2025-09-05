import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-duck_tmp_tmplawbgxjo_p6_FilterVowelsArray",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-duck_tmp_tmplawbgxjo_p6_FilterVowelsArray",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- The set of vowels used for filtering -/
def vowels : List Char := 

/-- 
Filters vowels from a sequence of characters.
Returns a new sequence containing only the vowels from the input.
-/
def FilterVowels (xs : Array Char) : Array Char :=
  if xs.size = 0 then
    #
  else if vowels.contains (xs.get (xs.size - 1)) then 
    FilterVowels (xs.extract 0 (xs.size - 1)) |>.push (xs.get (xs.size - 1))
  else
    FilterVowels (xs.extract 0 (xs.size - 1))

/--
Takes an array of characters and returns a new array containing only the vowels.
Ensures the returned array is fresh (newly allocated) and contains exactly the vowels from the input.
-/
def FilterVowelsArray (xs : Array Char) : Array Char := sorry

/--
Specification for FilterVowelsArray ensuring it returns a fresh array containing
exactly the vowels from the input array in the same order they appeared.
-/
theorem FilterVowelsArray_spec (xs : Array Char) (ys : Array Char) :
  ys = FilterVowelsArray xs →
  FilterVowels xs = ys := sorry

end DafnyBenchmarks