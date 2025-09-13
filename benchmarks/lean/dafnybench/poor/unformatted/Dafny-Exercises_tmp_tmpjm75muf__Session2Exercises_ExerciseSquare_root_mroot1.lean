import Std

open Std.Do

/-!
{
  "name": "Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root_mroot1",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root_mroot1",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Computes the integer square root of a non-negative number.
Translated from Dafny method mroot1.

@param n The input non-negative integer
@return r The integer square root satisfying the specification
-/
def mroot1 (n : Int) : Int := sorry

/--
Specification for mroot1 function.
Ensures that the returned value r is non-negative and satisfies r*r ≤ n < (r+1)*(r+1)
-/
theorem mroot1_spec (n : Int) :
  n ≥ 0 →
  let r := mroot1 n
  r ≥ 0 ∧ r * r ≤ n ∧ n < (r + 1) * (r + 1) := sorry

end DafnyBenchmarks