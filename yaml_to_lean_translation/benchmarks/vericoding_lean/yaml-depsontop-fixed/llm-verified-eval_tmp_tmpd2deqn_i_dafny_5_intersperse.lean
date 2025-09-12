import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "llm-verified-eval_tmp_tmpd2deqn_i_dafny_5_intersperse",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: llm-verified-eval_tmp_tmpd2deqn_i_dafny_5_intersperse",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Inserts a delimiter between elements of an array of integers.

@param numbers The input array of integers
@param delimiter The delimiter value to insert between elements
@return The array with delimiters inserted between elements
-/
def intersperse (numbers : Array Int) (delimiter : Int) : Array Int := sorry

/--
Specification for intersperse function:
1. Output size is 2 * input size - 1 if input is non-empty, 0 otherwise
2. Even indices contain original array elements
3. Odd indices contain the delimiter
-/
theorem intersperse_spec (numbers : Array Int) (delimiter : Int) :
  let result := intersperse numbers delimiter
  (result.size = if numbers.size > 0 then 2 * numbers.size - 1 else 0) ∧
  (∀ i, 0 ≤ i ∧ i < result.size → i % 2 = 0 → result.get i = numbers.get (i / 2)) ∧
  (∀ i, 0 ≤ i ∧ i < result.size → i % 2 = 1 → result.get i = delimiter) := sorry

end DafnyBenchmarks