import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_586_SplitAndAppend",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_586_SplitAndAppend",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Splits an array at index n and appends the parts in reverse order.
Input array l is split at index n, and the parts are appended with the second part first.

@param l The input array to split and append
@param n The index at which to split the array
@return The resulting array after splitting and appending
-/
def SplitAndAppend (l : Array Int) (n : Int) : Array Int := sorry

/--
Specification for SplitAndAppend:
- Requires n to be non-negative and less than array length
- Ensures output array has same length as input
- Ensures elements are rotated by n positions
-/
theorem SplitAndAppend_spec (l : Array Int) (n : Int) :
  n ≥ 0 ∧ n < l.size →
  let r := SplitAndAppend l n
  r.size = l.size ∧
  ∀ i, 0 ≤ i ∧ i < l.size → r.get ⟨i⟩ = l.get ((i + n) % l.size) := sorry

end DafnyBenchmarks