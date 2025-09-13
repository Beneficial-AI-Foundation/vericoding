import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_792_CountLists",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_792_CountLists",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Counts the number of lists in a sequence of integer lists.

@param lists The sequence of integer lists to count
@return The count of lists in the sequence
-/
def CountLists (lists : Array (Array Int)) : Int := sorry

/--
Specification for CountLists:
- The returned count is non-negative
- The count equals the size of the input sequence
-/
theorem CountLists_spec (lists : Array (Array Int)) :
  let count := CountLists lists
  count ≥ 0 ∧ count = lists.size := sorry

end DafnyBenchmarks