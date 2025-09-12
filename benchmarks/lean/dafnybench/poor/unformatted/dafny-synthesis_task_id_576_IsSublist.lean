import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_576_IsSublist",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_576_IsSublist",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Checks if one array is a sublist of another array.
Translated from Dafny method IsSublist.

@param sub The potential sublist to check
@param main The main list to search in
@return True if sub is a sublist of main
-/
def IsSublist (sub : Array Int) (main : Array Int) : Bool := sorry

/--
Specification for IsSublist method.
Ensures that the result is true if and only if there exists a valid index i
where sub matches a slice of main starting at index i.
-/
theorem IsSublist_spec (sub main : Array Int) :
  ∃ i, 0 ≤ i ∧ i ≤ main.size - sub.size ∧ 
  (∀ j, 0 ≤ j ∧ j < sub.size → sub.get ⟨j⟩ = main.get (i + j)) →
  IsSublist sub main = true := sorry

end DafnyBenchmarks