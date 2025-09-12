import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_587_ArrayToSeq",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_587_ArrayToSeq",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Converts an array of integers to a sequence (array in Lean).
Preserves length and elements.

@param a Input array of integers
@return Array containing same elements as input array
-/
def ArrayToSeq (a : Array Int) : Array Int := sorry

/--
Specification for ArrayToSeq:
- Output array has same size as input
- Elements are preserved at each index
-/
theorem ArrayToSeq_spec (a : Array Int) :
  let s := ArrayToSeq a
  s.size = a.size ∧ 
  ∀ i, 0 ≤ i ∧ i < a.size → s.get ⟨i⟩ = a.get ⟨i⟩ := sorry

end DafnyBenchmarks