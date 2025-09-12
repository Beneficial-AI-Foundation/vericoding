import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_414_AnyValueExists",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_414_AnyValueExists",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Checks if any value from seq1 exists in seq2.
Translated from Dafny method AnyValueExists.

@param seq1 First sequence to check
@param seq2 Second sequence to check against
@return True if any value from seq1 exists in seq2
-/
def AnyValueExists (seq1 : Array Int) (seq2 : Array Int) : Bool := sorry

/--
Specification for AnyValueExists method.
Ensures the result is true if and only if there exists an index i in seq1
such that seq1 is present in seq2.
-/
theorem AnyValueExists_spec (seq1 seq2 : Array Int) :
  AnyValueExists seq1 seq2 ↔ (∃ i, 0 ≤ i ∧ i < seq1.size ∧ seq2.contains (seq1.get ⟨i⟩)) := sorry

end DafnyBenchmarks