

/-!
{
"name": "dafny-synthesis_task_id_69_ContainsSequence",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_69_ContainsSequence",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
ContainsSequence checks if a sequence exists in a list of sequences.

@param list The list of integer sequences to search in
@param sub The sequence to search for
@return True if sub exists in list, false otherwise
-/
def ContainsSequence (list : Array (Array Int)) (sub : Array Int) : Bool := sorry

/--
Specification for ContainsSequence:
The result is true if and only if there exists an index i in the valid range
where sub equals the sequence at index i in list
-/
theorem ContainsSequence_spec (list : Array (Array Int)) (sub : Array Int) :
ContainsSequence list sub = (∃ i, 0 ≤ i ∧ i < list.size ∧ sub = list[i]!) := sorry
