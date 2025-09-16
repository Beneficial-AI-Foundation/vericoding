

/-!
{
"name": "dafny-synthesis_task_id_94_MinSecondValueFirst",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_94_MinSecondValueFirst",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the first element of the sequence that has the minimum second element.

@param s Array of integer sequences
@return The first element of the sequence with minimum second element
-/
def MinSecondValueFirst (s : Array (Array Int)) : Int := sorry

/--
Specification for MinSecondValueFirst:
- Requires array is non-empty
- Requires all sequences have at least 2 elements
- Ensures result is first element of sequence with minimum second element
-/
theorem MinSecondValueFirst_spec (s : Array (Array Int)) :
s.size > 0 ∧
(∀ i, 0 ≤ i ∧ i < s.size → s[i]!.size ≥ 2) →
∃ i, 0 ≤ i ∧ i < s.size ∧
MinSecondValueFirst s = (s[i]!)[0]! ∧
(∀ j, 0 ≤ j ∧ j < s.size → (s[i]!)[1]! ≤ (s[j]!)[1]!) := sorry
