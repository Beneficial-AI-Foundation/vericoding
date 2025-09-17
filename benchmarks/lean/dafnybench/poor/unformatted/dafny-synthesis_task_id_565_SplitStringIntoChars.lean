

/-!
{
"name": "dafny-synthesis_task_id_565_SplitStringIntoChars",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_565_SplitStringIntoChars",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Splits a string into an array of its characters.

@param s The input string to split
@return An array containing the characters of the input string
-/
def SplitStringIntoChars (s : String) : Array Char := sorry

/--
Specification for SplitStringIntoChars:
- The output array has the same length as the input string
- Each character in the output matches the corresponding character in the input
-/
theorem SplitStringIntoChars_spec (s : String) :
let v := SplitStringIntoChars s
v.size = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length → v[i]! = s.get ⟨i⟩ := sorry
