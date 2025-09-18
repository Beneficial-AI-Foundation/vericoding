import Init


/-!
{
"name": "dafny-synthesis_task_id_238_CountNonEmptySubstrings",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_238_CountNonEmptySubstrings",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Counts the number of non-empty substrings in a string.
The result is guaranteed to be non-negative and equal to (|s| * (|s| + 1)) / 2.
-/
def CountNonEmptySubstrings (s : String) : Int := sorry

/--
Specification for CountNonEmptySubstrings:
- Result is non-negative
- Result equals (|s| * (|s| + 1)) / 2
-/
theorem CountNonEmptySubstrings_spec (s : String) :
let count := CountNonEmptySubstrings s
count ≥ 0 ∧ count = (s.length * (s.length + 1)) / 2 := sorry
