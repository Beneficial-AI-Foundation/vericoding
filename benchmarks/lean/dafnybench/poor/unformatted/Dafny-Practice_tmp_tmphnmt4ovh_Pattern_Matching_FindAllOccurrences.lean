

/-!
{
"name": "Dafny-Practice_tmp_tmphnmt4ovh_Pattern Matching_FindAllOccurrences",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Practice_tmp_tmphnmt4ovh_Pattern Matching_FindAllOccurrences",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds all occurrences of a pattern in a text string.
Returns a list of natural number offsets where the pattern occurs.

@param text The text string to search in
@param pattern The pattern string to search for
@return A list of natural number offsets where pattern occurs in text
-/
def FindAllOccurrences (text pattern : String) : List Nat := sorry

/--
Specification for FindAllOccurrences:
1. All offsets returned must be valid positions where pattern can fit in text
2. An offset is in the result if and only if the pattern matches at that position
-/
theorem FindAllOccurrences_spec (text pattern : String) :
let offsets := FindAllOccurrences text pattern
(∀ i : Nat, i ∈ offsets → i + pattern.length ≤ text.length) ∧
(∀ i : Nat, i ≤ text.length - pattern.length →
(i ∈ offsets → (∀ j : Nat, j < pattern.length → text.get ⟨i + j⟩ = pattern.get ⟨j⟩)) ∧
((∀ j : Nat, j < pattern.length → text.get ⟨i + j⟩ = pattern.get ⟨j⟩) → i ∈ offsets)) := sorry
