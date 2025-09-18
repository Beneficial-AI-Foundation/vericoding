

/-!
{
"name": "dafny-exercise_tmp_tmpouftptir_filter_Filter",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_filter_Filter",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translates the Dafny Filter method which takes a sequence of characters and a set of characters
and returns a filtered set containing only characters present in both inputs.

@param a The input sequence of characters
@param b The input set of characters to filter against
@return A set containing characters present in both inputs
-/
def Filter (a : Array Char) (b : List Char) : List Char := sorry

/--
Specification for the Filter method ensuring that a character is in the output set
if and only if it appears in both input collections.
-/
theorem Filter_spec (a : Array Char) (b : List Char) (c : List Char) :
c = Filter a b →
(∀ x, (x ∈ a.toList ∧ x ∈ b) ↔ x ∈ c) := sorry
