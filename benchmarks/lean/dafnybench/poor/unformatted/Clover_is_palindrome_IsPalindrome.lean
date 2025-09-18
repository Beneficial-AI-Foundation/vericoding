

/-!
{
"name": "Clover_is_palindrome_IsPalindrome",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_is_palindrome_IsPalindrome",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if a sequence of characters is a palindrome.
Translated from Dafny method IsPalindrome.

@param x The input sequence of characters to check
@return True if the sequence is a palindrome, false otherwise
-/
def IsPalindrome (x : Array Char) : Bool := sorry

/--
Specification for IsPalindrome method.
States that the result is true if and only if each character matches its corresponding
character from the end of the sequence.
-/
theorem IsPalindrome_spec (x : Array Char) :
IsPalindrome x = true ↔
(∀ i, 0 ≤ i ∧ i < x.size → x[i]! = x[x.size - i - 1]!) := sorry
