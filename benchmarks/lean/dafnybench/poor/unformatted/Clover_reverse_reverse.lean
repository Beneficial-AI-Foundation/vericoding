

/-!
{
"name": "Clover_reverse_reverse",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_reverse_reverse",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Reverses the elements of an array in place.

@param a The array to reverse

Ensures that each element at index i in the result is equal to
the original element at index (length-1-i)
-/
def reverse (a : Array Int) : Array Int := sorry

/--
Specification for the reverse method.
States that after reversing, each element at index i equals
the original element at index (length-1-i).
-/
theorem reverse_spec (a : Array Int) :
∀ i, 0 ≤ i ∧ i < a.size →
(reverse a)[i]! = a[a.size - 1 - i]! := sorry
