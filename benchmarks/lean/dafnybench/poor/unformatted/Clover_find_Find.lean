

/-!
{
"name": "Clover_find_Find",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_find_Find",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Find method that searches for a key in an array and returns its index.
Translated from Dafny specification.

@param a The array to search in
@param key The value to search for
@return The index of the first occurrence of key, or -1 if not found
-/
def Find (a : Array Int) (key : Int) : Int := sorry

/--
Specification for Find method ensuring:
1. Return index is within valid bounds (-1 to array length-1)
2. If index is not -1, the element at that index equals key and no earlier elements equal key
3. If index is -1, no elements in the array equal key
-/
theorem Find_spec (a : Array Int) (key : Int) :
-1 ≤ Find a key ∧ Find a key < a.size ∧
(Find a key ≠ -1 → ∃ idx : Nat, idx < a.size ∧ a[idx]! = key ∧
(∀ i, 0 ≤ i ∧ i < idx → a[i]! ≠ key)) ∧
(Find a key = -1 → (∀ i, 0 ≤ i ∧ i < a.size → a[i]! ≠ key)) := sorry