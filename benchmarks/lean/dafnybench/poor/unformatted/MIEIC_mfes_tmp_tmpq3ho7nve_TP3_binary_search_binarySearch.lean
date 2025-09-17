

/-!
{
"name": "MIEIC_mfes_tmp_tmpq3ho7nve_TP3_binary_search_binarySearch",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: MIEIC_mfes_tmp_tmpq3ho7nve_TP3_binary_search_binarySearch",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate checking if an array is sorted in ascending order.
-/
def isSorted (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! ≤ a[j]!

/--
Binary search implementation that finds a value in a sorted array.
Returns the index of the value if found, -1 if not found.

@param a The sorted array to search in
@param x The value to search for
@return The index of x in a, or -1 if not found
-/
def binarySearch (a : Array Int) (x : Int) : Int := sorry

/--
Specification for binary search:
- Requires array to be sorted
- Ensures returned index is valid or -1
- Ensures if index found, element at index equals search value
- Ensures if not found (-1), value is not in array
-/
theorem binarySearch_spec (a : Array Int) (x : Int) :
isSorted a →
let index := binarySearch a x
(-1 ≤ index ∧ index < a.size ∧
(index ≠ -1 → a[index.toNat]! = x) ∧
(index = -1 → ∀ i:Nat, 0 ≤ i → i < a.size → a[i]! ≠ x)) := sorry
