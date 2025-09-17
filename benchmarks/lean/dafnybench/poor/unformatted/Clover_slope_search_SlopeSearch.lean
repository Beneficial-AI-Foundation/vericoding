

/-!
{
"name": "Clover_slope_search_SlopeSearch",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_slope_search_SlopeSearch",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
SlopeSearch finds a key in a 2D array that is sorted both by rows and columns.
Translated from Dafny method SlopeSearch.

Parameters:
- a: 2D array of integers
- key: integer value to search for

Returns:
- (m,n): indices where key is found in array a

Requirements:
- Array is sorted in ascending order within each row
- Array is sorted in ascending order within each column
- Key exists somewhere in the array

Ensures:
- Returned indices are valid array bounds
- Element at returned indices equals key
-/
def SlopeSearch (a : Array (Array Int)) (key : Int) : Int × Int := sorry

/--
Specification for SlopeSearch method
-/
theorem SlopeSearch_spec (a : Array (Array Int)) (key : Int) :
(∀ i j j', 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < j' ∧ j' < a[i]!.size →
a[i]![j]! ≤ a[i]![j']!) →
(∀ i i' j, 0 ≤ i ∧ i < i' ∧ i' < a.size ∧ 0 ≤ j ∧ j < a[i]!.size →
a[i]![j]! ≤ a[i']![j]!) →
(∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a[i]!.size ∧ a[i]![j]! = key) →
let (m, n) := SlopeSearch a key
0 ≤ m ∧ m < a.size ∧ 0 ≤ n ∧ n < a[m.natAbs]!.size ∧ a[m.natAbs]![n.natAbs]! = key := sorry
