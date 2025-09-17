

/-!
{
"name": "630-dafny_tmp_tmpz2kokaiq_Solution_BinarySearch",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: 630-dafny_tmp_tmpz2kokaiq_Solution_BinarySearch",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if an arr ay is sorted in ascending order.
Translated from Dafny's sorted function.
-/
def sorted (a : Array Int) : Prop :=
∀ i j , 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!

/--
Binary search implementation specification.
Translated from Dafny's BinarySearch method.

@param a The sorted array to search in
@param x The value to search for
@return index The index where x was found, or -1 if not found
-/
def BinarySearch (a : Array Int) (x : Int) : Int := sorry

/--
Specification for BinarySearch method.
-/
theorem BinarySearch_spec (a : Array Int) (x : Int) :
sorted a →
let index := BinarySearch a x
(0 ≤ index ∧ index < a.size → a[index.toNat]! = x) ∧
(index = -1 → ∀ i , 0 ≤ i ∧ i < a.size → a[i]! ≠ x) := sorry
