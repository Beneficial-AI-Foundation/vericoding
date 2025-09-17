

/-!
{
"name": "Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBinarySearch_binarySearch",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBinarySearch_binarySearch",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate indicating if an array is sorted in ascending order.
-/
def sorted (s : Array Int) : Prop :=
∀ u w : Nat, u < w → w < s.size → s[u]! ≤ s[w]!

/--
Binary search implementation that finds the position of an element in a sorted array.
Returns -1 if element not found.

Parameters:
- v: The sorted input array to search in
- elem: The element to search for

Returns:
- Position p such that all elements up to p are ≤ elem and all elements after p are > elem
-/
def binarySearch (v : Array Int) (elem : Int) : Int :=
sorry

/--
Specification for binary search:
1. Result is within valid bounds (-1 to array length-1)
2. All elements up to result are ≤ elem
3. All elements after result are > elem
-/


theorem binarySearch_spec (v : Array Int) (elem : Int) :
sorted v →
0 ≤ binarySearch v elem →
(∀ u : Nat, u ≤ Int.toNat (binarySearch v elem) ∧ u < v.size → v[u]! ≤ elem) ∧
(∀ w : Nat, Int.toNat (binarySearch v elem) < w ∧ w < v.size → v[w]! > elem) := sorry
