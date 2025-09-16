

/-!
{
"name": "Software-Verification_tmp_tmpv4ueky2d_Non-overlapping Intervals_non_overlapping_intervals_bubble_sort",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Software-Verification_tmp_tmpv4ueky2d_Non-overlapping Intervals_non_overlapping_intervals_bubble_sort",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Represents a 2D array with fixed second dimension of 2.
This simplifies the Dafny array2 type for our purposes.
-/
structure Array2D (α : Type) where
data : Array (Array α)
dim1_eq_2 : ∀ arr ∈ data, arr.size = 2

/--
Predicate indicating if a 2D array is sorted based on second column values
between indices l and u inclusive.
-/
def sorted (a : Array2D Int) (l u : Int) : Prop :=
∀ i j:Nat, 0 ≤ l → l ≤ i → i ≤ j → j ≤ u → u < a.data.size →
(a.data[i]!)[1]! ≤ (a.data[j]!)[1]!

/--
Predicate indicating if a 2D array is partitioned at index i,
meaning all elements before i are less than or equal to all elements after i
based on second column values.
-/
def partitioned (a : Array2D Int) (i : Int) : Prop :=
∀ k k':Nat, 0 ≤ k → k ≤ i → i < k' → k' < a.data.size →
(a.data[k]!)[1]! ≤ (a.data[k']!)[1]!

/--
Bubble sort implementation for 2D arrays.
Sorts based on the second column values.
-/
def bubble_sort (a : Array2D Int) : Array2D Int := sorry

/--
Specification for bubble_sort method.
Ensures the result is sorted on second column values.
-/
theorem bubble_sort_spec (a : Array2D Int) :
sorted (bubble_sort a) 0 (a.data.size - 1) := sorry
