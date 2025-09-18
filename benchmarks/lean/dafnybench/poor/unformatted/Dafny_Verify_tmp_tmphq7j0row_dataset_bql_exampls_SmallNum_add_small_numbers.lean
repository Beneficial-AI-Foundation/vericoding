

/-!
{
"name": "Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_SmallNum_add_small_numbers",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_SmallNum_add_small_numbers",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translates the Dafny method add_small_numbers which adds numbers from an array up to index n,
where each number is bounded by max.

@param a The input array of integers
@param n The number of elements to process
@param max The maximum value allowed in the array
@return The sum of the first n elements
-/
def add_small_numbers (a : Array Int) (n : Int) (max : Int) : Int := sorry

/--
Specification for add_small_numbers method ensuring:
1. n is positive
2. n is within array bounds
3. all elements up to n are bounded by max
4. result is bounded by max * n
-/
theorem add_small_numbers_spec (a : Array Int) (n : Int) (max : Int) (r : Int) :
n > 0 ∧
n ≤ a.size ∧
(∀ i : Nat, i < n → a[i]! ≤ max) →
r ≤ max * n := sorry
