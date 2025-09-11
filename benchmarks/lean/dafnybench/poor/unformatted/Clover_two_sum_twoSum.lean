

/-!
{
"name": "Clover_two_sum_twoSum",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_two_sum_twoSum",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds two indices i,j in an array such that nums + nums = target.
Translated from Dafny method twoSum.

@param nums The input array of integers
@param target The target sum to find
@return A pair of indices (i,j) that sum to target
-/
def twoSum (nums : Array Int) (target : Int) : Int × Int := sorry

/--
Specification for twoSum method ensuring:
1. Array has at least 2 elements
2. Solution exists in array
3. Returns valid indices i,j where nums + nums = target
4. No solution exists before index i
5. No solution exists between i and j
-/
theorem twoSum_spec (nums : Array Int) (target : Int) :
nums.size > 1 →
(∃ i j, 0 ≤ i ∧ i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target) →
let (i, j) := twoSum nums target
0 ≤ i ∧ i < j ∧ j < nums.size ∧ nums[i.toNat]! + nums[j.toNat]! = target ∧
(∀ ii jj, 0 ≤ ii ∧ ii < i ∧ ii < jj ∧ jj < nums.size → nums[ii.toNat]! + nums[jj.toNat]! ≠ target) ∧
(∀ jj, i < jj ∧ jj < j → nums[i.toNat]! + nums[jj.toNat]! ≠ target) := sorry