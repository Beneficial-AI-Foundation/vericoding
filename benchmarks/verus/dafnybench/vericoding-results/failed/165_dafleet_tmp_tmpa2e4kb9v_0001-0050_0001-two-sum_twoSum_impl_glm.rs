use vstd::prelude::*;

verus! {

/* https://leetcode.com/problems/two-sum/
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.
You may assume that each input would have exactly one solution, and you may not use the same element twice.
You can return the answer in any order.

Example 1:
Input: nums = [2,7,11,15], target = 9
Output: [0,1]
Explanation: Because nums[0] + nums[1] == 9, we return [0, 1].
*/


spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    let (i, j) = pair;
    &&& 0 <= i < nums.len()
    &&& 0 <= j < nums.len()
    &&& i != j  // "you may not use the same element twice"
    &&& nums[i] + nums[j] == target
}

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `Seq` were Python list
// - `Map` were Python dict

/* Discussions
1. It may be tempting to append `&& e_to_i[nums[i']] == i'` to the invariant (formula A),
  but this is wrong, because `nums` may contain redundant elements.
  Redundant elements will share the same key in `e_to_i`, the newer overwriting the older.

2. Tip: Generally, we often need invariants when copying data from a container to another.
  To specify a set/map, we often need "back and forth" assertions, namely:
  (a) What elements are in the map/set (like in formula A)
  (b) What do elements in the set/map satisfy (like in formula B)
*/

// <vc-helpers>
spec fn seq_i32_to_int(s: Seq<i32>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[i] as int)
}

proof fn lemma_exists_ordered_pair_to_indices(
    nums: Seq<i32>,
    target: i32,
) -> (pair: (int, int))
    requires exists|i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int)
    ensures 
        correct_pair(pair, seq_i32_to_int(nums), target as int),
        pair.0 < pair.1
{
    reveal(seq_i32_to_int);
    let (i, j) = choose |i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int);
    if i < j {
        (i, j)
    } else {
        (j, i)
    }
}
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: Seq<i32>, target: i32) -> (pair: (usize, usize))
    requires exists|i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int)
    ensures correct_pair((pair.0 as int, pair.1 as int), seq_i32_to_int(nums), target as int)
// </vc-spec>
// <vc-code>
{
    let target_int = target as int;
    reveal(seq_i32_to_int);
    
    let ghost i_witness: int = 0;
    let ghost j_witness: int = 0;
    proof {
        let temp = lemma_exists_ordered_pair_to_indices(nums, target);
        i_witness = temp.0;
        j_witness = temp.1;
    }
    
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            i_witness >= i as int,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i+1 <= j <= nums.len(),
                i_witness >= i as int,
                (i_witness == i as int ==> j_witness >= j as int),
        {
            if nums[i] + nums[j] == target {
                ghost {
                    assert(correct_pair((i as int, j as int), seq_i32_to_int(nums), target_int));
                }
                return (i, j);
            }
            j += 1;
        }
        i += 1;
    }
    
    ghost {
        assert(i_witness < nums.len() as int);
        assert(i_witness >= i as int);
        assert(i == nums.len());
        assert(i_witness >= nums.len() as int);
    }
    assert(false);
    (0, 0)
}
// </vc-code>

fn main() {}

}