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
    s.map(|i: int, v: i32| v as int)
}
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: Seq<i32>, target: i32) -> (pair: (usize, usize))
    requires exists|i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int)
    ensures correct_pair((pair.0 as int, pair.1 as int), seq_i32_to_int(nums), target as int)
// </vc-spec>
// <vc-code>
{
    let nums_int = seq_i32_to_int(nums);
    let mut e_to_i: Map<i32, usize> = Map::empty();
    
    for i in 0usize..nums.len()
        invariant
            // All entries in the map come from nums[0..i]
            forall|e: i32| #[trigger] e_to_i.contains_key(e) ==> 
                exists|j: int| 0 <= j < i as int && nums[j as int] == e && e_to_i[e] == j as usize,
            // All elements in nums[0..i] that are keys in the map point to valid indices
            forall|j: int| 0 <= j < i as int && e_to_i.contains_key(nums[j as int]) ==> 
                e_to_i[nums[j as int]] < i && nums[e_to_i[nums[j as int]] as int] == nums[j as int],
            // If we haven't found a solution yet, it must involve an element at index >= i
            forall|i1: int, j1: int| 
                correct_pair((i1, j1), nums_int, target as int) ==> 
                    i1 >= i as int || j1 >= i as int,
    {
        let current_num = nums[i as int];
        let complement = target - current_num;
        
        if e_to_i.contains_key(complement) {
            let j = e_to_i[complement];
            
            // Prove that this is a correct pair
            proof {
                assert(nums[j as int] == complement);
                assert(nums[i as int] + nums[j as int] == target);
                assert(j < i);  // j was added before i
                assert(j != i);
                assert(nums_int[j as int] == nums[j as int] as int);
                assert(nums_int[i as int] == nums[i as int] as int);
                assert(correct_pair((j as int, i as int), nums_int, target as int));
            }
            
            return (j, i);
        }
        
        e_to_i = e_to_i.insert(current_num, i);
    }
    
    // This should be unreachable due to the precondition
    proof {
        // The precondition guarantees a solution exists
        let (i_sol, j_sol) = choose|i: int, j: int| 
            correct_pair((i, j), nums_int, target as int);
        
        // By the loop invariant, if we exit the loop normally,
        // any solution must have both indices >= nums.len()
        assert(i_sol >= nums.len() as int || j_sol >= nums.len() as int);
        
        // But correct_pair requires both indices < nums.len()
        assert(i_sol < nums.len() as int && j_sol < nums.len() as int);
        assert(false);
    }
    
    unreached()
}
// </vc-code>

fn main() {}

}