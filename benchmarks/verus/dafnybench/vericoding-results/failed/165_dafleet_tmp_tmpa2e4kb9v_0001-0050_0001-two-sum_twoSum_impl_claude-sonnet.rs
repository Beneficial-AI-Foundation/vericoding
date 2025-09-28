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
    s.map(|i, v| v as int)
}

spec fn map_contains_nums_up_to(e_to_i: Map<i32, usize>, nums: Seq<i32>, k: int) -> bool {
    forall|i: int| 0 <= i < k ==> #[trigger] e_to_i.contains_key(nums[i])
}

spec fn map_values_are_valid_indices(e_to_i: Map<i32, usize>, nums: Seq<i32>) -> bool {
    forall|key: i32| e_to_i.contains_key(key) ==> {
        let idx = e_to_i[key];
        &&& idx < nums.len()
        &&& nums[idx as int] == key
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
    let mut e_to_i: Map<i32, usize> = Map::empty();
    let mut i: usize = 0;
    
    while i < nums.len() as usize
        invariant
            i <= nums.len(),
            map_contains_nums_up_to(e_to_i, nums, i as int),
            map_values_are_valid_indices(e_to_i, nums),
    {
        let complement = target - nums[i];
        
        if e_to_i.contains_key(complement) {
            let j = e_to_i.index(complement);
            
            proof {
                assert(j < nums.len());
                assert(nums[j as int] == complement);
                assert(nums[j as int] + nums[i as int] == target as int);
                assert(j != i);
            }
            
            return (j, i);
        }
        
        e_to_i = e_to_i.insert(nums[i], i);
        i += 1;
    }
    
    // This should be unreachable given the precondition
    assert(false);
    (0, 0)
}
// </vc-code>

fn main() {}

}