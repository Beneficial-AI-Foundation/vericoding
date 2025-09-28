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

// Helper predicates for the invariant
// (A) What elements are in the map
// For all indices `i'` from `0` to `i-1`, if `nums[i']` is a key in `e_to_i`,
// then `e_to_i[nums[i']]` is `i'`.
spec fn known_elements_in_map(i: int, nums_int: Seq<int>, e_to_i: Map<int, int>) -> bool {
    forall |k: int| #[trigger] e_to_i.dom().contains(k) ==>
        exists |idx: int| 0 <= idx < i && nums_int[idx] == k && e_to_i[k] == idx
}

// (B) What do elements in the map satisfy
// For all keys `k` in `e_to_i`, its value `e_to_i[k]` is an index `idx` such that
// `0 <= idx < i` and `nums_int[idx] == k`.
spec fn map_elements_satisfy_condition(i: int, nums_int: Seq<int>, e_to_i: Map<int, int>) -> bool {
    forall |k: int| #[trigger] e_to_i.dom().contains(k) ==>
        0 <= e_to_i[k] < i && nums_int[e_to_i[k]] == k
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
    let target_int = target as int;

    let mut e_to_i: Map<int, int> = Map::empty(); // Map from element value to its index

    let mut i: int = 0;

    while (i < nums_int.len())
        invariant
            0 <= i <= nums_int.len(),
            known_elements_in_map(i, nums_int, e_to_i),
            map_elements_satisfy_condition(i, nums_int, e_to_i),
            e_to_i.dom().finite(),
            nums_int.len() == nums.len(),
    {
        let current_num = nums_int[i];
        let complement = target_int - current_num;

        if (e_to_i.dom().contains(complement)) {
            let other_idx = e_to_i[complement];
            // Found a pair!
            return (other_idx as usize, i as usize);
        }

        let old_e_to_i = e_to_i; // Save the old map for proving invariants
        e_to_i = e_to_i.insert(current_num, i);

        proof {
            // Prove known_elements_in_map for the next iteration
            assert forall |k: int| #[trigger] e_to_i.dom().contains(k) implies
                exists |idx: int| 0 <= idx < i + 1 && nums_int[idx] == k && e_to_i[k] == idx
            by {
                if k == current_num {
                    assert(e_to_i[current_num] == i);
                    assert(0 <= i);
                    assert(i < i + 1);
                    assert(nums_int[i] == current_num);
                } else {
                    assert(old_e_to_i.dom().contains(k));
                    assert(known_elements_in_map(i, nums_int, old_e_to_i));
                    assert(exists |idx: int| 0 <= idx < i && nums_int[idx] == k && old_e_to_i[k] == idx);
                    let idx = old_e_to_i[k];
                    assert(0 <= idx);
                    assert(idx < i);
                    assert(idx < i + 1);
                    assert(nums_int[idx] == k);
                    assert(e_to_i[k] == old_e_to_i[k]);
                }
            }

            // Prove map_elements_satisfy_condition for the next iteration
            assert forall |k: int| #[trigger] e_to_i.dom().contains(k) implies
                0 <= e_to_i[k] < i + 1 && nums_int[e_to_i[k]] == k
            by {
                if k == current_num {
                    assert(e_to_i[current_num] == i);
                    assert(0 <= i);
                    assert(i < i + 1);
                    assert(nums_int[i] == current_num);
                } else {
                    assert(old_e_to_i.dom().contains(k));
                    assert(map_elements_satisfy_condition(i, nums_int, old_e_to_i));
                    let idx = old_e_to_i[k];
                    assert(0 <= idx);
                    assert(idx < i);
                    assert(idx < i + 1); // This inequality is crucial for the new invariant step.
                    assert(nums_int[idx] == k);
                    assert(e_to_i[k] == old_e_to_i[k]);
                }
            }
        }

        i = i + 1;
    }

    unreachable!();
}
// </vc-code>

fn main() {}

}