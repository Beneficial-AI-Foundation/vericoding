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

spec fn has_key<K, V>(m: Map<K, V>, k: K) -> bool {
    m.dom().contains(k)
}

proof fn map_insert_preserves_dom<K, V>(m: Map<K, V>, k: K, v: V)
    ensures m.insert(k, v).dom() == m.dom().insert(k)
{
}

proof fn map_insert_contains_key<K, V>(m: Map<K, V>, k: K, v: V)
    ensures has_key(m.insert(k, v), k)
{
}

proof fn map_insert_other_keys_unchanged<K, V>(m: Map<K, V>, k1: K, v: V, k2: K)
    requires k1 != k2
    ensures m.insert(k1, v).index(k2) == m.index(k2)
{
}

spec fn valid_pair_for_target(nums: Seq<int>, target: int, i: int, j: int) -> bool {
    0 <= i < nums.len() &&
    0 <= j < nums.len() &&
    i != j &&
    nums[i] + nums[j] == target
}

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    let (i, j) = pair;
    &&& 0 <= i < nums.len()
    &&& 0 <= j < nums.len()
    &&& i != j
    &&& nums[i] + nums[j] == target
}
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: Seq<i32>, target: i32) -> (pair: (usize, usize))
    requires exists|i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int)
    ensures correct_pair((pair.0 as int, pair.1 as int), seq_i32_to_int(nums), target as int)
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    let mut e_to_i: Map<int, usize> = Map::empty();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| has_key(e_to_i, k) ==> (0 <= e_to_i[k] as int && e_to_i[k] as int < i),
            forall|k: int| has_key(e_to_i, k) ==> seq_i32_to_int(nums)[e_to_i[k] as int] == k
    {
        let current = nums[i] as int;
        let complement = target as int - current;
        
        if has_key(e_to_i, complement) {
            let j_index = e_to_i[complement];
            proof {
                assert(seq_i32_to_int(nums)[j_index as int] == complement);
                assert(seq_i32_to_int(nums)[i as int] == current);
                assert(complement + current == target as int);
                assert(j_index != i);
            }
            return (j_index, i);
        }
        
        e_to_i = e_to_i.insert(current, i);
        i = i + 1;
    }
    
    proof {
        assert(false);
    }
    (0, 0)
}
// </vc-code>

fn main() {}

}