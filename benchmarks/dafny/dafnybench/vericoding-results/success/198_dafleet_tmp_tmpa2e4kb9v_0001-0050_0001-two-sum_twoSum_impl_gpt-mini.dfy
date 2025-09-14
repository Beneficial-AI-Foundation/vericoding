/* https://leetcode.com/problems/two-sum/
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.
You may assume that each input would have exactly one solution, and you may not use the same element twice.
You can return the answer in any order.

Example 1:
Input: nums = [2,7,11,15], target = 9
Output: [0,1]
Explanation: Because nums[0] + nums[1] == 9, we return [0, 1].
*/


ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  && 0 <= i < |nums|
  && 0 <= j < |nums|
  && i != j  // "you may not use the same element twice"
  && nums[i] + nums[j] == target
}

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `seq` were Python list
// - `map` were Python dict

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

// </vc-helpers>

// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
// </vc-spec>
// <vc-code>
{
  var n := |nums|;
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < i && 0 <= b < n && a != b ==> nums[a] + nums[b] != target
  {
    var j := i + 1;
    while j < n
      decreases n - j
      invariant i + 1 <= j <= n
      invariant forall a, b :: 0 <= a < i && 0 <= b < n && a != b ==> nums[a] + nums[b] != target
      invariant forall b0 :: i + 1 <= b0 < j ==> nums[i] + nums[b0] != target
    {
      if nums[i] + nums[j] == target {
        pair := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  // If we reach here, we have shown no distinct indices form the target sum.
  assert forall a, b :: 0 <= a < n && 0 <= b < n && a != b ==> nums[a] + nums[b] != target;
  // But the precondition guarantees existence of a correct pair; extract ghost witnesses to derive contradiction.
  ghost var gi, gj :| correct_pair((gi, gj), nums, target);
  // From the invariant we have nums[gi] + nums[gj] != target, contradicting correct_pair.
  assert nums[gi] + nums[gj] != target;
  assert false;
}
// </vc-code>

