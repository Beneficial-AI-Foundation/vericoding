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
ghost predicate no_solution_in_range(nums: seq<int>, target: int, end: int)
  requires 0 <= end <= |nums|
{
  forall i', j' :: 0 <= i' < end && 0 <= j' < end && i' != j' ==> nums[i'] + nums[j'] != target
}
// </vc-helpers>

// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
// </vc-spec>
// <vc-code>
{
  var e_to_i: map<int, int> := map[];
  var i := 0;
  
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall k :: k in e_to_i ==> exists i' :: 0 <= i' < i && nums[i'] == k && e_to_i[k] == i'
    invariant forall i' :: 0 <= i' < i ==> nums[i'] in e_to_i
    invariant no_solution_in_range(nums, target, i)
    invariant exists i', j' :: i <= i' < |nums| && 0 <= j' < |nums| && i' != j' && nums[i'] + nums[j'] == target
  {
    var complement := target - nums[i];
    if complement in e_to_i && e_to_i[complement] != i {
      return (e_to_i[complement], i);
    }
    e_to_i := e_to_i[nums[i] := i];
    i := i + 1;
  }
  
  // This should be unreachable due to the precondition
  return (0, 0);
}
// </vc-code>

