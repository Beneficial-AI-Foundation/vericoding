/* https://leetcode.com/problems/two-sum/
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.
You may assume that each input would have exactly one solution, and you may not use the same element twice.
You can return the answer in any order.

Example 1:
Input: nums = [2,7,11,15], target = 9
Output: [0,1]
Explanation: Because nums[0] + nums[1] == 9, we return [0, 1].
*/

//ATOM 

ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  && 0 <= i < |nums|
  && 0 <= j < |nums|
  && i != j  // "you may not use the same element twice"
  && nums[i] + nums[j] == target
}

//IMPL 

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `seq` were Python list
// - `map` were Python dict
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
{
  var e_to_i: map<int, int> := map[];
  
  for i := 0 to |nums|
    /* code modified by LLM (iteration 1): Fixed loop invariants to ensure termination and correctness */
    invariant forall k :: k in e_to_i ==> exists i' :: 0 <= i' < i && nums[i'] == k
    invariant forall k :: k in e_to_i ==> 0 <= e_to_i[k] < i && nums[e_to_i[k]] == k
    invariant forall i1, i2 :: 0 <= i1 < i2 < i && nums[i1] + nums[i2] == target ==> (target - nums[i2]) !in e_to_i || e_to_i[target - nums[i2]] != i1
  {
    var complement := target - nums[i];
    if complement in e_to_i {
      var j := e_to_i[complement];
      /* code modified by LLM (iteration 1): Added assertions to help verification */
      assert nums[j] == complement;
      assert nums[j] + nums[i] == target;
      assert 0 <= j < i < |nums|;
      assert j != i;
      pair := (j, i);
      return;
    }
    e_to_i := e_to_i[nums[i] := i];
  }
}

/* Discussions
1. It may be tempting to append `&& e_to_i[nums[i']] == i'` to the invariant (formula A),
  but this is wrong, because `nums` may contain redundant elements.
  Redundant elements will share the same key in `e_to_i`, the newer overwriting the older.
  
2. Tip: Generally, we often need invariants when copying data from a container to another.
  To specify a set/map, we often need "back and forth" assertions, namely:
  (a) What elements are in the map/set (like in formula A)
  (b) What do elements in the set/map satisfy (like in formula B)
*/