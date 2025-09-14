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
lemma exists_correct_pair_lemma(nums: seq<int>, target: int)
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures exists i, j :: 0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target
{
}

ghost predicate valid_map(e_to_i: map<int, int>, nums: seq<int>, k: int)
  requires 0 <= k <= |nums|
{
  forall i :: 0 <= i < k ==> nums[i] in e_to_i
}

ghost predicate map_indices_valid(e_to_i: map<int, int>, nums: seq<int>)
{
  forall e :: e in e_to_i ==> 0 <= e_to_i[e] < |nums| && nums[e_to_i[e]] == e
}

ghost predicate map_indices_less_than(e_to_i: map<int, int>, k: int)
{
  forall e :: e in e_to_i ==> e_to_i[e] < k
}

ghost predicate no_early_solution(nums: seq<int>, target: int, k: int)
  requires 0 <= k <= |nums|
{
  forall i, j :: 0 <= i < k && 0 <= j < k && i != j ==> nums[i] + nums[j] != target
}

lemma solution_exists_implies_future_solution(nums: seq<int>, target: int, k: int)
  requires 0 <= k < |nums|
  requires exists i, j :: correct_pair((i, j), nums, target)
  requires no_early_solution(nums, target, k)
  ensures exists i, j :: k <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target
{
  assert exists i, j :: 0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target;
  
  var wit_i, wit_j :| 0 <= wit_i < |nums| && 0 <= wit_j < |nums| && wit_i != wit_j && nums[wit_i] + nums[wit_j] == target;
  
  if wit_i >= k {
    assert k <= wit_i < |nums| && 0 <= wit_j < |nums| && wit_i != wit_j && nums[wit_i] + nums[wit_j] == target;
  } else if wit_j >= k {
    assert k <= wit_j < |nums| && 0 <= wit_i < |nums| && wit_j != wit_i && nums[wit_j] + nums[wit_i] == target;
  } else {
    assert 0 <= wit_i < k && 0 <= wit_j < k && wit_i != wit_j;
    assert nums[wit_i] + nums[wit_j] == target;
    assert false;
  }
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
  
  for i := 0 to |nums|
    invariant 0 <= i <= |nums|
    invariant valid_map(e_to_i, nums, i)
    invariant map_indices_valid(e_to_i, nums)
    invariant map_indices_less_than(e_to_i, i)
    invariant no_early_solution(nums, target, i)
  {
    var complement := target - nums[i];
    if complement in e_to_i {
      var j := e_to_i[complement];
      assert nums[j] == complement;
      assert nums[i] + nums[j] == target;
      assert j < i;
      assert i != j;
      return (j, i);
    }
    e_to_i := e_to_i[nums[i] := i];
  }
  
  solution_exists_implies_future_solution(nums, target, |nums|);
  assert false;
}
// </vc-code>

