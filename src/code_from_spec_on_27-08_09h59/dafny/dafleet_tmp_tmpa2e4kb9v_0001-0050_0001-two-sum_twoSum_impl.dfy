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
lemma existence_lemma(nums: seq<int>, target: int)
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures exists i, j :: 0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target
{
}

ghost predicate valid_map_entry(e_to_i: map<int, int>, nums: seq<int>, k: int)
{
  k in e_to_i && 0 <= e_to_i[k] < |nums| && nums[e_to_i[k]] == k
}

ghost predicate map_contains_prefix(e_to_i: map<int, int>, nums: seq<int>, prefix_len: int)
  requires 0 <= prefix_len <= |nums|
{
  forall k :: k in e_to_i ==> exists i :: 0 <= i < prefix_len && nums[i] == k
}

ghost predicate map_valid_indices(e_to_i: map<int, int>, nums: seq<int>)
{
  forall k :: k in e_to_i ==> valid_map_entry(e_to_i, nums, k)
}

lemma map_index_bounds(e_to_i: map<int, int>, nums: seq<int>, complement: int, i: int)
  requires map_valid_indices(e_to_i, nums)
  requires map_contains_prefix(e_to_i, nums, i)
  requires complement in e_to_i
  requires 0 <= i <= |nums|
  ensures e_to_i[complement] < i
{
  assert valid_map_entry(e_to_i, nums, complement);
  assert complement in e_to_i;
  assert exists j :: 0 <= j < i && nums[j] == complement;
  var j := e_to_i[complement];
  assert 0 <= j < |nums| && nums[j] == complement;
  assert exists k :: 0 <= k < i && nums[k] == complement;
}

lemma loop_invariant_preserved(e_to_i: map<int, int>, nums: seq<int>, i: int, new_e_to_i: map<int, int>)
  requires 0 <= i < |nums|
  requires map_contains_prefix(e_to_i, nums, i)
  requires map_valid_indices(e_to_i, nums)
  requires new_e_to_i == e_to_i[nums[i] := i]
  ensures map_contains_prefix(new_e_to_i, nums, i + 1)
  ensures map_valid_indices(new_e_to_i, nums)
{
}

lemma termination_condition(nums: seq<int>, target: int, e_to_i: map<int, int>)
  requires exists i, j :: correct_pair((i, j), nums, target)
  requires map_contains_prefix(e_to_i, nums, |nums|)
  requires map_valid_indices(e_to_i, nums)
  requires forall k :: 0 <= k < |nums| ==> 
    (target - nums[k] in e_to_i ==> e_to_i[target - nums[k]] >= k)
  ensures false
{
  existence_lemma(nums, target);
  var i, j :| 0 <= i < |nums| && 0 <= j < |nums| && i != j && nums[i] + nums[j] == target;
  
  var min_idx := if i < j then i else j;
  var max_idx := if i < j then j else i;
  
  assert 0 <= min_idx < max_idx < |nums|;
  var complement := target - nums[min_idx];
  assert nums[max_idx] == complement;
  
  assert forall k :: k in e_to_i ==> exists idx :: 0 <= idx < |nums| && nums[idx] == k;
  assert exists idx :: 0 <= idx < |nums| && nums[idx] == complement;
  assert complement in e_to_i;
  
  assert e_to_i[complement] >= min_idx;
  assert nums[e_to_i[complement]] == complement;
  
  if e_to_i[complement] == min_idx {
    assert nums[min_idx] == complement;
    assert nums[min_idx] + nums[max_idx] == target;
    assert 2 * nums[min_idx] == target;
  } else {
    assert e_to_i[complement] > min_idx;
    assert e_to_i[complement] < |nums|;
    assert e_to_i[complement] != min_idx;
    assert nums[min_idx] + nums[e_to_i[complement]] == target;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var e_to_i: map<int, int> := map[];
  
  for i := 0 to |nums|
    invariant 0 <= i <= |nums|
    invariant map_contains_prefix(e_to_i, nums, i)
    invariant map_valid_indices(e_to_i, nums)
    invariant forall k :: 0 <= k < i ==> 
      (target - nums[k] in e_to_i ==> e_to_i[target - nums[k]] >= k)
  {
    var complement := target - nums[i];
    
    if complement in e_to_i {
      var j := e_to_i[complement];
      assert nums[j] == complement;
      assert nums[i] + nums[j] == target;
      assert 0 <= i < |nums|;
      map_index_bounds(e_to_i, nums, complement, i);
      return (j, i);
    }
    
    e_to_i := e_to_i[nums[i] := i];
    loop_invariant_preserved(e_to_i[nums[i] := i], nums, i, e_to_i);
  }
  
  termination_condition(nums, target, e_to_i);
  return (0, 0);
}
// </vc-code>
