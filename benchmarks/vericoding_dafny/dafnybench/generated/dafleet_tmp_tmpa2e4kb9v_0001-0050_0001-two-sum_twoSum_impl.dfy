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

// <vc-helpers>
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
    // The map contains mappings for elements we've seen so far
    invariant forall val :: val in e_to_i ==> exists idx :: 0 <= idx < i && nums[idx] == val
    invariant forall idx :: 0 <= idx < i ==> nums[idx] in e_to_i
    // The map maps values to valid indices
    invariant forall val :: val in e_to_i ==> 0 <= e_to_i[val] < i
    // The map correctly maps values to their indices
    invariant forall val :: val in e_to_i ==> nums[e_to_i[val]] == val
    // If we haven't found a solution yet, no pair in processed elements sums to target
    invariant forall i1, i2 :: 0 <= i1 < i && 0 <= i2 < i && i1 != i2 ==> nums[i1] + nums[i2] != target
  {
    var complement := target - nums[i];
    
    if complement in e_to_i {
      var j := e_to_i[complement];
      // At this point we know:
      // - j = e_to_i[complement]
      // - 0 <= j < i (from invariant)
      // - nums[j] == complement (from invariant)
      // - complement + nums[i] == target (by definition of complement)
      // - j != i (since j < i)
      pair := (j, i);
      return;
    }
    
    e_to_i := e_to_i[nums[i] := i];
    i := i + 1;
  }
  
  // This point should never be reached due to the precondition
  assert false;
}
// </vc-code>

/* Discussions
  but this is wrong, because `nums` may contain redundant elements.
  Redundant elements will share the same key in `e_to_i`, the newer overwriting the older.

  To specify a set/map, we often need "back and forth" assertions, namely:
  (a) What elements are in the map/set (like in formula A)
  (b) What do elements in the set/map satisfy (like in formula B)
*/