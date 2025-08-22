// SPEC

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `seq` were Python list
// - `map` were Python dict
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
 requires exists i, j :: correct_pair((i, j), nums, target)
 ensures correct_pair(pair, nums, target)
{
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
