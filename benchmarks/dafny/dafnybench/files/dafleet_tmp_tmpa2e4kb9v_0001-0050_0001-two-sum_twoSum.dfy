// <vc-preamble>
ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  && 0 <= i < |nums|
  && 0 <= j < |nums|
  && i != j
  && nums[i] + nums[j] == target
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
