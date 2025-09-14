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
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall a, b :: 0 <= a < i && 0 <= b < |nums| && a != b ==> nums[a] + nums[b] != target
  {
    var j := 0;
    while j < |nums|
      invariant 0 <= i < |nums|
      invariant 0 <= j <= |nums|
      invariant forall a, b :: (0 <= a < i && 0 <= b < |nums| && a != b) || (a == i && 0 <= b < j && a != b) ==> nums[a] + nums[b] != target
    {
      if i != j && nums[i] + nums[j] == target {
        pair := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
