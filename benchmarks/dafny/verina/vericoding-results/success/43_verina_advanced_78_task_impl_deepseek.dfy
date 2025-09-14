// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma FindIndices(nums: array<int>, target: int)
  requires nums.Length > 1
  requires exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
{
}
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires
        nums.Length > 1 &&
        exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
    ensures
        0 <= result.0 < result.1 < nums.Length &&
        nums[result.0] + nums[result.1] == target
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := 1;
  while i < nums.Length - 1
    invariant 0 <= i < nums.Length
    invariant j == i + 1
    invariant forall k: int, l: int :: 0 <= k < i && k < l < nums.Length ==> nums[k] + nums[l] != target
  {
    while j < nums.Length
      invariant i < j <= nums.Length
      invariant forall l: int :: i < l < j ==> nums[i] + nums[l] != target
    {
      if nums[i] + nums[j] == target {
        result := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
    j := i + 1;
  }
}
// </vc-code>
