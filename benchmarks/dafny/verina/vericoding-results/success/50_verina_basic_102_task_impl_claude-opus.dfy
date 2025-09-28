// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: (int, int))
    requires 
        nums.Length > 1 &&
        (exists i: int, j: int :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures
        0 <= result.0 < result.1 < nums.Length &&
        nums[result.0] + nums[result.1] == target &&
        (forall i: int, j: int :: 0 <= i < j < nums.Length && i < result.0 ==> nums[i] + nums[j] != target)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < nums.Length - 1
    invariant 0 <= i < nums.Length
    invariant forall k: int, j: int :: 0 <= k < j < nums.Length && k < i ==> nums[k] + nums[j] != target
  {
    var j := i + 1;
    while j < nums.Length
      invariant i + 1 <= j <= nums.Length
      invariant forall k: int :: i + 1 <= k < j ==> nums[i] + nums[k] != target
      invariant forall k: int, m: int :: 0 <= k < j && k < i && i + 1 <= m < j ==> nums[k] + nums[m] != target
    {
      if nums[i] + nums[j] == target {
        return (i, j);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert false;
}
// </vc-code>
