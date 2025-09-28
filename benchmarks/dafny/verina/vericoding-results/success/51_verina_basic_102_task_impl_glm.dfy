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
  var i: int := 0;
  while i < nums.Length - 1
    invariant 0 <= i <= nums.Length - 1
    invariant forall i1: int, j1: int :: 0 <= i1 < j1 < nums.Length && i1 < i ==> nums[i1] + nums[j1] != target
    decreases nums.Length - i
  {
    var j: int := i + 1;
    while j < nums.Length
      invariant i+1 <= j <= nums.Length
      invariant forall j1: int :: i+1 <= j1 < j ==> nums[i] + nums[j1] != target
      decreases nums.Length - j
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
