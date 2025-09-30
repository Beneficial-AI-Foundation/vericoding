// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  while i < nums.Length - 1
    invariant 0 <= i < nums.Length
    invariant forall x, y :: 0 <= x < i && x < y < nums.Length ==> nums[x] + nums[y] != target
  {
    var j := i + 1;
    while j < nums.Length
      invariant i + 1 <= j <= nums.Length
      invariant forall y :: i + 1 <= y < j ==> nums[i] + nums[y] != target
    {
      if nums[i] + nums[j] == target {
        result := (i, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert false;
}
// </vc-code>
