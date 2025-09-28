// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxArray(nums: array<int>) returns (idx: int)
    requires
        nums.Length >= 1
    ensures
        0 <= idx && idx < nums.Length &&
        forall i :: 0 <= i && i < nums.Length ==> nums[i] <= nums[idx]
// </vc-spec>
// <vc-code>
{
  idx := 0;
  var j := 1;
  while j < nums.Length
    invariant 0 <= idx < nums.Length
    invariant 1 <= j <= nums.Length
    invariant forall i :: 0 <= i < j ==> nums[i] <= nums[idx]
  {
    if nums[j] > nums[idx] {
      idx := j;
    }
    j := j + 1;
  }
}
// </vc-code>
