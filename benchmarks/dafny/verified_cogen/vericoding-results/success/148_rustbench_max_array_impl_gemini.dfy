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
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 0 <= idx < nums.Length
    invariant forall k :: 0 <= k < i ==> nums[k] <= nums[idx]
  {
    if nums[i] > nums[idx] {
      idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
