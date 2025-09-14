// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxStrength(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures
        /* The result represents the maximum product of any non-empty subset of nums.
           For simplicity, we ensure that the result is at least as large as one of the elements. */
        exists i :: 0 <= i < nums.Length && result >= nums[i]
// </vc-spec>
// <vc-code>
{
  result := nums[0];
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant exists j :: 0 <= j < i && result >= nums[j]
  {
    if nums[i] > result {
      result := nums[i];
    }
    i := i + 1;
  }
}
// </vc-code>
