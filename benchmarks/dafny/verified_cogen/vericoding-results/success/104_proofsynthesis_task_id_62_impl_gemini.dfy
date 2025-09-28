// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SmallestNum(nums: array<int>) returns (min: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> min <= nums[i]
    ensures exists i :: 0 <= i < nums.Length && min == nums[i]
// </vc-spec>
// <vc-code>
{
  min := nums[0];
  var i: int := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall k :: 0 <= k < i ==> min <= nums[k]
    invariant exists k :: 0 <= k < i && min == nums[k]
  {
    if nums[i] < min {
      min := nums[i];
    }
    i := i + 1;
  }
}
// </vc-code>
