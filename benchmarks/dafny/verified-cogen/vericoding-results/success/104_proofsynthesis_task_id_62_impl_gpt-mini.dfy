// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SmallestNum(nums: array<int>) returns (min: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> min <= nums[i]
    ensures exists i :: 0 <= i < nums.Length && min == nums[i]
// </vc-spec>
// <vc-code>
{
  var i := 1;
  min := nums[0];
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> min <= nums[j]
    invariant exists k :: 0 <= k < i && min == nums[k]
  {
    if nums[i] < min {
      min := nums[i];
    }
    i := i + 1;
  }
}
// </vc-code>
