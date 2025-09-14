// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function intMin(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method SmallestNum(nums: array<int>) returns (min: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> min <= nums[i]
    ensures exists i :: 0 <= i < nums.Length && min == nums[i]
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 0 <= idx < i
    invariant forall j :: 0 <= j < i ==> nums[idx] <= nums[j]
    decreases nums.Length - i
  {
    if nums[i] < nums[idx] {
      idx := i;
    }
    i := i + 1;
  }
  min := nums[idx];
}
// </vc-code>
