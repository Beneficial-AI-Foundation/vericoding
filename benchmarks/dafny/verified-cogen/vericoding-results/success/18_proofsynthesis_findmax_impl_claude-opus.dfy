// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindMax(nums: array<int>) returns (ret: int)
    requires nums.Length > 0
    ensures forall i :: 0 <= i < nums.Length ==> nums[i] <= ret
    ensures exists i :: 0 <= i < nums.Length && nums[i] == ret
// </vc-spec>
// <vc-code>
{
  ret := nums[0];
  var i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> nums[j] <= ret
    invariant exists j :: 0 <= j < i && nums[j] == ret
  {
    if nums[i] > ret {
      ret := nums[i];
    }
    i := i + 1;
  }
}
// </vc-code>
