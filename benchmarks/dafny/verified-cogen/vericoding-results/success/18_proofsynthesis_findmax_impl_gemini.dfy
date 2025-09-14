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
    var max_index := 0;
    var i := 1;
    while i < nums.Length
      invariant 1 <= i <= nums.Length
      invariant 0 <= max_index < i
      invariant ret == nums[max_index]
      invariant forall k :: 0 <= k < i ==> nums[k] <= ret
    {
        if nums[i] > ret {
            ret := nums[i];
            max_index := i;
        }
        i := i + 1;
    }
}
// </vc-code>
