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
    var max_val := nums[0];
    var i := 1;
    while i < nums.Length
        invariant 0 < i <= nums.Length
        invariant forall j :: 0 <= j < i ==> nums[j] <= max_val
        invariant exists j :: 0 <= j < i && nums[j] == max_val
    {
        if nums[i] > max_val {
            max_val := nums[i];
        }
        i := i + 1;
    }
    ret := max_val;
}
// </vc-code>
